{-
 -  Core/Reason.hs -- handle individual proof tasks
 -  Copyright (c) 2001,2004,2007   Andrei Paskevich <atertium@gmail.com>
 -
 -  This file is part of SAD/Alice - a mathematical text verifier.
 -
 -  SAD/Alice is free software; you can redistribute it and/or modify
 -  it under the terms of the GNU General Public License as published by
 -  the Free Software Foundation; either version 3 of the License, or
 -  (at your option) any later version.
 -
 -  SAD/Alice is distributed in the hope that it will be useful,
 -  but WITHOUT ANY WARRANTY; without even the implied warranty of
 -  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 -  GNU General Public License for more details.
 -
 -  You should have received a copy of the GNU General Public License
 -  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 -}

module Alice.Core.Reason where

import Control.Monad

import Alice.Core.Base
import Alice.Core.Info
import Alice.Core.Unfold
import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Instr
import Alice.Data.Text
import Alice.Export.Prover

-- Reasoner

reason :: [Context] -> Context -> RM ()
reason cnt tc = do  flt <- askRSIB IBfilt True
                    dfl <- askRSIB IBchck True
                    let nct = context (flt && dfl) cnt tc
                    n <- askRSII IIdpth 7 ; guard $ n > 0
                    goalseq n nct tc $ splitG $ cnForm tc

goalseq :: Int -> [Context] -> Context -> [Formula] -> RM ()
goalseq n cnt tc (f:fs) = do  trv <> launch cnt ntc <> dlp
                              goalseq n (ntc : cnt) tc fs
  where
    rfr = reduce f
    ntc = setForm tc rfr

    trv = sbg >> guard (isTop rfr) >> incRSCI CIsubt

    dlp | n == 1  = rde >> mzero
        | True    = do  tsk <- unfold $ setForm tc (Not rfr) : cnt
                        let Context {cnForm = Not nfr} : nct = tsk
                        goalseq (pred n) nct tc $ splitG nfr

    rde = whenIB IBPrsn False $ rlog0 $ "reasoning depth exceeded"
    sbg = whenIB IBPrsn False $ rlog0 $ tri ++ "subgoal: " ++ show f
    tri = if (isTop rfr) then "trivial " else ""

goalseq _ _ _ _ = return ()


-- Call prover

launch :: [Context] -> Context -> RM ()
launch cnt tc = do  incRSCI CIprov; whenIB IBPtsk False debug
                    prd <- askRS rsPrdb ; ins <- askRS rsInst
                    let ext = justIO $ export prd ins cnt tc
                    ext >>= timer CTprov . justIO >>= guard
                    whenIB IBPrsn False $ rlog0 $ "...proved"
                    CntrT _ td <- liftM head $ askRS rsCntr
                    addRSTI CTprvy td ; incRSCI CIprvy
  where
    debug = do  rlog0 "prover task:"
                let tlb = map cnForm $ reverse cnt
                mapM_ ((putStrRM "  " >>) . printRM) tlb
                putStrRM "  |- " ; printRM $ cnForm tc


-- Goal splitting

splitG :: Formula -> [Formula]
splitG fr = spl $ albet $ strip fr
  where
    spl (All u f) = liftM (All u) (splitG f)
    spl (And f g) = mplus (splitG f) (splitG g)
    spl (Or f g)  = liftM2 zOr (splitG f) (splitG g)
    spl _         = return fr


-- Context filtering

context :: Bool -> [Context] -> Context -> [Context]
context df cnt tc = filter (not . isTop . cnForm) $ map chk cnt
  where
    chk c | cnLowL c  = c
          | lht       = setForm c $ lichten 0 f
          | dhd       = setForm c $ adroite 0 f
          | otherwise = c
      where
        lht | null ls = df && defn
            | True    = cnName c `notElem` ls

        dhd = defn || sign ; f = cnForm c
        defn = isDefn f ; sign = isSign f

    ls = cnLink tc

adroite :: Int -> Formula -> Formula
adroite n = sr
  where
    sr (All _ (Iff (Tag DHD (Trm "=" [_, t] _)) f))
        | isEqu f   = safeSubst t "" $ inst "" f
    sr (All _ (Imp (Tag DHD (Trm "=" [_, t] _)) f))
                    = safeSubst t "" $ inst "" f
    sr (All v f)    = let nn = show n ; fn = adroite (succ n)
                      in  All v $ bind nn $ fn $ inst nn f
    sr (Imp f g)    = Imp f (sr g)
    sr f            = f

lichten :: Int -> Formula -> Formula
lichten n = sr
  where
    sr (All _ (Iff (Tag DHD (Trm "=" [_, t] _)) f))
                    = sr $ safeSubst t "" $ inst "" f
    sr (All _ (Imp (Tag DHD (Trm "=" [_, t] _)) f))
                    = sr $ safeSubst t "" $ inst "" f
    sr (All v f)    = let nn = show n ; fn = lichten (succ n)
                      in  bool $ All v $ bind nn $ fn $ inst nn f
    sr (Iff f g)    = sr $ zIff f g
    sr (And f g)    = bool $ And (sr f) (sr g)
    sr (Imp f g)    = bool $ Imp (sm f) (sr g)
    sr (Tag _ f)    = sr f
    sr f | isEqu f  = sr $ foldr And Top $ trInfoA f
    sr f | isSort f = f
    sr _            = Top

    sm (Or  f g)    = bool $ Or  (sm f) (sm g)
    sm (And f g)    = bool $ And (sm f) (sm g)
    sm (Tag _ f)    = sm f
    sm f | isUnit f = f
    sm _            = Bot


-- Service stuff

isDefn (Iff (Tag DHD _) _)  = True
isDefn (All _ f)            = isDefn f
isDefn (Imp _ f)            = isDefn f
isDefn _                    = False

isSign (Imp (Tag DHD _) _)  = True
isSign (All _ f)            = isSign f
isSign (Imp _ f)            = isSign f
isSign _                    = False

isUnit (Not f)              = isUnit f
isUnit f                    = isTrm f || isTop f || isBot f

isSort (Trm _ (_:ts) _)     = all ground ts
isSort (Trm ('a':_) _ _)    = True
isSort (Not (Trm "=" _ _))  = True
isSort f                    = isTop f || isBot f

ground f  = not (isVar f) && allF ground f

