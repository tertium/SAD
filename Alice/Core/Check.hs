{-
 -  Core/Check.hs -- check symbols for well-definedness
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

module Alice.Core.Check (fillDef) where

import Control.Monad
import Data.Maybe

import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Instr
import Alice.Data.Text
import Alice.Core.Base
import Alice.Core.Info
import Alice.Core.Extras
import Alice.Core.Reason

fillDef :: Context -> [Context] -> Context -> RM Formula
fillDef ths cnt cx  = fill True False [] (Just True) 0 $ cnForm cx
  where
    fill pr _ fc sg n (Tag DHD f)
      = liftM (Tag DHD) $ fill pr True fc sg n f
    fill _ _ _ _ _ t | isThesis t
      = return $ cnForm ths
    fill pr _ fc _ _ v | isVar v
      = do  uin <- askRSIB IBinfo True
            let nct = cnRaise cnt cx fc
            return $ sinfo uin pr nct v
    fill pr nw fc sg n (Trm t ts is)
      = do  uin <- askRSIB IBinfo True
            let nct = cnRaise cnt cx fc
            nts <- mapM (fill False   nw fc sg n) ts
            nis <- mapM (fill True False fc sg n) is
            ntr <- setDef nw nct cx $ Trm t nts nis
            return $ sinfo uin pr nct $ specDef ntr
    fill pr nw fc sg n f = roundFM 'w' (fill pr nw) fc sg n f

    sinfo uin pr cnt trm
      | uin   = setInfo pr cnt trm
      | True  = trm { trInfo = selInfo [DEQ,DSD] trm }

setDef :: Bool -> [Context] -> Context -> Formula -> RM Formula
setDef nw cnt cx trm@(Trm t _ _)  = incRSCI CIsymb >>
      ((guard (elem ':' t) >> return trm)
    <> (guardNotIB IBchck True >> return trm)
    <> (msum $ map (testDef False cnt cx trm) dfs)
    <> (guard (t == "=" || elem '#' t) >> return trm)
    <> (msum $ map (testDef True  cnt cx trm) dfs)
    <> (guard nw >> nwt)
    <> (out >> mzero))
  where
    dfs = mapMaybe (findDef trm) cnt
    str = trm { trName = t ++ ':' : show (length dfs) }
    nwt = (guardIB IBsign True >> return str) <> return trm
    out = rlog (cnHead cx) $ "unrecognized: " ++ showsPrec 2 trm ""


-- Find relevant definitions and test them

type DefTrio = (Context, Formula, Formula)

findDef :: (MonadPlus m) => Formula -> Context -> m DefTrio
findDef trm cx  = dive Top 0 $ cnForm cx
  where
    dive gs _ (All _ (Iff (Tag DHD (Trm "=" [_, t] _)) f))
      = fine gs t $ Tag DEQ $ safeSubst t "" $ inst "" f
    dive gs _ (All _ (Imp (Tag DHD (Trm "=" [_, t] _)) f))
      = fine gs t $ Tag DIM $ safeSubst t "" $ inst "" f
    dive gs _ (Iff (Tag DHD t) f) = fine gs t $ Tag DEQ f
    dive gs _ (Imp (Tag DHD t) f) = fine gs t $ Tag DIM f

    dive gs n (All _ f) = dive gs (succ n) $ inst ('?':show n) f
    dive gs n (And g f) = dive gs n f `mplus` dive gs n g
    dive gs n (Imp g f) = dive (bool $ And gs g) n f
    dive _ _ _          = mzero

    fine gs tr@(Trm t _ _) fr =
      do  ngs <- match otr trm `ap` return gs
          nfr <- match otr wtr `ap` return fr
          return (cx, ngs, trm { trName = t, trInfo = [nfr] })
      where otr = tr { trName = takeWhile (/= ':') t }

    wtr = wipeInfo trm

testDef :: Bool -> [Context] -> Context -> Formula -> DefTrio -> RM Formula
testDef hard cnt cx trm (dc, gs, nt)
    = setup >> (guards <> (cleanup >> mzero)) >> cleanup >> return nt
  where
    guards  | hard  = do  whdchk $ header; incRSCI CIchkh
                          reason cnt $ setForm ccx gs; incRSCI CIchky
            | True  = do  guard $ rapid gs; incRSCI CIchkt
                          whdchk $ "trivial " ++ header

    setup   | hard  = do  askRSII IIchtl 1 >>= addRSIn . InInt IItlim
                          askRSII IIchdp 3 >>= addRSIn . InInt IIdpth
            | True  = return ()

    cleanup | hard  = do  drpRSIn $ IdInt IItlim
                          drpRSIn $ IdInt IIdpth
            | True  = return ()

    header  = "check: " ++ showsPrec 2 trm " vs " ++ cnName dc
    whdchk  = whenIB IBPchk False . rlog0

    ccx = let bl:bs = cnBran cx in cx { cnBran = bl { blLink = [] } : bs }

