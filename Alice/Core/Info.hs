{-
 -  Core/Info.hs -- gather and apply evidence literals
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

module Alice.Core.Info where

import Control.Monad
import Data.List

import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Text

-- Collect evidence

setInfo :: Bool -> [Context] -> Formula -> Formula
setInfo prd cnt trm = ntr
  where
    ntr = trm { trInfo = nte ++ nti }
    nti = eqi trm +++ trigger prd nct trm
    nte = selInfo [DEQ,DSD] trm

    eqi (Trm "=" [l@(Var _ []), r] _)
          = map (Tag DIM . replace l r) (trInfoI r)
    eqi _ = []

    nct =  act (trInfoA trm)
        ++ concatMap sct (offspring trm)
        ++ map cnForm cnt

    act = if prd then map (Imp trm) else id

    sct (Not t) = map Not (trInfoD t) ++ concatMap sct (trInfoO t)
    sct t       =          trInfoD t  ++ concatMap sct (trInfoI t)


-- Deductor

trigger :: Bool -> [Formula] -> Formula -> [Formula]
trigger prd cnt trm = fld (sr Top 0) cnt
  where
    sr ps nn (All _ f)  = sr ps (succ nn) $ inst ('?':show nn) f
    sr ps nn (Imp f g)  = sr (bool $ And ps f) nn g
    sr ps nn (And f g)  = sr ps nn f +++ sr ps nn g
    sr ps nn (Iff f g)  = sr ps nn $ zIff f g
    sr ps nn (Tag _ f)  = sr ps nn f
    sr ps _  f  | bad f = []
                | prd   = sm Top f ps
                | True  = fld (sl ps f) $ offspring f

    sl ps gl s  | gut s = map (Tag DIM) $ sq ps gl s
                | True  = []

    sm ps gl (Or  f g)  = sm ps gl f +++ sm ps gl g
    sm ps gl (And f g)  = sm (bool $ And f ps) gl g +++
                          sm (bool $ And g ps) gl f
    sm ps gl (Tag _ f)  = sm ps gl f
    sm _  _  f  | bad f = []
    sm ps gl (Not f)    = map (Tag DOR) $ sq ps gl f
    sm ps gl f          = map (Tag DIM) $ sq ps gl f

    sq ps gl s  = [ g | sbs <- match s trm,
                        let ngl = sbs gl, green ngl,
                        let nps = sbs ps, green nps,
                        rapid nps, let g = dlv ngl ]

    dlv (Not f) = Not $ skipInfo wipeInfo f
    dlv f       =       skipInfo wipeInfo f

    bad (Not f) = not $ isTrm f
    bad f       = not $ isTrm f

    gut s = not (isVar s) || green s
    fld f = foldr ((+++) . f) []


-- Simplification with evidence

rapid :: Formula -> Bool
rapid f = isTop $ reduce f

reduce :: Formula -> Formula
reduce f  | isTrm f = nfr
          | True    = bool $ mapF reduce f
  where
    nfr | triv f            = Top
        | any (twins f) plv = Top
        | any (twins f) nlv = Bot
        | any twq plv       = Top
        | any twq nlv       = Bot
        | otherwise         = f

    plv = [ f | f@(Trm _ _ _) <- alv ]
    nlv = [ f | Not f <- alv ]
    alv = infos f

    twq g = any (twins g) [ h | (Trm "=" [l,r] _) <- plv,
                      h <- [replace l r f, replace r l f]]

    triv (Trm "=" [l,r] _)  = twins l r
    triv f                  = isTop f

infos :: Formula -> [Formula]
infos = concatMap sct . offspring
  where
    sct (Not t) = trInfoO t ++ concatMap sct (trInfoO t)
    sct t       = trInfoI t ++ concatMap sct (trInfoI t)


-- Match

match :: (MonadPlus m) => Formula -> Formula -> m (Formula -> Formula)
match (Var v@('?':_) _) t       = return  $ safeSubst t v
match (Var u _)    (Var v _)    | u == v  = return id
match (Trm p ps _) (Trm q qs _) | p == q  = pairs ps qs
  where
    pairs (p:ps) (q:qs) = do  sb <- pairs ps qs
                              sc <- match (sb p) q
                              return $ sc . sb
    pairs [] []         = return id
    pairs _ _           = mzero
match _ _         = mzero

safeSubst :: Formula -> String -> Formula -> Formula
safeSubst t v = dive
  where
    dive (Var u _)  | u == v  = t
    dive f  | hasInfo f = skipInfo (mapF dive)
                            f { trInfo = map sbs $ trInfo f }
            | otherwise = mapF dive f

    sbs f@(Tag DIM _) = subst wtr v f
    sbs f@(Tag DOR _) = subst wtr v f
    sbs f             = safeSubst dtr v f

    dtr = wipeDefn t
    wtr = wipeInfo t

green :: Formula -> Bool
green (Var ('?':_:_) _) = False
green (Var ('!':_:_) _) = False
green f                 = allF green $ nullInfo f


-- Info handling

hasInfo f = isTrm f || isVar f || isInd f

nullInfo f  | hasInfo f = f {trInfo = []}
            | otherwise = f

nullDefn f  | hasInfo f = f {trInfo = remInfo [DEQ,DSD] f}
            | otherwise = f

wipeInfo f  = mapF wipeInfo $ nullInfo f

wipeDefn f  = mapF wipeDefn $ nullDefn f

skipInfo fn f | hasInfo f = (fn $ nullInfo f) {trInfo = trInfo f}
              | otherwise = fn f

selInfo ts f  = [ i | i@(Tag t _) <- trInfo f, t `elem` ts ]
remInfo ts f  = [ i | i@(Tag t _) <- trInfo f, t `notElem` ts ]

trInfoI t = [ e | Tag DIM e <- trInfo t ]
trInfoO t = [ e | Tag DOR e <- trInfo t ]
trInfoE t = [ e | Tag DEQ e <- trInfo t ]
trInfoS t = [ e | Tag DSD e <- trInfo t ]
trInfoC t = [ e | Tag DCN e <- trInfo t ]
trInfoN t = [ e | Tag DNC e <- trInfo t ]
trInfoD t = trInfoE t ++ trInfoS t
trInfoA t = trInfoD t ++ trInfoI t


-- Service stuff

(+++) = unionBy sameInfo

sameInfo (Tag DIM f) (Tag DIM g) = sameInfo f g
sameInfo (Tag DOR f) (Tag DOR g) = sameInfo f g
sameInfo (Tag _ _)   (Tag _ _)   = False
sameInfo (Not f)     (Not g)     = sameInfo f g
sameInfo f g                     = twins f g

children f  | isTrm f = trArgs f
            | True    = foldF children $ nullInfo f

offspring f = let x = children f
              in  x ++ concatMap offspring x

