{-
 -  Core/Extras.hs -- evidence recollection, adhoc definitions, wfcheck
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

module Alice.Core.Extras where

import Control.Monad

import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Text
import Alice.Core.Info

-- Recollect adhoc definitions and evidence literals

fillInfo :: [Context] -> Context -> Formula -> Formula
fillInfo cnt cx = reduce . fill True [] (Just True) 0
  where
    fill pr fc sg n fr
      | isVar fr    = sti fr
      | isTrm fr    = sti $ specDef $ fr { trArgs = nts }
      | otherwise   = roundF 'i' (fill pr) fc sg n fr
      where
        sti = setInfo pr $ cnRaise cnt cx fc
        nts = map (fill False fc sg n) (trArgs fr)


-- Infer adhoc definitions

specDef :: Formula -> Formula
specDef trm@(Trm "=" [l, r] _) | not (null sds)  = ntr
  where
    ntr = Trm "=" [l, r { trInfo = remInfo [DEQ,DSD] r }] nds
    sds = map (Tag DSD . replace (wipeDefn l) r) $ trInfoD r
    nds = sds ++ remInfo [DSD] trm

specDef trm | isTrm trm = otr { trInfo = nds }
  where
    (nds, otr) = pas (remInfo [DSD] trm) trm

    pas ds t  | isTrm t = let (nd, as) = foldr arg (ds, []) $ trArgs t
                          in  (nd, t { trArgs = as })
              | True    = (ds, t)

    arg a (ds, as)  = let (ad, na) = pas ds a
                          (nd, is) = foldr tst (ad, []) $ trInfo a
                      in  (nd, na { trInfo = is } : as)

    tst a (nd, ds)  = case a of
      Tag DEQ d ->        case specDig trm d of
                            Just f  ->  (Tag DSD f : nd, ds)
                            _       ->  (nd, a : ds)
      Tag DSD d ->        case specDig trm d of
                            Just f  ->  (Tag DSD f : nd, ds)
                            _       ->  (nd, a : ds)
      Tag DIM (Not d) ->  let ods = map (Tag DIM) $ trInfoO d
                              (ni, _) = foldr tst (nd, []) ods
                          in  (ni, a : ds)
      Tag DIM d ->        let (ni, _) = foldr tst (nd, []) $ trInfo d
                          in  (ni, a : ds)
      _ ->                (nd, a : ds)

specDef f = f

specDig :: (MonadPlus m) => Formula -> Formula -> m Formula
specDig trm = dive Top 0
  where
    dive gs _ (Iff (Trm "=" [l@(Var v@('?':_) _), t] _) f)
      | isTrm t && not (occurs l t) = fine gs t $ safeSubst t v f
    dive gs _ (Iff t f) | isTrm t   = fine gs t f
    dive gs n (All _ f) = dive gs (succ n) $ inst ('?':show n) f
    dive gs n (Imp g f) = dive (bool $ And gs g) n f
    dive gs n (And f g) = dive gs n f `mplus` dive gs n g
    dive _ _ _          = mzero

    fine gs tr fr =
      do  sbs <- match tr wtr
          let nfr = sbs fr; ngs = sbs gs
          guard $ green nfr && green ngs
          guard $ rapid ngs ; return nfr

    wtr = wipeDefn trm


-- Well-formedness checking

wfForm fs f | hasInfo f     = 1 + wfInfo fs f +
                                     sumF (wfForm fs) (nullInfo f)
            | otherwise     = 1 + sumF (wfForm fs) f

wfInfo fs f = sumap (wfevid (f:fs)) (trInfoI f) +
              sumap (wfevid (f:fs)) (trInfoO f) +
              sumap (wfForm (f:fs)) (trInfoD f)
  where
    wfevid fs (Not f) | isTrm f = 1 + sumap (wfargs fs) (trArgs f) + wfInfo fs f
    wfevid fs f | isTrm f       = 1 + sumap (wfargs fs) (trArgs f) + wfInfo fs f
    wfevid fs f                 = wferr "ill-formed info" (f:fs)

    wfargs ts t | not (hasInfo t)       = wferr "non-term argument" (t:ts)
                | not (null $ trInfo t) = wferr "nonempty trInfo" (t:ts)
                | isTrm t               = 1 + sumap (wfargs ts) (trArgs t)
                | not (green t)         = wferr "non-green var" (t:ts)
                | otherwise             = 1

    wferr es ts = error $ "wfcheck: " ++ es ++ concatMap trout ts

    sumap = (sum .) . map

    trout t = " in\n" ++ show t ++ trinf t
    trinf t | hasInfo t = show $ trInfo t
            | otherwise = ""

