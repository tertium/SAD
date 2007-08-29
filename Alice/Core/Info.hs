module Alice.Core.Info where

import Control.Monad
import Data.List

import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Instr
import Alice.Data.Text
import Alice.Core.Base

-- Collect evidence

fillInfo :: [Context] -> Context -> Formula
fillInfo cnt cx = reduce $ fill True [] (Just True) 0 $ cnForm cx
  where
    fill pr fc sg n fr
      | isThesis fr = fr
      | isVar fr    = sti fr
      | isTrm fr    = sti $ fr { trArgs = nts }
      | otherwise   = roundF (fill pr) fc sg n fr
      where
        sti = setInfo pr $ cnRaise cnt cx fc
        nts = map (fill False fc sg n) (trArgs fr)

setInfo :: Bool -> [Context] -> Formula -> Formula
setInfo prd cnt trm = ntr
  where
    ntr = trm { trInfo = nte ++ nts ++ nti }
    nte = map (Tag DEQ) $ trInfoE trm
    nts = map (Tag DSD) $ trInfoS trm
    nti = eqi trm +++ trigger prd nct trm

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
    sr ps nn f  | bad f = []
                | prd   = sm Top f ps
                | True  = fld (sl ps f) $ offspring f

    sl ps gl s  | gut s = map (Tag DIM) $ sq ps gl s
                | True  = []

    sm ps gl (Or  f g)  = sm ps gl f +++ sm ps gl g
    sm ps gl (And f g)  = sm (bool $ And f ps) gl g +++
                          sm (bool $ And g ps) gl f
    sm ps gl (Tag _ f)  = sm ps gl f
    sm ps gl f  | bad f = []
    sm ps gl (Not f)    = map (Tag DOR) $ sq ps gl f
    sm ps gl f          = map (Tag DIM) $ sq ps gl f

    sq ps gl s  = [ g | ngl <- match s wtr `ap` [gl], green ngl,
                        nps <- match s trm `ap` [ps], green nps,
                        rapid nps, let g = dlv ngl ]

    dlv (Not f) = Not $ skipInfo wipeInfo f
    dlv f       =       skipInfo wipeInfo f

    bad (Not f) = not $ isTrm f
    bad f       = not $ isTrm f

    gut s = not (isVar s) || green s
    fld f = foldr ((+++) . f) []
    wtr = wipeInfo trm


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
        | otherwise         = f

    plv = [ f | f <- lvs, isTrm f ]
    nlv = [ f | Not f <- lvs ]

    lvs = concatMap sct $ offspring f

    sct (Not t) = trInfoO t ++ concatMap sct (trInfoO t)
    sct t       = trInfoI t ++ concatMap sct (trInfoI t)

    triv (Trm "=" [l,r] _)  = twins l r
    triv f                  = isTop f


-- Match

match :: (MonadPlus m) => Formula -> Formula -> m (Formula -> Formula)
match (Var v@('?':_) _) t       = return  $ subst t v
match (Var u _)    (Var v _)    | u == v  = return id
match (Trm p ps _) (Trm q qs _) | p == q  = pairs ps qs
  where
    pairs (p:ps) (q:qs) = do  sb <- pairs ps qs
                              sc <- match (sb p) q
                              return $ sc . sb
    pairs [] []         = return id
    pairs _ _           = mzero
match _ _         = mzero

green :: Formula -> Bool
green (Var ('?':_) _) = False
green (Var ('!':_) _) = False
green f               = allF green $ nullInfo f


-- Service stuff

(+++) = unionBy ism
  where
    ism (Tag DIM f) (Tag DIM g) = twins f g
    ism (Tag DOR f) (Tag DOR g) = twins f g
    ism f g                     = False

children f  | isTrm f = trArgs f
            | True    = foldF children $ nullInfo f

offspring f = let x = children f
              in  x ++ concatMap offspring x

wfcheck f | hasInfo f = all wfinfo (trInfoI f)
                    &&  all wfinfo (trInfoO f)
                    &&  all wfcheck (trInfoD f)
                    &&  allF wfcheck (nullInfo f)
          | otherwise = allF wfcheck f
  where
    wfinfo (Not (Trm _ ts []))  = all wfinfo ts
    wfinfo (Trm _ ts [])        = all wfinfo ts
    wfinfo t  | not (hasInfo t) = error $ "wfcheck: " ++ show f
                                  ++ show (trInfo f) ++ '\n' : show t
              | null (trInfo t) = True
              | otherwise       = error $ "wfcheck: " ++ show f
                                  ++ show (trInfo f) ++ '\n' : show t
                                  ++ show (trInfo t)

