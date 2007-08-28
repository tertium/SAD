module Alice.Core.Local where

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
setInfo prd cnt otr = ntr
  where
    trm = specDef otr

    ntr = trm { trInfo = nte ++ nti }
    nte = map (Ann DEQ) $ trInfoE trm
    nti = eqi trm +++ trigger prd nct trm

    eqi (Trm "=" [l@(Var _ []), r] _)
          = map (Ann DIM . replace l r) (trInfoI r)
    eqi _ = []

    nct = act ++ sct ++ map cnForm cnt

    act = if prd then map (Imp trm) cur else cur
    cur = trInfoE trm ++ trInfoI trm

    sct = concatMap trInfoE $ offspring trm


-- Infer ad hoc definitions

specDef :: Formula -> Formula
specDef trm@(Trm "=" [l, r] is) | not (null nds)  = ntr
  where
    ntr = Trm "=" [l, r {trInfo = map (Ann DIM) $ trInfoI r}] nds
    nds = map (Ann DEQ . replace (wipeInfo l) r) (trInfoE r)

specDef trm@(Trm t ts is) | not (null $ trInfo ntr) = ntr
  where
    ntr = foldr add (Trm t [] []) ts

    add a (Trm t ts is)
      = let (ni, ns) = foldr tst (is, []) (trInfo a)
        in  Trm t (a { trInfo = ns } : ts) ni

    tst (Ann DEQ d) (nd, ds)
      = case dive Top 0 d
        of  Just f  ->  (Ann DEQ f : nd, ds)
            _       ->  (nd, Ann DEQ d : ds)
    tst d (nd, ds)  =   (nd, d : ds)

    dive gs _ (Iff (Trm "=" [Var v _, t] _) f) | isTrm t
                                  = fine gs t $ subst t v f
    dive gs _ (Iff t f) | isTrm t = fine gs t f
    dive gs n (All _ f) = dive gs (succ n) $ inst ('?':show n) f
    dive gs n (Imp g f) = dive (bool $ And gs g) n f
    dive gs n (And f g) = dive gs n f `mplus` dive gs n g
    dive _ _ _          = mzero

    fine gs tr@(Trm t _ _) fr =
      do  nfr <- match tr wtr `ap` return fr; guard $ grune nfr
          ngs <- match tr trm `ap` return gs; guard $ grune ngs
          guard $ rapid ngs; return nfr

    wtr = wipeInfo trm

specDef f = f


-- Deductor

trigger :: Bool -> [Formula] -> Formula -> [Formula]
trigger prd cnt trm = fld (sr Top 0) cnt
  where
    sr ps nn (All _ f)  = sr ps (succ nn) $ inst ('?':show nn) f
    sr ps nn (Imp f g)  = sr (bool $ And ps f) nn g
    sr ps nn (And f g)  = sr ps nn f +++ sr ps nn g
    sr ps nn (Iff f g)  = sr ps nn $ zIff f g
    sr ps nn (Ann _ f)  = sr ps nn f
    sr ps nn f  | bad f = []
                | prd   = sm Top f ps
                | True  = fld (sl ps f) $ offspring f

    sl ps gl s  = [ Ann DIM g | not (isVar s) || grune s,
                                g <- sq ps gl s, occurs trm g ]

    sm ps gl (Or  f g)  = sm ps gl f +++ sm ps gl g
    sm ps gl (And f g)  = sm (bool $ And f ps) gl g +++
                          sm (bool $ And g ps) gl f
    sm ps gl (Ann _ f)  = sm ps gl f
    sm ps gl f  | bad f = []
    sm ps gl (Not f)    = map (Ann DOR) $ sq ps gl f
    sm ps gl f          = map (Ann DIM) $ sq ps gl f

    sq ps gl s  = [ f | ngl <- match s wtr `ap` [gl], grune ngl,
                        nps <- match s trm `ap` [ps], grune nps,
                        rapid nps, f <- dlv ngl ]

    dlv (Not f)   = Not (wipeInfo f) : trInfoO f
    dlv f         = wipeInfo f       : trInfoI f

    fld f = foldr ((+++) . f) []

    bad (Not f) = not $ isTrm f
    bad f = not $ isTrm f

    wtr = wipeInfo trm


-- Simplification with evidence

rapid f = isTop $ reduce f

reduce f  | isTrm f = nfr
          | True    = bool $ mapF reduce f
  where
    nfr | triv f            = Top
        | any (twins f) plv = Top
        | any (twins f) nlv = Bot
        | otherwise         = f

    plv = [ f | f <- lvs, isTrm f ]
    nlv = [ f | Not f <- lvs ]
    lvs = concatMap trInfoI $ offspring f

    triv (Trm "=" [l,r] _)  = twins l r
    triv f                  = isTop f


-- Service stuff

(+++) = unionBy ism
  where
    ism (Ann DIM f) (Ann DIM g) = twins f g
    ism (Ann DOR f) (Ann DOR g) = twins f g
    ism f g                     = False

children f  | isTrm f = trArgs f
            | True    = foldF children $ nullInfo f

offspring f = let x = children f
              in  x ++ concatMap offspring x

grune (Var ('?':_) _) = False
grune (Var ('!':_) _) = False
grune f               = allF grune $ nullInfo f

wfcheck f | hasInfo f = all wfinfo (trInfoI f)
                    &&  all wfinfo (trInfoO f)
                    &&  all wfcheck (trInfoE f)
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

