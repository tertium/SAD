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

    nct = act ++ sct ++ oct

    act = if prd then map (Imp trm) cur else cur
    cur = trInfoE trm ++ trInfoI trm

    sct = concatMap def $ offspring trm
    def f | hasInfo f = trInfoE f -- ++ concatMap def (trInfoI f)
          | otherwise = foldF def f

    oct = filter flt $ map cnForm cnt
    flt f = not $ isDefn f || isSign f


-- Infer ad hoc definitions

specDef :: Formula -> Formula
specDef trm@(Trm "=" [l, r] is) | not (null nds)
        = Trm "=" [l, nullDEQ r] nds
  where
    nds = map (Ann DEQ . replace (wipeDEQ l) r) (trInfoE r)

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
    dive gs _ (Iff t f) = fine gs t f
    dive gs n (All _ f) = dive gs (succ n) $ inst ('?':show n) 0 f
    dive gs n (And f g) = dive gs n f `mplus` dive gs n g
    dive gs n (Imp g f) = dive (bool $ And gs g) n f
    dive _ _ _          = mzero

    fine gs tr@(Trm t _ _) fr =
      do  ngs <- match tr trm `ap` return gs
          nfr <- match tr (wipeDEQ trm) `ap` return fr
          guard $ grune ngs && grune nfr && rapid ngs
          return nfr

specDef f = f


-- Deductor

trigger :: Bool -> [Formula] -> Formula -> [Formula]
trigger prd cnt trm = fld (sr Top 0) cnt
  where
    sr ps nn (All _ f)  = sr ps (succ nn) $ inst ('?':show nn) 0 f
    sr ps nn (Exi _ f)  = sr ps (succ nn) $ inst ('!':show nn) 0 f
    sr ps nn (Iff f g)  = sr ps nn $ zIff f g
    sr ps nn (And f g)  = sr ps nn f +++ sr ps nn g
    sr ps nn (Imp f g)  = sr (bool $ And ps f) nn g
    sr ps nn (Ann _ f)  = sr ps nn f
    sr ps nn f  | bad f = []
                | prd   = sm Top f ps
                | True  = fld (sl ps f) $ offspring f

    sl ps gl s  = [ Ann DIM g | not (isVar s) || grune s,
                                g <- sq ps gl s,
                                occurs trm g ]

    sm ps gl (Or  f g)  = sm ps gl f +++ sm ps gl g
    sm ps gl (And f g)  = sm (bool $ And f ps) gl g +++
                          sm (bool $ And g ps) gl f
    sm ps gl (Ann _ f)  = sm ps gl f
    sm ps gl f  | bad f = []
                | True  = map (Ann DIM) (sq ps gl f) +++
                          map (Ann DOR) (sq ps gl (neg f))

    sq ps gl s  = [ f | sb <- match s trm,
                        let g = sb gl, grune g,
                        rapid $ sb ps, f <- dlv True g ]

    dlv s (Not f) = dlv (not s) f
    dlv True f    = wipeInfo f : trInfoI f
    dlv False f   = wipeInfo (Not f) : trInfoO f

    fld f = foldr ((+++) . f) []

    bad (Not f)   = bad f
    bad f = not $ isTrm f

    wtrm  = wipeDEQ trm


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

nullDEQ f | hasInfo f = let isDEQ (Ann DEQ _) = True ; isDEQ _ = False
                        in  f { trInfo = filter (not . isDEQ) (trInfo f) }
          | otherwise = f

wipeDEQ = skipInfo (mapF wipeDEQ) . nullDEQ

grune (Var ('?':_) _) = False
grune (Var ('!':_) _) = False
grune f               = allF grune $ nullInfo f

