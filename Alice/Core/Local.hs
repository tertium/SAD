module Alice.Core.Local where

import Data.List

import Alice.Data.Formula
import Alice.Data.Text

-- Local validity

fillDLV cnt fr  = fill True cnt True fr
  where
    fill pr cn sg f | isVar f = setDLV cn pr f
                    | isTrm f = setDLV cn pr $ specDef h
                    | True    = roundF (fill pr) cn sg f
      where h = f { trArgs = map (fill False cn sg) (trArgs f) }


setDLV cnt prd trm  = trm { trInfo = nti trm }
  where
    nti (Trm "=" [l@(Var _ []), r] _ _)
          = map (Ann DIM . replace l r) (trInfo r)
            +++ trigger nct prd trm
    nti _ = trigger nct prd trm

    act | isVar trm = []
        | not prd   = dedfn $ trDefn trm
        | True      = map (Imp trm) $ dedfn $ trDefn trm

    nct = act ++ concatMap def (offspring trm) ++ oct

    def (Trm _ _ hs dd) = dedfn dd ++ concatMap def hs
    def (Var _ hs)      = concatMap def hs
    def f               = foldF def [] (++) f

    dedfn = map (deAnn . rebind undot)
    undot ('.':'.':x) = '.':x ; undot ('.':x) = 'd':x
    oct = [ formulate bl | bl <- cnt, comtype bl /= Defn ]


trigger cnt prd fr  = fld (sr [] zTrue) cnt
  where
    sr vs ps (All v f)    = sr (v:vs) ps f
    sr vs ps (Iff f g)    = sr vs ps (zIff f g)
    sr vs ps (And f g)    = sr vs ps f +++ sr vs ps g
    sr vs ps (Imp f g)    = sr vs (bool $ And f ps) g
    sr vs ps f  | bad f   = []
                | prd     = sm vs zTrue f ps
                | True    = fld (sl vs ps f) (offspring f)

    sl vs ps f s          = [ g | s `notElem` vs, g <- sq vs ps f s,
                                  any (isMatch fr) (offspring g) ]

    sm vs ps gl (Or f g)  = sm vs ps gl f +++ sm vs ps gl g
    sm vs ps gl (And f g) = sm vs (bool $ And f ps) gl g
                            +++ sm vs (bool $ And g ps) gl f
    sm vs ps gl f | bad f = []
                  | True  = map (Ann DIM) (sq vs ps gl f)
                            +++ map (Ann DOR) (sq vs ps gl (Not f))

    sq vs ps gl s         = [ norm f |  sb <- match vs s fr,
                                        let g = sb gl; hs = sb ps,
                                        ground vs g, ground vs hs,
                                        rapid $ dequa hs,
                                        f <- dlv True (ded g) ]
    ground vs f = grn f
      where
        grn (Ann DSB f) = True
        grn f | isVar f = f `notElem` vs
              | isTrm f = all grn (trArgs f)
              | True    = foldF grn True (&&) f

    dequa (All _ _) = zTrm "?" [] ; dequa f | isTrm f = f
    dequa (Exi _ _) = zTrm "?" [] ; dequa f = mapF dequa f

    dlv s (Not f) = dlv (not s) f ; dlv s (Ann _ f) = dlv s f
    dlv True f  =     f : [ g | (Ann DIM g) <- trInfo f ]
    dlv False f = Not f : [ g | (Ann DOR g) <- trInfo f ]

    bad f = not (isUnit f) || isTrue f
    fld f = foldr (+++) [] . map f
    ded (Ann DSB f) = wipeD f
    ded f = mapF ded f

    norm (Ann a f)      = norm f
    norm (Not f)        = Not (norm f)
    norm (Trm t ts _ d) = Trm t (map wipe ts) [] d
    wipe (Trm t ts _ _) = Trm t (map wipe ts) [] []
    wipe (Var v _)      = Var v []

(+++) = unionBy ism
  where
    ism (Ann DIM _) (Ann DOR _) = False
    ism (Ann DOR _) (Ann DIM _) = False
    ism f g = isMatch f g

children f  | isInd f = []
            | isTrm f = map strip $ trArgs f
            | True    = foldF children f

offspring f = let x = children f
              in  x ++ concatMap offspring x




rapid = isTrue . reduce

reduce f  
| isTrm f = nfr
          | True    = bool $ mapF reduce f
  where
    nfr | triv f = zTrue
        | any (isMatch f) lvs = zTrue
        | any (isMatch $ Not f) lvs = zFalse
        | otherwise = f

    lvs = concatMap trInfo $ offspring f

--    triv (Trm "aSet" [t] _ _) = isSSS t  -- do we need it?
    triv (Trm "=" [l,r] _ _)  = twins l r
    triv f                    = isTrue f

infos :: Bool -> Bool -> Formula -> [Formula]
infos sg pr f@(Trm _ _ ss)  | pr  = map
  where
    
    h = if pr then f else zEqu f f

    dive g  | twins h g = if sg then Top else Bot
            | otherwise = bool $ mapF dive f


