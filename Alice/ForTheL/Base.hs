module Alice.ForTheL.Base where

import Control.Monad
import Data.Char
import Data.List

import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Text
import Alice.Parser.Base
import Alice.Parser.Prim
import Alice.Parser.Trans

-- Basic types

type UTerm    = (Formula -> Formula, Formula)
type UNotion  = (Formula -> Formula, Formula, String)

type MTerm    = (Formula -> Formula, [Formula])
type MNotion  = (Formula -> Formula, Formula, [String])

type Prim     = ([Patt], [Formula] -> Formula)


-- State definition

type FTL  = StateT  FState LPM
type LFTL = ReaderT FState (ReaderT [String] LPM)

data FState = FState {
  adj_expr, ver_expr, ntn_expr, snt_expr :: [Prim],
  cfn_expr, rfn_expr, lfn_expr, ifn_expr :: [Prim],
  cpr_expr, rpr_expr, lpr_expr, ipr_expr :: [Prim],
  tvr_expr :: [TVar], str_syms :: [[String]] }

initFS  = FState  eq [] [] sn
                  [] [] [] []
                  [] [] [] sp
                  [] []
  where
    eq  = [ ([Wd ["equal"], Wd ["to"], Vr], zTrm "="),
            ([Wd ["nonequal"], Wd ["to"], Vr], Not . zTrm "=") ]
    sp  = [ ([Sm "="], zTrm "="),
            ([Sm "!="], Not . zTrm "="),
            ([Sm "-<-"], zTrm "iLess") ]
    sn  = [ ([Sm "=", Vr], zTrm "=") ]

getExpr :: (FState -> [a]) -> (a -> LFTL b) -> LFTL b
getExpr e p = askS e >>= msum . map p

getDecl = lift netS
addDecl = rtrtm . ssrtm . (++)

doLFTL :: LFTL a -> FTL a
doLFTL  = rtstm $ flip runReaderT []


-- Pre-typed variables

type TVar = ([String], Formula)

prim_tvr :: LFTL MNotion
prim_tvr  = getExpr tvr_expr tvr
  where
    tvr (vr, nt)  = do  vs <- varlist
                        guard $ all (`elem` vr) vs
                        return (id, nt, vs)


-- Predicates: verbs and adjectives

prim_ver, prim_adj, prim_un_adj :: LFTL UTerm -> LFTL UTerm

prim_ver      = getExpr ver_expr . prim_prd
prim_adj      = getExpr adj_expr . prim_prd
prim_un_adj   = getExpr (filter (unary . fst) . adj_expr) . prim_prd
  where
    unary pt  = Vr `notElem` pt

prim_prd p (pt, fm) = do  (q, ts) <- wd_patt p pt
                          return (q, fm $ zHole:ts)


-- Multi-subject predicates: [a,b are] equal

prim_m_ver, prim_m_adj, prim_m_un_adj :: LFTL UTerm -> LFTL UTerm

prim_m_ver    = getExpr ver_expr . prim_ml_prd
prim_m_adj    = getExpr adj_expr . prim_ml_prd
prim_m_un_adj = getExpr (filter (unary . fst) . adj_expr) . prim_ml_prd
  where
    unary (Vr : pt) = Vr `notElem` pt
    unary (_  : pt) = unary pt
    unary _         = True

prim_ml_prd p (pt, fm)  = do  (q, ts) <- ml_patt p pt
                              return (q, fm $ zHole:zSlot:ts)


-- Notions and functions

prim_ntn, prim_of_ntn :: LFTL UTerm -> LFTL MNotion

prim_ntn p  = getExpr ntn_expr ntn
  where
    ntn (pt, fm)  = do  (q, vs, ts) <- nt_patt p pt
                        return (q, fm $ zHole:ts, vs)

prim_of_ntn p = getExpr ntn_expr ntn
  where
    ntn (pt, fm)  = do  (q, vs, ts) <- of_patt p pt
                        let fn v = fm $ (zVar v):zHole:ts
                        return (q, foldr1 And $ map fn vs, vs)

prim_cm_ntn :: LFTL UTerm -> LFTL MTerm -> LFTL MNotion
prim_cm_ntn p s = getExpr ntn_expr ntn
  where
    ntn (pt, fm)  = do  (q, vs, as, ts) <- cm_patt p s pt
                        let fn v = fm $ zHole:v:ts
                        return (q, foldr1 And $ map fn as, vs)

prim_fun :: LFTL UTerm -> LFTL UTerm
prim_fun  = (>>= fun) . prim_ntn
  where
    fun (q, Trm "=" [_, t] _, _) | not (occursH t) = return (q, t)
    fun _ = mzero


-- Symbolic primitives

prim_cpr  = getExpr cpr_expr . prim_csm     -- T ... T
prim_rpr  = getExpr rpr_expr . prim_rsm     -- v ... T
prim_lpr  = getExpr lpr_expr . prim_lsm     -- T ... v
prim_ipr  = getExpr ipr_expr . prim_ism     -- v ... v

prim_cfn  = getExpr cfn_expr . prim_csm
prim_rfn  = getExpr rfn_expr . prim_rsm
prim_lfn  = getExpr lfn_expr . prim_lsm
prim_ifn  = getExpr ifn_expr . prim_ism

prim_csm p (pt, fm) = sm_patt p pt >>= \l -> return $ fm l
prim_rsm p (pt, fm) = sm_patt p pt >>= \l -> return $ \t -> fm $ t:l
prim_lsm p (pt, fm) = sm_patt p pt >>= \l -> return $ \s -> fm $ l++[s]
prim_ism p (pt, fm) = sm_patt p pt >>= \l -> return $ \t s -> fm $ t:l++[s]

prim_snt :: LFTL Formula -> LFTL MNotion
prim_snt p  = varlist >>= getExpr snt_expr . snt
  where
    snt vs (pt, fm) = sm_patt p pt >>= \l -> return (id, fm $ zHole:l, vs)


-- Pattern parsing

data Patt = Wd [String] | Sm String | Vr | Nm deriving Eq

ml_patt p (Wd l :_: Vr : ls)
                      = wordOf l >> na_patt p ls
ml_patt p (Wd l : ls) = wordOf l >> ml_patt p ls
ml_patt _ _           = mzero

nt_patt p (Nm : ls)   = do  vs <- namlist
                            (q, ts) <- wd_patt p ls
                            return (q, vs, ts)
nt_patt p (Wd l : ls) = wordOf l >> nt_patt p ls
nt_patt _ _           = mzero

of_patt p (Nm : Wd l : Vr : ls)
                      = do  ofguard l; vs <- namlist
                            (q, ts) <- na_patt p ls
                            return (q, vs, ts)
of_patt p (Wd l : ls) = wordOf l >> of_patt p ls
of_patt _ _           = mzero

cm_patt p s (Nm : Wd l : Vr : ls)
                      = do  ofguard l; vs <- namlist; wordOf l
                            (r, as) <- s; when (null $ tail as) $
                              fail "several objects expected for `common'"
                            (q, ts) <- na_patt p ls
                            return (r . q, vs, as, ts)
cm_patt p s (Wd l:ls) = wordOf l >> cm_patt p s ls
cm_patt _ _ _         = mzero

na_patt p (Wd l : ls) = naguard l >> wordOf l >> wd_patt p ls
na_patt p ls          = wd_patt p ls

wd_patt p (Vr : ls)   = do  (r, t) <- p
                            (q, ts) <- wd_patt p ls
                            return (r . q, t:ts)
wd_patt p (Wd l : ls) = wordOf l >> wd_patt p ls
wd_patt _ []          = return (id, [])
wd_patt _ _           = mzero

sm_patt p (Vr : ls)   = liftM2 (:) p $ sm_patt p ls
sm_patt p (Sm s : ls) = string s >> sm_patt p ls
sm_patt _ []          = return []
sm_patt _ _           = mzero

ofguard = guard . elem "of"
naguard = guard . notElem "and"


-- Variables

namlist = varlist -|- liftM (:[]) hidden

varlist = do  vs <- chainEx (char ',') var
              nodups vs ; return vs

nodups vs = unless (null $ dups vs) $
              fail $ "duplicate names: " ++ show vs

hidden  = askPS psOffs >>= \ n -> return ('h':show n)

var     = do  v <- nextTkLex ; unless (all isAlpha v) $
                fail $ "invalid variable: " ++ show v
              skipSpace $ return ('x':v)

decl vs f = dive f
  where
    dive (All _ f)  = dive f
    dive (Exi _ f)  = dive f
    dive (Tag _ f)  = dive f
    dive (Imp f g)  = filter (noc f) (dive g)
    dive (And f g)  = dive f `union` filter (noc f) (dive g)
    dive (Trm ('a':_) (v@(Var u@('x':_) _):ts) _)
      | all (not . occurs v) ts = nifilt vs u
    dive (Trm "=" [v@(Var u@('x':_) _), t] _)
      | isTrm t && not (occurs v t) = nifilt vs u
    dive _  = []

    noc f v = not $ occurs (zVar v) f

free vs f = nub (dive f)
  where
    dive f@(Var u@('x':_) _)  = nifilt vs u ++ foldF dive f
    dive f                    = foldF dive f

overfree vs f
    | occurs zSlot f  = "too few subjects for an m-predicate " ++ inf
    | not (null sbs)  = "free undeclared variables: " ++ sbs ++ inf
    | not (null ovl)  = "overlapped variables: " ++ ovl ++ inf
    | otherwise       = ""
  where
    sbs = unwords $ map show $ free vs f
    ovl = unwords $ map show $ over vs f
    inf = "\n in translation: " ++ show f

    over vs (All v f) = bvrs vs v f
    over vs (Exi v f) = bvrs vs v f
    over vs f = foldF (over vs) f

    bvrs vs v f | elem v vs = [v]
                | null v    = over vs f
                | otherwise = over (v:vs) f


-- Service stuff

an    = wordOf ["a", "an"]
the   = wordOf ["the"]
is    = wordOf ["is", "be", "are"]

dot p = after p (char '.')

