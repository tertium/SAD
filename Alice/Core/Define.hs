module Alice.Core.Define (fillDef) where

import Control.Monad
import Data.Maybe

import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Instr
import Alice.Data.Text
import Alice.Core.Base
--import Alice.Core.Local
import Alice.Core.Reason

fillDef :: Formula -> [Context] -> Context -> RM Formula
fillDef ths cnt cx  = fill True [] (Just True) 0 $ cnForm cx
  where
    fill _ fc _ _ (Ann DHD (Trm "=" [v, t] _)) | isTrm t
      = liftM (Ann DHD . zEqu v) $ setDef True (cnRaise cnt cx fc) cx t
    fill _ fc _ _ (Ann DHD t)
      = liftM (Ann DHD) $ setDef True (cnRaise cnt cx fc) cx t
    fill pr fc _ _ v | isVar v
      = return v -- $ setInfo pr (cnRaise cnt cx fc) v
    fill _ _ _ _ t | isThesis t
      = return ths
    fill pr fc sg n (Trm t ts is)
      = do  let nct = cnRaise cnt cx fc
            nts <- mapM (fill False fc sg n) ts
            nis <- mapM (fill True  fc sg n) is
            ntr <- setDef False nct cx $ Trm t nts nis
            -- printRM $ trInfoE $ specDef ntr
            return $ {- setInfo pr nct $ -} specDef ntr
    fill pr fc sg n f = roundFM (fill pr) fc sg n f

setDef :: Bool -> [Context] -> Context -> Formula -> RM Formula
setDef nw cnt cx trm@(Trm t _ _)
    =  (guard (elem ':' t) >> return trm)
    <> (guardNotIB IBdefn True >> return trm)
    <> (msum $ map (testDef False cnt cx trm) dfs)
    <> (guard (t == "=" || elem '#' t) >> return trm)
    <> (msum $ map (testDef True  cnt cx trm) dfs)
    <> (guard nw >> return str)
    <> (out >> mzero)
  where
    dfs = mapMaybe (findDef trm) cnt
    str = trm { trName = t ++ ':' : show (length dfs) }
    out = rlog (cnHead cx) $ "unrecognized: " ++ showsPrec 2 trm ""


-- Find relevant definitions and test them

type DefTrio = (Context, Formula, Formula)

findDef :: Formula -> Context -> Maybe DefTrio
findDef trm cx  = dive Top 0 $ cnForm cx
  where
    dive gs _ (Iff (Ann DHD (Trm "=" [Var v _, t] _)) f) | isTrm t
                                  = fine gs t $ Ann DEQ $ subst t v f
    dive gs _ (Imp (Ann DHD (Trm "=" [Var v _, t] _)) f) | isTrm t
                                  = fine gs t $ Ann DIM $ subst t v f
    dive gs _ (Iff (Ann DHD t) f) = fine gs t $ Ann DEQ f
    dive gs _ (Imp (Ann DHD t) f) = fine gs t $ Ann DIM f

    dive gs n (All u f) = dive gs (succ n) $ inst ('?':show n) 0 f
    dive gs n (Imp g f) = dive (bool $ And gs g) n f
    dive _ _ _          = mzero

    fine gs tr@(Trm t _ _) fr =
      do  ngs <- match otr trm `ap` return gs
          nfr <- match otr (wipeDEQ trm) `ap` return fr
          return (cx, ngs, trm { trName = t, trInfo = [nfr] })
      where otr = tr { trName = takeWhile (/= ':') t }

testDef :: Bool -> [Context] -> Context -> Formula -> DefTrio -> RM Formula
testDef hard cnt cx trm (dc, gs, nt)
    = do  whdchk outlog
          guards <> (whdchk failed >> mzero)
          whdchk passed; return nt
  where
    guards  | hard  = reason cnt $ setForm cx gs
            | True  = guard $ isTop $ {- reduce -} gs
    outlog  | hard  = rlog (cnHead cx) $ header
            | True  = return ()
    passed  | hard  = rlog0 "check passed"
            | True  = rlog (cnHead cx) $ header ++ "... passed"
    failed  | hard  = rlog0 "check failed"
            | True  = rlog (cnHead cx) $ header ++ "... failed"

    header  = "check: " ++ showsPrec 2 trm " vs " ++ versus
    versus  = if cnTopL dc then cnName dc else "(internal)"
    whdchk  = whenIB IBdchk False


-- Infer ad hoc definitions

specDef :: Formula -> Formula
specDef  (Trm "=" [l, r] is) | not (null nds)
        = Trm "=" [l, nullDEQ r] (nds ++ is)
  where
    nds = map (Ann DEQ . replace (wipeDEQ l) r) (trInfoE r)

specDef trm@(Trm t ts is) = foldr add (Trm t [] is) ts
  where
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
    dive gs n (All u f) = dive gs (succ n) $ inst ('?':show n) 0 f
    dive gs n (And f g) = dive gs n f `mplus` dive gs n g
    dive gs n (Imp g f) = dive (bool $ And gs g) n f
    dive _ _ _          = mzero

    fine gs tr@(Trm t _ _) fr =
      do  ngs <- match tr trm `ap` return gs
          nfr <- match tr (wipeDEQ trm) `ap` return fr
          guard $ gut ngs && gut nfr && isTop ({- reduce -} ngs)
          return nfr

    gut (Var ('?':_) _) = False
    gut f = allF gut $ nullInfo f


-- Service stuff

nullDEQ f | hasInfo f = let isDEQ (Ann DEQ _) = True ; isDEQ _ = False
                        in  f { trInfo = filter (not . isDEQ) (trInfo f) }
          | otherwise = f

wipeDEQ = skipInfo (mapF wipeDEQ) . nullDEQ

