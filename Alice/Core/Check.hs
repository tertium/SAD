module Alice.Core.Check (fillDef) where

import Control.Monad
import Data.Maybe

import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Instr
import Alice.Data.Text
import Alice.Core.Base
import Alice.Core.Info
import Alice.Core.Reason

fillDef :: Context -> [Context] -> Context -> RM Formula
fillDef ths cnt cx  = fill True False [] (Just True) 0 $ cnForm cx
  where
    fill pr nw fc sg n (Tag DHD f)
      = liftM (Tag DHD) $ fill pr True fc sg n f
    fill _ _ fc _ _ t | isThesis t
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
    fill pr nw fc sg n f = roundFM (fill pr nw) fc sg n f

    sinfo uin pr cnt trm
      | uin   = setInfo pr cnt trm
      | True  = trm { trInfo = osd }
      where
        osd = map (Tag DEQ) (trInfoE trm) ++
              map (Tag DSD) (trInfoS trm)

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
    dive gs _ (Iff (Tag DHD (Trm "=" [Var v _, t] _)) f) | isTrm t
                                  = fine gs t $ Tag DEQ $ subst t v f
    dive gs _ (Imp (Tag DHD (Trm "=" [Var v _, t] _)) f) | isTrm t
                                  = fine gs t $ Tag DIM $ subst t v f
    dive gs _ (Iff (Tag DHD t) f) = fine gs t $ Tag DEQ f
    dive gs _ (Imp (Tag DHD t) f) = fine gs t $ Tag DIM f

    dive gs n (All _ f) = dive gs (succ n) $ inst ('?':show n) f
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
                          reason cnt $ setForm cx gs; incRSCI CIchky
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


-- Infer ad hoc definitions

specDef :: Formula -> Formula
specDef trm@(Trm "=" [l, r] _) | not (null nds)  = ntr
  where
    ntr = Trm "=" [l, r { trInfo = map (Tag DIM) $ trInfoI r }] (ods ++ nds)
    ods = map (Tag DIM) (trInfoI trm) ++ map (Tag DEQ) (trInfoE trm)
    nds = map (Tag DSD . replace (wipeInfo l) r) $ trInfoD r

specDef trm | isTrm trm = otr { trInfo = nds }
  where
    (nds, otr) = pas ods trm
    ods = map (Tag DIM) (trInfoI trm) ++ map (Tag DEQ) (trInfoE trm)

    pas ds t | isTrm t
      = let (nd, as) = foldr arg (ds, []) $ trArgs t
        in  (nd, t { trArgs = as })
    pas ds t = (ds, t)

    arg a (ds, as)
      = let (ad, na) = pas ds a
            (nd, is) = foldr tst (ad, []) $ trInfo a
        in  (nd, na { trInfo = is } : as)

    tst a@(Tag DEQ d) (nd, ds)
      = case specDig trm d
        of  Just f  ->  (Tag DSD f : nd, ds)
            _       ->  (nd, a : ds)

    tst a@(Tag DSD d) (nd, ds)
      = case specDig trm d
        of  Just f  ->  (Tag DSD f : nd, ds)
            _       ->  (nd, a : ds)

    tst a@(Tag DIM (Not d)) (nd, ds)
      = let (ni, _) = foldr tst (nd, []) $ concatMap trInfo $ trInfoO d
        in  (ni, a : ds)

    tst a@(Tag DIM d) (nd, ds)
      = let (ni, _) = foldr tst (nd, []) $ trInfo d
        in  (ni, a : ds)

    tst a (nd, ds)  = (nd, a : ds)

specDef f = f

specDig :: (MonadPlus m) => Formula -> Formula -> m Formula
specDig trm = dive Top 0
  where
    dive gs _ (Iff (Trm "=" [l@(Var v@('?':_) _), t] _) f)
      | isTrm t && not (occurs l t) = fine gs t $ subst t v f
    dive gs _ (Iff t f) | isTrm t   = fine gs t f
    dive gs n (All _ f) = dive gs (succ n) $ inst ('?':show n) f
    dive gs n (Imp g f) = dive (bool $ And gs g) n f
    dive gs n (And f g) = dive gs n f `mplus` dive gs n g
    dive _ _ _          = mzero

    fine gs tr@(Trm t _ _) fr =
      do  nfr <- match tr wtr `ap` return fr; guard $ green nfr
          ngs <- match tr trm `ap` return gs; guard $ green ngs
          guard $ rapid ngs; return nfr

    wtr = wipeInfo trm

