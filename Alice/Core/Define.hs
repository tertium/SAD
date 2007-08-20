module Alice.Core.Define where

import Alice.Data.Formula
import Alice.Data.Text
import Alice.Core.Local

fillDef cnt bl  = fill True cnt True $ blForm bl
  where
    fill pr cn sg (Ann DHD (Trm "=" [v, trm@(Trm t vs _ _)] _ _))
                      = liftM (Ann DHD . zEqu v . nullD) $ defs cn trm True
    fill pr cn sg (Ann DHD trm@(Trm t vs _ _))
                      = liftM (Ann DHD . nullD) $ defs cn trm True
    fill pr cn sg v@(Var _ _)
                      = return $ setDLV cn pr v
    fill pr cn sg f@(Trm t ts is df)
                      = do  nts <- mapM (fill False cn sg) ts
                            ndf <- mapM (fill True  cn sg) df
                            let rdf = map (rebind ('.':)) ndf
                            dtr <- defs cn (Trm t nts is rdf) False
                            let nbl = setDLV cn pr (specDef dtr)
                                fin [Ann _ _] = nullD nbl
                                fin _         = nbl
                            return $ fin $ trDefn nbl

    fill pr cn sg f   = roundFM (fill pr) cn sg f

    defs cn trm@(Trm t _ _ _) n
                      = do  let dfs = filter (relev t) cnt
                                spc = t ++ show (length dfs)
                            (guard (isDigit $ last t) >> return trm)
                              <> (guard (head t == '#') >> return trm)
                              <> msum (map (testDef cn bl trm False) dfs)
                              <> (guardPas >> return trm)
                              <> (guard (t == "=") >> return trm)
                              <> msum (map (testDef cn bl trm True) dfs)
                              <> (guard n >> return trm { trName = spc })
                              <> (failed trm >> mzero)

    relev t b = let def = blForm $ last $ textB $ blProf b
                    dtr = fst $ break isDigit $ fst $ headDef def
                in  (comtype b == Defn || comtype b == Desc) && dtr == t

    failed f  = rlog (blLine bl) $ showString "cannot recoginze symbol: "
                $ showsPrec 2 f ""


testDef cnt bl tr@(Trm _ ts _ _) hard dbl
    = do  outlog; mapM_ (check . regrd) (init block) <> failed
          passed; return $ Trm sc ts [] $ dfn (last block)
  where
    check f | hard  = reason cnt bl f
            | True  = guard $ rapid f
--            | True  = unless (rapid f) $ (rlog 0 $ "dlvs: " ++ show (concatMap trInfo ts)) >> mzero
    block   = map blForm $ textB $ blProf dbl
    regrd f = substs (reface ('g':) f) vs ts
    prepr f = resubst f vs $ map wipeD ts
    (sc,vs) = headDef $ last block

    dfn (Iff (Ann DHD (Trm "=" [v,t] _ _)) f) | isTrm t
                  = [prepr $ subst t v f]
    dfn (Iff _ f) = [prepr f]
    dfn (Imp (Ann DHD (Trm "=" [v,t] _ _)) f) | isTrm t
                  = [Ann DIM $ prepr $ subst t v f]
    dfn (Imp _ f) = [Ann DIM $ prepr f]
    dfn (All _ f) = dfn f

    passed  | hard  = onVerb 1 (rlog 0 "check passed")
            | True  = onVerb 1 (putStrLnIM "passed")
    failed  | hard  = onVerb 1 (rlog 0 "check failed") >> mzero
            | True  = onVerb 1 (putStrLnIM "failed") >> mzero
    outlog  = onVerb 1 $ orlog (blLine bl) $ showString "check: "
                $ showsPrec 2 tr $ " vs " ++ blMark dbl ++ "... "
    orlog   = if hard then rlog else rlogN


specDef f@(Trm "=" [l, r] is _) | isTrm r && not (null $ trDefn r)
  = Trm "=" [l, nullD r] is [replace (wipeD l) r $ head (trDefn r)]

specDef f@(Trm nam [l, r] is _) | isTrm r && elm && std (trDefn r)
  = Trm nam [l, nullD r] is [subst (wipeD l) v c]
  where
    elm = fst (break isDigit nam) == "aElementOf"
    (And _ (And (All v (Imp _ c)) _)) = head (trDefn r)
    std [And _ (And (All (Var ('.':'e':_) _) _) _)] = True
    std _ = False

specDef f = f


headDef (Ann _ f) = headDef f
headDef (All _ f) = headDef f
headDef (Imp f _) = headDef f
headDef (Iff f _) = headDef f
headDef (Trm "=" [_,t] _ _) | isTrm t = headDef t
headDef (Trm t vs _ _) = (t, vs)

