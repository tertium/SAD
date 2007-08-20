module Alice.Core.Reason where

import Control.Monad

--import Alice.Core.Local
import Alice.Core.Base
import Alice.Data.Context
import Alice.Data.Formula
import Alice.Data.Instr
import Alice.Data.Text
import Alice.Export.Prover

-- Reasoner

reason :: [Context] -> Context -> RM ()
reason cnt tc = do  dlp <- askRSII IIdpth 7
                    let nct = context (cnLink tc) cnt
                        gls = splitG $ cnForm tc
                    goalseq dlp nct tc gls

goalseq :: Int -> [Context] -> Context -> [Formula] -> RM ()
goalseq n cnt tc (f:fs) = do  trv <> lnc -- <> dlp
                              unless (null fs) dga
                              goalseq n nct tc fs
  where
    rfr = {- reduce -} f
    lnc = launch cnt rfr
--    dlp = defloop n cnt tc rfr
    nct = tc { cnForm = f } : cnt
    trv = sbg >> guard (isTop rfr) >> tri

    dga = whenIB IBsplt False $ rlog0 $ "passing to the next subgoal"
    sbg = whenIB IBsplt False $ rlog0 $ "subgoal: " ++ show f
    tri = whenIB IBplog False $ rlog0 $ "trivial"

goalseq _ _ _ _ = return ()

{-
defloop 0 _ _ = mzero
defloop n c f = do  tsk <- markup (dumbF (Not f) : c)
                    let exs = concatMap (markedF . formulate) tsk
                    guard $ not $ null exs; onVerb 1 $ xout exs
                    let (nb:nc) = expand n tsk
                        Block { blForm = Not nf } = nb
                    goalseq (pred n) nc $ splitG nf
  where
    xout es = rlog0 $ "unfold: " ++ concatMap xo es
    xo fr = ' ' : showsPrec 3 fr ""
-}

launch :: [Context] -> Formula -> RM ()
launch cnt fr = do  incRSCI CIprov; whenIB IBtask False debug
                    prd <- askRS rsPrdb ; ins <- askRS rsInst
                    let prv = justIO $ export prd ins cnt fr
                    timer CTprov prv >>= guard
  where
{-
    axc = dumbF (Not fr) : cnt
    bxc@(_:cxc) = axc ++ concatMap (pre . formulate) axc

    pre f@(Trm t ts _ _) | isSC f
          = let vs = map (zVar.('x':).show) [1..length ts]
            in  [dumbF $ foldr All (zSet $ zTrm t vs) vs]
    pre f | isTrm f = concatMap pre (trArgs f)
    pre v | isVar v = []; pre f = foldF pre [] (++) f
-}
    debug = do  rlog0 "prover task:"
                let tlb = fr : map cnForm cnt
                mapM_ printRM $ reverse tlb


-- Goal splitting

splitG :: Formula -> [Formula]
splitG fr = spl $ albet $ strip fr
  where
    spl (All u f) = liftM (All u) (splitG f)
    spl (And f g) = mplus (splitG f) (splitG g)
    spl (Or f g)  = liftM2 Or (splitG f) (splitG g)
    spl _         = return fr


-- Context filtering

context :: [String] -> [Context] -> [Context]
context ls cnt = filter (not . isTop . cnForm) $ map chk cnt
  where
    chk c | tst c = c
          | True  = c { cnForm = lichten $ cnForm c }

    tst c | not (cnIsTL c)  = True
          | null ls         = True -- not $ isDefn $ cnForm c
          | otherwise       = cnName c `elem` ls

lichten :: Formula -> Formula
lichten = sr . strip
  where
    sr (Iff (Ann DHD (Trm "=" [_, t] _)) f)
         | isTrm t  = sr $ strip $ subst t "." $ inst "." 0 f
    sr (Imp (Ann DHS (Trm "=" [_, t] _)) f)
         | isTrm t  = sr $ strip $ subst t "." $ inst "." 0 f
    sr (Iff f g)    = sr $ zIff f g
    sr (All v f)    = bool $ All v $ sr $ strip f
    sr (And f g)    = bool $ And (sr $ strip f) (sr $ strip g)
    sr (Imp f g)    = bool $ Imp (sm $ strip f) (sr $ strip g)
    sr f | isEqu f  = sr $ foldr And Top $ trInfoI f
    sr f | isSort f = f
    sr _            = Top

    sm (Or  f g)    = bool $ Or  (sm $ strip f) (sm $ strip g)
    sm (And f g)    = bool $ And (sm $ strip f) (sm $ strip g)
    sm f | isUnit f = f
    sm _            = Bot


-- Service stuff

isDefn :: Formula -> Bool
isDefn (Iff (Ann DHD _) _)  = True
isDefn (All _ f)            = isDefn f
isDefn (Imp _ f)            = isDefn f
isDefn _                    = False

isSign :: Formula -> Bool
isSign (Imp (Ann DHS _) _)  = True
isSign (All _ f)            = isSign f
isSign (Imp _ f)            = isSign f
isSign _                    = False

isSort :: Formula -> Bool
isSort (Not f)            = isEqu $ strip f
isSort (Trm ('a':_) _ _)  = True
isSort (Trm _ [_] _)      = True
isSort _                  = False

