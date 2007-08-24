module Alice.Core.Reason where

import Control.Monad

import Alice.Core.Base
--import Alice.Core.Local
import Alice.Core.Unfold
import Alice.Data.Context
import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Instr
import Alice.Data.Text
import Alice.Export.Prover

-- Reasoner

reason :: [Context] -> Context -> RM ()
reason cnt tc = do  dlp <- askRSII IIdpth 7
                    dfl <- askRSIB IBchck True
                    let nct = context dfl (cnLink tc) cnt
                    goalseq dlp nct tc $ splitG $ cnForm tc

goalseq :: Int -> [Context] -> Context -> [Formula] -> RM ()
goalseq n cnt tc (f:fs) = do  when (n == 0) $ rde >> mzero
                              trv <> launch cnt rfr <> dlp
                              unless (null fs) dga
                              goalseq n nct tc fs
  where
    rfr = {- reduce -} f
    nct = tc { cnForm = rfr } : cnt

    trv = sbg >> guard (isTop rfr) >> tri
    dlp = do  tsk <- unfold $ tc {cnForm = Not rfr} : cnt
              let Context {cnForm = Not nfr} : nct = tsk
              goalseq (pred n) nct tc $ splitG nfr

    rde = whenIB IBrlog False $ rlog0 $ "reasoning depth exceeded"
    dga = whenIB IBrlog False $ rlog0 $ "passing to the next subgoal"
    sbg = whenIB IBrlog False $ rlog0 $ "subgoal: " ++ show f
    tri = whenIB IBplog False $ rlog0 $ "trivial"

goalseq _ _ _ _ = return ()


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

context :: Bool -> [String] -> [Context] -> [Context]
context df ls cnt = filter (not . isTop . cnForm) $ map chk cnt
  where
    chk c | tst c = c { cnForm = lichten $ cnForm c }
          | True  = c

    tst c | not (cnIsTL c)  = False
          | null ls         = df && isDefn (cnForm c)
          | otherwise       = cnName c `notElem` ls

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

