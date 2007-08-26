module Alice.Core.Reason where

import Control.Monad

import Alice.Core.Base
import Alice.Core.Local
import Alice.Core.Unfold
import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Instr
import Alice.Data.Text
import Alice.Export.Prover

-- Reasoner

reason :: [Context] -> Context -> RM ()
reason cnt tc = do  dlp <- askRSII IIdpth 7
                    flt <- askRSIB IBfilt True
                    dfl <- askRSIB IBdefn True
                    let nct = context (flt && dfl) cnt tc
                    goalseq dlp nct tc $ splitG $ cnForm tc

goalseq :: Int -> [Context] -> Context -> [Formula] -> RM ()
goalseq n cnt tc (f:fs) = do  when (n == 0) $ rde >> mzero
                              trv <> launch cnt ntc <> dlp
                              unless (null fs) dga
                              goalseq n (ntc : cnt) tc fs
  where
    rfr = reduce f
    ntc = setForm tc rfr

    trv = sbg >> guard (isTop rfr) >> tri
    dlp = do  tsk <- unfold $ setForm tc (Not rfr) : cnt
              let Context {cnForm = Not nfr} : nct = tsk
              goalseq (pred n) nct tc $ splitG nfr

    rde = whenIB IBrlog False $ rlog0 $ "reasoning depth exceeded"
    dga = whenIB IBrlog False $ rlog0 $ "passing to the next subgoal"
    sbg = whenIB IBrlog False $ rlog0 $ "subgoal: " ++ show f
    tri = whenIB IBplog False $ rlog0 $ "trivial"

goalseq _ _ _ _ = return ()


-- Call prover

launch :: [Context] -> Context -> RM ()
launch cnt tc = do  incRSCI CIprov; whenIB IBtask False debug
                    prd <- askRS rsPrdb ; ins <- askRS rsInst
                    let prv = justIO $ export prd ins cnt tc
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
                let tlb = map cnForm (tc:cnt)
                mapM_ printRM $ reverse tlb


-- Goal splitting

splitG :: Formula -> [Formula]
splitG fr = spl $ albet $ strip fr
  where
    spl (All u f) = liftM (All u) (splitG f)
    spl (And f g) = mplus (splitG f) (splitG g)
    spl (Or f g)  = liftM2 zOr (splitG f) (splitG g)
    spl _         = return fr


-- Context filtering

context :: Bool -> [Context] -> Context -> [Context]
context df cnt tc = filter (not . isTop . cnForm) $ map chk cnt
  where
    chk c | tst c = c { cnForm = lichten $ cnForm c }
          | True  = c

    tst c | cnLowL c  = False
          | null ls   = df && isDefn (cnForm c)
          | otherwise = cnName c `notElem` ls

    ls = cnLink tc

lichten :: Formula -> Formula
lichten = sr
  where
    sr (Iff (Ann DHD (Trm "=" [_, t] _)) f)
         | isTrm t  = sr $ subst t "." $ inst "." 0 f
    sr (Imp (Ann DHD (Trm "=" [_, t] _)) f)
         | isTrm t  = sr $ subst t "." $ inst "." 0 f
    sr (Iff f g)    = sr $ zIff f g
    sr (All v f)    = bool $ All v $ sr f
    sr (And f g)    = bool $ And (sr f) (sr g)
    sr (Imp f g)    = bool $ Imp (sm f) (sr g)
    sr (Ann _ f)    = sr f
    sr f | isEqu f  = sr $ foldr And Top $ trInfoI f
    sr f | isSort f = f
    sr _            = Top

    sm (Or  f g)    = bool $ Or  (sm f) (sm g)
    sm (And f g)    = bool $ And (sm f) (sm g)
    sm (Ann _ f)    = sm f
    sm f | isUnit f = f
    sm _            = Bot

