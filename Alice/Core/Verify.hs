module Alice.Core.Verify (verify) where

import Control.Monad

import Alice.Core.Base
import Alice.Core.Define
import Alice.Core.Local
import Alice.Core.Reason
import Alice.Core.Thesis
import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Instr
import Alice.Data.Text
import Alice.Export.Base
import Alice.Import.Reader

-- Main verification loop

verify rst bs = runRM (vLoop False (Context Bot []) [] [] bs) rst

vLoop :: Bool -> Context -> [Block] -> [Context] -> [Text] -> RM [Text]
vLoop mot ths brn cnt (TB bl@(Block fr pr sg dv nm ls la fn li tx) : bs) =
  do  let sect = blLabl bl ++ showForm 0 bl ""
          sout = '[' : la ++ "] " ++ sect
      whenIB IBtran False $ putStrRM sout
      incRSCI CIsect

      let nbr = bl : brn
          cbl = Context fr nbr

      nfr <- fillDef ths cnt cbl

      flt <- askRSIB IBflat False
      let sth = Context (foldr zExi nfr dv) nbr
          bsg = null brn || blSign (head brn)
          smt = bsg && sg && not (noForm bl)
          spr = if flt then [] else pr

      npr <- if smt then splitTh smt sth nbr cnt spr
                    else splitTh smt ths nbr cnt pr

      mtv <- askRSIB IBmotv True
      let nbl = bl { blForm = deICH nfr, blBody = npr }
          nct = Context (formulate nbl) nbr : cnt
          (nmt, nth) = if mtv then thesis nct ths
                              else (sg, ths)

      nbs <- splitTh (mot && nmt) nth brn nct bs

      let fth = Imp (compose $ TB nbl : nbs) (cnForm ths)
      splitTh (mot && not nmt) (setForm ths fth) brn cnt []

      return $ TB nbl : nbs

vLoop True ths brn cnt [] = whenIB IBprov True prove >> return []
  where
    prove = do  let rl = rlog bl $ "goal: " ++ tx
                    bl = cnHead ths ; tx = blText bl
                incRSCI CIgoal ; whenIB IBgoal True rl
                reason cnt ths <>
                  (guardIB IBigno False >> incRSCI CIfail)

vLoop mot ths brn cnt (TI ins : bs) =
      procTI mot ths brn cnt ins >> vLoop mot ths brn cnt bs

vLoop mot ths brn cnt (TD ind : bs) =
      procTD mot ths brn cnt ind >> vLoop mot ths brn cnt bs

vLoop _ _ _ _ _ = return []


splitTh mot ths brn cnt bs = dive id cnt $ cnForm ths
  where
    dive c cn (Imp (Ann DIH f) g)  | closed f
                                   = dive c (setForm ths f : cn) g
    dive c cn (Imp (Ann DCH f) g)  | closed f
                                   = dive c (setForm ths f : cn) g
    dive c cn (Imp f g)            = dive (c . Imp f) cn g
    dive c cn (All v f)            = dive (c . All v) cn f
    dive c cn f                    = vLoop mot (setForm ths $ c f) brn cn bs

deICH = dive id
  where
    dive c (Imp (Ann DIH f) g)  = c g
    dive c (Imp (Ann DCH f) g)  = c $ Not f
    dive c (Imp f g)            = dive (c . Imp f) g
    dive c (All v f)            = dive (c . All v) f
    dive c f                    = c f


-- Instruction handling

procTI mot ths brn cnt = proc
  where
    proc (InCom ICthes)
      = do  let smt = if mot then "(mot): " else "(nmt): "
            rlog0 $ "current thesis " ++ smt ++ show (cnForm ths)

    proc (InCom ICsimp)
      = do  let tlb = filter cnTopL cnt
                tlf = map (lichten . cnForm) tlb
                srl = filter (not . isTop) tlf
            rlog0 $ "current simple rules:"
            mapM_ printRM srl

    proc (InCom _)  = rlog0 $ "unsupported instruction"

    proc (InBin IBverb False)
      = do  addRSIn $ InBin IBgoal False
            addRSIn $ InBin IBtran False
            addRSIn $ InBin IBdchk False
            addRSIn $ InBin IBunfl False
            addRSIn $ InBin IBrlog False
            addRSIn $ InBin IBplog False
            addRSIn $ InBin IBtask False

    proc (InBin IBverb True)
      = do  try IBgoal True
        <>  try IBrlog False
        <>  try IBtran False
        <>  try IBdchk False
        <>  try IBplog False
        <>  try IBunfl False
        <>  try IBtask False
        <>  return ()
      where
        try i d = askRSIB i d >>= guard . not
                    >> addRSIn (InBin i True)

    proc (InStr ISread "-") = proc (InStr ISread "")

    proc (InStr ISread file)
      = do  let fn = if null file then "stdin" else file
            txt <- timer CTpars $ justIO $ readText file
            trn <- askRSIB IBtext False
            if trn then mapM_ printRM txt else
              do  rlog0 $ fn ++ ": verification started"
                  let success = rlog0 $ fn ++ ": verification successful"
                      failure = rlog0 $ fn ++ ": verification failed"
                  (vLoop mot ths brn cnt txt >> success) <> failure

    proc (InStr ISprdb file)
      = do  prd <- justIO $ readPrDB file
            updateRS $ \ rs -> rs { rsPrdb = prd }

    proc i  = addRSIn i

procTD mot ths brn cnt = proc
  where
    proc i  = drpRSIn i

