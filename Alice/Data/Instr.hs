module Alice.Data.Instr where

import Control.Monad

data Instr  = InCom InCom
            | InInt InInt Int
            | InBin InBin Bool
            | InStr InStr String
            deriving Show

data Idrop  = IdCom InCom
            | IdInt InInt
            | IdBin InBin
            | IdStr InStr
            deriving Show


-- Instructions

data InCom  = ICexit  --  exit
            | ICPths  --  print current thesis
            | ICPcnt  --  print current simplified context
            deriving (Eq,Show)

data InInt  = IItlim  --  time limit per prover launch  (3 sec)
            | IIdpth  --  number of reasoner iterations (7)
            | IIchtl  --  time limit for checker's tasks (1 sec)
            | IIchdp  --  depth limit for checker's tasks (3)
            deriving (Eq,Show)

data InBin  = IBprov  --  prove goals (yes)
            | IBchck  --  look for applicable definitions (yes)
            | IBsign  --  rename symbols with diverging defs (yes)
            | IBinfo  --  accumulate evidences (yes)
            | IBthes  --  modify thesis (yes)
            | IBfilt  --  simplify the context (yes)
            | IBskip  --  ignore failed goals (no)
            | IBflat  --  do not descend into proofs (no)
            | IBPgls  --  print current goal (yes)
            | IBPrsn  --  print reasoner's log (no)
            | IBPsct  --  print current sentence (no)
            | IBPchk  --  print definition checks (no)
            | IBPprv  --  print prover's log (no)
            | IBPunf  --  print definition unfolds (no)
            | IBPtsk  --  print inference tasks (no)
            | IBPdmp  --  print tasks in prover's syntax (no)
            | IBtext  --  translation only (comline only)
            | IBverb  --  verbosity control (comline only)
            | IBhelp  --  print help (comline only)
            deriving (Eq,Show)

data InStr  = ISinit  --  init file (init.opt)
            | ISread  --  read file
            | ISprdb  --  prover database
            | ISprvr  --  current prover
            deriving (Eq,Show)


-- Ask functions

askIC :: [Instr] -> InCom -> Bool
askIC (InCom n : _) m | n == m  = True
askIC (_ : rs) m = askIC rs m
askIC _ _ = False

askII :: [Instr] -> InInt -> Int -> Int
askII (InInt n v : _) m _ | n == m  = v
askII (_ : rs) m d  = askII rs m d
askII _ _ d = d

askIB :: [Instr] -> InBin -> Bool -> Bool
askIB (InBin n v : _) m _ | n == m  = v
askIB (_ : rs) m d  = askIB rs m d
askIB _ _ d = d

askIS :: [Instr] -> InStr -> String -> String
askIS (InStr n v : _) m _ | n == m  = v
askIS (_ : rs) m d  = askIS rs m d
askIS _ _ d = d

dropI :: [Instr] -> Idrop -> [Instr]
dropI (InCom n   : rs) (IdCom m)  | n == m  = rs
dropI (InInt n _ : rs) (IdInt m)  | n == m  = rs
dropI (InBin n _ : rs) (IdBin m)  | n == m  = rs
dropI (InStr n _ : rs) (IdStr m)  | n == m  = rs
dropI (r : rs) i  = r : dropI rs i
dropI _ _ = []


-- Keywords

setIC :: [(InCom, [String])]
setIC = [ (ICexit,  ["exit", "quit"]),
          (ICPths,  ["thesis"]),
          (ICPcnt,  ["rules"]) ]

setII :: [(InInt, [String])]
setII = [ (IItlim,  ["timelimit"]),
          (IIdpth,  ["depthlimit"]),
          (IIchtl,  ["checktime"]),
          (IIchdp,  ["checkdepth"]) ]

setIB :: [(InBin, [String])]
setIB = [ (IBprov,  ["prove"]),
          (IBchck,  ["check"]),
          (IBsign,  ["sign"]),
          (IBinfo,  ["info"]),
          (IBthes,  ["thesis"]),
          (IBfilt,  ["filter"]),
          (IBskip,  ["skipfail"]),
          (IBflat,  ["flat"]),
          (IBPgls,  ["printgoal"]),
          (IBPsct,  ["printsection"]),
          (IBPchk,  ["printcheck"]),
          (IBPunf,  ["printunfold"]),
          (IBPrsn,  ["printreason"]),
          (IBPprv,  ["printprover"]),
          (IBPtsk,  ["printfulltask"]),
          (IBPdmp,  ["dump"]) ]

setIS :: [(InStr, [String])]
setIS = [ (ISread,  ["read"]),
          (ISprdb,  ["provers"]),
          (ISprvr,  ["prover"]) ]

readIX :: (MonadPlus m) => [(a, [String])] -> String -> m a
readIX ix s = msum $ map (return . fst) $ filter (elem s . snd) ix

