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
            | ICthes  --  print current thesis
            | ICsimp  --  print current simplified context
            deriving (Eq,Show)

data InInt  = IItlim  --  time limit per prover launch  (3 sec)
            | IIdpth  --  number of reasoner iterations (7)
            | IIchtl  --  time limit for checker's tasks (1 sec)
            | IIchdl  --  depth limit for checker's tasks (3)
            deriving (Eq,Show)

data InBin  = IBprov  --  prove goals (yes)
            | IBdefn  --  look for applicable definitions (yes)
            | IBinfo  --  accumulate evidences (yes)
            | IBfilt  --  simplify the context (yes)
            | IBflat  --  do not descend into proofs (no)
            | IBmotv  --  modify thesis (yes)
            | IBigno  --  ignore failed proofs (no)
            | IBgoal  --  print current goal (yes)
            | IBtran  --  print current sentence (no)
            | IBdchk  --  print definition checks (no)
            | IBunfl  --  print definition unfolds (no)
            | IBrlog  --  print reasoner's log (no)
            | IBplog  --  print prover's log (no)
            | IBtask  --  print inference tasks (no)
            | IBdump  --  dump tasks in prover's syntax (no)
            | IBtext  --  translation only
            | IBverb  --  verbosity control
            | IBhelp  --  print help
            deriving (Eq,Show)

data InStr  = ISinit  --  init file
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
          (ICthes,  ["thesis"]),
          (ICsimp,  ["rules"]) ]

setII :: [(InInt, [String])]
setII = [ (IItlim,  ["timelimit"]),
          (IIdpth,  ["depthlimit"]),
          (IIchtl,  ["checktime"]),
          (IIchdl,  ["checkdepth"]) ]

setIB :: [(InBin, [String])]
setIB = [ (IBprov,  ["prove"]),
          (IBdefn,  ["check"]),
          (IBinfo,  ["info"]),
          (IBfilt,  ["filter"]),
          (IBflat,  ["flat"]),
          (IBmotv,  ["trim"]),
          (IBigno,  ["skipfail"]),
          (IBgoal,  ["printgoal"]),
          (IBtran,  ["printsection"]),
          (IBdchk,  ["printcheck"]),
          (IBunfl,  ["printunfold"]),
          (IBrlog,  ["printreason"]),
          (IBplog,  ["printprover"]),
          (IBtask,  ["printfulltask"]),
          (IBdump,  ["dump"]) ]

setIS :: [(InStr, [String])]
setIS = [ (ISread,  ["read"]),
          (ISprdb,  ["provers"]),
          (ISprvr,  ["prover"]) ]

readIX :: (MonadPlus m) => [(a, [String])] -> String -> m a
readIX ix s = msum $ map (return . fst) $ filter (elem s . snd) ix

