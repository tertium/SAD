module Alice.Parser.Instr (instr,iread,iexit,idrop) where

import Control.Monad

import Alice.Data.Instr
import Alice.Parser.Base
import Alice.Parser.Prim

-- Instructions

instr :: (MonadPlus m, MonadPS m) => m Instr
instr = nulText >> exbrk (readTkLex >>= readIn >>= gut)
  where
    gut (InStr ISread _)  = fail "'read' not allowed here"
    gut (InCom ICexit)    = fail "'exit'/'quit' not allowed here"
    gut i = return i

iread :: (MonadPlus m, MonadPS m) => m Instr
iread = nulText >> exbrk (readTkLex >>= readIn >>= gut)
  where
    gut i@(InStr ISread _)  = return i
    gut _ = mzero

iexit :: (MonadPlus m, MonadPS m) => m ()
iexit = nulText >> exbrk (readTkLex >>= readIn >>= gut)
  where
    gut (InCom ICexit)  = return ()
    gut _ = mzero

idrop :: (MonadPlus m, MonadPS m) => m Idrop
idrop = nulText >> exbrk (char '/' >> readTkLex >>= readId)

readIn :: (MonadPlus m, MonadPS m) => String -> m Instr
readIn n  = readIC -|- readII -|- readIB -|- readIS -|- errins
  where
    readIC  = liftM  InCom (readIX setIC n)
    readII  = liftM2 InInt (readIX setII n) (readTok >>= readint)
    readIB  = liftM2 InBin (readIX setIB n) (readTok >>= readbin)
    readIS  = liftM2 InStr (readIX setIS n) (readTok)
    errins  = nextfail $ "unknown instruction: " ++ n

    readint s = case reads s of
      ((n,[]):_) | n >= 0 ->  return n
      _                   ->  readerr s

    readbin "yes" = return True
    readbin "on"  = return True
    readbin "no"  = return False
    readbin "off" = return False
    readbin s     = readerr s

    readerr s = nextfail $ "invalid instruction argument: " ++ s

readId :: (MonadPlus m, MonadPS m) => String -> m Idrop
readId n = readIC -|- readII -|- readIB -|- readIS -|- errins
  where
    readIC  = liftM IdCom (readIX setIC n)
    readII  = liftM IdInt (readIX setII n)
    readIB  = liftM IdBin (readIX setIB n)
    readIS  = liftM IdStr (readIX setIS n)
    errins  = nextfail $ "unknown instruction: " ++ n

readTok :: (MonadPlus m, MonadPS m) => m String
readTok = skipSpace $ liftM concat $ chnop (lex -|- chr)
  where
    lex = nextTkLex ; chr = nextTkChr >>= chk
    chk ']' = mzero ; chk c = return [c]

