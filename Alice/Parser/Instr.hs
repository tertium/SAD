{-
 -  Parser/Instr.hs -- instruction parsing
 -  Copyright (c) 2001,2004,2007   Andrei Paskevich <atertium@gmail.com>
 -
 -  This file is part of SAD/Alice - a mathematical text verifier.
 -
 -  SAD/Alice is free software; you can redistribute it and/or modify
 -  it under the terms of the GNU General Public License as published by
 -  the Free Software Foundation; either version 3 of the License, or
 -  (at your option) any later version.
 -
 -  SAD/Alice is distributed in the hope that it will be useful,
 -  but WITHOUT ANY WARRANTY; without even the implied warranty of
 -  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 -  GNU General Public License for more details.
 -
 -  You should have received a copy of the GNU General Public License
 -  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 -}

module Alice.Parser.Instr (instr,iread,iexit,idrop) where

import Control.Monad

import Alice.Data.Instr
import Alice.Parser.Base
import Alice.Parser.Prim

-- Instructions

instr :: LPM a Instr
instr = nulText >> exbrk (readTkLex >>= readIn >>= gut)
  where
    gut (InStr ISread _)  = nextfail "'read' not allowed here"
    gut (InCom ICexit)    = nextfail "'exit'/'quit' not allowed here"
    gut i = return i

iread :: LPM a Instr
iread = nulText >> exbrk (readTkLex >>= readIn >>= gut)
  where
    gut i@(InStr ISread _)  = return i
    gut _ = mzero

iexit :: LPM a ()
iexit = nulText >> exbrk (readTkLex >>= readIn >>= gut)
  where
    gut (InCom ICexit)  = return ()
    gut _ = mzero

idrop :: LPM a Idrop
idrop = nulText >> exbrk (char '/' >> readTkLex >>= readId)

readIn :: String -> LPM a Instr
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

readId :: String -> LPM a Idrop
readId n = readIC -|- readII -|- readIB -|- readIS -|- errins
  where
    readIC  = liftM IdCom (readIX setIC n)
    readII  = liftM IdInt (readIX setII n)
    readIB  = liftM IdBin (readIX setIB n)
    readIS  = liftM IdStr (readIX setIS n)
    errins  = nextfail $ "unknown instruction: " ++ n

readTok :: LPM a String
readTok = skipSpace $ liftM concat $ chnop (lxm -|- chr)
  where
    lxm = nextTkLex ; chr = nextTkChr >>= chk
    chk ']' = mzero ; chk c = return [c]

