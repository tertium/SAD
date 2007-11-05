{-
 -  Parser/Prim.hs -- core parser primitives
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

module Alice.Parser.Prim where

import Control.Monad
import Data.Char
import Data.List

import Alice.Parser.Base
import Alice.Parser.Token

-- Lexical primitives

nextToken, readToken :: LPM a Token
nextToken = getPS >>= nxtk
  where
    nxtk (PState pr po pl (t:ts) pd pf pp)
            = setPS (PState pr (succ po) pl ts (t:pd) pf pp) >> return t
    nxtk _  = nextfail $ "unexpected end of input"

nextEOI, readEOI :: LPM a ()
nextEOI = getPS >>= reoi
  where
    reoi (PState _ _ _ (t:_) _ _ _)
            = nextfail $ "unexpected token '" ++ show t ++ "'"
    reoi _  = return ()

skipSpace :: LPM a b -> LPM a b
skipSpace p = after p (getPS >>= sptk)
  where
    sptk (PState pr po pl (t@(TkSpc n):ts) pd pf pp)
            = setPS (PState pr (succ po) (pl + n) ts (t:pd) pf pp)
    sptk _  = return ()

nextTkChr, readTkChr :: LPM a Char
nextTkChr = nextToken >>= nxch
  where
    nxch (TkChr c)  = return c
    nxch t  = fail $ "unexpected token '" ++ show t ++ "'"

nextTkLex, readTkLex :: LPM a String
nextTkLex  = nextToken >>= nxwr
  where
    nxwr (TkLex w)  = return w
    nxwr t  = fail $ "unexpected token '" ++ show t ++ "'"

nextCharOf, readCharOf, charOf :: [Char] -> LPM a ()
nextCharOf cs = nextTkChr >>= nxch
  where
    nxch c  | c `elem` cs = return ()
            | otherwise   = fail $ "unexpected char '" ++ c : "'"

nextChar, readChar, char :: Char -> LPM a ()
nextChar  = nextCharOf . (:[])

nextWordOf, readWordOf, wordOf :: [String] -> LPM a ()
nextWordOf ws = nextTkLex >>= nxwr . map toLower
  where
    nxwr w  | w `elem` ws = return ()
            | otherwise   = fail $ "unexpected word '" ++ w ++ "'"

nextWord, readWord, word :: String -> LPM a ()
nextWord  = nextWordOf . (:[])

nextString, readString, string :: String -> LPM a ()
nextString s@(c:cs) = nextToken >>= nxtk
  where
    nxtk (TkChr d)  | c == d          = nextString cs
    nxtk (TkLex w)  | isPrefixOf w s  = nextString $ drop (length w) s
    nxtk t  = fail $ "unexpected token '" ++ show t ++ "'"
nextString _  = return ()

readEOI     = skipSpace nextEOI
readToken   = skipSpace nextToken
readTkChr   = skipSpace nextTkChr
readTkLex   = skipSpace nextTkLex

readCharOf  = skipSpace . nextCharOf
readChar    = skipSpace . nextChar
readWordOf  = skipSpace . nextWordOf
readWord    = skipSpace . nextWord
readString  = skipSpace . nextString

charOf      = skipSpace . nextCharOf
char        = skipSpace . nextChar
wordOf      = skipSpace . nextWordOf
word        = skipSpace . nextWord
string      = skipSpace . nextString


-- Grammar primitives

infixr 1 -|-
(-|-) :: LPM a b -> LPM a b -> LPM a b
(-|-) = mplus

infixr 1 -/-
(-/-) :: LPM a b -> LPM a b -> LPM a b
(-/-) = mtry

opt :: b -> LPM a b -> LPM a b
opt a m = m -|- return a

optEx :: b -> LPM a b -> LPM a b
optEx a m = m -/- return a

after :: LPM a b -> LPM a c -> LPM a b
after a b = a >>= ((b >>) . return)

expar, exbrk, exbrc :: LPM a b -> LPM a b
expar p = readChar '(' >> after p (readChar ')')
exbrk p = readChar '[' >> after p (readChar ']')
exbrc p = readChar '{' >> after p (readChar '}')

paren :: LPM a b -> LPM a b
paren p = p -|- expar p

parenEx :: LPM a b -> LPM a b
parenEx p = p -/- expar p

chnop :: LPM a b -> LPM a [b]
chnop p = liftM2 (:) p $ opt [] $ chnop p

chain :: LPM a c -> LPM a b -> LPM a [b]
chain o p = liftM2 (:) p $ opt [] $ o >> chain o p

chnopEx :: LPM a b -> LPM a [b]
chnopEx p = liftM2 (:) p $ optEx [] $ chnopEx p

chainEx :: LPM a c -> LPM a b -> LPM a [b]
chainEx o p = liftM2 (:) p $ optEx [] $ o >> chainEx o p

narrow :: Show b => LPM a b -> LPM a b
narrow m  = mtie m amb
  where
    amb [_] a = return a
    amb as  _ = nextfail $ "ambiguity:" ++ concatMap msg as
    msg a     = "\n    " ++ show a

