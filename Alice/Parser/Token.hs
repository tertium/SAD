{-
 -  Parser/Token.hs -- split input stream into tokens
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

module Alice.Parser.Token where

import Data.Char
import Data.List

data Token = TkLex String | TkChr Char | TkSpc Int

tokenize :: String -> [Token]

tokenize s  | not (null lx) = TkLex lx : tokenize rs
  where
    (lx,rs) = span isLexem s

tokenize s  | not (null wh) = merge $ tokenize rs
  where
    (wh,rs) = span isSpace s

    merge (TkSpc ml : tl) = TkSpc (nl + ml) : tl
    merge tl              = TkSpc  nl : tl

    nl = length $ filter isNLine wh

tokenize ('#' : rs) = tokenize $ snd $ break isNLine rs
tokenize (c : rs)   = TkChr c : tokenize rs
tokenize _          = []

isLexem :: Char -> Bool
isLexem c = isAscii c && isAlphaNum c || c == '_'

isNLine :: Char -> Bool
isNLine c = c == '\n'


-- Show instances

instance Show Token where
  showsPrec _ (TkLex w)  = showString w
  showsPrec _ (TkChr c)  = showChar c
  showsPrec _ _          = showChar ' '

