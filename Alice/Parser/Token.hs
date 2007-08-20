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
isLexem c = isAlphaNum c || c == '_'

isNLine :: Char -> Bool
isNLine c = c == '\n'


-- Show instances

instance Show Token where
  showsPrec _ (TkLex w)  = showString w
  showsPrec _ (TkChr c)  = showChar c
  showsPrec _ _          = showChar ' '

