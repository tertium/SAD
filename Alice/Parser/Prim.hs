module Alice.Parser.Prim where

import Control.Monad
import Data.Char
import Data.List

import Alice.Parser.Base
import Alice.Parser.Token

-- Lexical primitives

nextToken, readToken :: MonadPS m => m Token
nextToken = getPS >>= nxtk
  where
    nxtk (PState po pl (t:ts) pd pf pp)
            = setPS (PState (succ po) pl ts (t:pd) pf pp) >> return t
    nxtk _  = nextfail $ "unexpected end of input"

nextEOI, readEOI :: MonadPS m => m ()
nextEOI = getPS >>= reoi
  where
    reoi (PState _ _ (t:_) _ _ _)
            = nextfail $ "unexpected token '" ++ show t ++ "'"
    reoi ps = return ()

skipSpace :: MonadPS m => m a -> m a
skipSpace p = after p (getPS >>= sptk)
  where
    sptk (PState po pl (t@(TkSpc n):ts) pd pf pp)
            = setPS (PState (succ po) (pl + n) ts (t:pd) pf pp)
    sptk ps = return ()

nextTkChr, readTkChr :: MonadPS m => m Char
nextTkChr = nextToken >>= nxch
  where
    nxch (TkChr c)  = return c
    nxch t  = fail $ "unexpected token '" ++ show t ++ "'"

nextTkLex, readTkLex :: MonadPS m => m String
nextTkLex  = nextToken >>= nxwr
  where
    nxwr (TkLex w)  = return w
    nxwr t  = fail $ "unexpected token '" ++ show t ++ "'"

nextCharOf, readCharOf, charOf :: MonadPS m => [Char] -> m ()
nextCharOf cs = nextTkChr >>= nxch
  where
    nxch c  | c `elem` cs = return ()
            | otherwise   = fail $ "unexpected char '" ++ c : "'"

nextChar, readChar, char :: MonadPS m => Char -> m ()
nextChar  = nextCharOf . (:[])

nextWordOf, readWordOf, wordOf :: MonadPS m => [String] -> m ()
nextWordOf ws = nextTkLex >>= nxwr . map toLower
  where
    nxwr w  | w `elem` ws = return ()
            | otherwise   = fail $ "unexpected word '" ++ w ++ "'"

nextWord, readWord, word :: MonadPS m => String -> m ()
nextWord  = nextWordOf . (:[])

nextString, readString, string :: MonadPS m => String -> m ()
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
(-|-) :: MonadPlus m => m a -> m a -> m a
(-|-) = mplus

infixr 1 -/-
(-/-) :: MonadLazy m => m a -> m a -> m a
(-/-) = mtry

opt :: MonadPlus m => a -> m a -> m a
opt a m = m -|- return a

optEx :: MonadLazy m => a -> m a -> m a
optEx a m = m -/- return a

after :: Monad m => m a -> m b -> m a
after a b = a >>= ((b >>) . return)

expar, exbrk, exbrc :: MonadPS m => m a -> m a
expar p = readChar '(' >> after p (readChar ')')
exbrk p = readChar '[' >> after p (readChar ']')
exbrc p = readChar '{' >> after p (readChar '}')

paren :: (MonadPlus m, MonadPS m) => m a -> m a
paren p = p -|- expar p

parenEx :: (MonadLazy m, MonadPS m) => m a -> m a
parenEx p = p -/- expar p

chnop :: MonadPlus m => m a -> m [a]
chnop p = liftM2 (:) p $ opt [] $ chnop p

chain :: MonadPlus m => m a -> m b -> m [b]
chain o p = liftM2 (:) p $ opt [] $ o >> chain o p

chnopEx :: MonadLazy m => m a -> m [a]
chnopEx p = liftM2 (:) p $ optEx [] $ chnopEx p

chainEx :: MonadLazy m => m a -> m b -> m [b]
chainEx o p = liftM2 (:) p $ optEx [] $ o >> chainEx o p

narrow :: (MonadPS m, MonadLazy m, Show a) => m a -> m a
narrow m  = mtie m amb
  where
    amb [_] a = return a
    amb as  _ = nextfail $ "ambiguity:" ++ concatMap msg as
    msg a     = "\n    " ++ show a

