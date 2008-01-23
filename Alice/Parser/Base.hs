{-
 -  Parser/Base.hs -- parser state monad
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

module Alice.Parser.Base where

import Control.Monad
import Data.List

import Alice.Parser.Token

-- Parser state

data PState a = PState  { psProp :: a,
                          psOffs, psLine :: Int,
                          psRest, psDone :: [Token],
                          psFile, psLang :: String }

initPS :: a -> PState a
initPS a  = PState a 0 1 [] [] "" ""

type PRes a b = (b, PState a)
type PErr a   = (String, PState a)
type LPMR a b = ([PRes a b], [PErr a])

resadd :: LPMR a b -> LPMR a b -> LPMR a b
resadd (as, ea) (bs, eb) = (as ++ bs, ea ++ eb)

maxerr :: PErr a -> PErr a -> PErr a
maxerr e@(_, pe) d@(_, pd)
  | psOffs pe < psOffs pd = d
  | otherwise             = e

strerr :: [PErr a] -> String
strerr es = emsg ++ text
  where
    (e, PState _ _ l _ d f p) = foldr1 maxerr es
    emsg  = '[' : p ++ "] " ++ file ++ line ++ e
    file  = if null f then "line " else f ++ ":"
    line  = show (foldr lofs l d) ++ ": "
    text  = if null d then "" else "\n in text: "
                    ++ concatMap show (reverse d)
    lofs (TkSpc n) l = l - n ; lofs _ l = l


-- Lazy parser monad class

class MonadPlus m => MonadLazy m where
  mtry :: m a -> m a -> m a
  mtie :: m a -> ([a] -> a -> m b) -> m b


-- Simple list parser monad

newtype SLPM a b = SLPM { runSLPM :: PState a -> LPMR a b }

instance Monad (SLPM a) where
  fail e    = SLPM $ \ p -> ([], [(e, p)])
  return r  = SLPM $ \ p -> ([(r, p)], [])

  m >>= k   = SLPM $ after . runSLPM m
    where
      after (rs, e) = foldl app ([], e) rs
      app l (r, q)  = resadd (runSLPM (k r) q) l

instance MonadPlus (SLPM a) where
  mzero     = SLPM $ \ _ -> ([], [])
  mplus m k = SLPM $ \ p -> resadd (runSLPM m p) (runSLPM k p)

instance MonadLazy (SLPM a) where
  mtry m k  = SLPM $ \ p -> case runSLPM m p of
                ([], e) -> case runSLPM k p of
                  (rs, d) -> (rs, e ++ d)
                r -> r

  mtie m k  = SLPM $ after . runSLPM m
    where
      after (rs, e)   = foldl (app $ map fst rs) ([], e) rs
      app rs l (r, q) = resadd (runSLPM (k rs r) q) l


-- CPS list parser monad

newtype CLPM a b = CLPM { runCLPM :: forall c . (b -> SLPM a c) -> SLPM a c }

instance Monad (CLPM a) where
  fail e    = CLPM $ \ _ -> fail e
  return r  = CLPM $ \ k -> k r
  m >>= n   = CLPM $ \ k -> runCLPM m (\ b -> runCLPM (n b) k)

instance MonadPlus (CLPM a) where
  mzero     = CLPM $ \ _ -> mzero
  mplus m n = CLPM $ \ k -> mplus (runCLPM m k) (runCLPM n k)

instance MonadLazy (CLPM a) where
  mtry m n  = CLPM $ \ k -> SLPM $ \ p ->
                case runSLPM (runCLPM m return) p of
                  ([], e) -> case runSLPM (runCLPM n k) p of
                    (rs, d) -> (rs, e ++ d)
                  (rs, e) -> let app l (r, q) = resadd (runSLPM (k r) q) l
                             in  foldl app ([], e) rs

  mtie m n  = CLPM $ \ k -> mtie (runCLPM m return) (\ as a -> runCLPM (n as a) k)


-- Parser state manipulation

class MonadPState m where
  getPS :: m a (PState a)
  setPS :: PState a -> m a ()
  updatePS :: (PState a -> PState a) -> m a (PState a)

instance MonadPState SLPM where
  getPS = SLPM $ \ p -> ([(p, p)], [])
  setPS p = SLPM $ \ _ -> ([((), p)], [])
  updatePS fn = SLPM $ \ p -> ([(p, fn p)], [])

instance MonadPState CLPM where
  getPS = CLPM $ \ k -> SLPM $ \ p -> runSLPM (k p) p
  setPS p = CLPM $ \ k -> SLPM $ \ _ -> runSLPM (k ()) p
  updatePS fn = CLPM $ \ k -> SLPM $ \ p -> runSLPM (k p) (fn p)


-- List parser monad

type LPM = CLPM

runLPM :: LPM a b -> PState a -> LPMR a b
runLPM m = runSLPM $ runCLPM m return
-- runLPM = runSLPM

askPS :: (PState a -> b) -> LPM a b
askPS fn = liftM fn getPS

getText :: LPM a String
getText = askPS $ concatMap show . reverse . psDone

nulText :: LPM a Int
nulText = liftM psLine $ updatePS (\ ps -> ps { psDone = [] })

nextfail :: String -> LPM a b
nextfail e  = let nxof ps = ps { psOffs = succ (psOffs ps) }
              in  updatePS nxof >> fail e


-- Proper state manipulation

getS :: LPM a a
getS  = askPS psProp

setS :: a -> LPM a ()
setS s  = updatePS (\ p -> p { psProp = s }) >> return ()

updateS :: (a -> a) -> LPM a a
updateS fn  = let upd p = p { psProp = fn (psProp p) }
              in  liftM psProp $ updatePS upd

askS :: (a -> b) -> LPM a b
askS fn = askPS (fn . psProp)

