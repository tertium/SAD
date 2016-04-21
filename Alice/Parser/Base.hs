{-
 -  Parser/Base.hs -- parser state monad
 -  Copyright (c) 2001-2008  Andrei Paskevich <atertium@gmail.com>
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

import Control.Applicative
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


-- CPS parser monad

type CPMS a b   = PState a -> b -> b
type CPMC a b c = (c -> CPMS a b) -> (String -> CPMS a b) -> CPMS a b
newtype CPM a c = CPM { runCPM :: forall b . CPMC a b c }

instance Monad (CPM a) where
  return r  = CPM $ \ k _ -> k r
  m >>= n   = CPM $ \ k l -> runCPM m (\ b -> runCPM (n b) k l) l
  fail e    = CPM $ \ _ l -> l e

instance MonadPlus (CPM a) where
  mzero     = CPM $ \ _ _ _ z -> z
  mplus m n = CPM $ \ k l s -> runCPM m k l s . runCPM n k l s

instance Functor (CPM a) where
  fmap  = liftM

instance Applicative (CPM a) where
  pure  = return
  (<*>) = ap

instance Alternative (CPM a) where
  empty = mzero
  (<|>) = mplus


-- Lazy parser monad class and instance

class MonadPlus m => MonadLazy m where
  mtry :: m a -> m a -> m a
  mtie :: m a -> ([a] -> a -> m b) -> m b

instance MonadLazy (CPM a) where
  mtry m n  = CPM $ \ k l s z ->  let mz True = runCPM n k l s z
                                      mz _    = z
                                      mk b s z _ = k b s (z False)
                                      ml e s z f = l e s (z f)
                                  in  runCPM m mk ml s mz True

  mtie m n  = CPM $ \ k l s z ->  let mz rs = foldr (nz $ map fst rs) z rs
                                      nz bs (b,s) = runCPM (n bs b) k l s
                                      mk b s z rs = z ((b,s):rs)
                                      ml e s z rs = l e s (z rs)
                                  in  runCPM m mk ml s mz []


-- State parser monad class and instance

class MonadPState m where
  getPS :: m a (PState a)
  setPS :: PState a -> m a ()
  updatePS :: (PState a -> PState a) -> m a (PState a)

instance MonadPState CPM where
  getPS = CPM $ \ k _ s -> k s s
  setPS s = CPM $ \ k _ _ -> k () s
  updatePS fn = CPM $ \ k _ s -> k s (fn s)


-- Lazy parser monad

type LPM = CPM
type LPMR a b = Either String (PRes a b)

runLPM :: LPM a b -> PState a -> LPMR a b
runLPM m s = case runCPM m getres ignerr s (Left "") of
    Left _  -> runCPM m undefined geterr s (Left . strerr) []
    res     -> res
  where
    getres b s _  = Right (b,s)
    geterr e s z  = z . (:) (e,s)
    ignerr _ _ z  = z

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

maxerr :: PErr a -> PErr a -> PErr a
maxerr e@(_, pe) d@(_, pd)
  | psOffs pe < psOffs pd = d
  | otherwise             = e


-- Parser state manipulation

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

