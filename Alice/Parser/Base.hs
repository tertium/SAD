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


-- List parser monad

newtype LPM a b = LPM { runLPM :: PState a -> LPMR a b }

instance Monad (LPM a) where
  fail e    = LPM $ \ p -> ([], [(e, p)])
  return r  = LPM $ \ p -> ([(r, p)], [])

  m >>= k   = LPM $ after . runLPM m
    where
      after (rs, e) = foldl app ([], e) rs
      app l (r, q)  = resadd (runLPM (k r) q) l

instance MonadPlus (LPM a) where
  mzero     = LPM $ \ _ -> ([], [])
  mplus m k = LPM $ \ p -> resadd (runLPM m p) (runLPM k p)

instance MonadLazy (LPM a) where
  mtry m k  = LPM $ \ p -> case runLPM m p of
                ([], e) -> case runLPM k p of
                  (rs, d) -> (rs, e ++ d)
                r -> r

  mtie m k  = LPM $ after . runLPM m
    where
      after (rs, e)   = foldl (app $ map fst rs) ([], e) rs
      app rs l (r, q) = resadd (runLPM (k rs r) q) l


-- Parser state manipulation

getPS :: LPM a (PState a)
getPS   = LPM $ \ p -> ([(p, p)], [])

setPS :: PState a -> LPM a ()
setPS p = LPM $ \ _ -> ([((), p)], [])

updatePS :: (PState a -> PState a) -> LPM a (PState a)
updatePS fn = LPM $ \ p -> ([(p, fn p)], [])

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

