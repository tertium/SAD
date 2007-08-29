{-
 -  Core/Base.hs -- verifier state monad and common functions
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

module Alice.Core.Base where

import Control.Monad
import Data.IORef
import Data.List
import System.Time

import Alice.Data.Formula
import Alice.Data.Instr
import Alice.Data.Text
import Alice.Export.Base
import Alice.ForTheL.Base
import Alice.Parser.Base
import Alice.Parser.Token

-- Reasoner state

data RState = RState {  rsInst :: [Instr],
                        rsCntr :: [Count],
                        rsPrdb :: [Prover] }

data Count  = CntrT CntrT TimeDiff
            | CntrI CntrI Int

data CntrT  = CTpars
            | CTprov
            | CTprvy
            deriving Eq

data CntrI  = CIsect
            | CIgoal
            | CIfail
            | CIsubt
            | CIprov
            | CIprvy
            | CIsymb
            | CIchkt
            | CIchkh
            | CIchky
            | CIunfl
            deriving Eq

initRS :: RState
initRS  = RState [] [] []


-- IO Maybe monad

newtype RM a  = RM { runRM :: IORef RState -> IO (Maybe a) }

instance Monad RM where
  return r  = RM $ \ rs -> return $ Just r
  m >>= k   = RM $ \ rs -> runRM m rs >>= apply rs
    where
      apply rs (Just r) = runRM (k r) rs
      apply rs Nothing  = return Nothing

instance MonadPlus RM where
  mzero     = RM $ \ rs -> return Nothing
  mplus m k = RM $ \ rs -> runRM m rs >>= apply rs
    where
      apply rs Nothing  = runRM k rs
      apply rs x        = return x

infixr 1 <>
(<>) :: RM a -> RM a -> RM a
(<>) = mplus


-- State management

getRS       = RM $ \ rs -> liftM Just $ readIORef rs
askRS f     = RM $ \ rs -> liftM (Just . f) $ readIORef rs

setRS r     = RM $ \ rs -> liftM Just $ writeIORef rs r
updateRS f  = RM $ \ rs -> liftM Just $ modifyIORef rs f

askRSII i d = liftM (\ is -> askII is i d) (askRS rsInst)
askRSIB i d = liftM (\ is -> askIB is i d) (askRS rsInst)
askRSIS i d = liftM (\ is -> askIS is i d) (askRS rsInst)

addRSIn ins = updateRS $ \ rs -> rs { rsInst = ins : rsInst rs }
drpRSIn ind = updateRS $ \ rs -> rs { rsInst = dropI (rsInst rs) ind }
addRSTI c i = updateRS $ \ rs -> rs { rsCntr = CntrT c i : rsCntr rs }
addRSCI c i = updateRS $ \ rs -> rs { rsCntr = CntrI c i : rsCntr rs }
incRSCI c   = addRSCI c 1

timer c a   = do  b <- justIO $ getClockTime
                  r <- a
                  e <- justIO $ getClockTime
                  addRSTI c $ getTimeDiff e b
                  return r

guardIB i d     = askRSIB i d >>= guard
guardNotIB i d  = askRSIB i d >>= guard . not
whenIB i d a    = askRSIB i d >>= \ b -> when b a
unlessIB i d a  = askRSIB i d >>= \ b -> unless b a


-- Counter management

fetchCI c (CntrI d i : cs) | c == d = i : fetchCI c cs
fetchCI c (_ : cs) = fetchCI c cs
fetchCI _ _ = []

fetchCT c (CntrT d i : cs) | c == d = i : fetchCT c cs
fetchCT c (_ : cs) = fetchCT c cs
fetchCT _ _ = []

cumulCI c t = foldr (+) t . fetchCI c
cumulCT c t = foldr addToClockTime t . fetchCT c
maximCT c   = foldr max noTimeDiff . fetchCT c

getTimeDiff e b = let t = diffClockTimes e b
                      x = tdSec t ; y = tdPicosec t
                      (u, v) = y `divMod` 1000000000000
                  in  t { tdSec = x + fromInteger u, tdPicosec = v }

showTimeDiff t
  | th == 0 = dsh mn ++ ':' : dsh ss ++ '.' : dsh cs
  | True    = dsh th ++ ':' : dsh mn ++ ':' : dsh ss
  where
    TimeDiff ye mo da hr mn ss ps = normalizeTimeDiff t
    th    = hr + da * 24 + mo * 30 * 24 + ye * 365 * 24
    dsh n = if n < 10 then '0':show n else show n
    cs    = ps `div` 10000000000


-- IO management

justIO      = RM . const . liftM Just

putStrLnRM  = justIO . putStrLn
putStrRM    = justIO . putStr
printRM     = justIO . print

rlog0 tx = putStrLnRM $ "[Reason] " ++ tx

rlog bl tx = do tfn <- askRSIS ISread ""
                rlog0 $ blLabl tfn bl ++ tx

blLabl tf (Block { blFile = f, blLine = l })
  = (if null f || f == tf then "line " else f ++ ":") ++ show l ++ ": "

