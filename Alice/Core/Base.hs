{-
 -  Core/Base.hs -- verifier state monad and common functions
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

module Alice.Core.Base where

import Control.Monad
import Data.IORef
import Data.List
import Data.Time

import Alice.Data.Instr
import Alice.Data.Text
import Alice.Export.Base

-- Reasoner state

data RState = RState {  rsInst :: [Instr],
                        rsCntr :: [Count],
                        rsPrdb :: [Prover] }

data Count  = CntrT CntrT NominalDiffTime
            | CntrI CntrI Int

data CntrT  = CTprov
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


-- CPS IO Maybe monad

type CRMM a   = IO a -> IO a
type CRMC a b = (b -> CRMM a) -> CRMM a
newtype CRM b = CRM { runCRM :: forall a . IORef RState -> CRMC a b }

instance Monad CRM where
  return r  = CRM $ \ _ k -> k r
  m >>= n   = CRM $ \ s k -> runCRM m s (\ r -> runCRM (n r) s k)

instance MonadPlus CRM where
  mzero     = CRM $ \ _ _ -> id
  mplus m n = CRM $ \ s k -> runCRM m s k . runCRM n s k

justRS :: CRM (IORef RState)
justRS      = CRM $ \ s k -> k s

justIO :: IO a -> CRM a
justIO m    = CRM $ \ _ k -> (>>=) m . flip k

type RM = CRM
runRM :: RM a -> IORef RState -> IO (Maybe a)
runRM m s = runCRM m s ((return .) . (const . Just)) (return Nothing)

infixr 1 <>
(<>) :: RM a -> RM a -> RM a
(<>) = mplus


-- State management

getRS       = justRS >>= (justIO . readIORef)
askRS f     = justRS >>= (justIO . fmap f . readIORef)
setRS r     = justRS >>= (justIO . flip writeIORef r)
updateRS f  = justRS >>= (justIO . flip modifyIORef f)

askRSII i d = liftM (askII i d) (askRS rsInst)
askRSIB i d = liftM (askIB i d) (askRS rsInst)
askRSIS i d = liftM (askIS i d) (askRS rsInst)

addRSIn ins = updateRS $ \ rs -> rs { rsInst = ins : rsInst rs }
drpRSIn ind = updateRS $ \ rs -> rs { rsInst = dropI ind $ rsInst rs }
addRSTI c i = updateRS $ \ rs -> rs { rsCntr = CntrT c i : rsCntr rs }
addRSCI c i = updateRS $ \ rs -> rs { rsCntr = CntrI c i : rsCntr rs }
incRSCI c   = addRSCI c 1

timer c a   = do  b <- justIO $ getCurrentTime
                  r <- a
                  e <- justIO $ getCurrentTime
                  addRSTI c $ diffUTCTime e b
                  return r

guardIB i d     = askRSIB i d >>= guard
guardNotIB i d  = askRSIB i d >>= guard . not
whenIB i d a    = askRSIB i d >>= \ b -> when b a
unlessIB i d a  = askRSIB i d >>= \ b -> unless b a


-- Counter management

fetchCI c cs  = [ i | CntrI d i <- cs, c == d ]
fetchCT c cs  = [ i | CntrT d i <- cs, c == d ]

cumulCI c t = foldr (+) t . fetchCI c
cumulCT c t = foldr addUTCTime t . fetchCT c
maximCT c   = foldr max 0 . fetchCT c

showTimeDiff t
  | th == 0 = dsh mn ++ ':' : dsh ss ++ '.' : dsh cs
  | True    = dsh th ++ ':' : dsh mn ++ ':' : dsh ss
  where
    dsh n   = if n < 10 then '0':show n else show n
    tc      = truncate $ t * 100
    (ts,cs) = divMod tc 100
    (tm,ss) = divMod ts 60
    (th,mn) = divMod tm 60


-- IO management

printRM :: Show a => a -> RM ()

putStrLnRM  = justIO . putStrLn
putStrRM    = justIO . putStr
printRM     = justIO . print

rlog0 tx = putStrLnRM $ "[Reason] " ++ tx

rlog bl tx = do tfn <- askRSIS ISfile ""
                rlog0 $ blLabl tfn bl ++ tx

blLabl tf (Block { blFile = f, blLine = l })
  = (if null f || f == tf then "line " else f ++ ":") ++ show l ++ ": "

