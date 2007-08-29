{-
 -  Data/Formula.hs -- formula datatype and core functions
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

module Alice.Data.Formula where

import Control.Monad
import Data.Maybe
import qualified Data.Monoid as Monoid

data Formula  = All String  Formula       | Exi String  Formula
              | Iff Formula Formula       | Imp Formula Formula
              | Or  Formula Formula       | And Formula Formula
              | Tag Tag Formula           | Not Formula
              | Top                       | Bot
              | Trm { trName :: String,
                      trArgs :: [Formula],  trInfo :: [Formula] }
              | Var { trName :: String,     trInfo :: [Formula] }
              | Ind { trIndx :: Int,        trInfo :: [Formula] }

data Tag  = DIG | DMS | DMP | DHD | DIH | DCH
          | DIM | DOR | DEQ | DSD | DCN | DNC
          deriving (Eq,Show)


-- Traversing functions

mapF :: (Formula -> Formula) -> Formula -> Formula
mapF fn (All v f)       = All v (fn f)
mapF fn (Exi v f)       = Exi v (fn f)
mapF fn (Iff f g)       = Iff (fn f) (fn g)
mapF fn (Imp f g)       = Imp (fn f) (fn g)
mapF fn (Or  f g)       = Or  (fn f) (fn g)
mapF fn (And f g)       = And (fn f) (fn g)
mapF fn (Tag a f)       = Tag a (fn f)
mapF fn (Not f)         = Not (fn f)
mapF fn (Top)           = Top
mapF fn (Bot)           = Bot
mapF fn (Trm t ts ss)   = Trm t (map fn ts) (map fn ss)
mapF fn (Var v ss)      = Var v (map fn ss)
mapF fn (Ind v ss)      = Ind v (map fn ss)

mapFM :: (Monad m) => (Formula -> m Formula) -> Formula -> m Formula
mapFM fn (All v f)      = liftM (All v) (fn f)
mapFM fn (Exi v f)      = liftM (Exi v) (fn f)
mapFM fn (Iff f g)      = liftM2 Iff (fn f) (fn g)
mapFM fn (Imp f g)      = liftM2 Imp (fn f) (fn g)
mapFM fn (Or  f g)      = liftM2 Or  (fn f) (fn g)
mapFM fn (And f g)      = liftM2 And (fn f) (fn g)
mapFM fn (Tag a f)      = liftM (Tag a) (fn f)
mapFM fn (Not f)        = liftM  Not (fn f)
mapFM fn (Top)          = return Top
mapFM fn (Bot)          = return Bot
mapFM fn (Trm t ts ss)  = liftM2 (Trm t) (mapM fn ts) (mapM fn ss)
mapFM fn (Var v ss)     = liftM  (Var v) (mapM fn ss)
mapFM fn (Ind v ss)     = liftM  (Ind v) (mapM fn ss)


-- Logical traversing

roundF :: ([Formula] -> Maybe Bool -> Int -> Formula -> Formula)
        -> [Formula] -> Maybe Bool -> Int -> Formula -> Formula
roundF fn cn sg n  = dive
  where
    dive (All u f) =  let nf = fn cn sg (succ n); nn = 'u':show n
                      in  All u $ bind nn $ nf $ inst nn f
    dive (Exi u f) =  let nf = fn cn sg (succ n); nn = 'u':show n
                      in  Exi u $ bind nn $ nf $ inst nn f
    dive (Iff f g) =  let nf = fn cn Nothing n f
                      in  Iff nf $ fn cn Nothing n g
    dive (Imp f g) =  let nf = fn cn (liftM not sg) n f
                      in  Imp nf $ fn (nf:cn) sg n g
    dive (Or  f g) =  let nf = fn cn sg n f
                      in  Or nf $ fn (Not nf:cn) sg n g
    dive (And f g) =  let nf = fn cn sg n f
                      in  And nf $ fn (nf:cn) sg n g
    dive (Not f)   =  Not $ fn cn (liftM not sg) n f
    dive f         =  mapF (fn cn sg n) f

roundFM :: (Monad m) =>
          ([Formula] -> Maybe Bool -> Int -> Formula -> m Formula)
        -> [Formula] -> Maybe Bool -> Int -> Formula -> m Formula
roundFM fn cn sg n  = dive
  where
    dive (All u f)  = do  let nf = fn cn sg (succ n); nn = 'u':show n
                          liftM (All u . bind nn) $ nf $ inst nn f
    dive (Exi u f)  = do  let nf = fn cn sg (succ n); nn = 'u':show n
                          liftM (Exi u . bind nn) $ nf $ inst nn f
    dive (Iff f g)  = do  nf <- fn cn Nothing n f
                          liftM (Iff nf) $ fn cn Nothing n g
    dive (Imp f g)  = do  nf <- fn cn (liftM not sg) n f
                          liftM (Imp nf) $ fn (nf:cn) sg n g
    dive (Or  f g)  = do  nf <- fn cn sg n f
                          liftM (Or nf) $ fn (Not nf:cn) sg n g
    dive (And f g)  = do  nf <- fn cn sg n f
                          liftM (And nf) $ fn (nf:cn) sg n g
    dive (Not f)    = liftM Not $ fn cn (liftM not sg) n f
    dive f          = mapFM (fn cn sg n) f


-- Folding

foldF :: (Monoid.Monoid a) => (Formula -> a) -> Formula -> a
foldF fn (All _ f)      = fn f
foldF fn (Exi _ f)      = fn f
foldF fn (Iff f g)      = Monoid.mappend (fn f) (fn g)
foldF fn (Imp f g)      = Monoid.mappend (fn f) (fn g)
foldF fn (Or  f g)      = Monoid.mappend (fn f) (fn g)
foldF fn (And f g)      = Monoid.mappend (fn f) (fn g)
foldF fn (Tag _ f)      = fn f
foldF fn (Not f)        = fn f
foldF fn (Top)          = Monoid.mempty
foldF fn (Bot)          = Monoid.mempty
foldF fn (Trm _ ts ss)  = Monoid.mconcat $ map fn $ ts ++ ss
foldF fn (Var _ ss)     = Monoid.mconcat $ map fn ss
foldF fn (Ind _ ss)     = Monoid.mconcat $ map fn ss

allF :: (Formula -> Bool) -> Formula -> Bool
allF fn = Monoid.getAll . foldF (Monoid.All . fn)

anyF :: (Formula -> Bool) -> Formula -> Bool
anyF fn = Monoid.getAny . foldF (Monoid.Any . fn)

sumF :: (Num a) => (Formula -> a) -> Formula -> a
sumF fn = Monoid.getSum . foldF (Monoid.Sum . fn)


-- Bind, inst, subst

closed :: Formula -> Bool
closed  = dive 0
  where
    dive n (All _ g)  = dive (succ n) g
    dive n (Exi _ g)  = dive (succ n) g
    dive n (Ind v ss) = v < n && all (dive n) ss
    dive n f          = allF (dive n) f

bind :: String -> Formula -> Formula
bind v  = dive 0
  where
    dive n (All u g)  = All u $ dive (succ n) g
    dive n (Exi u g)  = Exi u $ dive (succ n) g
    dive n (Var u ss) | u == v
                      = Ind n $ map (dive n) ss
    dive n f          = mapF (dive n) f

inst :: String -> Formula -> Formula
inst v  = dive 0
  where
    dive n (All u g)  = All u $ dive (succ n) g
    dive n (Exi u g)  = Exi u $ dive (succ n) g
    dive n (Ind m ss) | m == n
                      = Var v $ map (dive n) ss
    dive n f          = mapF (dive n) f

subst :: Formula -> String -> Formula -> Formula
subst t v = dive
  where
    dive (Var u _)    | u == v  = t
    dive f            = mapF dive f

substs :: Formula -> [String] -> [Formula] -> Formula
substs f vs ts = dive f
  where
    dive f@(Var u _)  = fromMaybe (mapF dive f) (lookup u zvt)
    dive f            = mapF dive f
    zvt               = zip vs ts


-- Compare and replace

twins :: Formula -> Formula -> Bool
twins (Var u _)    (Var v _)    = u == v
twins (Trm p ps _) (Trm q qs _) | p == q  = pairs ps qs
  where
    pairs (p:ps) (q:qs) = twins p q && pairs ps qs
    pairs [] []         = True
    pairs _ _           = False
twins _ _         = False

occurs :: Formula -> Formula -> Bool
occurs t  = dive
  where
    dive f  = twins t f || anyF dive f

replace :: Formula -> Formula -> Formula -> Formula
replace t s = dive
  where
    dive f  | twins s f = t
            | otherwise = mapF dive f

