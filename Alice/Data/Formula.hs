module Alice.Data.Formula where

import Control.Monad
import Data.Maybe
import qualified Data.Monoid as Monoid


data Formula  = All String  Formula       | Exi String  Formula
              | Iff Formula Formula       | Imp Formula Formula
              | Or  Formula Formula       | And Formula Formula
              | Sub Formula Formula       | Ann Annotat Formula
              | Not Formula               | Top | Bot
              | Trm { trName :: String,
                      trArgs :: [Formula],  trInfo :: [Formula] }
              | Var { trName :: String,     trInfo :: [Formula] }
              | Ind { trIndx :: Int,        trInfo :: [Formula] }

data Annotat  = DIG | DMS | DMP | DIH | DCN | DHD
              | DIM | DOR | DEQ | DCH | DNC | DHS
              deriving Show


-- Traversing functions

mapF :: (Formula -> Formula) -> Formula -> Formula
mapF fn (All v f)       = All v (fn f)
mapF fn (Exi v f)       = Exi v (fn f)
mapF fn (Iff f g)       = Iff (fn f) (fn g)
mapF fn (Imp f g)       = Imp (fn f) (fn g)
mapF fn (Or  f g)       = Or  (fn f) (fn g)
mapF fn (And f g)       = And (fn f) (fn g)
mapF fn (Sub f g)       = Sub (fn f) (fn g)
mapF fn (Ann a f)       = Ann a (fn f)
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
mapFM fn (Sub f g)      = liftM2 Sub (fn f) (fn g)
mapFM fn (Ann a f)      = liftM (Ann a) (fn f)
mapFM fn (Not f)        = liftM  Not (fn f)
mapFM fn (Top)          = return Top
mapFM fn (Bot)          = return Bot
mapFM fn (Trm t ts ss)  = liftM2 (Trm t) (mapM fn ts) (mapM fn ss)
mapFM fn (Var v ss)     = liftM  (Var v) (mapM fn ss)
mapFM fn (Ind v ss)     = liftM  (Ind v) (mapM fn ss)


-- Folding

foldF :: (Monoid.Monoid a) => (Formula -> a) -> Formula -> a
foldF fn (All _ f)      = fn f
foldF fn (Exi _ f)      = fn f
foldF fn (Iff f g)      = Monoid.mappend (fn f) (fn g)
foldF fn (Imp f g)      = Monoid.mappend (fn f) (fn g)
foldF fn (Or  f g)      = Monoid.mappend (fn f) (fn g)
foldF fn (And f g)      = Monoid.mappend (fn f) (fn g)
foldF fn (Sub f g)      = Monoid.mappend (fn f) (fn g)
foldF fn (Ann _ f)      = fn f
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

bind :: String -> Int -> Formula -> Formula
bind v  = dive
  where
    dive n (All u g)  = All u $ dive (succ n) g
    dive n (Exi u g)  = Exi u $ dive (succ n) g
    dive n (Var u ss) | u == v
                      = Ind n $ map (dive n) ss
    dive n f          = mapF (dive n) f

inst :: String -> Int -> Formula -> Formula
inst v  = dive
  where
    dive n (All u g)  = All u $ dive (succ n) g
    dive n (Exi u g)  = Exi u $ dive (succ n) g
    dive n (Ind m _)  | m == n  = Var v []
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


-- Match, replace

{-
match :: (MonadPlus m) => Formula -> Formula -> m (Formula -> Formula)
match (Var u _)    (Var v _)    | u == v  = return id
match (Trm p ps _) (Trm q qs _) | p == q  = pairs ps qs
  where
    pairs (p:ps) (q:qs) = do  sb <- pairs ps qs
                              sc <- match (sb $ strip p) (strip q)
                              return $ sc . sb
    pairs [] []         = return id
    pairs _ _           = mzero
match (Ind v _) t = return $ inst t v
match _ _         = mzero
-}

twins :: Formula -> Formula -> Bool
twins (Var u _)    (Var v _)    = u == v
twins (Trm p ps _) (Trm q qs _) | p == q  = pairs ps qs
  where
    pairs (p:ps) (q:qs) = twins (strip p) (strip q) && pairs ps qs
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

strip :: Formula -> Formula
strip (Ann _ f) = strip f
strip (Sub _ f) = strip f
strip f         = f


-- Show instances

instance Show Formula where
  showsPrec p = showFormula p 0

showFormula :: Int -> Int -> Formula -> ShowS
showFormula p d = dive
    where
      dive (All v f)  = showString "forall " . binder f
      dive (Exi v f)  = showString "exists " . binder f
      dive (Iff f g)  = showParen True $ sinfix " iff " f g
      dive (Imp f g)  = showParen True $ sinfix " implies " f g
      dive (Or  f g)  = showParen True $ sinfix " or "  f g
      dive (And f g)  = showParen True $ sinfix " and " f g
      dive (Ann a f)  = showParen True $ shows a
                      . showString " :: " . dive f
      dive (Sub f g)  = showString "[" . sinfix "] " f g
      dive (Not f)    = showString "not " . dive f
      dive Top        = showString "truth"
      dive Bot        = showString "contradiction"

      dive (Trm "?th?" _ _)   = showString "thesis"
      dive (Trm "=" [l,r] _)  = sinfix " = " l r
      dive (Trm s ts _)       = showString s . sargs ts
      dive (Var s _)          = showString s
      dive (Ind i _)          = showChar 'v' . shows (d - 1 - i)

      sargs []  = id
      sargs _   | p == 1  = showString "(...)"
      sargs ts  = showArgs (showFormula (pred p) d) ts

      binder f      = showFormula p (succ d) (Ind 0 []) . showChar ' '
                    . showFormula p (succ d) f

      sinfix o f g  = dive f . showString o . dive g

showArgs sh (t:ts)  = showParen True $ sh t . showTail sh ts
showArgs sh _       = id

showTail sh ts      = foldr ((.) . ((showChar ',' .) . sh)) id ts

