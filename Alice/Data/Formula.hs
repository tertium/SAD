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
    dive n (Ind m _)  | m == n  = zVar v
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


-- Propositional tools

bool (All v Top)  = Top
bool (All v Bot)  = Bot
bool (Exi v Top)  = Top
bool (Exi v Bot)  = Bot
bool (Iff Top f)  = f
bool (Iff f Top)  = f
bool (Iff Bot f)  = bool $ Not f
bool (Iff f Bot)  = bool $ Not f
bool (Imp Top f)  = f
bool (Imp f Top)  = Top
bool (Imp Bot f)  = Top
bool (Imp f Bot)  = bool $ Not f
bool (Or  Top f)  = Top
bool (Or  f Top)  = Top
bool (Or  Bot f)  = f
bool (Or  f Bot)  = f
bool (And Top f)  = f
bool (And f Top)  = f
bool (And Bot f)  = Bot
bool (And f Bot)  = Bot
bool (Ann a Top)  = Top
bool (Ann a Bot)  = Bot
bool (Sub f Top)  = Top
bool (Sub f Bot)  = Bot
bool (Not Top)    = Bot
bool (Not Bot)    = Top
bool f            = f

strip (Ann _ f) = strip f
strip (Sub _ f) = strip f
strip f         = f

neg (Not f) = f
neg f = bool $ Not f

albet (Iff f g)       = And (Imp f g) (Imp g f)
albet (Imp f g)       = Or (Not f) g
albet (Not (All v f)) = Exi v $ Not f
albet (Not (Exi v f)) = All v $ Not f
albet (Not (Iff f g)) = Or (And (Not f) g) (And (Not g) f)
albet (Not (Imp f g)) = And (Not g) f
albet (Not (And f g)) = Or (Not f) (Not g)
albet (Not (Or f g))  = And (Not f) (Not g)
albet (Not (Not f))   = albet f
albet f               = f

deAnd = spl . albet
  where
    spl (And f g) = deAnd f ++ deAnd g
    spl f = [f]

deOr  = spl . albet
  where
    spl (Or f g)  = deOr f ++ deOr g
    spl f = [f]


-- Maybe quantification

mbBind v  = dive id
  where
    dive c s (All u f)  = dive (c . bool . All u) s f
    dive c s (Exi u f)  = dive (c . bool . Exi u) s f
    dive c s (Ann a f)  = dive (c . bool . Ann a) s f
    dive c s (Sub g f)  = dive (c . bool . Sub g) s f
    dive c s (Not f)    = dive (c . bool . Not) (not s) f
    dive c False (Imp f g)  = dive (c . bool . (`Imp` g)) True f
                      `mplus` dive (c . bool . (f `Imp`)) False g
    dive c False (Or f g)   = dive (c . bool . (`Or` g)) False f
                      `mplus` dive (c . bool . (f `Or`)) False g
    dive c True (And f g)   = dive (c . bool . (`And` g)) True f
                      `mplus` dive (c . bool . (f `And`)) True g
    dive c True (Trm "=" [l@(Var u _), t] _)
      | u == v && not (occurs l t) && closed t
                = return $ subst t u (c Top)
    dive _ _ _  = mzero

mbExi v f = fromMaybe (zExi v f) (mbBind v True f)
mbAll v f = fromMaybe (zAll v f) (mbBind v False f)


-- Useful macros

zAll v f  = All v $ bind v 0 f
zExi v f  = Exi v $ bind v 0 f

zIff f g  = And (Imp f g) (Imp g f)

zVar v    = Var v []
zTrm t ts = Trm t ts []
zThesis   = zTrm "?th?" []
zEqu t s  = zTrm "=" [t,s]
zSet t    = zTrm "aSet" [t]
zElm t s  = zTrm "aElementOf" [t,s]
zLess t s = zTrm "iLess" [t,s]
zSSS s ts = zTrm ('S':'S':'S':s) ts

isTop Top = True
isTop _   = False

isBot Bot = True
isBot _   = False

isInd (Ind _ _) = True
isInd _         = False

isVar (Var _ _) = True
isVar _         = False

isTrm (Trm _ _ _) = True
isTrm _           = False

isEqu (Trm "=" [_,_] _) = True
isEqu _                 = False

isThesis (Trm "?th?" [] _)  = True
isThesis _                  = False

isSSS (Trm ('S':'S':'S':_) _ _) = True
isSSS _                         = False

isUnit (Sub _ f)  = isUnit f
isUnit (Ann _ f)  = isUnit f
isUnit (Not f)    = isUnit f
isUnit f          = isTrm f

trInfoI t = [ e | Ann DIM e <- trInfo t ]
trInfoO t = [ e | Ann DOR e <- trInfo t ]
trInfoE t = [ e | Ann DEQ e <- trInfo t ]


-- Holes

zHole = zVar "?"
zSlot = zVar "!"

isHole (Var "?" _)  = True
isHole _            = False

isSlot (Var "!" _)  = True
isSlot _            = False

substH t  = subst t "?"
substS t  = subst t "!"

occursH = occurs zHole
occursS = occurs zSlot


-- Service stuff

infilt vs v = guard (v `elem` vs) >> return v
nifilt vs v = guard (v `notElem` vs) >> return v

dups (v:vs) = infilt vs v `mplus` dups vs
dups _      = mzero


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

      dive t  | isThesis t  = showString "thesis"
              | isEqu t     = let [l,r] = trArgs t in sinfix " = " l r
              | isTrm t     = showString (trName t) . sargs (trArgs t)
              | isVar t     = showString (trName t)
              | isInd t     = showChar 'v' . shows (d - 1 - trIndx t)

      sargs []  = id
      sargs _   | p == 1  = showString "(...)"
      sargs ts  = showArgs (showFormula (pred p) d) ts

      binder f      = showFormula p (succ d) (Ind 0 []) . showChar ' '
                    . showFormula p (succ d) f

      sinfix o f g  = dive f . showString o . dive g

showArgs sh (t:ts)  = showParen True $ sh t . showTail sh ts
showArgs sh _       = id

showTail sh ts      = foldr ((.) . ((showChar ',' .) . sh)) id ts

