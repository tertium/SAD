module Alice.Data.Kit where

import Control.Monad
import Data.Maybe

import Alice.Data.Formula

-- Alpha-beta normalization

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


-- Boolean simplification

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

neg (Not f) = f
neg f = bool $ Not f


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


-- Holes and slots

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


-- Info handling

hasInfo f = isTrm f || isVar f || isInd f

nullInfo f  | hasInfo f = f {trInfo = []}
            | otherwise = f

skipInfo fn f | hasInfo f = (fn $ nullInfo f) {trInfo = trInfo f}
              | otherwise = fn f

trInfoI t = [ e | Ann DIM e <- trInfo t ]
trInfoO t = [ e | Ann DOR e <- trInfo t ]
trInfoE t = [ e | Ann DEQ e <- trInfo t ]
trInfoC t = [ e | Ann DCN e <- trInfo t ]
trInfoN t = [ e | Ann DNC e <- trInfo t ]


-- Misc stuff

isUnit (Sub _ f)    = isUnit f
isUnit (Ann _ f)    = isUnit f
isUnit (Not f)      = isUnit f
isUnit (Trm _ _ _)  = True
isUnit _            = False

infilt vs v = guard (v `elem` vs) >> return v
nifilt vs v = guard (v `notElem` vs) >> return v

dups (v:vs) = infilt vs v `mplus` dups vs
dups _      = mzero

