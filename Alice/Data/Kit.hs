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
bool (Tag a Top)  = Top
bool (Tag a Bot)  = Bot
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
    dive c s (Tag a f)  = dive (c . bool . Tag a) s f
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

zAll v f  = All v $ bind v f
zExi v f  = Exi v $ bind v f

zIff f g  = And (Imp f g) (Imp g f)

zOr (Not f) g = Imp f g
zOr f g       = Or  f g

zVar v    = Var v []
zTrm t ts = Trm t ts []
zThesis   = zTrm "#TH#" []
zEqu t s  = zTrm "=" [t,s]
zSet t    = zTrm "aSet" [t]
zElm t s  = zTrm "aElementOf" [t,s]
zLess t s = zTrm "iLess" [t,s]
zSSS s ts = zTrm ('S':'C':':':s) ts

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

isThesis (Trm "#TH#" [] _)  = True
isThesis _                  = False

isSSS (Trm ('S':'C':':':_) _ _) = True
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


-- Special formulas

isDefn (Iff (Tag DHD _) _)  = True
isDefn (All _ f)            = isDefn f
isDefn (Imp _ f)            = isDefn f
isDefn _                    = False

isSign (Imp (Tag DHD _) _)  = True
isSign (All _ f)            = isSign f
isSign (Imp _ f)            = isSign f
isSign _                    = False

isUnit (Not f)              = isUnit f
isUnit f                    = isTrm f || isTop f || isBot f

isSort (Trm _ (_:ts) _)     = all ground ts
isSort (Trm ('a':_) _ _)    = True
isSort (Not (Trm "=" _ _))  = True
isSort f                    = isTop f || isBot f

ground f  = not (isVar f) && allF ground f

strip (Tag _ f) = strip f
strip f         = f


-- Info handling

hasInfo f = isTrm f || isVar f || isInd f

nullInfo f  | hasInfo f = f {trInfo = []}
            | otherwise = f

wipeInfo f  = mapF wipeInfo $ nullInfo f

skipInfo fn f | hasInfo f = (fn $ nullInfo f) {trInfo = trInfo f}
              | otherwise = fn f

trInfoI t = [ e | Tag DIM e <- trInfo t ]
trInfoO t = [ e | Tag DOR e <- trInfo t ]
trInfoE t = [ e | Tag DEQ e <- trInfo t ]
trInfoS t = [ e | Tag DSD e <- trInfo t ]
trInfoC t = [ e | Tag DCN e <- trInfo t ]
trInfoN t = [ e | Tag DNC e <- trInfo t ]
trInfoD t = trInfoE t ++ trInfoS t
trInfoA t = trInfoD t ++ trInfoI t


-- Misc stuff

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
      dive (Tag a f)  = showParen True $ shows a
                      . showString " :: " . dive f
      dive (Not f)    = showString "not " . dive f
      dive Top        = showString "truth"
      dive Bot        = showString "contradiction"

      dive (Trm "#TH#" _ _)   = showString "thesis"
      dive (Trm "=" [l,r] _)  = sinfix " = " l r
      dive (Trm s ts is)      = showString s . sargs ts -- . sinfo is
      dive (Var s _)          = showString s
      dive (Ind i _)  | i < d = showChar 'v' . shows (d - i - 1)
                      | True  = showChar 'v' . showChar '?'

      sargs []  = id
      sargs _   | p == 1  = showString "(...)"
      sargs ts  = showArgs (showFormula (pred p) d) ts

      sinfo []      = id
      sinfo (t:ts)  = showChar '[' . showFormula 0 d t
                    . showTail (showFormula 0 d) ts . showChar ']'

      binder f      = showFormula p (succ d) (Ind 0 []) . showChar ' '
                    . showFormula p (succ d) f

      sinfix o f g  = dive f . showString o . dive g

showArgs sh (t:ts)  = showParen True $ sh t . showTail sh ts
showArgs sh _       = id

showTail sh ts      = foldr ((.) . ((showChar ',' .) . sh)) id ts

