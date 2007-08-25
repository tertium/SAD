module Alice.Export.TPTP (tptpOut) where

import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Text
import Alice.Export.Base

tptpOut :: Prover -> Int -> [Context] -> Context -> String
tptpOut pr tl cn gl = tsk ""
  where
    tsk = foldr ((.) . tptpForm ",hypothesis,") cnj cn
    cnj = tptpForm ",conjecture," gl


-- Formula print

tptpForm :: String -> Context -> ShowS
tptpForm s (Context f (Block { blName = m } : _))
          = showString "fof(m"
          . showString (if null m then "_" else m)
          . showString s . tptpTerm 0 f . showString ").\n"

tptpTerm :: Int -> Formula -> ShowS
tptpTerm d = dive
  where
    dive (All v f)  = showParen True $ showString " ! " . binder f
    dive (Exi v f)  = showParen True $ showString " ? " . binder f
    dive (Iff f g)  = sinfix " <=> " f g
    dive (Imp f g)  = sinfix " => " f g
    dive (Or  f g)  = sinfix " | " f g
    dive (And f g)  = sinfix " & " f g
    dive (Ann a f)  = dive f
    dive (Sub f g)  = dive f
    dive (Not f)    = showParen True $ showString " ~ " . dive f
    dive Top        = showString "$true"
    dive Bot        = showString "$false"
    dive t| isEqu t = let [l, r] = trArgs t in sinfix " = " l r
          | isTrm t = showTrName t . showArgs dive (trArgs t)
          | isVar t = showTrName t
          | isInd t = showChar 'X' . shows (d - 1 - trIndx t)

    sinfix o f g  = showParen True $ dive f . showString o . dive g

    binder f  = showChar '[' . tptpTerm (succ d) (Ind 0 [])
              . showString "] : " . tptpTerm (succ d) f

showTrName = showString . (:) 's' . filter (/= ':') . trName

