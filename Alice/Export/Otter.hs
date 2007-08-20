module Alice.Export.Otter (otterOut) where

import Alice.Data.Context
import Alice.Data.Formula
import Alice.Data.Text
import Alice.Export.Base

otterOut :: Prover -> Int -> [Context] -> Formula -> String
otterOut pr tl cn gl = (hdr . sos . usa) ""
  where
    hdr = foldr ((.) . sop) tlm (prArgs pr)
    sop o = showString o . showString ".\n"

    tlm = showString "assign(max_seconds," . shows tl . showString ").\n"

    aut = if elem "set(auto)" (prArgs pr) then "usable" else "sos"
    sos = showString "formula_list(" . showString aut . showString ").\n"
        . otterForm (Not gl) . eol

    usa = showString "formula_list(usable).\n"
        . foldr ((.) . otterForm . cnForm) equ cn . eol

    equ = showString "all x (x = x).\n"
    eol = showString "end_of_list.\n"


-- Formula print

otterForm :: Formula -> ShowS
otterForm f = otterTerm 0 f . showString ".\n"

otterTerm :: Int -> Formula -> ShowS
otterTerm d = dive
  where
    dive (All v f)  = showString "$Quantified(all," . binder f . showChar ')'
    dive (Exi v f)  = showString "$Quantified(exists," . binder f . showChar ')'
    dive (Iff f g)  = showString "<->" . showArgs dive [f,g]
    dive (Imp f g)  = showString "->" . showArgs dive [f,g]
    dive (Or  f g)  = showString "|" . showArgs dive [f,g]
    dive (And f g)  = showString "&" . showArgs dive [f,g]
    dive (Ann a f)  = dive f
    dive (Sub f g)  = dive f
    dive (Not f)    = showString "-" . showArgs dive [f]
    dive Top        = showString "$T"
    dive Bot        = showString "$F"
    dive t| isEqu t = showString "=" . showArgs dive (trArgs t)
          | isTrm t = showString (trName t) . showArgs dive (trArgs t)
          | isVar t = showString (trName t)
          | isInd t = showChar 'v' . shows (d - 1 - trIndx t)

    binder f  = otterTerm (succ d) (Ind 0 []) . showChar ','
              . otterTerm (succ d) f

