{-
 -  Export/Otter.hs -- print proof task in Otter syntax
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

module Alice.Export.Otter (otterOut) where

import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Text
import Alice.Export.Base

otterOut :: Prover -> Int -> [Context] -> Context -> String
otterOut pr tl cn gl = (hdr . usa . sos) ""
  where
    hdr = foldr ((.) . showString) tlm $ filter ((== '.') . last) $ prArgs pr
    tlm = showString "assign(max_seconds," . shows tl . showString ").\n"
        . showString "set(prolog_style_variables).\n"

    usa = showString "formula_list(usable).\n"
        . foldr (flip (.) . otterForm . cnForm) equ cn . eol

    aut = if elem "set(auto)." (prArgs pr) then "usable" else "sos"
    sos = showString "formula_list(" . showString aut . showString ").\n"
        . otterForm (Not $ cnForm gl) . eol

    equ = showString "all X (X = X).\n"
    eol = showString "end_of_list.\n"


-- Formula print

otterForm :: Formula -> ShowS
otterForm f = otterTerm 0 f . showString ".\n"

otterTerm :: Int -> Formula -> ShowS
otterTerm d = dive
  where
    dive (All _ f)  = showString "(all " . binder f . showChar ')'
    dive (Exi _ f)  = showString "(exists " . binder f . showChar ')'
    dive (Iff f g)  = showString "<->" . showArgs dive [f,g]
    dive (Imp f g)  = showString "->" . showArgs dive [f,g]
    dive (Or  f g)  = showString "|" . showArgs dive [f,g]
    dive (And f g)  = showString "&" . showArgs dive [f,g]
    dive (Tag _ f)  = dive f
    dive (Not f)    = showString "-" . showArgs dive [f]
    dive Top        = showString "$T"
    dive Bot        = showString "$F"
    dive t| isEqu t = showString "=" . showArgs dive (trArgs t)
          | isTrm t = showTrName t . showArgs dive (trArgs t)
          | isVar t = showTrName t
          | isInd t = showChar 'W' . shows (d - 1 - trIndx t)

    binder f  = otterTerm (succ d) (Ind 0 []) . showChar ' '
              . otterTerm (succ d) f

showTrName = showString . filter (/= ':') . trName

