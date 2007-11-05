{-
 -  Export/TPTP.hs -- print proof task in TPTP syntax
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

module Alice.Export.TPTP (tptpOut) where

import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Text
import Alice.Export.Base

tptpOut :: Prover -> Int -> [Context] -> Context -> String
tptpOut _ _ cn gl = (axs . cnj) ""
  where
    axs = foldr (flip (.) . tptpForm ",hypothesis,") id cn
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
    dive (All _ f)  = showParen True $ showString " ! " . binder f
    dive (Exi _ f)  = showParen True $ showString " ? " . binder f
    dive (Iff f g)  = sinfix " <=> " f g
    dive (Imp f g)  = sinfix " => " f g
    dive (Or  f g)  = sinfix " | " f g
    dive (And f g)  = sinfix " & " f g
    dive (Tag _ f)  = dive f
    dive (Not f)    = showParen True $ showString " ~ " . dive f
    dive Top        = showString "$true"
    dive Bot        = showString "$false"
    dive t| isEqu t = let [l, r] = trArgs t in sinfix " = " l r
          | isTrm t = showTrName t . showArgs dive (trArgs t)
          | isVar t = showTrName t
          | isInd t = showChar 'W' . shows (d - 1 - trIndx t)

    sinfix o f g  = showParen True $ dive f . showString o . dive g

    binder f  = showChar '[' . tptpTerm (succ d) (Ind 0 [])
              . showString "] : " . tptpTerm (succ d) f

showTrName = showString . (:) 's' . filter (/= ':') . trName

