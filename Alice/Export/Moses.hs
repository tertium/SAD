{-
 -  Export/Moses.hs -- print proof task in Moses syntax
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

module Alice.Export.Moses (mosesOut) where

import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Text
import Alice.Export.Base

mosesOut :: Prover -> Int -> [Context] -> Context -> String
mosesOut pr tl cn gl = (prm . cnj . tlm) ""
  where
    prm = foldr ((.) . mosesForm) id cn
    cnj = showChar '?' . mosesTerm 0 (cnForm gl) . showChar '\n'
    tlm = shows tl . showChar '\n'


-- Formula print

mosesForm :: Context -> ShowS
mosesForm (Context f (Block { blName = m } : _))
          = showString (if null m then "_" else m)
          . showChar '\n' . mosesTerm 0 f . showChar '\n'

mosesTerm :: Int -> Formula -> ShowS
mosesTerm d = dive
  where
    dive (All v f)  = showChar '@' . binder f
    dive (Exi v f)  = showChar '$' . binder f
    dive (Iff f g)  = showChar '~' . binary f g
    dive (Imp f g)  = showChar '>' . binary f g
    dive (Or  f g)  = showChar '|' . binary f g
    dive (And f g)  = showChar '&' . binary f g
    dive (Tag a f)  = dive f
    dive (Not f)    = showChar '!' . dive f
    dive Top        = showChar '+'
    dive Bot        = showChar '-'
    dive t| isEqu t = let [l,r] = trArgs t in showChar '=' . binary l r
          | isTrm t = showTrName t . showParen True (sargs $ trArgs t)
          | isVar t = showTrName t . showParen True id
          | isInd t = showChar 'w' . shows (d - 1 - trIndx t)

    binder f  = mosesTerm (succ d) (Ind 0 []) . showChar ' '
              . mosesTerm (succ d) f

    binary f g  = dive f . showChar ' ' . dive g

    sargs (t:ts)  = dive t . showChar ' ' . sargs ts
    sargs _       = id

showTrName = showString . filter (/= ':') . trName

