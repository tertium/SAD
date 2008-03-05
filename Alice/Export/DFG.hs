{-
 -  Export/DFG.hs -- print proof task in DFG syntax
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

module Alice.Export.DFG (dfgOut) where

import Data.List

import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Text
import Alice.Export.Base

dfgOut :: Prover -> Int -> [Context] -> Context -> String
dfgOut _ _ cn gl = (hdr . sym . axm . cnj . eop) ""
  where
    hdr = showString "begin_problem(A).list_of_descriptions.name({*EA*})."
        . showString "author({*EA*}).status(unknown).description({*EA*})."
        . eol

    sym = showString "list_of_symbols.\n" . dfgSLS (gl:cn) . eol

    axm = showString "list_of_formulae(axioms).\n" . axs . eol
    cnj = showString "list_of_formulae(conjectures).\n" . gll . eol

    eol = showString "end_of_list.\n"
    eop = showString "end_problem.\n"

    axs = foldr (flip (.) . dfgForm) id cn
    gll = dfgForm gl


-- Formula print

dfgForm :: Context -> ShowS
dfgForm (Context f (Block { blName = m } : _))
        = showString "formula(" . dfgTerm 0 f . showChar ','
        . showString (if null m then "_" else m) . showString ").\n"

dfgTerm :: Int -> Formula -> ShowS
dfgTerm d = dive
  where
    dive (All _ f)  = showString "forall" . showParen True (binder f)
    dive (Exi _ f)  = showString "exists" . showParen True (binder f)
    dive (Iff f g)  = showString "equiv" . showArgs dive [f,g]
    dive (Imp f g)  = showString "implies" . showArgs dive [f,g]
    dive (Or  f g)  = showString "or" . showArgs dive [f,g]
    dive (And f g)  = showString "and" . showArgs dive [f,g]
    dive (Tag _ f)  = dive f
    dive (Not f)    = showString "not" . showArgs dive [f]
    dive Top        = showString "true"
    dive Bot        = showString "false"
    dive t| isEqu t = showString "equal" . showArgs dive (trArgs t)
          | isTrm t = showTrName t . showArgs dive (trArgs t)
          | isVar t = showTrName t
          | isInd t = showChar 'W' . shows (d - 1 - trIndx t)

    binder f  = showChar '[' . dfgTerm (succ d) (Ind 0 [])
              . showString "]," . dfgTerm (succ d) f

showTrName = showString . filter (/= ':') . trName


-- Symbol count

dfgSLS :: [Context] -> ShowS
dfgSLS tsk  = sls "functions" fns . sls "predicates" pds
  where
    sls s (hd:tl) = showString s . showChar '[' . shs hd
                  . showTail shs tl . showString "].\n"
    sls _ _ = id

    shs (s, a)  = showParen True $ stn s . showChar ',' . shows a
    stn = showString . filter (/= ':')

    pds = [ (s, a) | (True,  s, a) <- sms ]
    fns = [ (s, a) | (False, s, a) <- sms ]
    sms = foldr (union . nub . dfgSyms True . cnForm) [] tsk

dfgSyms :: Bool -> Formula -> [(Bool, String, Int)]
dfgSyms s f | isEqu f   = concatMap (dfgSyms False) $ trArgs f
dfgSyms s (Trm t ts _)  = (s, t, length ts) : concatMap (dfgSyms False) ts
dfgSyms s (Var v _)     = [(s, v, 0)]
dfgSyms s (Ind _ _)     = []
dfgSyms s f             = foldF (dfgSyms s) f

