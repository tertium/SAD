{-
 -  Import/FOL.hs -- parser for simple first order syntax
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

module Alice.Import.FOL (fol) where

import Control.Monad
import Data.Char

import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Text
import Alice.Parser.Base
import Alice.Parser.Prim

-- First-order text

fol :: LPM a [Text]
fol = u1 -/- u2 -/- u3
  where
    u1  = liftM2 ((:).TB) (narrow formula) fol
    u2  = liftM ((:[]).TB) contra
    u3  = readEOI >> return []

formula = do  let sign = optEx False $ char ':' >> return True
              li <- nulText; ty <- sign; f <- iff_form; char '.'
              fn <- askPS psFile; la <- askPS psLang; tx <- getText
              return $ Block f [] ty [] "" [] la fn li tx

contra  = do  li <- nulText; char ':'; let tx = "contradiction"
              readEOI; fn <- askPS psFile; la <- askPS psLang
              return $ Block Bot [] True [] "" [] la fn li tx

-- Binary formulas

iff_form  = bi_form imp_form imp_form iff_op Iff id
imp_form  = bi_form dis_form imp_form imp_op Imp id
dis_form  = bi_form con_form dis_form dis_op Or  id
con_form  = bi_form dot_form con_form con_op And id

-- Grouping: parentheses and Church's dot

dot_form  = (char '.' >> iff_form) -/- par_form
par_form  = (char '(' >> after iff_form (char ')')) -/- all_form

-- Quantifiers

all_form  = (all_op >> qu_head sAll) -/- exi_form
exi_form  = (exi_op >> qu_head sExi) -/- neg_form
qu_head o = liftM2 (flip $ foldr o) (com_seq sym) dot_form

-- Unary formulas

neg_form  = (neg_op >> liftM Not dot_form) -/-
            (word "true"  >> return Top) -/-
            (word "false" >> return Bot) -/- equ_form

equ_form  = do  t <- sin_term; optEx t (equ t -/- neq t)
  where
    equ t = equ_op >> liftM (zEqu t) sin_term
    neq t = neq_op >> liftM (Not . zEqu t) sin_term

sin_term  = liftM2 sTrm sym seq_term -/- liftM sVar sym
seq_term  = char '(' >> after (com_seq sin_term) (char ')')

sym = do  s <- nextTkLex
          guard (map toLower s `notElem` opers)
          skipSpace (return s)

-- Service stuff

bi_form lf rf op cn cm =
    lf >>= \ f -> (op >> liftM (cn f) rf) -/- (return $ cm f)

com_seq p = bi_form p (com_seq p) (char ',') (:) (:[])

sAll  = zAll . ('x':)
sExi  = zExi . ('x':)
sVar  = zVar . ('x':)
sTrm  = zTrm . ('s':)

iff_op  = char '~' -/- word "iff"
imp_op  = char '>' -/- word "implies"
dis_op  = char '|' -/- word "or"
con_op  = char '&' -/- word "and"
neg_op  = char '-' -/- word "not"
all_op  = char '@' -/- word "forall"
exi_op  = char '$' -/- word "exists"
equ_op  = char '='
neq_op  = string "!="

opers = ["iff", "implies", "or", "and", "not", "forall", "exists", "true", "false"]

