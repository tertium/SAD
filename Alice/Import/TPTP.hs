{-
 -  Import/TPTP.hs -- parser for TPTP syntax
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

module Alice.Import.TPTP (tptp) where

import Control.Monad
import Data.Char
import Data.List

import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Text
import Alice.Parser.Base
import Alice.Parser.Prim

tptp :: LPM a [Text]
tptp  = fof -/- cnf

fof = u1 -/- u2 -/- u3
  where
    u1  = liftM2 ((:).TB) (narrow t_frm) fof
    u2  = include >> return []
    u3  = readEOI >> return []

cnf = u1 -/- u2 -/- u3
  where
    u1  = liftM2 ((:).TB) (narrow t_cls) cnf
    u2  = include >> return []
    u3  = liftM ((:[]).TB) contra

contra  = do  li <- nulText; let tx = "contradiction"
              readEOI; fn <- askPS psFile; la <- askPS psLang
              return $ Block Bot [] True [] "" [] la fn li tx

t_frm   = do  li <- nulText; wordOf ["fof","input_formula"]
              char '('; nm <- readTkLex; char ','; ty <- prmcnj
              char ','; fr <- formula; annots; char ')'; char '.'
              let vs = free fr; nv = unwords $ map show vs
              unless (null vs) $ fail $ "free variables: " ++ nv
              fn <- askPS psFile; la <- askPS psLang; tx <- getText
              return $ Block fr [] ty [] nm [] la fn li tx

t_cls   = do  li <- nulText; wordOf ["cnf","input_clause"]
              char '('; nm <- readTkLex; char ','; ty <- prmcnj
              char ','; f <- cnfform -/- expar cnfform -/- exbrk clause
              annots; char ')'; char '.'; let cl = foldr zAll f (free f)
              fn <- askPS psFile; la <- askPS psLang; tx <- getText
              return $ Block cl [] False [] nm [] la fn li tx

include = do  word "include"; char '('; nextChar '\''; nextWord "axioms"
              nextChar '/'; nulText; nextTkLex; nextCharOf ['+','-']
              nextTkLex; nextChar '.'; nextWordOf ["ax","eq"]
              ax <- getText; char '\''; char ')'; char '.'
              fail $ ax ++ " is inaccessible"

clause  = optEx Bot $ liftM (foldr1 Or) $ chainEx (char ',') lit
  where
    lit = (string "++" >> tatm) -/- liftM Not (string "--" >> tatm)

cnfform = liftM (foldr1 Or) $ chainEx (char '|') lit
  where
    lit = tatm -/- liftM Not (char '~' >> tatm)

formula = un_formula >>= \ f -> optEx f (binTail f)

binTail f = iff -/- xor -/- imp -/- pmi
          -/- or -/- nor -/- and -/- nan
  where
    iff = liftM (Iff f) $ string "<=>" >> formula
    xor = liftM (Not . Iff f) $ string "<~>" >> formula
    imp = liftM (Imp f) $ string "=>" >> formula
    pmi = liftM (\ g -> Imp g f) $ string "<=" >> formula
    or  = liftM (Or f) $ string "|" >> formula
    nor = liftM (Not . Or f) $ string "~|" >> formula
    and = liftM (And f) $ string "&" >> formula
    nan = liftM (Not . And f) $ string "~&" >> formula

un_formula  = uqu -/- equ -/- neg -/- tatm -/- expar formula
  where
    uqu = do  char '!'; char '['; vs <- chainEx (char ',') tvr
              char ']'; char ':'; f <- un_formula
              return $ foldr sAll f vs

    equ = do  char '?'; char '['; vs <- chainEx (char ',') tvr
              char ']'; char ':'; f <- un_formula
              return $ foldr sExi f vs

    neg = liftM Not $ char '~' >> un_formula

tatm =  tru -/- fls -/- eql -/- atm
  where
    tru = string "$true" >> return Top
    fls = string "$false" >> return Bot
    eql = string "equal" >> expar beq
    beq = liftM2 zEqu arg (char ',' >> arg)
    atm = arg >>= \ t -> optEx t (equ t -/- neq t)
    equ t = liftM (zEqu t) $ string "=" >> arg
    neq t = liftM (Not . zEqu t) $ string "!=" >> arg
    ars = optEx [] $ expar $ chainEx (char ',') arg
    arg = liftM sVar tvr -/- liftM2 sTrm sym ars

tvr = do  v@(c:_) <- nextTkLex; guard (isUpper c); skipSpace (return v)
sym = do  s@(c:_) <- nextTkLex; guard (isLower c); skipSpace (return s)

-- Service stuff

annots :: LPM a ()
annots = return ()

prmcnj = (p >> return False) -/- (c >> return True)
  where
    p = wordOf ["axiom","hypothesis","definition","lemma","theorem","plain"]
    c = wordOf ["conjecture","lemma_conjecture","negated_conjecture"]

sAll  = zAll . ('x':)
sExi  = zExi . ('x':)
sVar  = zVar . ('x':)
sTrm  = zTrm . ('s':)

free (Var v _)  = [v]
free f          = nub $ foldF free f

