{-
 -  ForTheL/Intro.hs -- aliases, definitions, signature extensions
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

module Alice.ForTheL.Intro where

import Control.Monad
import Data.Char
import Data.List

import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Text
import Alice.ForTheL.Base
import Alice.ForTheL.Phrase
import Alice.ForTheL.Pattern
import Alice.Parser.Base
import Alice.Parser.Prim
import Alice.Parser.Trans

-- Introduction of synonyms, pretyped variables, and aliases

isyms = do  nulText
            ss <- doLFTL $ narrow sym ; st <- getS
            setS st { str_syms = ss : str_syms st }
  where
    sym = exbrk $ do  w <- wlexem ; h <- opt w $ sfx w ; char '/'
                      sls <- chain (char '/') $ wlexem -|- sfx w
                      return $ h : sls

    sfx w = nextChar '-' >> liftM (w ++) readTkLex

itvar = do  nulText; word "let"
            tv <- doLFTL $ narrow tvr ; st <- getS
            setS st { tvr_expr = tv : tvr_expr st }
  where
    tvr = do  vs@(_:_) <- varlist
              (q, f) <- stand >> dot anotion
              g <- liftM q $ dig f [zHole]
              let wfc = overfree [] g
              unless (null wfc) (fail wfc)
              return (vs, renull g)

alias = do  nulText; word "let"
            (f, g) <- doLFTL $ narrow $ prd -|- ntn
            getS >>= newExpr f (renull g); return ()
  where
    prd = do  f <- new_prd avr
              g <- stand >> dot statement
              prdvars f g ; return (f, g)

    ntn = do  (n, u) <- new_nnm avr
              (q, f) <- stand >> dot anotion
              h <- liftM q $ dig f [zVar u]
              funvars n h ; return (n, h)

renull (All v f)  = All "" f
renull (Exi v f)  = Exi "" f
renull f          = mapF renull f


-- Extraction of new primitives from definitions and sigexts

extPrim bl  = liftM nbb $ ext $ blForm lbl
  where
    nbb f = bl { blBody = reverse $ TB lbl { blForm = f } : ibl }

    (TB lbl :ibl) = reverse $ blBody bl

    ext (All u f) = liftM (zAll u) $ ext $ inst u f
    ext (Iff l r) = liftM (`Iff` r) (ext l)
    ext (Imp l r) = liftM (`Imp` r) (ext l)
    ext (Tag a f) = liftM (Tag a)   (ext f)
    ext f = getS >>= newExpr f f


-- Definitions and sigexts

definition  = def_prd -|- def_ntn
signaturex  = sig_prd -|- sig_ntn

def_prd = do  f <- old_prd mnn ; g <- statement
              prdvars f g ; return $ Iff (Tag DHD f) g
  where
    mnn = iff -|- string "<=>"

sig_prd = do  f <- old_prd mnn ; g <- statement -|- atm
              prdvars f g ; return $ Imp (Tag DHD f) g
  where
    mnn = word "is" -|- word "implies" -|- string "=>"
    atm = an >> wordOf ["atom","relation"] >> return Top

def_ntn = do  (n, u) <- old_ntn ieq; (q, f) <- anotion
              let v = zVar u ; fn = replace v (trm n)
              h <- liftM (fn . q) $ dig (set f) [v]
              ntnvars n h ; return $ zAll u $ Iff (Tag DHD n) h
  where
    ieq = char '=' -|- iqt
    iqt = is >> opt () (word "equal" >> word "to")
    trm (Trm "=" [_,t] _) = t ; trm t = t

    set (Tag DIG (Trm "=" [l, r@(Trm _ _ [Tag DEQ d])] _))
          = Tag DIG $ replace l r d
    set n = n

sig_ntn = do  (n, u) <- old_ntn is; (q, f) <- anotion -|- nmn
              let v = zVar u ; fn = replace v (trm n)
              h <- liftM (fn . q) $ dig f [v]
              ntnvars n h ; return $ zAll u $ Imp (Tag DHD n) h
  where
    nmn = an >> wordOf ["notion","function","constant"] >> return (id,Top)
    trm (Trm "=" [_,t] _) = t ; trm t = t


-- Overloaded patterns

old_prd p = after old p -/- after (new_prd nvr) p
  where
    old = una -|- mul -|- old_spr

    una = do  v <- zvr; (_, f) <- uad -|- uve
              return $ substH v f

    mul = do  (u,v) <- mvr; (_, f) <- mad -|- mve
              return $ substH u $ substS v f

    uad = is >> prim_adj variable
    mad = is >> prim_m_adj variable
    uve = prim_ver variable
    mve = prim_m_ver variable

    mvr = liftM2 (,) zvr (com >> zvr)
    com = word "and" -|- char ','

old_ntn p = after old p -/- after (new_ntn nvr) p
  where
    old = ntn -|- (old_sfn >>= eqt)
    ntn = art >> prim_ntn variable >>= single >>= out
    eqt t = do  v <- hidden ; return (zEqu (zVar v) t, v)
    out (_, n, v) = return (substH (zVar v) n, v)

old_spr = cpr -|- lpr -|- rpr -|- ipr
  where
    cpr = prim_cpr zvr
    lpr = liftM2 ($) (prim_lpr zvr) zvr
    rpr = liftM2 (flip ($)) zvr (prim_rpr zvr)
    ipr = liftM2 ($) (liftM2 (flip ($)) zvr (prim_ipr zvr)) zvr

old_sfn = cfn -|- lfn -|- rfn -|- ifn
  where
    cfn = prim_cfn zvr
    lfn = liftM2 ($) (prim_lfn zvr) zvr
    rfn = liftM2 (flip ($)) zvr (prim_rfn zvr)
    ifn = liftM2 ($) (liftM2 (flip ($)) zvr (prim_ifn zvr)) zvr

zvr = liftM zVar var


-- Well-formedness checking

funvars f d | not ifq   = prdvars f d
            | not idq   = nextfail $ "illegal function alias: " ++ show d
            | otherwise = prdvars (zTrm s (v:vs)) d
  where
    ifq = isEqu f && isTrm t
    idq = isEqu d && not (occurs u p)
    (Trm "=" [v, t] _)  = f
    (Trm "=" [u, p] _)  = d
    (Trm s vs _)        = t

ntnvars f d | not ifq   = prdvars f d
            | otherwise = prdvars (zTrm s (v:vs)) d
  where
    ifq = isEqu f && isTrm t
    (Trm "=" [v, t] _)  = f
    (Trm s vs _)        = t

prdvars f d | not flt   = nextfail $ "compound expression: " ++ show f
            | null wfc  = return ()
            | otherwise = nextfail wfc
  where
    wfc = overfree (free [] f) d
    flt = isTrm f && pvs [] (trArgs f)

    pvs ls (Var v@('h':_) _ : vs)  = notElem v ls && pvs (v:ls) vs
    pvs ls (Var v@('x':_) _ : vs)  = notElem v ls && pvs (v:ls) vs
    pvs _ []                       = True
    pvs _ _                        = False

