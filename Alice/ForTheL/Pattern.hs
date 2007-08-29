{-
 -  ForTheL/Pattern.hs -- handle new syntactic primitives
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

module Alice.ForTheL.Pattern where

import Control.Monad
import Data.Char
import Data.List

import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Text
import Alice.ForTheL.Base
import Alice.Parser.Base
import Alice.Parser.Prim
import Alice.Parser.Trans

-- Expression generation

newExpr t@(Trm ('i':'s':' ':_) vs _) f st = setS ns >> return nf
  where
    (pt, nf) = wexp st t f
    fm  = substs nf $ map trName vs
    ns  = st { adj_expr = (pt, fm) : adj_expr st }

newExpr t@(Trm ('d':'o':' ':_) vs _) f st = setS ns >> return nf
  where
    (pt, nf) = wexp st t f
    fm  = substs nf $ map trName vs
    ns  = st { ver_expr = (pt, fm) : ver_expr st }

newExpr t@(Trm ('m':'i':'s':' ':_) vs _) f st = setS ns >> return nf
  where
    ((hp:tp), nf) = wexp st t f
    pt  = hp : Wd [] : Vr : tp
    fm  = substs nf $ map trName vs
    ns  = st { adj_expr = (pt, fm) : adj_expr st }

newExpr t@(Trm ('m':'d':'o':' ':s) vs _) f st = setS ns >> return nf
  where
    ((hp:tp), nf) = wexp st t f
    pt  = hp : Wd [] : Vr : tp
    fm  = substs nf $ map trName vs
    ns  = st { ver_expr = (pt, fm) : ver_expr st }

newExpr t@(Trm ('a':' ':s) vs _) f st = setS ns >> return nf
  where
    (pt, nf) = wexp st t f
    fm  = substs nf $ map trName vs
    ns  = st { ntn_expr = (pt, fm) : ntn_expr st }

newExpr (Trm "=" [v, t@(Trm ('a':' ':s) vs _)] _) f st
        = setS ns >> return nf
  where
    (pt, nf) = wexp st t f
    fm  = substs nf $ map trName (v:vs)
    ns  = st { ntn_expr = (pt, fm) : ntn_expr st }

newExpr t@(Trm s vs _) f st | elem ' ' s  = setS nn >> return nf
  where
    (pt, nf) = sexp t f ; fm = substs nf $ map trName vs
    csm = lsm && rsm ; lsm = nvr (head pt) ; rsm = nvr (last pt)
    nvr Vr = False ; nvr _ = True

    ns  | csm   = st { cpr_expr = (pt, fm) : cpr_expr st }
        | lsm   = st { lpr_expr = (init pt, fm) : lpr_expr st }
        | rsm   = st { rpr_expr = (tail pt, fm) : rpr_expr st }
        | True  = st { ipr_expr = (init (tail pt), fm) : ipr_expr st }

    nn  | snt   = ns { snt_expr = (tail pt, fm) : snt_expr st }
        | True  = ns

    snt = not lsm && elem (trName $ head vs) (decl [] nf)

newExpr (Trm "=" [_, t@(Trm s vs _)] _) (Trm "=" [v, f] _) st
        | elem ' ' s = setS ns >> return (zEqu v nf)
  where
    (pt, nf) = sexp t f ; fm = substs nf $ map trName vs
    csm = lsm && rsm ; lsm = nvr (head pt) ; rsm = nvr (last pt)
    nvr Vr = False ; nvr _ = True

    ns  | csm   = st { cfn_expr = (pt, fm) : cfn_expr st }
        | lsm   = st { lfn_expr = (init pt, fm) : lfn_expr st }
        | rsm   = st { rfn_expr = (tail pt, fm) : rfn_expr st }
        | True  = st { ifn_expr = (init (tail pt), fm) : ifn_expr st }

newExpr _ f _ = return f


-- Pattern extraction

wexp st t@(Trm s vs _) f = (pt, nf)
  where
    pt  = map get_patt ws
    nt  = zTrm (pr ++ get_name pt) vs
    nf  = replace nt t f
    ss  = str_syms st
    (pr:ws) = words s

    get_patt "." = Nm
    get_patt "#" = Vr
    get_patt  w  = Wd $ foldl union [w] $ filter (elem w) ss

    get_name (Wd ((c:cs):_):ls) = toUpper c : cs ++ get_name ls
    get_name (_:ls)             = get_name ls
    get_name []                 = ""

sexp t@(Trm s vs _) f = (pt, nf)
  where
    pt  = map get_patt (words s)
    nt  = zTrm ('s' : get_name pt) vs
    nf  = replace nt t f

    get_patt "#" = Vr
    get_patt  w  = Sm w

    get_name (Sm s:ls)  = symEncode s ++ get_name ls
    get_name (_:ls)     = get_name ls
    get_name []         = ""


-- New patterns

new_prd tvr = una -/- mul -/- new_sym tvr
  where
    una = do  v <- tvr; (t, vs) <- uad -|- uve
              return $ zTrm t (v:vs)

    mul = do  (u,v) <- mvr; (t, vs) <- mad -|- mve
              return $ zTrm t (u:v:vs)

    uad = do  is ; (t, vs) <- pt_head wlexem tvr ; return ("is " ++ t, vs)
    mad = do  is ; (t, vs) <- pt_head wlexem tvr ; return ("mis " ++ t, vs)
    uve = do  (t, vs) <- pt_head wlexem tvr ; return ("do " ++ t, vs)
    mve = do  (t, vs) <- pt_head wlexem tvr ; return ("mdo " ++ t, vs)

    mvr = liftM2 (,) tvr (com >> tvr)
    com = word "and" -|- char ','

new_ntn tvr = ntn -/- fun -/- new_nnm tvr
  where
    ntn = do  an ; (t, v:vs) <- pt_name wlexem tvr
              return (zTrm ("a " ++ t) (v:vs), trName v)

    fun = do  the; (t, v:vs) <- pt_name wlexem tvr
              return (zEqu v $ zTrm ("a " ++ t) vs, trName v)

new_nnm tvr = ntn -/- fun -/- (new_sym tvr >>= eqt)
  where
    ntn = do  an ; (t, v:vs) <- pt_nonm wlexem tvr
              return (zTrm ("a " ++ t) (v:vs), trName v)

    fun = do  the; (t, v:vs) <- pt_nonm wlexem tvr
              return (zEqu v $ zTrm ("a " ++ t) vs, trName v)

    eqt t = do  v <- hidden ; return (zEqu (zVar v) t, v)

new_sym tvr = lsm -|- rsm
  where
    lsm = do  (t, vs) <- pt_head slexem tvr
              return $ zTrm t vs

    rsm = do  (t, vs) <- pt_tail slexem tvr
              guard $ not $ null $ tail $ words t
              return $ zTrm t vs


-- Pattern parsing

pt_name lex tvr = do  l <- liftM unwords $ chnop lex; n <- nam
                      (ls, vs) <- opt ([], []) $ pt_head lex tvr
                      return (l ++ " . " ++ ls, n:vs)

pt_nonm lex tvr = do  l <- liftM unwords $ chnop lex; n <- hid
                      (ls, vs) <- opt ([], []) $ pt_shot lex tvr
                      return (l ++ " . " ++ ls, n:vs)

pt_shot lex tvr = do  l <- lex; (ls, vs) <- pt_tail lex tvr
                      return (l ++ ' ' : ls, vs)

pt_head lex tvr = do  l <- liftM unwords $ chnop lex
                      (ls, vs) <- opt ([], []) $ pt_tail lex tvr
                      return (l ++ ' ' : ls, vs)

pt_tail lex tvr = do  v <- tvr
                      (ls, vs) <- opt ([], []) $ pt_head lex tvr
                      return ("# " ++ ls, v:vs)


-- In-pattern lexemes and variables

wlexem  = do  l <- wlx; guard $ all isAlpha l; return $ map toLower l

slexem  = slex -|- wlx
  where
    slex  = skipSpace $ chnopEx $ nextTkChr >>= nxc
    nxc c = guard (c `elem` symChars) >> return c

wlx = do  l <- liftM (const "?") (nvr -/- avr) -/- readTkLex
          guard $ all isAlphaNum l &&
            not (isAlpha (head l) && null (tail l)) &&
            l `notElem` ["a", "an", "the", "is", "are", "be"]
          return l

nvr = do  v <- var; dvs <- getDecl; tvs <- askS tvr_expr
          guard $ v `elem` dvs || any (elem v . fst) tvs
          return $ zVar v

avr = do  v <- var; guard $ null $ tail $ tail v
          return $ zVar v

nam = do  n <- liftM (const Top) nvr -/- avr
          guard $ isVar n ; return n

hid = liftM zVar hidden

