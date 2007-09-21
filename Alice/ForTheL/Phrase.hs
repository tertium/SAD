{-
 -  ForTheL/Phrase.hs -- sentence grammar
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

module Alice.ForTheL.Phrase where

import Control.Monad
import Data.List
import Data.Maybe

import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Text
import Alice.ForTheL.Base
import Alice.Parser.Prim
import Alice.Parser.Base
import Alice.Parser.Trans

-- Statement syntax

statement = headed -|- (aon_chain atomic >>= stail)

headed  = u1 -|- u2 -|- u3
  where
    u1  = liftM2 Imp (word "if" >> statement) (word "then" >> statement)
    u2  = liftM Not $ wrong >> statement
    u3  = liftM2 ($) qu_chain statement

stail x = opt x $ u1 -|- u2 -|- u3 -|- u4
  where
    u1  = liftM (And x) $ word "and" >> headed
    u2  = liftM (Or  x) $ word "or"  >> headed
    u3  = liftM (Iff x) $ iff >> statement
    u4  = do  wordOf ["when","where"]; y <- statement
              return $ foldr zAll (Imp y x) (decl [] y)

atomic  = atom -|- thereis -|- (wehve >> (smform -|- thesis))

smform  = liftM2 (flip ($)) s_form $ opt id qu_chain

thesis  = art >> (u1 -|- u2 -|- u3)
  where
    u1  = word "thesis" >> return zThesis
    u2  = word "contrary" >> return (Not zThesis)
    u3  = word "contradiction" >> return Bot

thereis = there >> (u1 -|- u2)
  where
    u1  = liftM hchain $ comma $ art >> notion
    u2  = do  word "no"; (q, f, v) <- notion
              return $ Not $ foldr mbExi (q f) v

    hchain ((q, f, v):ns) = foldr mbExi (bool $ And (q f) $ hchain ns) v
    hchain _  = Top

selection = liftM hchain $ comma $ art >> notion
  where
    hchain ((q, f, v):ns) = foldr xExi (bool $ And (q f) $ hchain ns) v
    hchain _  = Top

    xExi ('x':_) f = f
    xExi v f = mbExi v f


-- Atomic syntax

atom :: LFTL Formula
atom  = do  (q, ts) <- term_seq
            p <- and_chain does_literal
            liftM2 (q .) (opt id qu_chain) (dig p ts)

does_literal  = u1 -|- u2 -|- u3 -|- u4
  where
    u1  = does >> literal prim_ver
    u2  = does >> m_literal prim_m_ver
    u3  = has >> has_literal
    u4  = is >> and_chain (isa_literal -|- is_literal)

is_literal  = u1 -|- u2 -|- u3
  where
    u1  = literal prim_adj
    u2  = m_literal prim_m_adj
    u3  = with >> has_literal

isa_literal = u1 -|- u2
  where
    u1  = do  (q, f) <- anotion; return $ q f
    u2  = do  word "not"; (q, f) <- anotion; let unf = dig f [zHole]
              optEx (q $ Not f) $ liftM (q . Tag DIG . Not) unf

has_literal = u1 -|- u2 -|- u3 -|- u4
  where
    u1  = liftM (Tag DIG . hchain) (comma $ art >> possess)
    u2  = art >> word "common" >> liftM hchain (comma $ liftM digadd possess)
    u3  = do  word "no"; (q, f, v) <- possess
              return $ q $ Tag DIG $ Not $ foldr mbExi f v
    u4  = do  word "no"; word "common"; (q, f, v) <- possess
              return $ q $ Not $ foldr mbExi (Tag DIG f) v

    hchain ((q, f, v):ns) = q $ foldr mbExi (bool $ And f $ hchain ns) v
    hchain _  = Top

literal p   = positive p  -|- (word "not" >> negative p)
m_literal p = mpositive p -|- (word "not" >> mnegative p)
mpositive p = spositive p -|- (word "pairwise" >> ppositive p)
mnegative p = snegative p -|- (word "pairwise" >> pnegative p)

positive p  = do  (q, f) <- p term; return $ q $ Tag DIG f
spositive p = do  (q, f) <- p term; return $ q $ Tag DMS f
ppositive p = do  (q, f) <- p term; return $ q $ Tag DMP f

negative p  = do  (q, f) <- p term; return $ q $ Tag DIG $ Not f
snegative p = do  (q, f) <- p term; return $ q $ Not $ Tag DMS f
pnegative p = do  (q, f) <- p term; return $ q $ Not $ Tag DMP f


-- Notion syntax

anotion = art >> gnotion basentn rat >>= single >>= hol
  where
    hol (q, f, v) = return (q, subst zHole v f)
    rat = liftM (Tag DIG) stattr

notion  = gnotion (basentn -|- sym_notion) stattr >>= digntn

possess = gnotion (prim_of_ntn term) stattr >>= digntn

gnotion nt ra  =  do  ls <- liftM reverse la; (q, f, v) <- nt
                      rs <- opt [] $ liftM (:[]) (rc -|- ra)
                      return (q, foldr1 And $ f : ls ++ rs, v)
  where
    la  = opt [] $ liftM2 (:) lc la
    lc  = positive prim_un_adj -|- mpositive prim_m_un_adj
    rc  = and_chain is_literal -|- (that >> and_chain does_literal)

basentn = liftM digadd (prim_ntn term -|- cm -|- sym_eqnt -|- set_eqnt)
  where
    cm  = word "common" >> prim_cm_ntn term term_seq

stattr  = such >> that >> statement

digadd (q, f, v)  = (q, Tag DIG f, v)

digntn (q, f, v)  = dig f (map zVar v) >>= \ g -> return (q, g, v)

single (q, f, [v])  = return (q, f, v)
single _            = nextfail "inadmissible multinamed notion"


-- Term syntax

term_seq :: LFTL MTerm
term_seq  = liftM (foldl1 fld) $ comma mterm
  where
    fld (q, ts) (r, ss) = (q . r, ts ++ ss)

mterm :: LFTL MTerm
mterm = qu_notion -|- liftM s2m nn_term
  where
    s2m (q, t) = (q, [t])

term :: LFTL UTerm
term  = (qu_notion >>= m2s) -|- nn_term
  where
    m2s (q, [v]) = return (q, v)
    m2s _ = nextfail "inadmissible multinamed notion"

qu_notion :: LFTL MTerm
qu_notion = paren (fa -|- ex -|- no)
  where
    fa  = do  wordOf ["every", "each", "all", "any"]; (q, f, v) <- notion
              return (q . flip (foldr zAll) v . Imp f, map zVar v)

    ex  = do  word "some"; (q, f, v) <- notion
              return (q . flip (foldr zExi) v . And f, map zVar v)

    no  = do  word "no"; (q, f, v) <- notion
              return (q . flip (foldr zAll) v . Imp f . Not, map zVar v)

qu_chain  = liftM (foldl fld id) $ word "for" >> comma qu_notion
  where
    fld x (y, _)  = x . y

nn_term   = sym_term -|- paren (art >> (set_term -|- prim_fun term))

fo_term   = sym_term -|- paren (art >> (set_term -|- prim_fun fo_term))


-- Symbolic notation

sym_notion  = (paren (prim_snt s_term) -|- prim_tvr) >>= (digntn . digadd)

sym_eqnt    = do  t <- s_term; guard $ isTrm t
                  v <- hidden; return (id, zEqu zHole t, [v])

sym_term    = liftM ((,) id) s_term

variable    = liftM ((,) id) s_var

s_form  = liftM snd s_iff
  where
    s_iff = s_imp >>= bin_f Iff (string "<=>" >> s_imp)
    s_imp = s_dis >>= bin_f Imp (string "=>"  >> s_imp)
    s_dis = s_con >>= bin_f Or  (string "\\/" >> s_dis)
    s_con = s_una >>= bin_f And (string "/\\" >> s_con)
    s_una = s_all -|- s_exi -|- s_not -|- s_dot -|- s_atm
    s_all = liftM2 (qua_f zAll Imp) (word "forall" >> sym_notion) s_una
    s_exi = liftM2 (qua_f zExi And) (word "exists" >> sym_notion) s_una
    s_not = liftM (una_f Not) $ word "not" >> s_una
    s_dot = liftM ((,) False) $ char ':' >> s_form
    s_atm = liftM ((,) True)  $ s_atom

    una_f o (s, f)      = (s, o f)
    qua_f q o (_, f, v) = una_f $ flip (foldr q) v . o f

    bin_f o p r@(True, f) = opt r $ liftM (una_f $ o f) p
    bin_f _ _ r           = return r

    s_atom  = s_chain -|- prim_cpr s_term -|- expar statement
    s_chain = liftM (foldl1 And . concat) s_hd

    s_ts    = chain (char ',') s_term
    s_hd    = l_hd -|- (s_ts >>= s_tl)
    s_tl ls = i_tl ls -|- r_tl ls

    l_hd    = do  pr <- prim_lpr s_term ; rs <- s_ts
                  liftM (map pr rs:) $ opt [] $ s_tl rs

    i_tl ls = do  pr <- prim_ipr s_term ; rs <- s_ts
                  let f = [ pr l r | l <- ls, r <- rs ]
                  liftM (f:) $ opt [] $ s_tl rs

    r_tl ls = do  pr <- prim_rpr s_term
                  return [map pr ls]

s_term    = i_term
  where
    i_term  = l_term >>= i_tl
    i_tl t  = opt t $ (prim_ifn s_term `ap` return t `ap` i_term) >>= i_tl

    l_term  = r_term -|- (prim_lfn s_term `ap` l_term)

    r_term  = c_term >>= r_tl
    r_tl t  = opt t $ (prim_rfn s_term `ap` return t) >>= r_tl

    c_term  = s_var -|- expar s_term -|- prim_cfn s_term -|- set_strm

s_var     = liftM zVar var


-- Set notation

set_eqnt  = do  sets; v <- namlist; t <- set_of
                return (id, zEqu zHole t, v)

set_term  = sets >> namlist >> liftM ((,) id) set_of

set_of  = word "of" >> (u1 -|- u2 -|- u3)
  where
    u1  = notion >>= single >>= ntnset
    u2  = do t <- ft; s <- condn >> statement; trmset t s
    u3  = comma ft >>= finset
    ft  = liftM snd fo_term

set_strm  = exbrc (u1 -|- u2 -|- u3)
  where
    u1  = do  (q, f, v) <- notion >>= single
              s <- opt Top (char '|' >> statement)
              ntnset (q, bool $ And f s, v)
    u2  = do t <- ft; s <- (char '|' >> statement); trmset t s
    u3  = chain (char ',') ft >>= finset
    ft  = liftM snd fo_term

ntnset (q, f, v)  = retset v $ q f

trmset t s  = do  v <- hidden ; let u = zVar v
                  vs <- liftM (`decl` s) getDecl
                  retset v $ foldr mbExi (And s $ zEqu t u) vs

finset ts   = do  v <- hidden ; let u = zVar v
                  retset v $ foldl1 Or $ map (zEqu u) ts

retset v fe = do  (_:h) <- hidden ; let u = zVar v
                  let ex = zAll v $ Iff (zElm u zHole) fe
                      nt = zSSS h $ map zVar (free [] ex)
                      nf = And (zSet nt) (substH nt ex)
                  return $ nt { trInfo = [Tag DEQ nf] }


-- Digger

dig f [_] | occursS f  = fail "too few subjects for an m-predicate"
dig f ts  = return (dive f)
  where
    dive (Tag DIG f)  = down (digS) f
    dive (Tag DMS f)  = down (digM $ zip ts $ tail ts) f
    dive (Tag DMP f)  = down (digM $ pairMP ts) f
    dive f  | isTrm f = f
    dive f  = mapF dive f

    down fn (And f g) = And (down fn f) (down fn g)
    down fn f         = foldl1 And (fn f)

    digS f  | occursH f = map (\ x -> substH x f) ts
            | otherwise = [f]

    digM ps f | not (occursS f) = digS f
              | not (occursH f) = map (\ y -> substS y f) $ tail ts
              | otherwise = map (\ (x,y) -> substS y $ substH x f) ps

    pairMP (t:ts) = [ (t, s) | s <- ts ] ++ pairMP ts
    pairMP _      = []


-- Chains

aon_chain p = (p >>= ao) -|- (word "neither" >> nr)
  where
    ao f  = liftM (foldl And f) (word "and" >> chain (word "and") p)
        -|- liftM (foldl Or  f) (word "or"  >> chain (word "or")  p)
        -|- return f
    nr    = liftM (foldl1 And . map Not) (chain (word "nor") p)

and_chain = liftM (foldl1 And) . chain (word "and")

comma = chain (word "and" -|- char ',')


-- Service stuff

has   = wordOf ["has", "have"]
with  = wordOf ["with", "of", "having"]
such  = wordOf ["such", "so"]
that  = wordOf ["that"]
sets  = wordOf ["set", "sets"]
does  = opt () $ wordOf ["does", "do"]
wehve = opt () $ word "we" >> word "have"
art   = opt () $ wordOf ["a", "an", "the"]
condn = (such >> that) -|- (word "provided" >> opt () that)
wrong = mapM_ word ["it","is","wrong","that"]
there = word "there" >> (is -|- wordOf ["exists","exist"])
iff   = mapM_ word ["if","and","only","if"] -|- word "iff"
stand = word "denote" -|- (word "stand" >> word "for")

