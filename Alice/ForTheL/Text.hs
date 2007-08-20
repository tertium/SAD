module Alice.ForTheL.Text (forthel) where

import Control.Monad
import Data.Char
import Data.List
import Data.Maybe

import Alice.Data.Formula
import Alice.Data.Text
import Alice.ForTheL.Base
import Alice.ForTheL.Intro
import Alice.ForTheL.Phrase
import Alice.Parser.Base
import Alice.Parser.Prim
import Alice.Parser.Instr
import Alice.Parser.Trans

-- Top-level grammar

forthel = u1 -/- u2 -/- u3 -/- u5 -/- u6 -/- u7 -/- u8 -/- u4
  where
    u1  = liftM2 ((:).TB) topsent forthel
    u2  = liftM2 ((:).TB) (defsect -/- sigsect) forthel
    u3  = liftM2 ((:).TB) (axmsect -/- thmsect) forthel
    u4  = (alias -/- itvar -/- isyms) >> forthel
    u5  = (iexit -/- readEOI) >> return []
    u6  = liftM2 ((:).TI) iread (return [])
    u7  = liftM2 ((:).TI) instr forthel
    u8  = liftM2 ((:).TD) idrop forthel

axmsect = topsect False axm axmaff
defsect = topsect False def define >>= extPrim
sigsect = topsect False sig sigext >>= extPrim
thmsect = topsect True  thm (proof affirm)

topsect s h p = doLFTL $
    do  li <- nulText ; nm <- h
        tx <- getText ; bs <- tps
        la <- askPS psLang ; fn <- askPS psFile
        return $ Block zHole bs s [] nm [] la fn li tx
  where
    tps = u1 -/- u2 -/- u3 -/- u4
    u1  = assume >>= pretvr tps
    u2  = liftM2 ((:).TI) instr tps
    u3  = liftM2 ((:).TD) idrop tps
    u4  = p >>= pretvr (return [])

topsent = doLFTL $
    do  li <- nulText ; bs@(TB bl:rs) <- pra
        la <- askPS psLang ; fn <- askPS psFile
        return $ if null rs then bl { blName = "" }
          else Block zHole bs True [] "" [] la fn li ""
  where pra = proof affirm >>= pretvr (return [])


-- Affirmations and selections with(out) a proof

data Scheme = Nul | Sht | Raw | InS | InT Formula deriving Show

proof p = do  m1 <- shw; bl <- p
              let fr = blForm bl
              m2 <- prf; dvs <- getDecl
              it <- imth m1 m2 >>= itrm fr
              let ovs = free (blDecl bl ++ dvs) fr
              nf <- iths fr it $ free (ovs ++ dvs) it
              addDecl ovs $ body m1 m2 $ bl { blForm = nf }
  where
    body Nul Nul = return
    body _   Sht = prfsent
    body _   _   = prfsect

    imth (InT _) (InT _) = fail "conflicting induction schemes"
    imth m@(InT _) _  = return m ; imth _ m@(InT _)  = return m
    imth m@InS _      = return m ; imth _ m          = return m

    itrm _      (InT t) = return t
    itrm (All v _) InS  = return $ zVar v
    itrm _         InS  = fail "invalid induction thesis"
    itrm _ _            = return Top

    iths fr Top _       = return fr
    iths fr it vs       = liftM (iapp it) $ icnt vs fr
    iapp it cn          = cn $ Ann DIH $ substH it $ cn $ zLess it zHole

    icnt vs (Imp g f)   = liftM (Imp g .) $ icnt vs f
    icnt vs (All v f)   = liftM (zAll v .) $ icnt (delete v vs) f
    icnt [] f           = return (`Imp` f)
    icnt _ _            = fail "invalid induction thesis"


-- Proof schemes

shw = narrow $ optEx Nul $ letus >> dem >> after met that
prf = narrow $ optEx Nul $ sht -|- (word "proof" >> dot met)

sht = word "indeed" >> return Sht

met = opt Raw $ word "by" >> (u1 -|- u2 -|- u3)
  where
    u1  = word "contradiction" >> return Raw
    u2  = word "case" >> word "analysis" >> return Raw
    u3  = word "induction" >> opt InS (word "on" >> on)
    on  = liftM (InT . snd) fo_term


-- Low-level sections: proofs, proof cases and frames

prfsent bl  = do  lb <- lowsent ; return bl { blBody = [TB lb] }

prfsect bl  = do  bs <- lowtext ; ls <- link
                  return bl { blBody = bs, blLink = blLink bl ++ ls }

lowtext = u1 -/- u2 -/- u3 -/- u4 -/- u5 -/- u6
  where
    u1  = lowsent >>= pretvr lowtext
    u2  = liftM2 ((:).TB) frame lowtext
    u3  = liftM2 ((:).TI) instr lowtext
    u4  = liftM2 ((:).TD) idrop lowtext
    u5  = qed >> return []
    u6  = castext

lowsent = assume -/- proof (affirm -/- choose)

castext = u1
  where
    rst = u1 -/- u2 -/- u3 -/- u4
    u1  = liftM2 ((:).TB) cassect rst
    u2  = liftM2 ((:).TI) instr rst
    u3  = liftM2 ((:).TD) idrop rst
    u4  = qed >> return []

cassect = do  bl@(Block { blForm = fr }) <- cashyp
              prfsect $ bl { blForm = Imp (Ann DCH fr) zThesis }

frame   = do  li <- nulText ; nm <- frm
              tx <- getText ; bs <- dot lowtext
              la <- askPS psLang ; fn <- askPS psFile
              return $ Block zHole bs True [] nm [] la fn li tx


-- Sentences

choose  = sentence True  (chs >> selection) asmvars link
cashyp  = sentence True  (cas >> statement) rawvars link
affirm  = sentence True  (aff >> statement) affvars link
axmaff  = sentence True  (aff >> statement) affvars noln
assume  = sentence False (asm >> statement) asmvars noln
define  = sentence True definition defvars noln
sigext  = sentence True signaturex defvars noln

sentence s pf pvars pl = narrow $
    do  li <- nulText ; fr <- pf ; ls <- pl
        tx <- getText ; vs <- getDecl >>= pvars fr
        la <- askPS psLang ; fn <- askPS psFile
        return $ Block fr [] s vs "__" ls la fn li tx

defvars f dvs | null xvs  = affvars f dvs
              | otherwise = nextfail err
  where
    xvs = filter (`notElem` free [] f) dvs
    err = "extra variables in the guard:" ++ sbs
    sbs = concatMap ((' ':) . show) xvs

asmvars f dvs = do  let nds = decl dvs f
                    affvars f $ nds ++ dvs
                    return nds

affvars f dvs = do  tvs <- askS $ concatMap fst . tvr_expr
                    let nvs = intersect tvs $ free dvs f
                    rawvars f $ dvs ++ nvs

rawvars f dvs = let wfc = overfree dvs f
                in  if null wfc then return [] else fail wfc


pretvr p bl = do  dvs <- getDecl; tvs <- askS tvr_expr
                  let bvs = blDecl bl
                      ovs = free (bvs ++ dvs) (blForm bl)
                      ofr = foldl1 And $ map (`gdc` tvs) ovs
                      obl = zbl { blForm = ofr, blDecl = ovs }
                  rst <- addDecl (ovs ++ bvs) $ liftM (TB bl :) p
                  return $ if (null ovs) then rst else TB obl : rst
  where
    gdc v = substH (zVar v) . snd . fromJust . find (elem v . fst)
    zbl   = bl { blBody = [], blSign = False, blLink = [] }


-- Service stuff

noln  = dot $ return []
link  = dot $ opt [] $ expar $ word "by" >> chain (char ',') readTkLex
hdr p = dot $ p >> opt "" readTkLex

axm = hdr $ word "axiom"
def = hdr $ word "definition"
sig = hdr $ word "signature"
thm = hdr $ wordOf ["theorem", "lemma", "corollary", "proposition"]
frm = hdr $ wordOf ["part", "block", "frame"]

dem = wordOf ["prove", "show", "demonstrate"]
qed = wordOf ["end", "qed", "trivial", "obvious"]

cas = word "case"
asm = word "let" -|- lus
lus = letus >> wordOf ["assume", "presume", "suppose"] >> opt () that
chs = hence >> letus >> wordOf ["choose", "take", "consider"]
aff = hence

letus  = opt () $ (word "let" >> word "us") -|- (word "we" >> word "can")
hence  = opt () $ wordOf ["then", "hence", "thus", "therefore"]

