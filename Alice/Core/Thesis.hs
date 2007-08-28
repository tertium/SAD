module Alice.Core.Thesis (thesis) where

import Control.Monad
import Data.List
import Data.Maybe

import Alice.Core.Base
import Alice.Core.Local
import Alice.Data.Formula
import Alice.Data.Kit
import Alice.Data.Text


thesis :: [Context] -> Context -> (Bool, Context)
thesis cnt@(ct:_) tc = (nmt, setForm tc nth)
  where
    nmt = cnSign ct || isJust ith
    nth = tmWipe (tmDown $ cnForm ct) jth
    jth | cnSign ct = ths
        | otherwise = fromMaybe ths ith
    ith = tmInst cnt tc
    ths = cnForm tc


-- Reduce f in sight of hs

tmWipe hs f | any (tmComp 0 $ f) hs     = Top
            | any (tmComp 0 $ Not f) hs = Bot
            | isTrm f                   = f
            | otherwise                 = bool $ mapF (tmWipe hs) f

tmComp n f g  = cmp (albet f) (albet g)
  where
    cmp (All _ a) (All _ b) = tmComp (succ n) (inst nvr a) (inst nvr b)
    cmp (Exi _ a) (Exi _ b) = tmComp (succ n) (inst nvr a) (inst nvr b)
    cmp (And a b) (And c d) = tmComp n a c && tmComp n b d
    cmp (Or a b) (Or c d)   = tmComp n a c && tmComp n b d
    cmp (Ann _ a) b         = tmComp n a b
    cmp a (Ann _ b)         = tmComp n a b
    cmp a b                 = twins a b

    nvr = show n


-- Instantiate f with vs in sight of h

tmInst (ct:cnt) tc = find gut insts
  where
    insts = map snd $ runTM (tmPass cnt tc) $ cnDecl ct
    gut g = isTop $ tmWipe (tmFlat 0 $ Not g) $ cnForm ct

tmFlat n  = flat . albet
  where
    flat (Exi _ f) = tmFlat (succ n) (inst nvr f)
    flat (And g f) = tmDown g ++ tmFlat n f
    flat f         = [f]

    nvr = '.' : show n

tmDown = spl . albet
  where
    spl (And f g) = tmDown f ++ tmDown g
    spl (Not f) | hasInfo f = Not f : concatMap (tmDown . Not) (trInfoD f)
                              ++  concatMap tmDown (trInfoO f)
    spl f | hasInfo f       = f : concatMap tmDown (trInfoD f)
                              ++  concatMap tmDown (trInfoI f)
    spl f = [f]


-- Find possible instantiations

tmPass cnt tc = pass [] (Just True) 0 $ cnForm tc
  where
    pass fc sg n h  = dive h
      where
        dive h@(All u f)    = case sg of  Just True   -> qua u f h
                                          _           -> return h
        dive h@(Exi u f)    = case sg of  Just False  -> qua u f h
                                          _           -> return h
        dive h@(Trm _ _ is) = return h `mplus` dfs h
        dive h              = roundFM pass fc sg n h

        qua u f = mplus (tmVars u f >>= dive) . roundFM pass fc sg n
        dfs = msum . map (dive . fillInfo nct . setForm tc) . trInfoD
        nct = cnRaise cnt tc fc

tmVars u f  = TM (vrs [])
  where
    vrs ov (v:vs) | gut u v = (ov ++ vs, inst v f) : vrs (v:ov) vs
                  | True    = vrs (v:ov) vs
    vrs ov _                = []

    gut x@('x':_) y = x == y
    gut _ _         = True


-- Thesis monad

newtype TM res = TM { runTM :: [String] -> [([String], res)] }

instance Monad TM where
  return r  = TM $ \ s -> [(s, r)]
  m >>= k   = TM $ \ s -> concatMap apply (runTM m s)
    where apply (s, r) = runTM (k r) s

instance MonadPlus TM where
  mzero     = TM $ \ s -> []
  mplus m k = TM $ \ s -> runTM m s ++ runTM k s

