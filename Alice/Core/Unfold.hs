module Alice.Core.Unfold (unfold) where

import Control.Monad
import Data.Maybe

import Alice.Data.Context
import Alice.Data.Formula
import Alice.Data.Instr
import Alice.Data.Kit
import Alice.Data.Text
import Alice.Core.Base
--import Alice.Core.Local

-- Definition expansion

unfold :: [Context] -> RM [Context]
unfold tsk  = do  when (null exs) $ ntu >> mzero
                  unf ; addRSCI CIunfl $ length exs
                  return $ foldr exp [] mts
  where
    mts = markup tsk
    exs = concatMap (markedF . cnForm) mts

    exp c cnt = c {cnForm = unfoldF cnt c (cnForm c)} : cnt

    ntu = whenIB IBunfl False $ rlog0 $ "nothing to unfold"
    unf = whenIB IBunfl False $ rlog0 $ "unfold: " ++ out
    out = concatMap (flip (showsPrec 3) " ") exs

unfoldF cnt cx f = fill [] (Just True) 0 f
  where
    fill fc sg n f | isTrm f  = let nct = cnJoin cnt cx fc
                                in  unfoldA nct (fromJust sg) f
    fill fc sg n (Iff f g)    = roundF fill fc sg n (zIff f g)
    fill fc sg n f            = roundF fill fc sg n f

unfoldA cnt s f = {- reduce $ fillDLV cnt -} nfr
  where
    nfr = foldr (if s then And else Imp) nbs (expS f)
    nbs = foldr (if s then And else Or ) wip (expA f)
    wip = wipeDCN f

    expS h  = foldF expT $ nullInfo h
    expT h  = expS h ++ expA h
    expA h  = getDCN h


-- Trivial markup

markup tsk  = map mrk loc ++ glb
  where
    (loc, glb) = span (not . cnIsTL) tsk

    mrk c = c {cnForm = tot $ cnForm c}
    tot f | isTrm f   = skipInfo (mapF tot) $ markDCN f
          | otherwise = skipInfo (mapF tot) f

markDCN f = f { trInfo = map mrk (trInfo f) }
  where
    mrk (Ann DEQ f) = Ann DCN f   -- DEQ lost!!!
    mrk f           = f

wipeDCN (Ann DCN _) = Top
wipeDCN f@(Ann DIM _) = f
wipeDCN f@(Ann DOR _) = f
wipeDCN f@(Ann DEQ _) = f
wipeDCN f = mapF wipeDCN f


-- Service stuff

markedF f | isDCN f   = f : foldF markedF (nullInfo f)
          | otherwise =     foldF markedF (nullInfo f)

isDCN     = not . null . getDCN

getDCN f  | hasInfo f = trInfoC f
          | otherwise = []

