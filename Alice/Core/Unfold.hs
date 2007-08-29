module Alice.Core.Unfold (unfold) where

import Control.Monad
import Data.Maybe

import Alice.Data.Formula
import Alice.Data.Instr
import Alice.Data.Kit
import Alice.Data.Text
import Alice.Core.Base
import Alice.Core.Info

-- Definition expansion

unfold :: [Context] -> RM [Context]
unfold tsk  = do  when (null exs) $ ntu >> mzero
                  unf ; addRSCI CIunfl $ length exs
                  return $ foldr exp [] mts
  where
    mts = markup tsk
    exs = concatMap marked mts

    exp c cnt = setForm c (unfoldF cnt c) : cnt

    ntu = whenIB IBPunf False $ rlog0 $ "nothing to unfold"
    unf = whenIB IBPunf False $ rlog0 $ "unfold: " ++ out
    out = foldr (. showChar ' ') "" exs

unfoldF cnt cx = fill [] (Just True) 0 (cnForm cx)
  where
    fill fc sg n f | isTrm f  = unfoldA (fromJust sg) f
    fill fc sg n (Iff f g)    = roundF fill fc sg n (zIff f g)
    fill fc sg n f            = roundF fill fc sg n f

unfoldA sg fr = nfr
  where
    nfr = foldr (if sg then And else Imp) nbs (expS fr)
    nbs = foldr (if sg then And else Or ) wip (expA fr)
    wip = wipeDCN fr

    expS h  = foldF expT $ nullInfo h
    expT h  = expS h ++ expA h
    expA h  = getDCN h


-- Trivial markup

markup tsk  = map mrk loc ++ glb
  where
    (loc, glb) = break cnTopL tsk

    mrk c = c {cnForm = tot $ cnForm c}
    tot f | isTrm f   = skipInfo (mapF tot) $ markDCN f
          | otherwise = skipInfo (mapF tot) f

markDCN f = f { trInfo = map mrk (trInfo f) }
  where
    mrk (Tag DEQ f) = Tag DCN f   -- DEQ lost!!!
    mrk (Tag DSD f) = Tag DCN f   -- DEQ lost!!!
    mrk f           = f

wipeDCN (Tag DCN _) = Top
wipeDCN f@(Tag DIM _) = f
wipeDCN f@(Tag DOR _) = f
wipeDCN f@(Tag DEQ _) = f
wipeDCN f@(Tag DSD _) = f
wipeDCN f = mapF wipeDCN f


-- Service stuff

marked cx = mrk 0 $ cnForm cx
  where
    mrk n (All _ f)     = mrk (succ n) f
    mrk n (Exi _ f)     = mrk (succ n) f
    mrk n f | isDCN f   = showParen True (showFormula 3 n f . lin)
                        : foldF (mrk n) (nullInfo f)
            | otherwise = foldF (mrk n) (nullInfo f)

    lin = showChar ',' . shows (blLine $ cnHead cx)

isDCN     = not . null . getDCN

getDCN f  | hasInfo f = trInfoC f
          | otherwise = []

