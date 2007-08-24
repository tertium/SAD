module Alice.Data.Context where

import Data.Maybe
import Control.Monad

import Alice.Data.Formula
import Alice.Data.Text

data Context  = Context { cnBran :: [Block], cnForm :: Formula }

cnHead  = head . cnBran
cnTail  = tail . cnBran
cnTopL  = null . cnTail
cnLowL  = not . cnTopL

cnSign  = blSign . cnHead
cnDecl  = blDecl . cnHead
cnName  = blName . cnHead
cnLink  = blLink . cnHead

cnJoin :: [Context] -> Context -> [Formula] -> [Context]
cnJoin cnt cx fs  = foldr ((:) . \ f -> cx { cnForm = f }) cnt fs


-- Logical traversing

roundF :: ([Formula] -> Maybe Bool -> Int -> Formula -> Formula)
        -> [Formula] -> Maybe Bool -> Int -> Formula -> Formula
roundF fn cn sg n  = dive
  where
    dive (All u f) =  let nf = fn cn sg (succ n) ; nn = show n
                      in  All u $ bind nn 0 $ nf $ inst nn 0 f
    dive (Exi u f) =  let nf = fn cn sg (succ n) ; nn = show n
                      in  Exi u $ bind nn 0 $ nf $ inst nn 0 f
    dive (Iff f g) =  let nf = fn cn Nothing n f
                      in  Iff nf $ fn cn Nothing n g
    dive (Imp f g) =  let nf = fn cn (liftM not sg) n f
                      in  Imp nf $ fn (nf:cn) sg n g
    dive (Or  f g) =  let nf = fn cn sg n f
                      in  Or nf $ fn (Not nf:cn) sg n g
    dive (And f g) =  let nf = fn cn sg n f
                      in  And nf $ fn (nf:cn) sg n g
    dive (Sub f g) =  let nf = fn cn Nothing n f
                      in  Sub nf $ fn (nf:cn) sg n g
    dive (Not f)   =  Not $ fn cn (liftM not sg) n f
    dive f         =  mapF (fn cn sg n) f

roundFM :: (Monad m) =>
          ([Formula] -> Maybe Bool -> Int -> Formula -> m Formula)
        -> [Formula] -> Maybe Bool -> Int -> Formula -> m Formula
roundFM fn cn sg n  = dive
  where
    dive (All u f)  = do  let nf = fn cn sg (succ n) ; nn = show n
                          liftM (All u . bind nn 0) $ nf $ inst nn 0 f
    dive (Exi u f)  = do  let nf = fn cn sg (succ n) ; nn = show n
                          liftM (Exi u . bind nn 0) $ nf $ inst nn 0 f
    dive (Iff f g)  = do  nf <- fn cn Nothing n f
                          liftM (Iff nf) $ fn cn Nothing n g
    dive (Imp f g)  = do  nf <- fn cn (liftM not sg) n f
                          liftM (Imp nf) $ fn (nf:cn) sg n g
    dive (Or  f g)  = do  nf <- fn cn sg n f
                          liftM (Or nf) $ fn (Not nf:cn) sg n g
    dive (And f g)  = do  nf <- fn cn sg n f
                          liftM (And nf) $ fn (nf:cn) sg n g
    dive (Sub f g)  = do  nf <- fn cn Nothing n f
                          liftM (Sub nf) $ fn (nf:cn) sg n g
    dive (Not f)    = liftM Not $ fn cn (liftM not sg) n f
    dive f          = mapFM (fn cn sg n) f

