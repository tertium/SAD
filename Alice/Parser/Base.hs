module Alice.Parser.Base where

import Control.Monad
import Data.List

import Alice.Parser.Token

-- Parser state

data PState = PState  { psOffs, psLine :: Int,
                        psRest, psDone :: [Token],
                        psFile, psLang :: String }

initPS :: PState
initPS  = PState 0 1 [] [] "" ""

type PRes a = (a, PState)
type PErr   = (String, PState)
type LPMR a = ([PRes a], [PErr])

resadd :: LPMR a -> LPMR a -> LPMR a
resadd (as, ea) (bs, eb) = (as ++ bs, ea ++ eb)

maxerr :: PErr -> PErr -> PErr
maxerr e@(_, pe) d@(_, pd)
  | psOffs pe < psOffs pd = d
  | otherwise             = e

strerr :: [PErr] -> String
strerr es = lang ++ file ++ line ++ e ++ text
  where
    (e, PState _ l _ d f p) = foldr maxerr ie es
    lang  = '[' : p ++ "] " ; ie = ("", initPS)
    file  = if null f then "line " else f ++ ":"
    line  = show (foldr lofs l d) ++ ": "
    text  = if null d then "" else "\n in text: "
                    ++ concatMap show (reverse d)
    lofs (TkSpc n) l = l - n ; lofs _ l = l


-- Parser state monad class

class Monad m => MonadPS m where
  getPS :: m PState
  getPS = updatePS id

  setPS :: PState -> m ()
  setPS ps  = updatePS (const ps) >> return ()

  updatePS :: (PState -> PState) -> m PState
  updatePS fn = do  ps <- getPS
                    setPS (fn ps)
                    return ps

askPS :: MonadPS m => (PState -> a) -> m a
askPS fn = getPS >>= return . fn

getText :: MonadPS m => m String
getText = askPS psDone >>= return . concatMap show . reverse

nulText :: MonadPS m => m Int
nulText = liftM psLine $ updatePS (\ ps -> ps { psDone = [] })

nextfail :: MonadPS m => String -> m a
nextfail e  = let nxof ps = ps { psOffs = succ (psOffs ps) }
              in  updatePS nxof >> fail e


-- Lazy parser monad class

class MonadPlus m => MonadLazy m where
  mtry :: m a -> m a -> m a
  mtie :: m a -> ([a] -> a -> m b) -> m b


-- List parser monad

newtype LPM a = LPM { runLPM :: PState -> LPMR a }

instance Monad LPM where
  fail e    = LPM $ \ p -> ([], [(e, p)])
  return r  = LPM $ \ p -> ([(r, p)], [])

  m >>= k   = LPM $ after . runLPM m
    where
      after (rs, e) = foldl app ([], e) rs
      app l (r, q)  = resadd (runLPM (k r) q) l

instance MonadPlus LPM where
  mzero     = LPM $ \ p -> ([], [])
  mplus m k = LPM $ \ p -> resadd (runLPM m p) (runLPM k p)

instance MonadLazy LPM where
  mtry m k  = LPM $ \ p -> case runLPM m p of
                ([], e) -> case runLPM k p of
                  (rs, d) -> (rs, e ++ d)
                r -> r

  mtie m k  = LPM $ after . runLPM m
    where
      after (rs, e)   = foldl (app $ map fst rs) ([], e) rs
      app rs l (r, q) = resadd (runLPM (k rs r) q) l

instance MonadPS LPM where
  getPS   = LPM $ \ p -> ([(p, p)], [])
  setPS p = LPM $ \ _ -> ([((), p)], [])
  updatePS fn = LPM $ \ p ->
        let np = fn p in ([(p, np)], [])

{-
doLPM :: (MonadPS n) => LPM a -> n a
doLPM m = do  p <- getPS ; case runLPM m p of
                ((r, q):_, _) ->  setPS q >> return r
                (_, (e, q))   ->  setPS q >> fail e


-- Either parser monad

newtype EPM a = EPM { runEPM :: PState -> Either PErr (PRes a) }

instance Monad EPM where
  m >>= k   = EPM $ either Left (uncurry $ runEPM . k) . runEPM m
  return r  = EPM $ Right . (,) r
  fail e    = EPM $ Left . (,) e

instance MonadPlus EPM where
  mzero     = fail ""
  mplus m k = EPM $ \ p -> case runEPM m p of
                Left e  -> case runEPM k p of
                  Left d  -> Left $ maxerr e d
                  r -> r
                r -> r

instance MonadPS EPM where
  getPS   = EPM $ \ p -> Right (p, p)
  setPS p = EPM $ \ _ -> Right ((), p)
  updatePS fn = EPM $ \ p -> Right (p, fn p)

doEPM :: (MonadPS n) => EPM a -> n a
doEPM m = do  p <- getPS ; case runEPM m p of
                Right (r, q)  ->  setPS q >> return r
                Left (e, q)   ->  setPS q >> fail e
-}
