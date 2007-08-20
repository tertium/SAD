module Alice.Parser.Trans where

import Control.Monad
import Data.List

import Alice.Parser.Base

-- Monad transformer class

class MonadTrans t where
  lift :: Monad m => m a -> t m a


-- Reader monad transformer

newtype ReaderT s m a = ReaderT { runReaderT :: s -> m a }

instance MonadTrans (ReaderT s) where
  lift  = ReaderT . const

instance Monad m => Monad (ReaderT s m) where
  fail    = lift . fail
  return  = lift . return
  m >>= k = ReaderT $ \ s ->  do  r <- runReaderT m s
                                  runReaderT (k r) s

instance MonadPlus m => MonadPlus (ReaderT s m) where
  mzero = lift mzero
  mplus m k = ReaderT $ \ s -> mplus (runReaderT m s) (runReaderT k s)

instance MonadPS m => MonadPS (ReaderT s m) where
  getPS     = lift getPS
  setPS     = lift . setPS
  updatePS  = lift . updatePS

instance MonadLazy m => MonadLazy (ReaderT s m) where
  mtry m k  = ReaderT $ \ s -> mtry (runReaderT m s) (runReaderT k s)
  mtie m k  = let nk s rs r = runReaderT (k rs r) s
              in  ReaderT $ \ s -> mtie (runReaderT m s) (nk s)

netS :: Monad m => ReaderT s m s
netS  = ReaderT $ return

askS :: Monad m => (s -> a) -> ReaderT s m a
askS  = ReaderT . (return .)


-- State monad transformer

newtype StateT s m a = StateT { runStateT :: s -> m (a, s) }

instance MonadTrans (StateT s) where
  lift m  = StateT $ \ s -> m >>= \ r -> return (r, s)

instance Monad m => Monad (StateT s m) where
  fail    = lift . fail
  return  = lift . return
  m >>= k = StateT $ \ s -> do  (r,t) <- runStateT m s
                                runStateT (k r) t

instance MonadPlus m => MonadPlus (StateT s m) where
  mzero = lift mzero
  mplus m k = StateT $ \ s -> mplus (runStateT m s) (runStateT k s)

instance MonadPS m => MonadPS (StateT s m) where
  getPS     = lift getPS
  setPS     = lift . setPS
  updatePS  = lift . updatePS

instance MonadLazy m => MonadLazy (StateT s m) where
  mtry m k  = StateT $ \ s -> mtry (runStateT m s) (runStateT k s)
  mtie m k  = let nk rs (r,t) = runStateT (k (map fst rs) r) t
              in  StateT $ \ s -> mtie (runStateT m s) nk

getS :: Monad m => StateT s m s
getS  = StateT $ \ s -> return (s, s)

setS :: Monad m => s -> StateT s m ()
setS s  = StateT $ \ _ -> return ((), s)


-- Monad conversion

ssrtm :: (Monad m) => (s -> t) -> ReaderT t m a -> ReaderT s m a
ssrtm f m = netS >>= lift . runReaderT m . f

rtrtm :: (Monad m, Monad n) => (m a -> n a) -> ReaderT s m a -> ReaderT s n a
rtrtm f m = netS >>= lift . f . runReaderT m

rtstm :: (Monad m, Monad n) => (m a -> n a) -> ReaderT s m a -> StateT s n a
rtstm f m = getS >>= lift . f . runReaderT m

ststm :: (Monad m, Monad n) => (m (a,s) -> n (a,s)) -> StateT s m a -> StateT s n a
ststm f m = getS >>= lift . f . runStateT m >>= \ (r,s) -> setS s >> return r

