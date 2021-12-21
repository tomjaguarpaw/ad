{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

module Main where
import Data.Proxy
import Data.Monoid
import Data.Reflection
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Class (lift, MonadTrans)

-- show
-- Values of type 'a' in our dynamically constructed 'Ord' instance
newtype O a s  = O { runO :: a }

pO :: proxy s -> a -> O a s
pO _ = O

-- A dictionary describing an 'Ord' instance.
newtype Ord_ a = Ord_ { compare_ :: a -> a -> Ordering }

-- Utility
isEq :: Ordering -> Bool
isEq EQ = True
isEq _  = False

instance Reifies s (Ord_ a) => Eq (O a s) where
  a == b = isEq (compare_ (reflect a) (runO a) (runO b))

instance (Eq (O a s), Reifies s (Ord_ a)) => Ord (O a s) where
  compare a b = compare_ (reflect a) (runO a) (runO b)

-- Dynamically construct an 'Ord' instance out of a comparsion operator.
withOrd :: (a -> a -> Ordering)
        -> (forall s. Reifies s (Ord_ a)
             => (a -> O a s)
             -> (O a s -> a)
             -> r)
        -> r
withOrd f v = reify (Ord_ f) (asTypeOf v)
  where asTypeOf :: (((a -> O a s) -> (O a s -> a) -> t) -> proxy s -> t)
        asTypeOf v _ = v O runO

-- Regular ord instance
example1 :: Bool
example1 = withOrd (compare :: Int -> Int -> Ordering) (\p _ -> p 1 > p 2)

-- Backwards ord instance
example2 :: Int
example2 = withOrd (flip compare) $ \p unP -> unP $ max (p 1) (p 2)

main1 :: IO ()
main1 = print example1 >> print example2
-- /show


data IntState (t :: (* -> *) -> * -> *) (m :: * -> *) = IntState
  { get :: t m Int
  , set :: Int -> t m ()
  }

newtype StringWriter (t :: (* -> *) -> * -> *) (m :: * -> *) = StringWriter
  { write :: String -> t m ()
  }

class THoistable (f :: ((* -> *) -> * -> *) -> (* -> *) -> *) where
  tHoist :: (forall m a. t m a -> t' m a)
         -> f t m
         -> f t' m

instance THoistable IntState where
  tHoist f is = IntState { get = f (get is), set = f . set is }

instance THoistable StringWriter where
  tHoist f sr = StringWriter { write = f . write sr }

intState :: (Monad (t IO), MonadTrans t) => IntState t IO
intState = IntState { get = lift (putStrLn "Getting") >> pure 666, set = lift . print }

stringWriter :: MonadTrans t => StringWriter t IO
stringWriter = StringWriter { write = lift . putStrLn . ("Writing: " ++) }

class Has f (t :: (* -> *) -> * -> *) (m :: * -> *) where
  have :: f t m

instance Has StringWriter t IO => Has StringWriter (T IntState s t) IO where
  have = tHoist T have

instance MonadTrans t => MonadTrans (T k s t) where
  lift x = T (lift x)

foo :: (Monad (t m), Has IntState t m, Has StringWriter t m) => t m ()
foo = do
  i <- get have
  write have ("I got " ++ show i)
  if i < 0
    then set have 1000
    else set have (i + 1)

newtype T (k :: ((* -> *) -> * -> *) -> (* -> *) -> *) s (t :: (* -> *) -> * -> *) (m :: * -> *) a = T { unT :: t m a }

instance Functor (t m) => Functor (T k s t m) where
  fmap f (T t) = T (fmap f t)

instance Applicative (t m) => Applicative (T k s t m) where
  pure a = T (pure a)
  T f <*> T x = T (f <*> x)

instance Monad (t m) => Monad (T k s t m) where
  return = pure
  T m >>= f = T (m >>= \x -> case f x of T t -> t)

instance forall s t m f. (THoistable f, Reifies s (f t m)) => Has f (T f s t) m where
  have = tHoist T (reflect (Nothing :: Maybe s))

handle :: f t m
       -> (forall s. Reifies s (f t m) => (T f s t m a -> t m a) -> r)
       -> r
handle is v = reify is (asTypeOf v)
  where asTypeOf :: (((T k s t1 m1 a1 -> t1 m1 a1) -> t2) -> proxy s -> t2)
        asTypeOf v _ = v (\(T t) -> t)

handleT :: f t m
        -> (forall s. Reifies s (f t m) => T f s t m a)
        -> t m a
handleT is t = handle is ($ t)

baz :: (MonadTrans t, Has StringWriter t IO, Monad (t IO)) => t IO ()
baz = handleT intState foo

bar :: (MonadTrans t, Monad (t IO)) => t IO ()
bar = handleT stringWriter baz

main :: IO ()
main = runIdentityT bar
