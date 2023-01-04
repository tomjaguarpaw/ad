{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wall #-}

module Main where

import Control.Exception (Exception, throwIO, tryJust)
import Data.Kind (Type)
import Data.Proxy (Proxy (Proxy))
import Data.Reflection
import qualified Data.Unique
import Data.Void (Void)
import GHC.IO.Unsafe (unsafePerformIO)
import GHC.IORef (IORef, newIORef, readIORef, writeIORef)
import Unsafe.Coerce (unsafeCoerce)
import Prelude hiding (read)

newtype Eff (es :: [Type]) a = Eff {unsafeUnEff :: IO a}
  deriving stock (Functor)
  deriving newtype (Applicative, Monad)

runEff :: Eff '[] a -> a
runEff = unsafePerformIO . unsafeUnEff

newtype Error e s = Error (forall a. e -> IO a)

newtype State s e = State (IORef s)

class (e :: Type) :> (es :: [Type])

instance {-# OVERLAPPING #-} e :> (e : es)

instance e :> es => e :> (x : es)

raise :: s :> ss => Error e s -> e -> Eff ss a
raise (Error throw) e = Eff (throw e)

handleError ::
  (forall s. Error e s -> Eff (s : ss) a) ->
  Eff ss (Either e a)
handleError f =
  Eff $ withScopedException_ (\throw -> unsafeUnEff (f (Error throw)))

read :: e :> es => State s e -> Eff es s
read (State r) = Eff (readIORef r)

write :: e :> es => State s e -> s -> Eff es ()
write (State r) s = Eff (writeIORef r s)

modify :: (e :> es) => State t e -> (t -> t) -> Eff es ()
modify state f = do
  s <- read state
  write state (f s)

handleState ::
  forall a s es.
  s ->
  (forall e. State s e -> Eff (e : es) a) ->
  Eff es (a, s)
handleState s f = Eff $ do
  r <- newIORef s
  let state = State r :: State s ()

  unsafeUnEff $ do
    a <- f state
    s' <- read state
    pure (a, s')

main :: IO ()
main = putStrLn "Hello, Haskell!"

example :: s :> ss => Error String s -> Eff ss a
example = (\e -> raise e "My error")

example2 :: Eff ss (Either String a)
example2 = handleError example

example3 :: Either String a
example3 = runEff example2

example4 :: Error String s -> Eff ss (Error String s)
example4 = pure

-- Couldn't match type ‘a’ with ‘Error String s’ because type variable
-- ‘s’ would escape its scope
-- exampleDoesn'tWork = handleError example4

example5 :: (e :> es, s :> es) => Error String s -> State Int e -> Eff es ()
example5 e s = do
  foo <- read s
  modify s (+ 1)
  _ <- raise e ("Hello " ++ show foo)
  modify s (+ 1)

example6 :: e' :> es => Error String e' -> Eff es ((), Int)
example6 = \e -> handleState 10 (example5 e)

example6a :: st :> es => State Int st -> Eff es (Either String ())
example6a = \s -> handleError (\e -> example5 e s)

example7 :: Eff es (Either String ((), Int))
example7 = handleError example6

example7a :: Eff es (Either String (), Int)
example7a = handleState 10 example6a

data TypeLevel s a

data TypeLevel' s

class Has t s | s -> t where
  have :: forall s'. t s'

data Forall f where
  Forall :: {unForall :: forall a. f a} -> Forall f

instance Reifies s (Forall t) => Has t (TypeLevel' s) where
  have = unForall (reflect @s Proxy)

type HasError e s = Has (Error e) s

type HasState s = Has (State s)

raiseE :: forall s e ss a. (HasError e s, s :> ss) => e -> Eff ss a
raiseE = raise (have @(Error e) @s @s)

readS :: forall s e ss. s :> ss => HasState e s => Eff ss e
readS = read (have @(State e) @s @s)

writeS :: forall s e ss. (HasState e s, s :> ss) => e -> Eff ss ()
writeS = write (have @(State e) @s @s)

modifyS :: forall e s ss. (HasState s e, e :> ss) => (s -> s) -> Eff ss ()
modifyS f = do
  s <- readS @e
  writeS @e (f s)

exampleS5 ::
  forall ex st ss.
  (st :> ss, ex :> ss, HasError String ex, HasState Int st) =>
  Eff ss ()
exampleS5 = do
  foo <- readS @st
  modifyS @st (+ 1)
  _ <- raiseE @ex ("Hello " ++ show foo)
  modifyS @st (+ 1)

handleErrorE ::
  forall e ss a.
  (forall s. HasError e s => Proxy s -> Eff (s : ss) a) ->
  Eff ss (Either e a)
handleErrorE f =
  handleError
    ( \(e :: Error e s') ->
        reify @(Forall (Error e))
          (forallError e)
          ( \(_ :: Proxy s) ->
              coerceEff (f @(TypeLevel' s) (Proxy @_))
          )
    )
  where
    coerceEff = Eff . unsafeUnEff
    forallError e = Forall (let Error t = e in Error t)

handleStateS ::
  forall st a es.
  st ->
  (forall e. HasState st e => Proxy e -> Eff (e : es) a) ->
  Eff es (a, st)
handleStateS st f =
  handleState
    st
    ( \(s :: State st e) ->
        reify @(Forall (State st))
          (forallState s)
          ( \(_ :: Proxy s) ->
              coerceEff (f @(TypeLevel' s) (Proxy @_))
          )
    )
  where
    coerceEff = Eff . unsafeUnEff
    forallState e = Forall (let State t = e in State t)

example6S :: forall st ss. (HasState Int st, st :> ss) => Eff ss (Either String ())
example6S = handleErrorE (\(Proxy :: Proxy ex) -> exampleS5 @ex @st)

example7S :: Eff ss (Either String (), Int)
example7S = handleStateS 10 (\(Proxy :: Proxy st) -> example6S @st)

-- withScopedException :: ((forall a. e -> IO a) -> IO r) -> IO (Either e r)

scopedExceptionExample :: IO (Either String (Either Int Void))
scopedExceptionExample = do
  withScopedException_ $ \throw1 ->
    withScopedException_ $ \throw2 ->
      if (1 :: Int) < 0
        then throw1 "Hello"
        else throw2 1234

-- ghci> scopedExceptionExample
-- Left "Hello"

data MyException where
  MyException :: e -> Data.Unique.Unique -> MyException

instance Show MyException where
  show _ = "<MyException>"

instance Exception MyException

withScopedException_ :: ((forall a. e -> IO a) -> IO r) -> IO (Either e r)
withScopedException_ f = do
  fresh <- Data.Unique.newUnique

  flip tryJust (f (\e -> throwIO (MyException e fresh))) $ \case
    MyException e tag ->
      -- unsafeCoerce is very unpleasant
      if tag == fresh then Just (unsafeCoerce e) else Nothing

data PromptTag a = PromptTag

newPromptTag :: IO (PromptTag a)
newPromptTag = undefined

prompt :: PromptTag a -> IO a -> IO a
prompt = undefined

control0 :: PromptTag a -> ((IO b -> IO a) -> IO a) -> IO b
control0 = undefined

withScopedExceptionBad :: ((e -> IO (Either e r)) -> IO r) -> IO (Either e r)
withScopedExceptionBad body = do
  promptTag <- newPromptTag
  prompt promptTag $ do
    l <- control0 promptTag $ \myThrow -> do
      r <- body (myThrow . pure)
      pure (Right r)
    pure (Left l)

withScopedException :: ((forall a. e -> IO a) -> IO r) -> IO (Either e r)
withScopedException body = do
  promptTag <- newPromptTag
  prompt promptTag $ do
    r <- body (\e -> control0 promptTag (\_ -> pure (Left e)))
    pure (Right r)
