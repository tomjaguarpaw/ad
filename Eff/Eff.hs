{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE KindSignatures   #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Main where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Morph
import           Control.Monad.Trans.Writer
import           Control.Monad.Trans.Reader
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.State
import           Control.Monad.Trans.Free
import           Control.Monad.Trans.Identity
import           Control.Exception

-- In this example we work in the category of monad morphisms.  They
-- are rank-2 maps between type constructors.  (They are supposed to
-- preserve the monad operations, but we can't check that in the type
-- system.)

-- See https://www.reddit.com/r/haskell/comments/cury0b/monad_transformer_optics/

type a ~> b = forall r . a r -> b r

-- It turns out that using the functions that commute monad
-- transformers past each other (see [Commutors] below) we can define
-- functions that look a lot like van Laarhoven optics, just at a
-- higher rank.

lensIdentity
  :: (MFunctor t, Monad a, Monad b)
  => LensLike t (IdentityT a) (IdentityT b) a b
lensIdentity f = commuteIdentityT . hoist f

unlensIdentity
  :: (MFunctor t, Monad a, Monad b)
  => LensLike t a b (IdentityT a) (IdentityT b)
unlensIdentity f = hoist runIdentityT . f . IdentityT

-- `MonadTrans` is like `Pointed` so this is akin to an affine traversal
--
-- https://wiki.haskell.org/Why_not_Pointed%3F
--
-- https://www.reddit.com/r/haskell/comments/60fha5/affine_traversal/df6830k/
affineState
  :: (MonadTrans t, MFunctor t, Monad (t (StateT s b)), Monad b)
  => LensLike t (StateT s a) (StateT s b) a b
affineState f s = commuteStateT (hoistState f s)

-- Affine traversals will exist for WriterT, ReaderT, ExceptT, MaybeT
-- and FreeT, because their commutors all have that MonadTrans
-- constraint.

transformed
  :: (Monad a, MFunctor t)
  => ASetter (t a) (t b) a b
transformed f = IdentityT . hoist (runIdentityT . f)

-- A worse way of doing transformed because it picks up an extra
-- constraint.
transformed'
  :: (Monad a, Monad b, MFunctor t)
  => ASetter (t a) (t b) a b
transformed' f = uncommuteIdentityT . hoist f

-- In fact we can literally just crib some of the definitions from
-- lens.

type LensLike f s (t :: * -> *) a b = (a ~> f b) -> (s ~> f t)

type ASetter s t a b = (a ~> IdentityT b) -> (s ~> IdentityT t)

-- In lens:
--
--     over l f = runIdentity #. l (Identity #. f)
--
-- which is almost identical!
over :: ASetter s t a b -> (a ~> b) -> (s ~> t)
over l f = runIdentityT . l (IdentityT . f)

-- In lens:
--
--     traverseOf = id
--
-- We can't eta-reduce all the way because of the higher rank type in
-- LensLike
traverseOf :: LensLike f s t a b -> (a ~> f b) -> (s ~> f t)
traverseOf l = l

sequenceOf :: LensLike f s t (f b) b -> (s ~> f t)
sequenceOf l = l id

-- Squash the StateT next to the b, pulling the f outsite
squashState :: (Monad b, Monad n, MFunctor f, MonadTrans f,
                Monad (f (StateT s b)))
            => (StateT s b ~> n) -> (StateT s (f b) ~> f n)
squashState f = over transformed f . sequenceOf affineState

commuteStateViaLens :: (MonadTrans t, MFunctor t,
                        Monad (t (StateT s m)), Monad m)
                    => StateT s (t m) r -> t (StateT s m) r
commuteStateViaLens = squashState id

-- I can't imagine that we can write `set` or `view` although I
-- haven't looked in detail into why not.


overTransformed :: (MFunctor t, Monad a) => (a ~> b) -> (t a ~> t b)
overTransformed = over transformed

hoist' :: (MFunctor t, Monad a) => (a ~> b) -> (t a ~> t b)
hoist' = hoist

-- THE END

-- It feels like there should be much more to say about this.  If you
-- have anything to say then please contact me:
--
--    http://web.jaguarpaw.co.uk/~tom/contact


-- [Applicatives]

class MApplicative t where
  liftMA2 :: (forall x. a x -> b x -> c x) -> t a x -> t b x -> t c x

instance MApplicative (ExceptT e) where
  liftMA2 f eax ebx = ExceptT (f (runExceptT eax) (runExceptT ebx))

-- [Lifts]

liftState :: Functor m => m ~> StateT s m
liftState m = StateT $ \ s -> flip fmap m $ \a -> (a, s)

-- [Hoists]

type Hoist t = forall m n a. (m ~> n) -> t m a -> t n a

hoistExcept :: Hoist (ExceptT e)
hoistExcept f = ExceptT . f . runExceptT

hoistMaybe :: Hoist MaybeT
hoistMaybe nat = MaybeT . nat . runMaybeT

hoistReader :: Hoist (ReaderT r)
hoistReader nat m = ReaderT (\i -> nat (runReaderT m i))

hoistState :: Hoist (StateT s)
hoistState nat m = StateT (\s -> nat (runStateT m s))

hoistWriter :: Hoist (WriterT w)
hoistWriter nat m = WriterT (nat (runWriterT m))

hoistFreeT :: (Functor m, Functor f) => (forall a. m a -> n a) -> FreeT f m b -> FreeT f n b
hoistFreeT mh = FreeT . mh . fmap (fmap (Main.hoistFreeT mh)) . runFreeT

hoist1FreeT :: (Functor m, Functor f)
            => (forall a. m a -> m a)
            -> FreeT f m b
            -> FreeT f m b
hoist1FreeT f (FreeT m) = FreeT (f m)

-- Bracket

-- FIXME: Add a part that is not masked
data BracketT m c where
  BracketT :: m a -> (a -> IO b) -> (a -> m c) -> BracketT m c

instance Functor m => Functor (BracketT m) where
  fmap f (BracketT ma mb mc) = BracketT ma mb ((fmap . fmap) f mc)

instance Applicative m => Applicative (BracketT m) where
  pure c = BracketT (pure ()) (const (pure ())) (const (pure c))
  BracketT fa fb fc <*> BracketT xa xb xc =
    BracketT ((,) <$> fa <*> xa) (\(f, x) -> fb f *> xb x) (\(f, x) -> fc f <*> xc x)

instance Monad (BracketT IO) where
  BracketT ma mb mc >>= f =
    let m = do
          BracketT ma' mb' mc' <- bracket ma mb ((fmap . fmap) f mc)
          a <- ma'
          -- FIXME: get rid of this pure () with another existential
          pure (mb' a *> pure (), mc' a)
    in BracketT m fst snd

liftBracketT :: Applicative m => m ~> BracketT m
liftBracketT m = BracketT m pure pure

runBracketIO :: BracketT IO ~> IO
runBracketIO (BracketT ma mb mc) = bracket ma mb mc

hoistBracketT :: (forall a. m a -> n a) -> BracketT m a -> BracketT n a
hoistBracketT f (BracketT ma mb mc) = BracketT (f ma) mb (f. mc)

addRelease :: Applicative m => IO b -> BracketT m a -> BracketT m a
addRelease release (BracketT ma mb mc) = BracketT ma (\x -> mb x *> release) mc

commuteBracketTG :: (Monad m, MonadTrans t, Monad (t (BracketT m)),
                     Monad (BracketT m))
                 => (forall m n a. Monad n
                       => (forall a. n a -> m a) -> t n a -> t m a)
                 -> (forall m n a. Monad n
                       => (forall a. n a -> n a) -> t n a -> t n a)
                 -> BracketT (t m) a
                 -> t (BracketT m) a
commuteBracketTG hoist' hoist1 (BracketT ma mb mc) = do
  a <- hoist' liftBracketT ma
  let mb' = mb a
  let mc' = hoist' liftBracketT (mc a)

  let r = hoist1 (addRelease mb') mc'

  r

runBracketTG :: (MonadTrans t, Monad (t (BracketT IO)))
             => (forall m n a. Monad n
                       => (forall a. n a -> m a) -> t n a -> t m a)
                 -> (forall m n a. Monad n
                       => (forall a. n a -> n a) -> t n a -> t n a)
             -> BracketT (t IO) a -> t IO a
runBracketTG hoist' hoist1 = hoist' runBracketIO . commuteBracketTG hoist' hoist1

exampleFree :: IO ()
exampleFree =
  let foo = commuteBracketTG Main.hoistFreeT hoist1FreeT $
            BracketT (do
               write "Hello"
               lift (putStrLn "Acquiring resource")
               pure ())
           (\() -> putStrLn "Releasing resource")
           (\() -> do
               lift (putStrLn "A")
               lift (putStrLn "A12")
               write "There"
               lift (putStrLn "B")
               write "Bob"
               lift (putStrLn "C")
               write "Baz"
               lift (putStrLn "D")

               lift (putStrLn "v-- Release?")
               error "Foo")

  in go' foo

  where write s = liftF (s, ())

        go :: FreeT ((,) String) (BracketT IO) a -> IO a
        go (FreeT (BracketT ma mb mc)) = do
          bracket ma mb (\a -> do
                            mc a >>= \case
                              Pure c -> pure c
                              Free (s, rest) -> do
                                go rest)

        go' = go3 . go2

        go3 :: FreeT ((,) String) IO a -> IO a
        go3 = iterT (\(s, io) -> putStrLn s *> io)

        go2 :: FreeT ((,) String) (BracketT IO) a -> FreeT ((,) String) IO a
        go2 (FreeT (BracketT ma mb mc)) = do
          FreeT $ bracket ma mb (\a -> do
                                    mca <- mc a
                                    pure (fmap go2 mca))

-- [Commutors]: Commutors for various monad transformers

-- See https://www.reddit.com/r/haskell/comments/cualvg/does_this_monadcommute_exist/

commuteIdentityT
  :: (MFunctor t, Monad m) => IdentityT (t m) b -> t (IdentityT m) b
commuteIdentityT = hoist IdentityT . runIdentityT

uncommuteIdentityT
  :: (MFunctor t, Monad m) => t (IdentityT m) b -> IdentityT (t m) b
uncommuteIdentityT = IdentityT . hoist runIdentityT

commuteStateT
  :: (MonadTrans t, MFunctor t, Monad (t (StateT s m)), Monad m)
  => StateT s (t m) b
  -> t (StateT s m) b
commuteStateT f = do
  s       <- lift get
  (a, s') <- hoist lift (runStateT f s)
  lift (put s')
  return a

commuteWriterT
  :: (Monad (t (WriterT w m)), MFunctor t, Monad m, MonadTrans t, Monoid w)
  => WriterT w (t m) b
  -> t (WriterT w m) b
commuteWriterT f = do
  (a, w) <- hoist lift (runWriterT f)
  lift (tell w)
  return a

commuteReaderT
  :: (Monad (t (ReaderT r m)), MFunctor t, Monad m, MonadTrans t)
  => ReaderT r (t m) b
  -> t (ReaderT r m) b
commuteReaderT f = do
  r <- lift ask
  hoist lift (runReaderT f r)

commuteExceptT
  :: (Monad (t (ExceptT e m)), MFunctor t, Monad m, MonadTrans t)
  => ExceptT e (t m) b
  -> t (ExceptT e m) b
commuteExceptT f = do
  e_a <- hoist lift (runExceptT f)
  case e_a of
    Left  e -> lift (throwE e)
    Right a -> return a

commuteMaybeT
  :: (Monad (t (MaybeT m)), MFunctor t, Monad m, MonadTrans t)
  => MaybeT (t m) b
  -> t (MaybeT m) b
commuteMaybeT f = do
  ma <- hoist lift (runMaybeT f)
  case ma of
    Nothing -> lift (MaybeT (return Nothing))
    Just a  -> return a

commuteFreeT
  :: ( Monad (t (FreeT f m))
     , Functor f
     , MFunctor t
     , Monad m
     , Monad (t m)
     , MonadTrans t
     )
  => FreeT f (t m) b
  -> t (FreeT f m) b
commuteFreeT f = do
  ma <- hoist lift (runFreeT f)
  case ma of
    Free fa -> commuteFreeT (join (liftF fa))
    Pure a  -> return a
