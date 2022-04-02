{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
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

-- Bracket

data BracketT m c where
  Done :: c -> BracketT m c
  BracketT :: m (IO (), BracketT m c) -> BracketT m c

instance Functor m => Functor (BracketT m) where
  fmap f = \case
    Done c -> Done (f c)
    BracketT m -> BracketT ((fmap . fmap . fmap) f m)

instance Applicative m => Applicative (BracketT m) where
  pure = Done
  -- This is sort of "parallel".  It doesn't actually match ap.
  BracketT f <*> BracketT x =
    BracketT ((\(af, mf) (ax, mx) -> (af *> ax, mf <*> mx)) <$> f <*> x)

instance Applicative m => Monad (BracketT m) where
  Done c >>= f = f c
  BracketT m >>= f = BracketT ((fmap . fmap) (>>= f) m)

instance MonadTrans BracketT where
  lift = liftBracketT

liftBracketT :: Applicative m => m ~> BracketT m
liftBracketT m = BracketT (fmap (\x -> (pure (), pure x)) m)

instance MFunctor BracketT where
  hoist f = \case
    Done c -> Done c
    BracketT m -> BracketT (f ((fmap . fmap) (hoist f) m))

addRelease :: Applicative m => IO () -> BracketT m a -> BracketT m a
addRelease release = \case
  Done c -> BracketT (pure (release, pure c))
  BracketT m -> BracketT $ flip fmap m $ \(release1, m') ->
    (release1 *> release, m')

acquire :: Functor m => m (IO (), a) -> BracketT m a
acquire m = BracketT ((fmap . fmap) Done m)

runBracketTG :: (MonadTrans t, Monad (t (BracketT IO)))
             => (forall m n a. Monad n
                       => (forall a. n a -> m a) -> t n a -> t m a)
             -> BracketT (t IO) a -> t IO a
runBracketTG hoist' = hoist' runBracketIO . commuteBracketTG hoist'
  where runBracketIO :: BracketT IO a -> IO a
        runBracketIO = \case
          Done a -> pure a
          BracketT m -> bracket m fst (runBracketIO . snd)

commuteBracketTG :: (Monad m, MonadTrans t, Monad (t (BracketT m)))
                 => (forall m n a. Monad n
                       => (forall a. n a -> m a) -> t n a -> t m a)
                 -> BracketT (t m) a
                 -> t (BracketT m) a
commuteBracketTG hoist' = \case
  Done c -> lift (Done c)
  BracketT m -> do
    (release, body) <- hoist' liftBracketT m
    hoist' (addRelease release) (commuteBracketTG hoist' body)

runBracketT :: (MonadTrans t, MFunctor t, Monad (t (BracketT IO)))
            => BracketT (t IO) a -> t IO a
runBracketT = runBracketTG hoist

commuteBracketT :: (Monad m, MonadTrans t, MFunctor t, Monad (t (BracketT m)))
                => BracketT (t m) a
                -> t (BracketT m) a
commuteBracketT = commuteBracketTG hoist

example = flip runStateT () $ runBracketT $ BracketT $ do
  lift (putStrLn "Acquiring resource")

  pure (putStrLn "Releasing resource",
        do
          (lift . lift) (putStrLn "v-- Release?")
          error "Foo"
       )

example' = flip runStateT "Hello" $ runBracketT $ do
  s <- lift get
  (lift . lift) (putStrLn s)
  lift (put "bar")

  s2 <- acquire $ do
    s1 <- get
    lift (putStrLn ("Acquiring resource 1 based on " ++ s1))
    pure (putStrLn ("Releasing resource 1 based on " ++ s1), s1)

  lift (put "baz")

  s3 <- acquire $ do
    s1 <- get
    lift (putStrLn ("Acquiring resource 2 based on " ++ s1))
    pure (putStrLn ("Releasing resource 2 based on " ++ s1), s1)

  (lift . lift) (putStrLn ("Using resource 1 based on " ++ s2))
  (lift . lift) (putStrLn ("Using resource 2 based on " ++ s3))

  (lift . lift) (putStrLn "v-- Release?")
  error "Foo"

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
