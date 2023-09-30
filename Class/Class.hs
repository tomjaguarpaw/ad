{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}

import           Data.Kind                      ( Constraint )
import           Data.Function                  ( on )
import           Data.Functor.Compose           ( Compose(Compose)
                                                , getCompose
                                                )
import           Control.Arrow ((&&&))
import Control.Monad.Identity (Identity(Identity), runIdentity)

import Control.Applicative (liftA2, Const(Const), getConst)
import Data.Monoid (All(All), getAll)

import Data.Functor.Product (Product(Pair))
import Data.Functor.Sum (Sum(InL, InR))

import Data.Semigroup (Semigroup, (<>))

import qualified Data.Reflection as R
import Data.Proxy (Proxy(Proxy))

-- { Classes

type instance Subclasses (SemigroupD a) = ()
data SemigroupD a = SemigroupD {
  (.<>) :: a -> a -> a
  }

type instance Subclasses (MonoidD a) = Class (SemigroupD a)
data MonoidD a = MonoidD {
    memptyD  :: a
  }

type instance Subclasses (EqD a) = ()
data EqD a = EqD {
  (.==) :: a -> a -> Bool
  }

type instance Subclasses (OrdD a) = Class (EqD a)
data OrdD a = OrdD {
    compareD :: a -> a -> Ordering
  , (.<)  :: a -> a -> Bool
  --- vv bit of a wart that we have to have this.  We need it to
  --- implement Preserves.
  , (..==) :: a -> a -> Bool
  }

type instance Subclasses (FunctorD f) = ()
data FunctorD f = FunctorD {
  fmapD :: forall a b. (a -> b) -> f a -> f b
  }

type instance Subclasses (ApplicativeD f) = Class (FunctorD f)
data ApplicativeD f = ApplicativeD {
    pureD   :: forall a. a -> f a
  , (.<*>)  :: forall a b. f (a -> b) -> f a -> f b
  , liftA2D :: forall a b c. (a -> b -> c) -> f a -> f b -> f c
  }

-- }

-- { User-defined data types

data Foo a = Foo { foo1 :: Maybe a, foo2 :: [Int] }

data Bar a = Bar1 (Maybe a)
           | Bar2 [Int]

data Baz a = Baz { unBaz :: Maybe [a] }

-- "Derived by compiler"
deriveForFoo :: ( Class (f [Int])
                , Class (f (Maybe a))
                , Preserves (,) f
                , Invariant (->) (->) f )
             => f (Foo a)
deriveForFoo =
  mapInvariant (uncurry Foo) (foo1 &&& foo2) (preserve methods methods)

-- "Derived by compiler"
deriveForBar :: ( Class (f [Int])
                , Class (f (Maybe a))
                , Preserves Either f
                , Invariant (->) (->) f)
             => f (Bar a)
deriveForBar =
  mapInvariant
  (either Bar1 Bar2)
  (\case { Bar1 a -> Left a; Bar2 a -> Right a})
  (preserve methods methods)

-- "Derived by compiler"
deriveForBaz :: forall (f :: (* -> *) -> *).
                ( Preserves Compose f
                , Class (f Maybe)
                , Class (f [])
                , Invariant NatTrans (->) f)
             => f Baz
deriveForBaz =
  mapInvariant
  (NatTrans (Baz . getCompose))
  (NatTrans (Compose . unBaz))
  (preserve methods methods)

instance Class (EqD a) => Class (EqD (Foo a)) where
  methods = deriveForFoo

instance Class (OrdD a) => Class (OrdD (Foo a)) where
  methods = deriveForFoo

instance Class (SemigroupD a) => Class (SemigroupD (Foo a)) where
  methods = deriveForFoo

instance Class (MonoidD a) => Class (MonoidD (Foo a)) where
  methods = deriveForFoo

instance Class (EqD a) => Class (EqD (Bar a)) where
  methods = deriveForBar

instance Class (OrdD a) => Class (OrdD (Bar a)) where
  methods = deriveForBar

instance Class (FunctorD Baz) where
  methods = deriveForBaz

instance Class (ApplicativeD Baz) where
  methods = deriveForBaz

-- }

-- { Library

preserveClass :: (Preserves f d, Class (d a), Class (d b)) => d (f a b)
preserveClass = preserve methods methods

type family Subclasses (a :: *) :: Constraint

class Subclasses a => Class (a :: *) where
  methods :: a

class Invariant c c' f where
  mapInvariant :: c a b -> c b a -> c' (f a) (f b)

class Preserves p f where
  preserve :: f a -> f b -> f (p a b)

(.:) :: (a -> b) -> (c1 -> c2 -> a) -> c1 -> c2 -> b
(.:) f g a b = f (g a b)

-- }

-- { Standard library instances

instance (Class (EqD a), Class (EqD b)) => Class (EqD (Either a b)) where
  methods = preserveClass

instance (Class (EqD a), Class (EqD b)) => Class (EqD (a, b)) where
  methods = preserveClass

instance (Class (SemigroupD a), Class (SemigroupD b)) => Class (SemigroupD (a, b)) where
  methods = preserveClass

instance (Class (MonoidD a), Class (MonoidD b)) => Class (MonoidD (a, b)) where
  methods = preserveClass

instance (Class (FunctorD f), Class (FunctorD g))
  => Class (FunctorD (Compose f g)) where
  methods = preserveClass

instance (Class (ApplicativeD f), Class (ApplicativeD g))
  => Class (ApplicativeD (Compose f g)) where
  methods = preserveClass

instance (Class (OrdD a), Class (OrdD b)) => Class (OrdD (a, b)) where
  methods = preserveClass

instance (Class (OrdD a), Class (OrdD b)) => Class (OrdD (Either a b)) where
  methods = preserveClass

instance Class (EqD Int) where
  methods = fromOldClass

instance Class (OrdD Int) where
  methods = fromOldClass

instance Class (EqD a) => Class (EqD [a]) where
  methods = deriveListViaMaybe

instance Class (FunctorD (Const a)) where
  methods = fromOldClass

instance (Class (FunctorD f), Class (FunctorD g))
  => Class (FunctorD (Sum f g)) where
  methods = preserveClass

instance (Class (FunctorD f), Class (FunctorD g))
  => Class (FunctorD (Product f g)) where
  methods = preserveClass

instance Monoid a => Class (ApplicativeD (Const a)) where
  methods = fromOldClass

instance Class (ApplicativeD []) where
  methods = fromOldClass

instance Class (FunctorD Identity) where
  methods = fromOldClass

instance Class (FunctorD []) where
  methods = deriveListViaPair1

instance Class (FunctorD (Either e)) where
  methods = fromOldClass

instance Class (ApplicativeD (Either e)) where
  methods = fromOldClass

instance Class (FunctorD Maybe) where
  methods = deriveMaybeViaEither1

instance Class (ApplicativeD Maybe) where
  methods = deriveMaybeViaEither1

instance Class (EqD ()) where
  methods = fromOldClass

instance Class (OrdD ()) where
  methods = fromOldClass

instance Class (OrdD a) => Class (OrdD [a]) where
  methods = deriveListViaMaybe

instance Class (OrdD a) => Class (OrdD (Maybe a)) where
  methods = deriveMaybeViaEither

instance Class (EqD a) => Class (EqD (Maybe a)) where
  methods = deriveMaybeViaEither

instance Class (SemigroupD [a]) where
  methods = fromOldClass

instance Class (MonoidD [a]) where
  methods = fromOldClass

instance Class (SemigroupD a) => Class (MonoidD (Maybe a)) where
  methods = MonoidD { memptyD = Nothing }

instance Class (SemigroupD a) => Class (SemigroupD (Maybe a)) where
  methods = SemigroupD { (.<>) = \a b -> case (a, b) of
                          (Nothing, Nothing) -> Nothing
                          (Nothing, Just b') -> Just b'
                          (Just a', Nothing) -> Just a'
                          (Just a', Just b') -> Just ((.<>) methods a' b')
                          }

-- }

-- { Preservations

eitherPreserve :: Class (f Int)
               => (forall z. f z -> z -> z -> t)
               -> f a
               -> f b
               -> Either a b
               -> Either a b
               -> t
eitherPreserve op e1 e2 a b =
  case (a, b) of
    (Left l1, Left l2) ->
      op e1 l1 l2
    (Right r1, Right r2) ->
      op e2 r1 r2
    (Left _, Right _) ->
      op methods (1 :: Int) 2
    (Right _, Left _) ->
      op methods (2 :: Int) 1

productPreserve :: Applicative g
                => (forall z. f z -> z -> z -> g z)
                -> (g (a, b) -> r)
                -> f a
                -> f b
                -> (a, b)
                -> (a, b)
                -> r
productPreserve op r e1 e2 (a1, b1) (a2, b2) =
  r ((,) <$> op e1 a1 a2 <*> op e2 b1 b2)

using :: (t2 -> t3 -> t4 -> t)
      -> (t -> t1) -> t2 -> t3 -> t4 -> t1
(op `using` g) d a b = g (op d a b)

instance Preserves Either OrdD where
  preserve e1 e2 = OrdD { compareD = eitherPreserve compareD e1 e2
                        , (.<)     = eitherPreserve (.<) e1 e2
                        , (..==)   = eitherPreserve (..==) e1 e2
                        }

instance Preserves (,) OrdD where
  preserve e1 e2 = OrdD {
      compareD = productPreserve
                 (compareD `using` Const)
                 getConst
                 e1
                 e2
    , (.<) = \(a1,a2) (b1,b2) ->
               (.<) e1 a1 b1
               || ((..==) e1 a1 b1 && (.<) e2 a2 b2)
    , (..==) = productPreserve
               ((..==) `using` (Const . All))
               (getAll . getConst)
               e1
               e2
    }

instance Preserves (,) SemigroupD where
  preserve m1 m2 = SemigroupD {
    (.<>) = productPreserve ((.<>) `using` Identity) runIdentity m1 m2
 }

instance Preserves (,) MonoidD where
  preserve s1 s2 = MonoidD { memptyD = (memptyD s1, memptyD s2) }


instance Preserves Compose FunctorD where
  preserve f1 f2 =
    FunctorD { fmapD = \f c -> Compose ((fmapD f1 . fmapD f2) f (getCompose c)) }

instance Preserves Compose ApplicativeD where
  preserve f1 f2 =
    ApplicativeD { pureD  = Compose . pureD f1 . pureD f2
                 , (.<*>) = \(Compose f) (Compose x) ->
                     Compose (liftA2D f1 ((.<*>) f2) f x)
                 , liftA2D = \f (Compose x) (Compose y) ->
                     Compose (liftA2D f1 (liftA2D f2 f) x y)
                 }

instance Preserves Either EqD where
  preserve e1 e2 = EqD { (.==) = eitherPreserve (.==) e1 e2 }

instance Preserves Sum FunctorD where
  preserve f1 f2 = FunctorD { fmapD = \f -> \case
                                InL l -> InL (fmapD f1 f l)
                                InR r -> InR (fmapD f2 f r)
                            }

instance Preserves Product FunctorD where
  preserve f1 f2 = FunctorD {
    fmapD = \f (Pair l r) -> Pair (fmapD f1 f l) (fmapD f2 f r)
    }

instance Preserves (,) EqD where
  preserve e1 e2 = EqD {
    (.==) = productPreserve
            ((.==) `using` (Const . All))
            (getAll . getConst)
            e1
            e2
    }

-- }

-- { Invariances

data NatTrans f g = NatTrans { runNatTrans :: forall a. f a -> g a }

instance Invariant (->) (->) EqD where
  mapInvariant _ g e = EqD { (.==) = (.==) e `on` g }

instance Invariant (->) (->) OrdD where
  mapInvariant _ g e = OrdD { compareD = compareD e `on` g
                            , (.<) = (.<) e `on` g
                            , (..==) = (..==) e `on` g
                            }

instance Invariant (->) (->) SemigroupD where
  mapInvariant f g s =
    SemigroupD { (.<>) = f .: ((.<>) s `on` g) }

instance Invariant (->) (->) MonoidD where
  mapInvariant f _ m = MonoidD { memptyD = f (memptyD m) }

instance Invariant NatTrans (->) FunctorD where
  mapInvariant g h f =
    FunctorD { fmapD = \i -> runNatTrans g . fmapD f i . runNatTrans h }

instance Invariant NatTrans (->) ApplicativeD where
  mapInvariant g h f =
    ApplicativeD { pureD  = runNatTrans g . pureD f
                 , (.<*>) = \a b -> runNatTrans g ((.<*>) f (runNatTrans h a)
                                                            (runNatTrans h b))
                 , liftA2D = \i a b ->
                     runNatTrans g (liftA2D f i (runNatTrans h a) (runNatTrans h b))
                 }

-- }

-- { Deriving strategies

deriveListViaMaybe :: (Invariant (->) (->) f, Class (f (Maybe (a, [a]))))
                   => f [a]
deriveListViaMaybe = mapInvariant (\case Nothing -> []
                                         Just as -> uncurry (:) as)
                                   (\case []     -> Nothing
                                          (a:as) -> Just (a, as))
                     methods

deriveMaybeViaEither :: (Invariant (->) (->) f, Class (f (Either () a)))
                     => f (Maybe a)
deriveMaybeViaEither = mapInvariant (\case Left () -> Nothing
                                           Right a -> Just a)
                                    (\case Nothing -> Left ()
                                           Just a  -> Right a)
                                    methods

deriveMaybeViaEither1 :: ( Invariant NatTrans (->) f
                         , Class (f (Either ())) )
                      => f Maybe
deriveMaybeViaEither1 =
  mapInvariant (NatTrans (\case Left () -> Nothing
                                Right a -> Just a))
               (NatTrans (\case Nothing -> Left ()
                                Just a  -> Right a))
               methods

type MaybeF = Sum (Const ()) (Product Identity [])

deriveListViaPair1 :: ( Invariant NatTrans (->) f
                       , Class (f MaybeF) )
                    => f []
deriveListViaPair1 =
   mapInvariant (NatTrans (\case InL _ -> []
                                 InR (Pair (Identity a) as) -> a:as))
                (NatTrans (\case []     -> InL (Const ())
                                 (a:as) -> InR (Pair (Identity a) as)))
                methods

-- }

-- { FromOldClass

class FromOldClass c f | f -> c where
  fromOldClass :: forall a. c a => f a

instance FromOldClass Eq EqD where
  fromOldClass = EqD { (.==) = (==) }

instance FromOldClass Ord OrdD where
  fromOldClass = OrdD {
      compareD = compare
    , (.<)     = (<)
    , (..==)   = (==)
    }

instance FromOldClass Semigroup SemigroupD where
  fromOldClass = SemigroupD { (.<>) = (<>) }

instance FromOldClass Monoid MonoidD where
  fromOldClass = MonoidD { memptyD = mempty }

instance FromOldClass Functor FunctorD where
  fromOldClass = FunctorD { fmapD = fmap }

instance FromOldClass Applicative ApplicativeD where
  fromOldClass = ApplicativeD { pureD = pure, (.<*>) = (<*>), liftA2D = liftA2 }

-- }

-- { Reflection

newtype Reflected f a s = Reflected { unReflect :: a }

unreflected :: Reflected f a s -> proxy s -> a
unreflected (Reflected a) _ = a

instance ( Subclasses (f (Reflected f a s))
         , Invariant (->) (->) f
         , R.Reifies s (f a) )
        => Class (f (Reflected f a s)) where
  methods = reflectedMethods

reify :: f a
      -> (forall (s :: *). R.Reifies s (f a) => t -> Reflected f a s)
      -> t
      -> a
reify d m xs = R.reify d (unreflected (m xs))

reflectedMethods :: (Invariant (->) (->) f, R.Reifies s (f a))
                 => f (Reflected t a s)
reflectedMethods = getCompose (reflectResult (Compose . mapReflected))

mapReflected :: Invariant (->) (->) g => g a -> g (Reflected f a s)
mapReflected = mapInvariant Reflected unReflect

reflectResult :: forall f s a. R.Reifies s a => (a -> f s) -> f s
reflectResult f = f (R.reflect (Proxy :: Proxy s))

instance (R.Reifies s (SemigroupD a), Class (SemigroupD a))
      => Semigroup (Reflected SemigroupD a s) where
  (<>)  = (.<>) methods

-- }

main = pure ()
