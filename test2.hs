{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}

import           Data.Kind                      ( Constraint )
import           Data.Function                  ( on )
import           Data.Functor.Compose           ( Compose(Compose)
                                                , getCompose
                                                )
import           Control.Arrow ((&&&))
import Control.Monad.Identity (Identity(Identity), runIdentity)

import Control.Applicative (liftA2, Const(Const), getConst)
import Data.Monoid (All(All), getAll)

data SemigroupD a = SemigroupD {
  (.<>) :: a -> a -> a
  }

data MonoidD a = MonoidD {
    memptyD  :: a
  }

data EqD a = EqD {
  (.==) :: a -> a -> Bool
  }

data OrdD a = OrdD {
    compareD :: a -> a -> Ordering
  , (.<)  :: a -> a -> Bool
  --- vv bit of a wart that we have to have this.  We need it to
  --- implement Preserves.
  , (..==) :: a -> a -> Bool
  }

data FunctorD f = FunctorD {
  fmapD :: forall a b. (a -> b) -> f a -> f b
  }

data ApplicativeD f = ApplicativeD {
    pureD   :: forall a. a -> f a
  , (.<*>)  :: forall a b. f (a -> b) -> f a -> f b
  , liftA2D :: forall a b c. (a -> b -> c) -> f a -> f b -> f c
  }

type instance Subclasses SemigroupD a = ()
type instance Subclasses MonoidD a = Class SemigroupD a
type instance Subclasses EqD a = ()
type instance Subclasses OrdD a = Class EqD a
type instance Subclasses FunctorD f = ()
type instance Subclasses ApplicativeD f = Class FunctorD f

instance Preserves Either EqD where
  preserve e1 e2 = EqD { (.==) = eitherPreserve (.==) e1 e2 }

instance Preserves (,) EqD where
  preserve e1 e2 = EqD {
    (.==) = productPreserve
            ((.==) `using` (Const . All))
            (getAll . getConst)
            e1
            e2
    }

eitherPreserve :: Class f Int
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

instance (Class EqD a, Class EqD b) => Class EqD (Either a b) where
  methods = preserveClass

instance (Class EqD a, Class EqD b) => Class EqD (a, b) where
  methods = preserveClass

instance (Class SemigroupD a, Class SemigroupD b) => Class SemigroupD (a, b) where
  methods = preserveClass

instance (Class MonoidD a, Class MonoidD b) => Class MonoidD (a, b) where
  methods = preserveClass

instance (Class FunctorD f, Class FunctorD g)
  => Class FunctorD (Compose f g) where
  methods = preserveClass

instance (Class ApplicativeD f, Class ApplicativeD g)
  => Class ApplicativeD (Compose f g) where
  methods = preserveClass

data Foo a = Foo { foo1 :: Maybe a, foo2 :: [Int] }

data Bar a = Bar1 (Maybe a)
           | Bar2 [Int]

data Baz a = Baz { unBaz :: Maybe [a] }

-- "Derived by compiler"
deriveForFoo :: ( Class f [Int]
                , Class f (Maybe a)
                , Preserves (,) f
                , Invariant (->) (->) f )
             => f (Foo a)
deriveForFoo =
  mapInvariant (uncurry Foo) (foo1 &&& foo2) (preserve methods methods)

-- "Derived by compiler"
deriveForBar :: ( Class f [Int]
                , Class f (Maybe a)
                , Preserves Either f
                , Invariant (->) (->) f)
             => f (Bar a)
deriveForBar =
  mapInvariant
  (either Bar1 Bar2)
  (\case { Bar1 a -> Left a; Bar2 a -> Right a})
  (preserve methods methods)

deriveForBaz :: forall (f :: (* -> *) -> *).
                ( Preserves Compose f
                , Class f Maybe
                , Class f []
                , Invariant NatTrans (->) f)
             => f Baz
deriveForBaz =
  mapInvariant
  (NatTrans (Baz . getCompose))
  (NatTrans (Compose . unBaz))
  (preserve methods methods)

instance Class EqD a => Class EqD (Foo a) where
  methods = deriveForFoo

instance Class OrdD a => Class OrdD (Foo a) where
  methods = deriveForFoo

instance Class SemigroupD a => Class SemigroupD (Foo a) where
  methods = deriveForFoo

instance Class MonoidD a => Class MonoidD (Foo a) where
  methods = deriveForFoo

instance Class EqD a => Class EqD (Bar a) where
  methods = deriveForBar

instance Class OrdD a => Class OrdD (Bar a) where
  methods = deriveForBar

instance Class FunctorD Baz where
  methods = deriveForBaz

instance Class ApplicativeD Baz where
  methods = deriveForBaz

-- { Library

preserveClass :: (Preserves f d, Class d a, Class d b) => (d (f a b))
preserveClass = preserve methods methods

type family Subclasses (f :: k -> *) (a :: k) :: Constraint

class Subclasses f a => Class (f :: k -> *) (a :: k) where
  methods :: f a

class Invariant c c' f where
  mapInvariant :: c a b -> c b a -> c' (f a) (f b)

class Preserves (p :: k -> k -> k) (f :: k -> *) where
  preserve :: f a -> f b -> f (p a b)

(.:) :: (a -> b) -> (c1 -> c2 -> a) -> c1 -> c2 -> b
(.:) f g a b = f (g a b)

-- }

-- { Standard library

instance Class EqD Int where
  methods = EqD { (.==) = (==) }

instance Class OrdD Int where
  methods = OrdD { (.<)   = (<)
                 , (..==) = (.==) methods
                 }

instance Class EqD a => Class EqD [a] where
  methods = EqD { (.==) = let
                   (.===) = \a b ->
                     case (a, b) of
                       ([],[]) -> True
                       (a':as, b':bs) -> (.==) methods a' b' && (.===) as bs
                       (_:_, []) -> False
                       ([], _:_) -> False
                   in (.===)
               }

instance Class FunctorD [] where
  methods = FunctorD { fmapD = fmap }

instance Class ApplicativeD [] where
  methods = ApplicativeD { pureD  = pure
                         , (.<*>) = (<*>)
                         , liftA2D = liftA2
                         }

instance Class FunctorD Maybe where
  methods = FunctorD { fmapD = fmap }

instance Class ApplicativeD Maybe where
  methods = ApplicativeD { pureD   = pure
                         , (.<*>)  = (<*>)
                         , liftA2D = liftA2
                         }

instance Class OrdD a => Class OrdD [a] where
  methods = OrdD { (.<) = \a b -> case (a, b) of
                     ([],  []) -> False
                     (_:_, []) -> False
                     ([], _:_) -> True
                     (a':as, b':bs) -> (.<) methods a' b'
                                       || ((..==) methods a' b'
                                          && (.<) methods as bs)
                 , (..==) = (.==) methods
                 }

instance Class OrdD a => Class OrdD (Maybe a) where
  methods = OrdD { (.<) = \a b -> case (a, b) of
                       (Nothing,  Nothing) -> False
                       (Just _, Nothing)   -> False
                       (Nothing, Just _)   -> True
                       (Just a', Just b')  -> (.<) methods a' b'
                 , (..==) = (.==) methods
                 }

instance Class SemigroupD a => Class MonoidD (Maybe a) where
  methods = MonoidD { memptyD = Nothing }

instance Class EqD a => Class EqD (Maybe a) where
  methods = EqD { (.==) = \a b ->
                     case (a, b) of
                       (Nothing, Nothing) -> True
                       (Just a', Just b') -> (.==) methods a' b'
                       (Nothing, Just _)  -> False
                       (Just _, Nothing)  -> False
               }

instance Class SemigroupD [a] where
  methods = SemigroupD { (.<>) = (++) }

instance Class MonoidD [a] where
  methods = MonoidD { memptyD = [] }

instance Class SemigroupD a => Class SemigroupD (Maybe a) where
  methods = SemigroupD { (.<>) = \a b -> case (a, b) of
                          (Nothing, Nothing) -> Nothing
                          (Nothing, Just b') -> Just b'
                          (Just a', Nothing) -> Just a'
                          (Just a', Just b') -> Just ((.<>) methods a' b')
                          }


data NatTrans f g = NatTrans { runNatTrans :: forall a. f a -> g a }

instance Invariant (->) (->) EqD where
  mapInvariant _ g e = EqD { (.==) = (.==) e `on` g }

instance Invariant (->) (->) OrdD where
  mapInvariant _ g e = OrdD { (.<) = (.<) e `on` g
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
