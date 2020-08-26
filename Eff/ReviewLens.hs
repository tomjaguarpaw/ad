{-# OPTIONS_GHC -fdefer-type-errors #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

import           Data.Profunctor                ( dimap
                                                , rmap
                                                , Profunctor
                                                , Strong
                                                , Choice
                                                , left'
                                                , first'
                                                )
import qualified Control.Lens                  as L

data Foo a b = Foo { fooA :: [a], fooB :: b } deriving Show

-- A lens that's also a review, assuming the non-existent typeclass
--
--     p a b -> p (a, Maybe c) (b, Maybe c)
--
-- with instances for (->) and Tagged.
b
  :: (Profunctor p, Functor f)
  => (forall a b c . p a b -> p (a, Maybe c) (b, Maybe c))
  -> p b (f b')
  -> p (Foo a b) (f (Foo a b'))
b perhaps =
  dimap
      (\(Foo a b) -> (b, Just (Foo a)))
      (\(fb, mf) -> fmap
        (case mf of
          Nothing -> Foo []
          Just f  -> f
        )
        fb
      )
    . perhaps

blens :: (Functor f, Strong p) => p b (f b') -> p (Foo a b) (f (Foo a b'))
blens = b first'

breview
  :: (Functor f, Profunctor p) => p b (f b') -> p (Foo a b) (f (Foo a b'))
breview = b (dimap fst (\b -> (b, Nothing)))
