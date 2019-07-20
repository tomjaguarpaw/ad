{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

import Control.Category
import Data.Profunctor
import Prelude hiding (id, (.))

class (Profunctor arr, Category arr)
  => O arr m _1 v s p | arr -> m, arr -> v, arr -> s, arr -> p, arr -> _1 where
  type T arr :: * -> *

  assocR :: m (m a b) c
            `arr` m a (m b c)

  assocL :: m a (m b c)
            `arr` m (m a b) c

  unitI :: a `arr` (a `m` _1)

  unitE :: (a `m` _1) `arr` a

  comm :: m a b `arr` m b a

  inl :: v a `arr` v (m a b)

  inr :: v b `arr` v (m a b)

  (|><|) :: arr a1 b1
         -> arr a2 b2
         -> arr (m a1 a2)
                (m b1 b2)

  pair :: v a `m` v b
          `arr` v (a `p` b)

  unpair :: v (a `p` b)
            `arr` v a `m` v b

  match :: ((m (v ai1) ci) `arr` (m (v ao1) co))
        -> ((m (v ai2) ci) `arr` (m (v ao2) co))
        -> ((m (v (s ai1 ai2)) ci)
            `arr` (v (s ao1 ao2) `m` co))

  dup :: a `arr` (a `m` a)

  add :: (T arr a `m` T arr a) `arr` T arr a

foo :: O arr m _1 v s p
    => arr a1 z
    -> arr z a2
    -> arr (b1 `m` c1) (b2 `m` c2)
    -> arr ((a1 `m` b1) `m` c1) ((a2 `m` b2) `m` c2)
foo l m r = assocR >>> ((l >>> m) |><| r) >>> assocL

data R arr m _1 (v :: * -> *) (s :: * -> * -> *) (p :: * -> * -> *) a b =
  forall r. R (a `arr` (r `m` b)) ((r `m` T arr b) `arr` T arr a)

instance (O arr m _1 v s p, Category arr)
  => Category (R arr m _1 v s p) where
  id = R (id >>> unitI >>> comm) (comm >>> unitE >>> id)

  f . g = case f of
    R f1 f2 -> case g of
      R g1 g2 -> R (assocL <<< (id |><| f1) <<< g1)
                   (assocR >>> (id |><| f2) >>> g2)


{-
instance O arr m v s p => O (R arr m v s p) m v s p where
-}
