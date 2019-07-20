{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

import Control.Category
import Data.Profunctor

class Mon m where
  assocR :: m (m a b) c
         -> m a (m b c)

  assocL :: m a (m b c)
         -> m (m a b) c

  comm :: m a b -> m b a

class (Profunctor arr, Category arr, Mon m)
  => O arr m v s p | arr -> m, arr -> v, arr -> s, arr -> p where
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

foo :: O arr m v s p
    => arr a1 z
    -> arr z a2
    -> arr (b1 `m` c1) (b2 `m` c2)
    -> arr ((a1 `m` b1) `m` c1) ((a2 `m` b2) `m` c2)
foo l m r = dimap assocR assocL ((l >>> m) |><| r)
