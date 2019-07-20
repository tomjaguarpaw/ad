{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

import Control.Category
import Prelude hiding (id, (.))

class Category arr
  => O arr m _1 v s p t | arr -> m, arr -> v, arr -> s, arr -> p, arr -> _1,
                          arr -> t where
  assocR :: m (m a b) c
            `arr` m a (m b c)

  assocL :: m a (m b c)
            `arr` m (m a b) c

  tangentMu :: t (a `m` b) `arr` (t a `m` t b)
  tangentMw :: (t a `m` t b) `arr` t (a `m` b)

  unitI :: a `arr` (_1 `m` a)

  unitE :: (_1 `m` a) `arr` a

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

  add :: (t a `m` t a) `arr` t a

foo :: O arr m _1 v s p t
    => arr a1 z
    -> arr z a2
    -> arr (b1 `m` c1) (b2 `m` c2)
    -> arr ((a1 `m` b1) `m` c1) ((a2 `m` b2) `m` c2)
foo l m r = assocR >>> ((l >>> m) |><| r) >>> assocL

data R arr m _1 (v :: * -> *) (s :: * -> * -> *) (p :: * -> * -> *) t a b =
  forall r. R (a `arr` (r `m` b)) ((r `m` t b) `arr` t a)

instance O arr m _1 v s p t
  => Category (R arr m _1 v s p t) where
  id = R (id >>> unitI) (unitE >>> id)

  f . g = case f of
    R f1 f2 -> case g of
      R g1 g2 -> R (assocL <<< (id |><| f1) <<< g1)
                   (assocR >>> (id |><| f2) >>> g2)

instance O arr m _1 v s p t => O (R arr m _1 v s p t) m _1 v s p t where
  assocR = R (assocR >>> unitI)
             (unitE
              >>> tangentMu
              >>> (id |><| tangentMu)
              >>> assocL
              >>> (tangentMw |><| id)
              >>> tangentMw)

  assocL = R (assocL >>> unitI)
             (unitE
              >>> tangentMu
              >>> (tangentMu |><| id)
              >>> assocR
              >>> (id |><| tangentMw)
              >>> tangentMw)
  tangentMu = R (tangentMu >>> unitI)
                undefined
