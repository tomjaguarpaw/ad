{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-} --  Try to get rid of this

import Control.Category
import Prelude hiding (id, (.), (>>))

class Category arr => T arr s p tv | arr -> s p tv where
  sPush :: tv (s a b) `arr` s (tv a) (tv b)
  pPush :: tv (p a b) `arr` p (tv a) (tv b)
  flipT :: (a `arr` b) -> (b `arr` a)

class Category arr => C arr varr v m t | arr -> varr v m t where
  arrV  :: (a `varr` b) -> (v a `arr` v b)
  arrTa :: (a `arr` b) -> (t a `arr` t b)
  flipC :: (a `arr` b) -> (b `arr` a)

  assoc :: m (m a b) c `arr` m a (m b c)

  tPush :: t (a `m` b) `arr` (t a `m` t b)
  tJoin :: t (t a) `arr` t a

  tVar   :: t (v a) `arr` v (tv a)

  tUnit :: t _1 `arr` _1

  unit :: a `arr` (_1 `m` a)

  comm :: m a b `arr` m b a

class Category arr
  => O arr tarr m _1 v s p t | arr -> tarr m v s p _1 t
  where
  arrT :: (a `tarr` b) -> (a `arr` b)

  inl :: v a `arr` v (s a b)

  inr :: v b `arr` v (s a b)

  (|><|) :: arr a1 b1
         -> arr a2 b2
         -> arr (m a1 a2)
                (m b1 b2)

  ignore :: a `arr` _1

  pair :: v a `m` v b `arr` v (a `p` b)
  unpair :: v (a `p` b) `arr` v a `m` v b

  match :: ((ci `m` v ai1) `arr` (co `m` v ao1))
        -> ((ci `m` v ai2) `arr` (co `m` v ao2))
        -> ((ci `m` v (s ai1 ai2))
            `arr` (co `m` v (s ao1 ao2)))

  dup :: a `arr` (a `m` a)

  add :: (t a `m` t a) `arr` t a

foo :: (C tarr varr v m t, O arr tarr m _1 v s p t)
    => arr a1 z
    -> arr z a2
    -> arr (b1 `m` c1) (b2 `m` c2)
    -> arr ((a1 `m` b1) `m` c1) ((a2 `m` b2) `m` c2)
foo l m r = arrT assoc >>> ((l >>> m) |><| r) >>> arrT (flipC assoc)

data R arr (tarr :: * -> * -> *) m _1
       (v :: * -> *) (s :: * -> * -> *) (p :: * -> * -> *) t
       (tv :: * -> *) a b =
  forall r. R (a `arr` (r `m` b)) ((r `m` t b) `arr` t a)

instance (C tarr varr v m t, O arr tarr m _1 v s p t)
  => Category (R arr tarr m _1 v s p t tv) where
  id = R (id >>> arrT unit) (arrT (flipC unit) >>> id)

  f . g = case f of
    R f1 f2 -> case g of
      R g1 g2 -> R (arrT (flipC assoc) <<< (id |><| f1) <<< g1)
                   (arrT assoc >>> (id |><| f2) >>> g2)

instance (O arr tarr m _1 v s p t, C tarr varr v m t)
  => O (R arr tarr m _1 v s p t tv) tarr m _1 v s p t where
  inl = R (inl >>> arrT unit)
          undefined
