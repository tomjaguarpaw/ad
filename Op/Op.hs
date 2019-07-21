{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-} --  Try to get rid of this
{-# LANGUAGE NoMonomorphismRestriction #-}

import Control.Category
import Prelude hiding (id, (.), (>>))

class Category arr => Monoidal arr m where
  (|><|) :: arr a1 b1
         -> arr a2 b2
         -> arr (m a1 a2)
                (m b1 b2)

class Category arr => T arr s p tv | arr -> s p tv where
  sPush :: tv (s a b) `arr` s (tv a) (tv b)
  pPush :: tv (p a b) `arr` p (tv a) (tv b)
  flipT :: (a `arr` b) -> (b `arr` a)

class Category arr => C arr varr v m _1 t | arr -> varr v m _1 t where
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
  => O arr tarr m _1 v s p t u | arr -> tarr m v s p _1 t u
  where
  arrT :: (a `tarr` b) -> (a `arr` b)

  inl :: v a `arr` v (s a b)

  inr :: v b `arr` v (s a b)

  ignore :: a `arr` _1

  zero :: _1 `arr` t a

  unitT :: _1 `arr` v u

  pair :: (v a `m` v b) `arr` v (a `p` b)
  unpair :: v (a `p` b) `arr` (v a `m` v b)

  caseS :: ((ci `m` v ai1) `arr` co)
        -> ((ci `m` v ai2) `arr` co)
        -> ((ci `m` v (s ai1 ai2)) `arr` co)

  dup :: a `arr` (a `m` a)

  add :: (t a `m` t a) `arr` t a

foo :: (Monoidal arr m, C tarr varr v m _1 t, O arr tarr m _1 v s p t u)
    => arr a1 z
    -> arr z a2
    -> arr (b1 `m` c1) (b2 `m` c2)
    -> arr ((a1 `m` b1) `m` c1) ((a2 `m` b2) `m` c2)
foo l m r = arrT assoc >>> ((l >>> m) |><| r) >>> arrT (flipC assoc)

data R arr (tarr :: * -> * -> *) m _1
       (v :: * -> *) (s :: * -> * -> *) (p :: * -> * -> *) t
       (u :: *) a b =
  forall r. R (a `arr` (v r `m` b)) ((v r `m` t b) `arr` t a)

instance (Monoidal arr m, C tarr varr v m _1 t, O arr tarr m _1 v s p t u)
  => Category (R arr tarr m _1 v s p t u) where
  id = R bling blong

  f . g = case f of
    R f1 f2 -> case g of
      R g1 g2 ->
        R ((pair |><| id) <<< arrT (flipC assoc) <<< (id |><| f1) <<< g1)
          ((unpair |><| id) >>> arrT assoc >>> (id |><| f2) >>> g2)

bling :: (Monoidal arr m, O arr tarr m _1 v s p t u, C tarr varr v m _1 t)
      => a `arr` (v u `m` a)
bling = arrT unit >>> (unitT |><| id)

blong :: (Monoidal arr m, O arr tarr m _1 v s p t u, C tarr varr v m _1 t)
      => (v u `m` a) `arr` a
blong = (ignore |><| id) >>> arrT (flipC unit)

instance (Monoidal arr m, Monoidal tarr m, O arr tarr m _1 v s p t u,
          C tarr varr v m _1 t, T varr s p tv)
  => O (R arr tarr m _1 v s p t u) tarr m _1 v s p t u where
  arrT f = R (arrT f >>> bling)
             (blong >>> arrT (flipC (arrTa f)))

  inl = R (inl >>> bling)
          (bar >>> baz >>> quux)

  ignore = R (ignore >>> bling)
             (blong >>> arrT tUnit >>> zero)

  pair = R (pair >>> bling)
           flub

  zero = R (zero >>> bling)
           (blong >>> ignore >>> zero)

  caseS = \f g -> case f of
    R f1 f2 -> case g of
      R g1 g2 -> R (caseS (f1 >>> (inl |><| id))
                          (g1 >>> (inr |><| id)))
                   (arrT comm
                    >>> caseS (arrT comm >>> f2 >>> arrT tPush
                               >>> (id |><| (arrT tVar >>> inl)))
                              (arrT comm >>> g2 >>> arrT tPush
                               >>> (id |><| (arrT tVar >>> inr)))
                    >>> (id |><| arrT (flipC (arrV sPush)))
                    >>> (id |><| arrT (flipC tVar)
                    >>> arrT (flipC tPush)))

  dup = R (dup >>> bling) (add <<< arrT tPush <<< blong)

  add = R (add >>> bling) (arrT (flipC tPush) <<< dup <<< blong)

  unitT = R (unitT >>> bling) (zero <<< ignore <<< blong)

flub :: (O arr tarr m _1 v s p t u, C tarr varr v m _1 t, T varr s p tv,
         Monoidal tarr m, Monoidal arr m)
     => (v u `m` t (v (p a b))) `arr` t (v a `m` v b)
flub = blong
       >>> arrT tVar
       >>> arrT (arrV pPush)
       >>> unpair
       >>> arrT (flipC (tVar |><| tVar))
       >>> arrT (flipC tPush)

flubber :: (O arr tarr m _1 v s p t u, C tarr varr v m _1 t, T varr s p tv,
            Monoidal arr m)
        => (v u `m` t (v (p a b))) `arr` t (v (p a b))
flubber = blong

bar :: (O arr tarr m _1 v s p t u, C tarr varr v m _1 t, T varr s p tv,
        Monoidal arr m)
    => ((v u `m` (t (v (s a b)))) `arr` (_1 `m` (v (s (tv a) (tv b)))))
bar = blong >>> arrT (tVar >>> arrV sPush >>> unit)

baz :: (Monoidal arr m, O arr tarr m _1 v s p t u, C tarr varr v m _1 t,
        T varr s p tv)
    => (_1 `m` (v (s (tv a) (tv b)))) `arr` v (tv a)
baz = caseS (arrT (flipC unit))
            (ignore >>> zero >>> arrT tVar)

quux :: (Monoidal arr m, O arr tarr m _1 v s p t u, C tarr varr v m _1 t,
         T varr s p tv)
     => v (tv a) `arr` t (v a)
quux = arrT (flipC tVar)

runR :: (Monoidal arr m,
         C tarr varr v m _1 t,
         O arr tarr m _1 v s p t u)
     => R arr tarr m _1 v s p t u a b
     -> arr (a `m` t b) (t a `m` b)
runR (R f g) = (f |><| id)
               >>> arrT assoc
               >>> (id |><| arrT comm)
               >>> arrT (flipC assoc)
               >>> (g |><| id)
