{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

import Control.Category
import Prelude hiding (id, (.), (>>))

class T arr s p tv | arr -> s p tv where
  tsPush :: tv (s a b) `arr` s (tv a) (tv b)
  tsPull :: s (tv a) (tv b) `arr` tv (s a b)

  tpPush :: tv (p a b) `arr` p (tv a) (tv b)
  tpPull :: p (tv a) (tv b) `arr` tv (p a b)

class Category arr
  => O arr tarr m _1 v s p t tv | arr -> tarr m v s p _1 t tv
  where
  assocR :: m (m a b) c
            `arr` m a (m b c)

  assocL :: m a (m b c)
            `arr` m (m a b) c

  tangentMu :: t (a `m` b) `arr` (t a `m` t b)
  tangentMw :: (t a `m` t b) `arr` t (a `m` b)

  tJoin :: t (t a) `arr` t a
  tDup  :: t a `arr` t (t a)

  tVar   :: t (v a) `arr` v (tv a)
  tUnvar :: v (tv a) `arr` t (v a)

  tUnitE :: t _1 `arr` _1
  tUnitI :: _1 `arr` t _1

  unitI :: a `arr` (_1 `m` a)

  unitE :: (_1 `m` a) `arr` a

  comm :: m a b `arr` m b a

  inl :: v a `arr` v (s a b)

  inr :: v b `arr` v (s a b)

  (|><|) :: arr a1 b1
         -> arr a2 b2
         -> arr (m a1 a2)
                (m b1 b2)

  ignore :: a `arr` _1

  pair :: v a `m` v b
          `arr` v (a `p` b)

  unpair :: v (a `p` b)
            `arr` v a `m` v b

  match :: ((ci `m` v ai1) `arr` (co `m` v ao1))
        -> ((ci `m` v ai2) `arr` (co `m` v ao2))
        -> ((ci `m` v (s ai1 ai2))
            `arr` (co `m` v (s ao1 ao2)))

  dup :: a `arr` (a `m` a)

  add :: (t a `m` t a) `arr` t a

foo :: O arr tarr m _1 v s p t tv
    => arr a1 z
    -> arr z a2
    -> arr (b1 `m` c1) (b2 `m` c2)
    -> arr ((a1 `m` b1) `m` c1) ((a2 `m` b2) `m` c2)
foo l m r = assocR >>> ((l >>> m) |><| r) >>> assocL

data R arr tarr m _1 (v :: * -> *) (s :: * -> * -> *) (p :: * -> * -> *) t
       (tv :: * -> *) a b =
  forall r. R (a `arr` (r `m` b)) ((r `m` t b) `arr` t a)

instance O arr tarr m _1 v s p t tv
  => Category (R arr tarr m _1 v s p t tv) where
  id = R (id >>> unitI) (unitE >>> id)

  f . g = case f of
    R f1 f2 -> case g of
      R g1 g2 -> R (assocL <<< (id |><| f1) <<< g1)
                   (assocR >>> (id |><| f2) >>> g2)

instance O arr tarr m _1 v s p t tv => O (R arr tarr m _1 v s p t tv) tarr m _1 v s p t tv where
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
                (unitE
                 >>> tangentMu
                 >>> (tJoin |><| tJoin)
                 >>> tangentMw
                 >>> tDup)

  tangentMw = R (tangentMw >>> unitI)
                (unitE
                 >>> tJoin
                 >>> tangentMu
                 >>> (tDup |><| tDup)
                 >>> tangentMw)

  tJoin = R (tJoin >>> unitI)
            (unitE >>> tDup)

  tDup = R (tDup >>> unitI)
           (unitE >>> tJoin)

  unitI = R (unitI >>> unitI)
            (unitE >>> tangentMu >>> (tUnitE |><| id) >>> unitE)

  unitE = R (unitE >>> unitI)
            (unitE >>> (tangentMw <<< (tUnitI |><| id) <<< unitI))

  tUnitE = R (tUnitE >>> unitI)
             (unitE >>> tDup) -- Not wholly convinced by this

  tUnitI = R (tUnitI >>> unitI)
             (unitE >>> tJoin) -- Not wholly convinced by this

  comm = R (comm >>> unitI)
           (unitE >>> tangentMu >>> comm >>> tangentMw)

  inl = R (inl >>> unitI)
          undefined
