{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-} --  Try to get rid of this
{-# LANGUAGE NoMonomorphismRestriction #-}

import Control.Applicative (liftA2)
import Control.Category
import Data.Functor.Identity (Identity(Identity), runIdentity)
import Data.Tuple (swap)
import Prelude hiding (id, (.), (>>))

class Category arr => Monoidal arr m where
  (|><|) :: arr a1 b1
         -> arr a2 b2
         -> arr (m a1 a2)
                (m b1 b2)

class Category arr => T (arr :: k -> k -> *) s p tv | arr -> s p tv where
  sPush :: tv (s a b) `arr` s (tv a) (tv b)
  pPush :: tv (p a b) `arr` p (tv a) (tv b)
  flipT :: (a `arr` b) -> (b `arr` a)

class Monoidal arr m => C (arr :: k -> k -> *) (varr :: ty -> ty -> *)
  (v :: ty -> k) (m :: k -> k -> k) (_1 :: k) (t :: k -> k) (tv :: ty -> ty)
  | arr -> varr v m _1 t tv where
  arrV  :: (a `varr` b) -> (v a `arr` v b)
  arrTa :: (a `arr` b) -> (t a `arr` t b)
  flipC :: (a `arr` b) -> (b `arr` a)

  assoc :: m (m a b) c `arr` m a (m b c)

  tPush :: t (a `m` b) `arr` (t a `m` t b)
  tJoin :: t (t a) `arr` t a

  tVar :: t (v a) `arr` v (tv a)

  tUnit :: t _1 `arr` _1

  unit :: a `arr` (_1 `m` a)

  comm :: m a b `arr` m b a

class Monoidal arr m
  => O (arr :: c -> c -> *) tarr m (_1 :: c) (v :: ty -> c)
       (s :: ty -> ty -> ty) (p :: ty -> ty -> ty) (t :: c -> c)
       (u :: ty) (tv :: ty -> ty) (f :: ty)
  | arr -> tarr m v s p _1 t u tv f
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

  scale :: (v f `m` v (tv a)) `arr` v (tv a)

  dot :: (v (tv a) `m` v (tv a)) `arr` v f

  plus :: (v f `m` v f) `arr` v f

  times :: (v f `m` v f) `arr` v f

foo :: (C tarr varr v m _1 t tv, O arr tarr m _1 v s p t u tv f)
    => arr a1 z
    -> arr z a2
    -> arr (b1 `m` c1) (b2 `m` c2)
    -> arr ((a1 `m` b1) `m` c1) ((a2 `m` b2) `m` c2)
foo l m r = arrT assoc >>> ((l >>> m) |><| r) >>> arrT (flipC assoc)

data R arr (tarr :: * -> * -> *) m _1
       (v :: * -> *) (s :: * -> * -> *) (p :: * -> * -> *) t
       (u :: *) (tv :: * -> *) f a b =
  forall r. R (a `arr` (v r `m` b)) ((v r `m` t b) `arr` t a)

instance (C tarr varr v m _1 t tv, O arr tarr m _1 v s p t u tv f)
  => Category (R arr tarr m _1 v s p t u tv f) where
  id = R bling blong

  f . g = case f of
    R f1 f2 -> case g of
      R g1 g2 ->
        R ((pair |><| id) <<< arrT (flipC assoc) <<< (id |><| f1) <<< g1)
          ((unpair |><| id) >>> arrT assoc >>> (id |><| f2) >>> g2)

instance (C tarr varr v m _1 t tv, O arr tarr m _1 v s p t u tv f)
  => Monoidal (R arr tarr m _1 v s p t u tv f) m where
  f |><| g = case f of
    R f1 f2 -> case g of
      R g1 g2 ->
        R ((f1 |><| g1)
           >>> arrT ((comm |><| id)
                     >>> assoc
                     >>> (id |><| flipC assoc)
                     >>> flipC assoc
                     >>> (comm |><| id)
                     >>> assoc)
           >>> (pair |><| id))
          (arrT (flipC tPush)
           <<< (f2 |><| g2)
           <<< blah)

blah :: (C tarr varr v m _1 t tv, O arr tarr m _1 v s p t u tv f)
    => ((v (r1 `p` r2)) `m` (t (a `m` b)))
        `arr` ((v r1 `m` t a) `m` (v r2 `m` (t b)))
blah = arrT (flipC ((comm |><| id)
                     >>> assoc
                     >>> (id |><| flipC assoc)
                     >>> flipC assoc
                     >>> (comm |><| id)
                     >>> assoc))
           <<< (unpair |><| arrT tPush)

bling :: (O arr tarr m _1 v s p t u tv f, C tarr varr v m _1 t tv)
      => a `arr` (v u `m` a)
bling = arrT unit >>> (unitT |><| id)

blong :: (O arr tarr m _1 v s p t u tv f, C tarr varr v m _1 t tv)
      => (v u `m` a) `arr` a
blong = (ignore |><| id) >>> arrT (flipC unit)

instance (O arr tarr m _1 v s p t u tv f,
          C tarr varr v m _1 t tv, T varr s p tv)
  => O (R arr tarr m _1 v s p t u tv f) tarr m _1 v s p t u tv f where
  arrT f = R (arrT f >>> bling)
             (blong >>> arrT (flipC (arrTa f)))

  inl = R (inl >>> bling)
          (blong >>> bar >>> baz >>> quux)

  inr = R (inr >>> bling)
          (blong >>> bar >>> bazFlip >>> quux)

  ignore = R (ignore >>> bling)
             (blong >>> arrT tUnit >>> zero)

  pair = R (pair >>> bling)
           (blong >>> flub)

  unpair = R (unpair >>> bling)
             (blong >>> flib)

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

  plus = R (plus >>> bling) (arrT (flipC tPush) <<< dup <<< blong)

  scale = R (flab >>> (pair |><| scale))
            undefined

  dot = R (flab >>> (pair |><| dot))
            undefined

  times = R (flab >>> (pair |><| times))
            undefined

flab :: (O arr tarr m _1 v s p t u tv f, C tarr varr v m _1 t tv, T varr s p tv)
     => arr (m a1 a2) (m (m a1 a2) (m a1 a2))
flab = (dup |><| dup)
       >>> arrT assoc
       >>> (id |><| arrT (flipC assoc))
       >>> (id |><| arrT comm)
       >>> arrT (flipC assoc)

flub :: (O arr tarr m _1 v s p t u tv f, C tarr varr v m _1 t tv, T varr s p tv)
     => t (v (p a b)) `arr` t (v a `m` v b)
flub = arrT (tVar >>> arrV pPush)
       >>> unpair
       >>> arrT (flipC ((tVar |><| tVar) <<< tPush))

flib :: (O arr tarr m _1 v s p t u tv f, C tarr varr v m _1 t tv, T varr s p tv)
     => t (v a `m` v b) `arr` t (v (p a b))
flib = arrT (tPush >>> (tVar |><| tVar))
       >>> pair
       >>> arrT (flipC (arrV pPush <<< tVar))

bar :: (O arr tarr m _1 v s p t u tv f, C tarr varr v m _1 t tv, T varr s p tv)
    => (t (v (s a b))) `arr` (_1 `m` (v (s (tv a) (tv b))))
bar = arrT (tVar >>> arrV sPush >>> unit)

baz :: (O arr tarr m _1 v s p t u tv f, C tarr varr v m _1 t tv)
    => (_1 `m` (v (s (tv a) (tv b)))) `arr` v (tv a)
baz = caseS (arrT (flipC unit))
            (ignore >>> zero >>> arrT tVar)

bazFlip :: (O arr tarr m _1 v s p t u tv f, C tarr varr v m _1 t tv)
        => (_1 `m` (v (s (tv a) (tv b)))) `arr` v (tv b)
bazFlip = caseS (ignore >>> zero >>> arrT tVar)
                (arrT (flipC unit))

quux :: (O arr tarr m _1 v s p t u tv f, C tarr varr v m _1 t tv)
     => v (tv a) `arr` t (v a)
quux = arrT (flipC tVar)

runR :: (C tarr varr v m _1 t tv,
         O arr tarr m _1 v s p t u tv f)
     => R arr tarr m _1 v s p t u tv f a b
     -> arr (a `m` t b) (t a `m` b)
runR (R f g) = (f |><| id)
               >>> arrT assoc
               >>> (id |><| arrT comm)
               >>> arrT (flipC assoc)
               >>> (g |><| id)

data Hask a b = Hask { runHask :: a -> b }

data HaskId a b = HaskId { hi :: Hask a b, hiFlip :: Hask b a }

flipIso :: HaskId a b -> HaskId b a
flipIso f = HaskId (hiFlip f) (hi f)

data Ty = F | U | S Ty Ty | P Ty Ty | Tangent Ty

data TyI a where
  TyIF  :: Float -> TyI 'F
  TyIU  :: TyI 'U
  TyIS  :: Either (TyI a) (TyI b) -> TyI ('S a b)
  TyIP  :: (TyI a, TyI b) -> TyI ('P a b)
  TyITF :: Float -> TyI ('Tangent 'F)
  TyITU :: TyI ('Tangent 'U)
  TyITS :: Either (TyI ('Tangent a)) (TyI ('Tangent b))
        -> TyI ('Tangent ('S a b))
  TyITP :: (TyI ('Tangent a), TyI ('Tangent b)) -> TyI ('Tangent ('P a b))
  TyITT :: TyI ('Tangent a) -> TyI ('Tangent ('Tangent a))

tyToTangent :: TyI a -> TyI ('Tangent a)
tyToTangent = \case
  TyIF f -> TyITF f
  TyIU   -> TyITU
  TyIS e -> TyITS $ case e of
    Left l  -> Left (tyToTangent l)
    Right r -> Right (tyToTangent r)
  TyIP (p1, p2) -> TyITP (tyToTangent p1, tyToTangent p2)
  TyITF t -> TyITT (TyITF t)
  TyITU   -> TyITT (TyITU)
  TyITS t -> TyITT (TyITS t)
  TyITP t -> TyITT (TyITP t)
  TyITT t -> TyITT (TyITT t)

tyFromTangent :: TyI ('Tangent a) -> TyI a
tyFromTangent = \case
  TyITF f -> TyIF f
  TyITU   -> TyIU
  TyITS e -> case e of
    Left l  -> TyIS (Left (tyFromTangent l))
    Right l -> TyIS (Right (tyFromTangent l))
  TyITP (p1, p2) -> TyIP (tyFromTangent p1, tyFromTangent p2)
  TyITT e -> e

data Ctx ty = CU | CTy ty | CP (Ctx ty) (Ctx ty) | CTangent (Ctx ty)

data CtxI c where
  CtxU  :: CtxI 'CU
  CtxTy :: TyI ty -> CtxI ('CTy ty)
  CtxP  :: (CtxI c1, CtxI c2) -> CtxI ('CP c1 c2)
  CtxTangent :: CtxI ctx -> CtxI ('CTangent ctx)

data TyT a = TyT { unTyT :: TyI ('Tangent a) }

data FArr f a b = FArr { runFArr :: f a -> f b }

data IdC arr a b = IdC { idC :: a `arr` b, idCFlip :: b `arr` a }

instance Category (FArr f) where
  id = FArr id
  f . g = FArr (runFArr f . runFArr g)

instance Category arr => Category (IdC arr) where
  id = IdC id id
  f . g = IdC (idC f <<< idC g)
              (idCFlip f >>> idCFlip g)

type TyHask = FArr TyI
type TyHaskId = IdC TyHask

instance Category Hask where
  id = Hask id
  f . g = Hask (runHask f . runHask g)

instance Category HaskId where
  id = HaskId id id
  f . g = HaskId (hi f <<< hi g) (hiFlip f >>> hiFlip g)

instance Monoidal Hask (,) where
  f |><| g = Hask (\(a, b) -> (runHask f a, runHask g b))

instance Monoidal HaskId (,) where
  f |><| g = HaskId (hi f |><| hi g) (hiFlip f |><| hiFlip g)

instance T TyHaskId 'S 'P 'Tangent where
  sPush = IdC (FArr (\case (TyITS e) -> TyIS e))
              (FArr (\case (TyIS e) -> TyITS e))
  pPush = IdC (FArr (\case (TyITP e) -> TyIP e))
              (FArr (\case (TyIP e) -> TyITP e))
  flipT x = IdC (idCFlip x) (idC x)

instance Monoidal (IdC (FArr CtxI)) 'CP where
  f |><| g =
    IdC (FArr $ \(CtxP (a1, a2)) ->
            CtxP (runFArr (idC f) a1, runFArr (idC g) a2))
        (FArr $ \(CtxP (a1, a2)) ->
            CtxP (runFArr (idCFlip f) a1, runFArr (idCFlip g) a2))

instance C (IdC (FArr CtxI)) TyHaskId 'CTy 'CP 'CU 'CTangent 'Tangent where
  arrV x = IdC (FArr $ \case (CtxTy e) -> CtxTy (runFArr (idC x) e))
               (FArr $ \case (CtxTy e) -> CtxTy (runFArr (idCFlip x) e))

  arrTa x = IdC
    (FArr $ \case (CtxTangent e) -> CtxTangent (runFArr (idC x) e))
    (FArr $ \case (CtxTangent e) -> CtxTangent (runFArr (idCFlip x) e))

  flipC x = IdC (idCFlip x) (idC x)

  assoc = IdC (FArr $ \case (CtxP (CtxP (a, b), c)) -> CtxP (a, CtxP (b, c)))
              (FArr $ \case CtxP (a, CtxP (b, c)) -> (CtxP (CtxP (a, b), c)))

  tJoin = IdC (FArr $ \case CtxTangent a -> a)
              (FArr $ \case a -> CtxTangent a)

  tVar = IdC (FArr $ \case CtxTangent (CtxTy e) -> CtxTy (tyToTangent e))
             (FArr $ \case CtxTy ty -> CtxTangent (CtxTy (tyFromTangent ty)))
{-

  tJoin = HaskId undefined undefined

  tVar = undefined

  tUnit = HaskId (Hask (const ()))
                 (Hask TangentUnit)

  unit = HaskId (Hask (\x -> (((), x)))) (Hask (\((), x) -> x))

  comm = HaskId (Hask swap) (Hask swap)

instance O Hask HaskId (,) () Identity Either (,) Identity () Identity Float
    where
  arrT = hi

  inl = Hask (fmap Left)

  inr = Hask (fmap Right)

  ignore = Hask (const ())

  unitT = Hask (const (Identity ()))

  pair = Hask (uncurry (liftA2 (,)))
  unpair = Hask (\(Identity (x, y)) -> (Identity x, Identity y))

  caseS f g = Hask $ \(ci, e) -> case runIdentity e of
    Left l  -> runHask f (ci, Identity l)
    Right r -> runHask g (ci, Identity r)

  dup = Hask (\x -> (x, x))

  plus  = Hask (uncurry (liftA2 (+)))
  times = Hask (uncurry (liftA2 (*)))

--  pPush = Hask runIdentity >>> \(x, y) -> (Identity x, Identity y))
-}
