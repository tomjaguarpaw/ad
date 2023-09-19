{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module Main where

import Control.Arrow ((>>>))
import Data.Functor.Const (Const (Const, getConst))
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (Proxy))
import Prelude hiding (pi)

{- Section: Summary of the idea

The idea of this library is to take a sum type like

    data Sum arg1 ... argn = C1 t1 | ... | Cm tm

and generate a Sigma type that is isomorphic to it

    data SumTag = C1 | ... | Cm

    f = \case { C1 -> t1, ..., Cm -> tm }

    Sigma (c :: SumTag). f c

and to take a product type like

    data Sum arg1 ... argn = C t1 tm

and generate a Pi type that is isomorphic to it

    data ProductTag = F1 | ... | Fm

    f = \case { F1 -> t1, ..., Fm -> tm }

    Pi (t :: ProductTag). f t

(The isomorphisms are expressed in this library though sumToSigma,
sigmaToSum, productToPi and piToProduct.)

The hope is that it's easier to work generically with Sigma and Pi
types than arbitrary Haskell data definitions.  Of course, to code up
Sigma and Pi types in Haskell requires a fair bit of machinery, and
that's the bulk of this library!

-}

-- Section: User code

-- Currently this library works for types with multiple constructors
-- each with a single field ...
data Sum a b
  = A Int
  | B Bool
  | C a
  | D a
  | E b

-- ... or with a single constructor with multiple fields.
data Product a = Product Int Bool a

-- General ADTs are work-in-progress.  The work-in-progress is under
-- "Attempt at a nested version" below.
data SumOfProducts a b
  = SP1 a b
  | SP2
  | SP3 a
  | SP4 b
  | SP5 Char

-- We can obtain show generically!
showSum :: (Show a, Show b) => Sum a b -> String
showSum = genericShowSum

-- We can obtain show generically!
showProduct :: (Show a) => Product a -> String
showProduct = genericShowProduct

showSumOfProducts :: (Show a, Show b) => SumOfProducts a b -> String
showSumOfProducts = genericShowNested

main :: IO ()
main = do
  mapM_ (putStrLn . showSum) [A 1, B True, C 'x', D 'y', E ()]
  putStrLn (showProduct (Product 1 True 'x'))
  putStrLn (showSumOfProducts (SP1 True 'x'))
  putStrLn (showSumOfProducts @() @() SP2)
  putStrLn (showSumOfProducts @() @() (SP5 'y'))

-- Section: Generics library
data Sigma t f where
  Sigma :: forall t i f. (Known t i) => f i -> Sigma t f

data Dict c where Dict :: (c) => Dict c

class Known t (i :: t) | i -> t where
  know :: Singleton t i

knowProxy :: forall t i f. (Known t i) => f i -> Singleton t i
knowProxy _ = know @_ @i

-- | @Singleton t@ is the "singleton type" version of @t@
class Tag t where
  data Singleton t :: t -> Type

  -- | All the types of kind @t@
  type Tags t :: [t]

  data Pi t :: (t -> Type) -> Type

  getPi' :: forall (i :: t) (f :: t -> Type). Pi t f -> Singleton t i -> f i
  makePi :: (forall (i :: t). (Known t i) => f i) -> Pi t f

  knowns :: Singleton t i -> Dict (Known t i)

  traversePi ::
    forall (f :: t -> Type) (g :: t -> Type) m.
    (Applicative m) =>
    (forall (i :: t). Singleton t i -> f i -> m (g i)) ->
    Pi t f ->
    m (Pi t g)

  provideConstraint' ::
    (ForeachField (f :: FunctionSymbol t) c) =>
    Proxy c ->
    Proxy f ->
    Singleton t i ->
    ((c (FieldType f i)) => r) ->
    r

makePi' :: (Tag t) => (forall (i :: t). Singleton t i -> f i) -> Pi t f
makePi' f = makePi (f know)

getPi ::
  forall t (i :: t) (f :: t -> Type). (Known t i, Tag t) => Pi t f -> f i
getPi pi = getPi' pi know

-- Useful for obtaining @t@ without making it visible in signatures.
type FunctionSymbol :: Type -> Type
type FunctionSymbol t = Proxy t -> Type

-- This is a defunctionalized mapping from @t@ to @Type@, represented
-- by the function symbol @f@.  We need this defunctionalized version
-- because we can't partially apply type synonyms.
class FieldTypes (f :: FunctionSymbol t) where
  type FieldType' t f (i :: t) :: Type

-- Useful for passing @t@ implicitly, without bringing it into scope.
type FieldType :: FunctionSymbol t -> t -> Type
type FieldType (f :: FunctionSymbol t) i = FieldType' t f i

-- | @ForEachField f c@ means that for each @i@ of kind @t@,
-- @FieldType f i@ has an instance for @c@.
type ForeachField (f :: FunctionSymbol t) c =
  ForeachField' t f c (Tags t)

-- | The implementation of @ForeachField@
type family
  ForeachField' t (f :: FunctionSymbol t) c (ts :: [t]) ::
    Constraint
  where
  ForeachField' _ _ _ '[] = ()
  ForeachField' t f c (i : is) =
    (c (FieldType' t f i), ForeachField' t f c is)

-- | Witness to the property of @ForEachField@
provideConstraint ::
  forall c t (f :: FunctionSymbol t) r i.
  (Tag t) =>
  (ForeachField f c) =>
  Singleton t i ->
  ((c (FieldType f i)) => r) ->
  r
provideConstraint = provideConstraint' (Proxy @c) (Proxy @f)

-- | We can't partially apply type families so instead we
-- defunctionalize them to a symbol @f@ and then wrap them up in a
-- newtype for use when we do need to partially apply them.
type Newtyped :: forall t. FunctionSymbol t -> t -> Type
newtype Newtyped f i = Newtyped {getNewtyped :: FieldType f i}

mashPiSigma ::
  (Tag t) =>
  Pi t f1 ->
  Sigma t f2 ->
  (forall i. (Known t i) => f1 i -> f2 i -> r) ->
  r
mashPiSigma pi (Sigma f) k = k (getPi' pi know) f

traversePi_ ::
  (Applicative m, Tag t) =>
  (forall (i :: t). Singleton t i -> f i -> m ()) ->
  Pi t f ->
  m ()
-- This implementation could be better
traversePi_ f = fmap (const ()) . traversePi (\st -> fmap Const . f st)

toListPi :: (Tag t) => (forall (i :: t). Singleton t i -> f i -> a) -> Pi t f -> [a]
toListPi f = getConst . traversePi_ (\st x -> Const [f st x])

-- Sum types will (or could -- that isn't implemented yet) have an
-- instance of this class generated for them
class
  IsSum (sum :: Type) (sumf :: FunctionSymbol t)
    | sum -> sumf,
      sumf -> sum
  where
  sumConNames :: Pi t (Const String)
  sumToSigma :: sum -> Sigma t (Newtyped sumf)
  sigmaToSum :: Sigma t (Newtyped sumf) -> sum

-- Product types will (or could -- that isn't implemented yet) have an
-- instance of this class generated for them
class
  IsProduct (product :: Type) (productf :: FunctionSymbol t)
    | product -> productf,
      productf -> product
  where
  productConName :: String
  productToPi :: product -> Pi t (Newtyped productf)
  piToProduct :: Pi t (Newtyped productf) -> product

-- Section: Client of the generics library, between the generics
-- library and the user.  It provides a generic implementation of
-- Show.

showField ::
  forall t (f :: FunctionSymbol t) i.
  (Tag t, ForeachField f Show) =>
  Singleton t i ->
  Newtyped f i ->
  String
showField t = provideConstraint @Show @_ @f t show . getNewtyped

genericShowSum' ::
  forall t x (f :: FunctionSymbol t).
  (Tag t, ForeachField f Show) =>
  Pi t (Const String) ->
  (x -> Sigma t (Newtyped f)) ->
  x ->
  String
genericShowSum' pi f x = mashPiSigma pi (f x) $ \(Const conName) field ->
  conName ++ " " ++ showField know field

genericShowSum ::
  forall sum t (f :: FunctionSymbol t).
  (Tag t, IsSum sum f, ForeachField f Show) =>
  sum ->
  String
genericShowSum =
  genericShowSum' @_ @sum (sumConNames @_ @sum) sumToSigma

genericShowProduct' ::
  forall t x (f :: FunctionSymbol t).
  (ForeachField f Show, Tag t) =>
  String ->
  (x -> Pi t (Newtyped f)) ->
  x ->
  String
genericShowProduct' conName f x =
  conName ++ " " ++ unwords (toListPi showField (f x))

genericShowProduct ::
  forall product t (f :: FunctionSymbol t).
  (Tag t, IsProduct product f, ForeachField f Show) =>
  product ->
  String
genericShowProduct =
  genericShowProduct' @t (productConName @_ @product) productToPi

-- Section: Generated code.  The generics library could in principle
-- generate this, but that isn't implemented yet.

-- For data Sum

-- | One value for each constructor of the sum type
data SumTag = ATag | BTag | CTag | DTag | ETag

instance Known SumTag ATag where know = SATag

instance Known SumTag BTag where know = SBTag

instance Known SumTag CTag where know = SCTag

instance Known SumTag DTag where know = SDTag

instance Known SumTag ETag where know = SETag

instance Tag SumTag where
  data Singleton SumTag t where
    SATag :: Singleton SumTag ATag
    SBTag :: Singleton SumTag BTag
    SCTag :: Singleton SumTag CTag
    SDTag :: Singleton SumTag DTag
    SETag :: Singleton SumTag ETag

  knowns = \case
    SATag -> Dict
    SBTag -> Dict
    SCTag -> Dict
    SDTag -> Dict
    SETag -> Dict

  data Pi SumTag f = PiSSumTag (f ATag) (f BTag) (f CTag) (f DTag) (f ETag)
  type Tags SumTag = [ATag, BTag, CTag, DTag, ETag]
  getPi' (PiSSumTag f1 f2 f3 f4 f5) = \case
    SATag -> f1
    SBTag -> f2
    SCTag -> f3
    SDTag -> f4
    SETag -> f5
  makePi f = PiSSumTag f f f f f

  traversePi f (PiSSumTag a b c d e) =
    PiSSumTag <$> f know a <*> f know b <*> f know c <*> f know d <*> f know e

  provideConstraint' = \_ _ -> \case
    SATag -> \r -> r
    SBTag -> \r -> r
    SCTag -> \r -> r
    SDTag -> \r -> r
    SETag -> \r -> r

-- | A symbol used so that we can defunctionalize the mapping
-- @SumFamily@
data SumF (a :: Type) (b :: Type) (t :: Proxy SumTag)

instance FieldTypes (SumF a b) where
  type FieldType' _ (SumF a b) t = SumFamily a b t

type family SumFamily (a :: Type) (b :: Type) (t :: SumTag) :: Type where
  SumFamily _ _ ATag = Int
  SumFamily _ _ BTag = Bool
  SumFamily a _ CTag = a
  SumFamily a _ DTag = a
  SumFamily _ b ETag = b

instance IsSum (Sum a b) (SumF a b) where
  sumConNames =
    makePi' $
      Const . \case
        SATag -> "A"
        SBTag -> "B"
        SCTag -> "C"
        SDTag -> "D"
        SETag -> "E"

  sumToSigma = \case
    A p -> Sigma @_ @ATag (Newtyped p)
    B p -> Sigma @_ @BTag (Newtyped p)
    C p -> Sigma @_ @CTag (Newtyped p)
    D p -> Sigma @_ @DTag (Newtyped p)
    E p -> Sigma @_ @ETag (Newtyped p)

  sigmaToSum = \case
    Sigma (f@(getNewtyped -> p)) -> case knowProxy f of
      SATag -> A p
      SBTag -> B p
      SCTag -> C p
      SDTag -> D p
      SETag -> E p

-- For data Product

-- One value for each constructor of the product type
data ProductTag = Field1 | Field2 | Field3

instance Known ProductTag Field1 where know = SField1

instance Known ProductTag Field2 where know = SField2

instance Known ProductTag Field3 where know = SField3

instance Tag ProductTag where
  data Singleton ProductTag t where
    SField1 :: Singleton ProductTag Field1
    SField2 :: Singleton ProductTag Field2
    SField3 :: Singleton ProductTag Field3

  knowns = \case
    SField1 -> Dict
    SField2 -> Dict
    SField3 -> Dict

  data Pi ProductTag f = PiSProductTag (f Field1) (f Field2) (f Field3)
  type Tags ProductTag = [Field1, Field2, Field3]

  getPi' (PiSProductTag f1 f2 f3) = \case
    SField1 -> f1
    SField2 -> f2
    SField3 -> f3
  makePi f = PiSProductTag f f f

  traversePi f (PiSProductTag f1 f2 f3) =
    PiSProductTag <$> f know f1 <*> f know f2 <*> f know f3

  provideConstraint' = \_ _ -> \case
    SField1 -> \r -> r
    SField2 -> \r -> r
    SField3 -> \r -> r

-- | A symbol used so that we can defunctionalize the mapping
-- @ProductFamily@
data ProductF (a :: Type) (t :: Proxy ProductTag)

instance FieldTypes (ProductF a) where
  type FieldType' _ (ProductF a) t = ProductFamily a t

type family ProductFamily (a :: Type) (t :: ProductTag) :: Type where
  ProductFamily _ Field1 = Int
  ProductFamily _ Field2 = Bool
  ProductFamily a Field3 = a

instance IsProduct (Product a) (ProductF a) where
  productConName = "Product"
  productToPi (Product f1 f2 f3) =
    makePi'
      ( Newtyped . \case
          SField1 -> f1
          SField2 -> f2
          SField3 -> f3
      )

  piToProduct pi =
    Product (getField @Field1) (getField @Field2) (getField @Field3)
    where
      getField :: forall i. (Known ProductTag i) => ProductFamily a i
      getField = getNewtyped (getPi @_ @i pi)

-- Attempt at a nested version

-- Trying to promote constructors of non-uniform (or
-- "non-parametric"?) data types is a mess.  This is the only way I've
-- come up with.  For more details see
--
-- https://mail.haskell.org/pipermail/haskell-cafe/2023-September/136341.html

data NestedProductATag = NA1 | NA2

data NestedProductBTag

data NestedProductCTag = NC1

data NestedProductDTag = ND1

data NestedProductETag = NE1

type family NestedProductTagF a where
  NestedProductTagF ATag = NestedProductATag
  NestedProductTagF BTag = NestedProductBTag
  NestedProductTagF CTag = NestedProductCTag
  NestedProductTagF DTag = NestedProductDTag
  NestedProductTagF ETag = NestedProductETag

type NestedProductTag :: SumTag -> Type
newtype NestedProductTag (a :: SumTag)
  = NestedProductTag (NestedProductTagF a)

type SNestedProductATag :: NestedProductTag ATag -> Type
data SNestedProductATag a where
  SNA1 :: SNestedProductATag ('NestedProductTag NA1)
  SNA2 :: SNestedProductATag ('NestedProductTag NA2)

type SNestedProductBTag :: NestedProductTag BTag -> Type
data SNestedProductBTag a

type SNestedProductCTag :: NestedProductTag CTag -> Type
data SNestedProductCTag a where
  SNC1 :: SNestedProductCTag ('NestedProductTag NC1)

type SNestedProductDTag :: NestedProductTag DTag -> Type
data SNestedProductDTag a where
  SND1 :: SNestedProductDTag ('NestedProductTag ND1)

type SNestedProductETag :: NestedProductTag ETag -> Type
data SNestedProductETag a where
  SNE1 :: SNestedProductETag ('NestedProductTag NE1)

type SNestedProductTagF :: forall (a :: SumTag) -> NestedProductTag a -> Type
type family SNestedProductTagF a where
  SNestedProductTagF ATag = SNestedProductATag
  SNestedProductTagF BTag = SNestedProductBTag
  SNestedProductTagF CTag = SNestedProductCTag
  SNestedProductTagF DTag = SNestedProductDTag
  SNestedProductTagF ETag = SNestedProductETag

instance Known (NestedProductTag ATag) ('NestedProductTag NA1) where
  know = SNestedProductTag SNA1

instance Known (NestedProductTag ATag) ('NestedProductTag NA2) where
  know = SNestedProductTag SNA2

instance Known (NestedProductTag CTag) ('NestedProductTag NC1) where
  know = SNestedProductTag SNC1

instance Known (NestedProductTag DTag) ('NestedProductTag ND1) where
  know = SNestedProductTag SND1

instance Known (NestedProductTag ETag) ('NestedProductTag NE1) where
  know = SNestedProductTag SNE1

type TheTags :: forall (a :: SumTag) -> [NestedProductTag a]
type family TheTags a where
  TheTags ATag = '[ 'NestedProductTag NA1, 'NestedProductTag NA2]
  TheTags BTag = '[]
  TheTags CTag = '[ 'NestedProductTag NC1]
  TheTags DTag = '[ 'NestedProductTag ND1]
  TheTags ETag = '[ 'NestedProductTag NE1]

type ThePi :: forall (a :: SumTag) -> (NestedProductTag a -> Type) -> Type
type family ThePi a b where
  ThePi ATag f = (f ('NestedProductTag NA1), f ('NestedProductTag NA2))
  ThePi BTag f = ()
  ThePi CTag f = f ('NestedProductTag NC1)
  ThePi DTag f = f ('NestedProductTag ND1)
  ThePi ETag f = f ('NestedProductTag NE1)

instance (Known SumTag a) => Tag (NestedProductTag a) where
  newtype Singleton (NestedProductTag a) i = SNestedProductTag {unSNestedProductTag :: SNestedProductTagF a i}

  type Tags (NestedProductTag a) = TheTags a

  data Pi (NestedProductTag a) f = NestedPi {unNestedPi :: ThePi a f}

  getPi' =
    unNestedPi
      >>> fmap
        (. unSNestedProductTag)
        ( case know @_ @a of
            SATag -> \(thePi1, thePi2) -> \case
              SNA1 -> thePi1
              SNA2 -> thePi2
            SBTag -> \() -> \case {}
            SCTag -> \thePi -> \case SNC1 -> thePi
            SDTag -> \thePi -> \case SND1 -> thePi
            SETag -> \thePi -> \case SNE1 -> thePi
        )

  knowns =
    unSNestedProductTag >>> case know @_ @a of
      SATag -> \case
        SNA1 -> Dict
        SNA2 -> Dict
      SBTag -> \case {}
      SCTag -> \case SNC1 -> Dict
      SDTag -> \case SND1 -> Dict
      SETag -> \case SNE1 -> Dict

  makePi x = NestedPi $ case know @_ @a of
    SATag -> (x, x)
    SBTag -> ()
    SCTag -> x
    SDTag -> x
    SETag -> x

  traversePi f = traverseNestedPi $ case know @_ @a of
    SATag -> \(thePi1, thePi2) ->
      (,) <$> f know thePi1 <*> f know thePi2
    SBTag -> pure
    SCTag -> f know
    SDTag -> f know
    SETag -> f know
    where
      traverseNestedPi g (NestedPi thePi) =
        NestedPi <$> g thePi

  provideConstraint' = \_ _ -> case know @_ @a of
    SATag -> \case
      SNestedProductTag SNA1 -> \r -> r
      SNestedProductTag SNA2 -> \r -> r
    SBTag -> \case SNestedProductTag a -> case a of {}
    SCTag -> \case SNestedProductTag SNC1 -> \r -> r
    SDTag -> \case SNestedProductTag SND1 -> \r -> r
    SETag -> \case SNestedProductTag SNE1 -> \r -> r

-- Wow, this WrapPi/BetterConst stuff is some deep magic
type WrapPi ::
  forall (t :: Type).
  forall (f :: t -> Type) ->
  (forall (z :: t). f z -> Type) ->
  t ->
  Type
newtype WrapPi f k s = WrapPi (Pi (f s) k)

type BetterConst :: forall f. Type -> forall z. f z -> Type
newtype BetterConst t x = BetterConst t

foo :: Sigma SumTag (WrapPi NestedProductTag (BetterConst String))
foo =
  Sigma @_ @ATag
    ( WrapPi
        ( makePi'
            ( \(st :: Singleton (NestedProductTag ATag) i) ->
                case knowns st of
                  Dict ->
                    case know @_ @i of
                      SNestedProductTag SNA1 -> BetterConst "SNA1"
                      SNestedProductTag SNA2 -> BetterConst "SNA2"
            )
        )
    )

-- | A symbol used so that we can defunctionalize the mapping
-- @SumFamily@
data SumOfProductsF (a :: Type) (b :: Type) (s :: SumTag) (t :: Proxy (NestedProductTag s))

-- Do I need to generalise this?
instance FieldTypes (SumOfProductsF a b s) where
  type FieldType' _ (SumOfProductsF a b s) t = SumOfProductsFamily a b s t

type SumOfProductsFamily :: Type -> Type -> forall (s :: SumTag) -> NestedProductTag s -> Type
type family SumOfProductsFamily (a :: Type) (b :: Type) (s :: SumTag) (t :: NestedProductTag s) :: Type where
  SumOfProductsFamily a _ ATag ('NestedProductTag NA1) = a
  SumOfProductsFamily _ b ATag ('NestedProductTag NA2) = b
  SumOfProductsFamily a _ CTag ('NestedProductTag NC1) = a
  SumOfProductsFamily _ b DTag ('NestedProductTag ND1) = b
  SumOfProductsFamily _ _ ETag ('NestedProductTag NE1) = Char

type Newtyped2 :: Type -> Type -> forall (s :: SumTag). NestedProductTag s -> Type
newtype Newtyped2 a b (i :: NestedProductTag s) = Newtyped2 {getNewtyped2 :: SumOfProductsFamily a b s i}

type ForeachTopField a b c = ForeachTopField' a b c (Tags SumTag)

type ForeachTopField' ::
  Type -> Type -> (Type -> Constraint) -> [SumTag] -> Constraint
type family ForeachTopField' a b c ts where
  ForeachTopField' _ _ _ '[] = ()
  ForeachTopField' a b c (t : ts) =
    (ForeachNestedField a b c t, ForeachTopField' a b c ts)

type ForeachNestedField a b c s =
  ForeachNestedField' a b c s (Tags (NestedProductTag s))

type ForeachNestedField' ::
  Type ->
  Type ->
  (Type -> Constraint) ->
  forall (s :: SumTag) ->
  [NestedProductTag s] ->
  Constraint
type family ForeachNestedField' a b c s ns where
  ForeachNestedField' _ _ _ _ '[] = ()
  ForeachNestedField' a b c s (n : ns) =
    (c (SumOfProductsFamily a b s n), ForeachNestedField' a b c s ns)

provideConstraintNested ::
  forall a b c (s :: SumTag) (n :: NestedProductTag s) r.
  (Known SumTag s) =>
  (ForeachTopField a b c) =>
  Singleton (NestedProductTag s) n ->
  ((c (SumOfProductsFamily a b s n)) => r) ->
  r
provideConstraintNested s = case know @_ @s of
  SATag -> case s of
    SNestedProductTag SNA1 -> \r -> r
    SNestedProductTag SNA2 -> \r -> r
  SBTag -> case s of {}
  SCTag -> case s of
    SNestedProductTag SNC1 -> \r -> r
  SDTag -> case s of
    SNestedProductTag SND1 -> \r -> r
  SETag -> case s of
    SNestedProductTag SNE1 -> \r -> r

genericShow' ::
  forall a b x.
  (ForeachTopField a b Show) =>
  Pi SumTag (Const String) ->
  (x -> Sigma SumTag (WrapPi NestedProductTag (Newtyped2 a b))) ->
  x ->
  String
genericShow' pi f x = mashPiSigma pi (f x) $ \(Const conName) (WrapPi fields) ->
  conName
    ++ " "
    ++ unwords
      ( toListPi
          ( \(su :: Singleton (NestedProductTag s) n) ->
              provideConstraintNested @a @b @Show su show . getNewtyped2
          )
          fields
      )

genericShowNested :: (Show a, Show b) => SumOfProducts a b -> String
genericShowNested =
  genericShow' sumOfProductsConNames sumOfProductsToSigmaOfPi

sumOfProductsConNames :: Pi SumTag (Const String)
sumOfProductsConNames =
  makePi' $
    Const . \case
      SATag -> "SP1"
      SBTag -> "SP2"
      SCTag -> "SP3"
      SDTag -> "SP4"
      SETag -> "SP5"

sumOfProductsToSigmaOfPi ::
  forall a b.
  SumOfProducts a b ->
  Sigma SumTag (WrapPi NestedProductTag (Newtyped2 a b))
sumOfProductsToSigmaOfPi = \case
  SP1 a b ->
    Sigma
      ( WrapPi
          ( makePi'
              ( \(st :: Singleton (NestedProductTag ATag) i) ->
                  case knowns st of
                    Dict ->
                      case know @_ @i of
                        SNestedProductTag SNA1 -> Newtyped2 a
                        SNestedProductTag SNA2 -> Newtyped2 b
              )
          )
      )
  SP2 ->
    Sigma
      ( WrapPi
          ( makePi'
              ( \(st :: Singleton (NestedProductTag BTag) i) ->
                  case knowns st of
                    Dict ->
                      case know @_ @i of {}
              )
          )
      )
  SP3 a ->
    Sigma
      ( WrapPi
          ( makePi'
              ( \(st :: Singleton (NestedProductTag CTag) i) ->
                  case knowns st of
                    Dict ->
                      case know @_ @i of
                        SNestedProductTag SNC1 -> Newtyped2 a
              )
          )
      )
  SP4 a ->
    Sigma
      ( WrapPi
          ( makePi'
              ( \(st :: Singleton (NestedProductTag DTag) i) ->
                  case knowns st of
                    Dict ->
                      case know @_ @i of
                        SNestedProductTag SND1 -> Newtyped2 a
              )
          )
      )
  SP5 a ->
    Sigma
      ( WrapPi
          ( makePi'
              ( \(st :: Singleton (NestedProductTag ETag) i) ->
                  case knowns st of
                    Dict ->
                      case know @_ @i of
                        SNestedProductTag SNE1 -> Newtyped2 a
              )
          )
      )
