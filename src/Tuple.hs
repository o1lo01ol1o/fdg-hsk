{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS -Wall -fno-warn-unticked-promoted-constructors -fno-warn-missing-signatures #-}
module Tuple () where
import Data.Distributive
import Data.Key hiding (lookup)
import NumHask.Array (Array(..))
import Data.Singletons.Prelude (SingI(..))
import NumHask.Prelude as P hiding (Shape, Down, Up, SingI)
import Prelude hiding (lookup, Nat)


import Control.Applicative (liftA2)


data family Sing (x :: k)

class KnownSing x where
  knownSing :: Sing x

data instance  Sing (xs :: [k]) where
        SNil :: Sing '[]
        SCons :: Sing x -> Sing xs -> Sing (x ': xs)

instance KnownSing '[] where
  knownSing = SNil

instance (KnownSing x, KnownSing xs) => KnownSing (x ': xs) where
  knownSing = SCons knownSing knownSing

data Direction
  = Up
  | Down

data Shape = ShElem [P.Nat] | ShTuple Direction [Shape]

data instance  Sing (gs :: Direction) where
        SUp :: Sing Up
        SDown :: Sing Down

instance KnownSing Up where
  knownSing = SUp

instance KnownSing Down where
  knownSing = SDown

deriving instance Show (Sing (d :: Direction))

data instance  Sing (shape :: Shape) where
        SShElem :: Sing (ShElem ns)
        SShTuple :: Sing d -> Sing shapes -> Sing (ShTuple d shapes)

instance KnownSing (ShElem ns) where
  knownSing = SShElem 

instance (KnownSing d, KnownSing shapes) => KnownSing (ShTuple d shapes) where
  knownSing = SShTuple knownSing knownSing

data TupleTree shape a where
  Elem :: (SingI ns) => Array ns a -> TupleTree (ShElem ns) a
  Tuple :: Sing d -> TupleForest shapes a -> TupleTree (ShTuple d shapes) a

deriving instance Functor (TupleTree shape)
deriving instance Show a => Show (TupleTree shape a)

-- applyTupleTree ::
--      TupleTree shape (a -> b) -> TupleTree shape a -> TupleTree shape b
-- applyTupleTree =
--   \case
--     Elem f ->
--       \case
--         Elem x -> Elem (f x)
--     Tuple d forest1 ->
--       \case
--         Tuple _ forest2 -> Tuple d (forest1 `applyTupleForest` forest2)

-- pureTupleTree :: Sing shape -> Array ns b -> TupleTree shape a
-- pureTupleTree =
--   \case
--     SShElem -> Elem 
--     SShTuple d shapes -> \a -> Tuple d (pureTupleForest shapes a)

-- instance KnownSing shape => Applicative (TupleTree shape) where
--   (<*>) = applyTupleTree
--   pure = pureTupleTree knownSing

--have to make int -> Sing functions to implment index since Rep family only has access to shape and not subshape needed by indexes.
--probably need those existential closures to prove the int is in bounds

instance Keyed (TupleTree shape) where
    mapWithKey = mapWithKeyRep

instance KnownSing shape => Indexable (TupleTree shape) where
    index = lookup

instance KnownSing shape => Distributive (TupleTree shape) where
    distribute = distributeRep

instance KnownSing shape => Representable (TupleTree shape) where
    type Rep (TupleTree shape) = [Int]
    tabulate f = case knownSing :: Sing shape of
       SShElem -> tabulate f

data TupleForest shapes a where
  ForestNil :: TupleForest '[] a
  ForestCons
    :: TupleTree shape a
    -> TupleForest shapes a
    -> TupleForest (shape ': shapes) a

infixr `ForestCons`

deriving instance Functor (TupleForest shapes)
deriving instance Show a => Show (TupleForest shape a)

-- applyTupleForest ::
--      TupleForest shape (a -> b) -> TupleForest shape a -> TupleForest shape b
-- applyTupleForest =
--   \case
--     ForestNil ->
--       \case
--         ForestNil -> ForestNil
--     ForestCons t1 ts1 ->
--       \case
--         ForestCons t2 ts2 ->
--           ForestCons (t1 `applyTupleTree` t2) (ts1 `applyTupleForest` ts2)

-- pureTupleForest :: Sing shapes -> a -> TupleForest shapes a
-- pureTupleForest =
--   \case
--     SNil -> pure ForestNil
--     SCons x xs -> ForestCons <$> pureTupleTree x <*> pureTupleForest xs

-- instance KnownSing shapes => Applicative (TupleForest shapes) where
--   (<*>) = applyTupleForest
--   pure = pureTupleForest knownSing

-- instance (Num a, KnownSing shape) => Num (TupleTree shape a) where
--   negate      = fmap P.negate
--   (+)         = liftA2 (P.+)
--   (*)         = liftA2 (P.*)
--   fromInteger = pure . P.fromInteger
--   abs         = fmap P.abs
--   signum      = fmap signum

type ExampleShape
   = ShTuple Up '[ ShElem '[1,2,3], ShTuple Up '[ ShElem '[1,2], ShElem '[1]], ShTuple Down '[ ShElem '[1,2,34], ShElem '[1,2]]]

-- example :: TupleTree ExampleShape String
-- example =
--   Tuple
--     SUp
--     (Elem "t" `ForestCons`
--      Tuple SUp (Elem "x" `ForestCons` Elem "y" `ForestCons` ForestNil) `ForestCons`
--      Tuple SDown (Elem "p_x" `ForestCons` Elem "p_y" `ForestCons` ForestNil) `ForestCons`
--      ForestNil)

data TreeIndex shape subshape where
  IxNil :: TreeIndex shape shape
  IxCons
    :: ForestIndex shapes subshape
    -> TreeIndex subshape subsubshape
    -> TreeIndex (ShTuple d shapes) subsubshape

infixr `IxCons`

data ForestIndex shapes subshape where
  IxZ :: ForestIndex (shape ': shapes) shape
  IxS :: ForestIndex shapes subshape -> ForestIndex (shape ': shapes) subshape

exampleIx0 = IxZ `IxCons` IxNil
exampleIx1 = IxS IxZ `IxCons` IxNil
exampleIx2 = IxS IxZ `IxCons` IxZ `IxCons` IxNil
exampleIx3 = IxS (IxS IxZ) `IxCons` IxS IxZ `IxCons` IxNil

lookup :: TreeIndex shape subshape -> TupleTree shape a -> TupleTree subshape a
lookup = \case
  IxNil -> id
  IxCons x xs -> \case
    Tuple _ ts -> lookup xs (at x ts)

at ::
     ForestIndex shapes subshape -> TupleForest shapes a -> TupleTree subshape a
at =
  \case
    IxZ ->
      \case
        ForestCons x _ -> x
    IxS n ->
      \case
        ForestCons _ xs -> at n xs

-- instance (AdditiveMagma a) => AdditiveMagma (Tuple sh a) where
--   plus (C arr) (C brr) = C $ plus arr brr

-- instance (AdditiveUnital a) => AdditiveUnital (Tuple sh a) where
--   zero = pureRep zero

-- instance (AdditiveAssociative a) =>
--          AdditiveAssociative (Tuple sh a)

-- instance (AdditiveCommutative a) =>
--          AdditiveCommutative (Tuple sh a)

-- instance (AdditiveInvertible a) => AdditiveInvertible (Tuple sh a) where
--   negate = fmapRep negate

-- instance (Additive a) => Additive (Tuple sh a)

-- instance (AdditiveGroup a) => AdditiveGroup (Tuple sh a)

-- instance (MultiplicativeMagma a) =>
--          MultiplicativeMagma (Tuple sh a) where
--   times = liftR2 times

-- instance ( MultiplicativeUnital a) =>
--          MultiplicativeUnital (Tuple a) where
--   one = pureRep one

-- instance ( MultiplicativeAssociative a) =>
--          MultiplicativeAssociative (Tuple a)

-- instance (MultiplicativeCommutative a) =>
--          MultiplicativeCommutative (Tuple a)

-- instance (MultiplicativeInvertible a) =>
--          MultiplicativeInvertible (Tuple a) where
--   recip = fmapRep recip

-- instance (Multiplicative a) => Multiplicative (Tuple a)

-- instance (MultiplicativeGroup a) =>
--          MultiplicativeGroup (Tuple a)

-- instance ( MultiplicativeMagma a, Additive a) =>
--          Distribution (Tuple a)

-- instance (Semiring a) => Semiring (Tuple a)

-- instance (Ring a) => Ring (Tuple a)

-- instance (CRing a) => CRing (Tuple a)

-- instance (Field a) => Field (Tuple a)

-- instance (ExpField a) => ExpField (Tuple a) where
--   exp = fmapRep exp
--   log = fmapRep log

-- instance (BoundedField a) => BoundedField (Tuple a) where
--   isNaN f = or (fmapRep isNaN f)

-- instance (Signed a) => Signed (Tuple a) where
--   sign = fmapRep sign
--   abs = fmapRep abs

-- instance (ExpField a) => Normed (Tuple a) a where
--   size r = sqrt $ foldr (+) zero $ (** (one + one)) <$> r

-- instance (Epsilon a) => Epsilon (Tuple a) where
--   nearZero f = and (fmapRep nearZero f)
--   aboutEqual a b = and (liftR2 aboutEqual a b)

-- instance (ExpField a) => Metric (Tuple a) a where
--   distance a b = size (a - b)

-- instance ( Integral a) => Integral (Tuple a) where
--   divMod a b = (d, m)
--     where
--       x = liftR2 divMod a b
--       d = fmap fst x
--       m = fmap snd x

-- instance (CRing a, Num a, Semiring a) => Hilbert (Tuple) a where
--   a <.> b = sum $ liftR2 (*) a b








