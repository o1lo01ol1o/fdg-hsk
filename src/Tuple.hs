{-# LANGUAGE TypeInType #-}
{-# LANGUAGE OverloadedLists, OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds, TemplateHaskell, UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module Tuple () where

import NumHask.Array as A
import NumHask.Prelude as P
import Data.HVect as HV
import Data.Singletons
import Data.Singletons.Prelude.Eq ((:==))
import Data.Singletons.Prelude.Bool ((:&&))
import Data.Singletons.Prelude.Ord ((:>))
import Data.Singletons.Prelude.List ((:!!))
import Data.Singletons.Prelude.Num ((:+), (:-))
import Data.Singletons.TH (promote, singletons, ErrorSym0)
import Data.Tree as T
import Data.Kind (type(*), Type)


$(promote
    [d|

  data TTree a = Branch [TTree a]
               | Leaf a
               | NilTree
  |])

type family AllShapes t where
  AllShapes '[] = '[]
  AllShapes (t:ts) = TupShape t : AllShapes ts

type family TupShape t where
  TupShape (Tuple sh a) = sh

type family IsTup t where
  IsTup (Tuple sh a) = 'True
  IsTup _ = 'False

type family IsEmpty t where
  IsEmpty '[] = 'True
  IsEmpty _ = 'False

type family AllAreTups ts where
  AllAreTups (t:ts) = ('True :== IsTup t) :&& AllAreTups ts
  AllAreTups '[] = 'False

type family GetNthTree n (sh :: TTree [P.Nat]) where
  GetNthTree 0 NilTree = NilTree
  GetNthTree 0 (Leaf a) = Leaf a
  GetNthTree n (Branch ls) = ls :!! n
  GetNthTree _ _ = ErrorSym0 @@ "Whoa!"

type ValidTups tps = (AllAreTups tps ~ 'True, IsEmpty tps ~ 'False)


type family InBounds i hv where
  InBounds i hv = HV.HVectLen hv :> i

type IsInBounds i hv = InBounds i hv ~ True

data Tuple (sh :: TTree [P.Nat]) a where
  C :: A.Array (s :: [P.Nat]) a -> Tuple ('Leaf s) a
  U :: (ValidTups tps) => HVect tps -> Tuple ('Branch (AllShapes tps)) a
  D :: (ValidTups tps) => HVect tps -> Tuple ('Branch (AllShapes tps)) a

type family HNat2Nat (n :: HV.Nat) :: P.Nat where
  HNat2Nat (HV.Zero) = 0
  HNat2Nat (HV.Succ n) = 1 :+ (HNat2Nat n)

type family Nat2HNat (n :: P.Nat) :: HV.Nat where
  Nat2HNat 0 = HV.Zero
  Nat2HNat n = HV.Succ (Nat2HNat (n :- 1))

-- data LNat = Z | S LNat
-- data Vec (a :: Type) (n :: LNat) where
--   NilV :: Vec a Z
--   ConsV :: a -> Vec a n -> Vec a (S n)

-- data HVec :: (k -> Type) -> [k] -> Type where
--   NilHV :: HVec mkShape '[]
--   ConsHV :: mkShape a -> HVec mkShape as -> HVec mkShape (a ': as)

homp_ :: HV.SNat n -> HVect tps -> HV.HVectIdx n tps
homp_ i v = i HV.!! v

comp_ ::
     (SingI n
     -- , ValidTups tps
      -- , hn ~ (Nat2HNat n), IsInBounds hn tps,  HV.HVectIdx hn tps ~ Tuple (GetNthTree n s) a
     )
  => Tuple s a
  -> Sing n
  -> Tuple (GetNthTree n s) a 
comp_ (U v) n =
  case ((fromSing n) :: Integer) of
    i -> case HV.intToSNat (P.fromIntegral i) of
           AnySNat s -> homp_ s v 
      

-- component :: (SingI l, l ~ [Int]) => Tuple s a -> (forall l.  Sing l)  -> Tuple sh a
-- -- component a [] = a
-- component (U v) ll = case fromSing ll of
--                        [] -> error "Should never happen!"
--                        (x:xs) -> component (case HV.intToSNat x of (AnySNat n) -> n HV.!! v) (case toSing xs of SomeSing xsx -> xsx)
-- component (D v)  ll = component (case HV.intToSNat x of (AnySNat n) -> n HV.!! v) xs


-- mapHV :: (Tuple sh a -> Tuple sh a) -> HVect b -> HVect b
-- mapHV _ HNil = HNil
-- mapHV fn ((:&:) x xs) = (fn x) :&:  (mapHV fn xs)

-- monOp :: forall a sh. (forall s v. Array s a -> Array v a) -> Tuple sh a -> Tuple sh a
-- monOp fn (C arr ) = C $ (fn arr)
-- monOp fn (U vs) = U $ mapHV (monOp fn) vs
-- monOp fn (D vs) = D $ mapHV (monOp fn) vs

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








