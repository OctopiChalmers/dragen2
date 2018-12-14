{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}

module Test.QuickCheck.Branching where

import Data.Kind
import Data.Proxy
import Data.Reflection

import GHC.TypeLits
import GHC.Generics.Countable

import Test.QuickCheck

import Data.Matrix (Matrix, (<->), (<|>))
import qualified Data.Matrix as Matrix

import Data.Vector (Vector, (!))
import qualified Data.Vector as Vector

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map


type FamIx  = Int
type Level  = Int
type QCSize = Int

type Vector2 a = Vector (Vector a)
type Vector3 a = Vector (Vector (Vector a))
type Vector4 a = Vector (Vector (Vector (Vector a)))

type Hist = Map String Double


class Branching (fam :: Type -> Type) where
  -- | The constructor or pattern name
  names :: Vector2 String
  -- | Is the the type representing a single constructor?
  atomic :: Vector2 Bool
  -- | The generation frequency when size > 0
  probs :: Vector2 Double
  -- | The generation frequency when size = 0
  probs0 :: Vector2 Double
  -- | The "branching factor" to each member of the mutually recursive family
  beta :: Vector3 Double
  -- | The "expansion factor" to each member of the mutually recursive family
  eta :: Vector4 Double


----------------------------------------
-- | Some utilities

famSize :: forall fam. Branching fam => Int
famSize = Vector.length (names @fam)

names' :: forall fam. Branching fam => FamIx -> Vector String
names' ix = names @fam ! ix

atomic' :: forall fam. Branching fam => FamIx -> Vector Bool
atomic' ix = atomic @fam ! ix

probs' :: forall fam. Branching fam => FamIx -> Vector Double
probs' ix = probs @fam ! ix

probs0' :: forall fam. Branching fam => FamIx -> Vector Double
probs0' ix = probs0 @fam ! ix

beta' :: forall fam. Branching fam => FamIx -> FamIx -> Vector Double
beta' from to = (!to) <$> beta @fam ! from

eta' :: forall fam. Branching fam => FamIx -> FamIx -> Vector2 Double
eta' from to = (!to) <$> eta @fam ! from

atomicNames :: forall fam. Branching fam => Vector2 String
atomicNames = flip Vector.imap (names @fam)
  (\fix -> Vector.ifilter (\cix  -> const ((! cix) (atomic' @fam fix))))

(<<>>) :: Vector2 a -> Vector2 a -> Vector2 a
(<<>>) = Vector.zipWith (<>)

(.+.), (.*.) :: Vector Double -> Vector Double -> Vector Double
(.+.) = Vector.zipWith (+)
(.*.) = Vector.zipWith (*)

col, row :: Vector a -> Matrix a
col = Matrix.colVector
row = Matrix.rowVector

vec :: Matrix a -> Vector a
vec = Matrix.getRow 1


fmap2 :: (a -> b) -> Vector2 a -> Vector2 b
fmap2 = fmap . fmap

build :: Int -> Int -> (Int -> Int -> Matrix a) -> Matrix a
build rn cn mkElem = foldr1 (<->) (mkRow <$> [1..rn])
  where mkRow r = foldr1 (<|>) (mkElem r <$> [1..cn])

----------------------------------------
-- | Prediction matrices

initial :: forall fam. Branching fam => FamIx -> Matrix Double
initial ix = row (foldr1 (<>) (Vector.imap nullify (probs @fam)))
  where nullify ix' | ix == ix' = id
        nullify _               = fmap (const 0)

mean :: forall fam. Branching fam => Matrix Double
mean = build (famSize @fam) (famSize @fam) mkElem
  where mkElem r c = col (beta'  @fam (r-1) (c-1))
                   * row (probs' @fam (c-1))

mean0 :: forall fam. Branching fam => Matrix Double
mean0 = build (famSize @fam) (famSize @fam) mkElem
  where mkElem r c = col (beta'   @fam (r-1) (c-1))
                   * row (probs0' @fam (c-1))

expand :: forall fam. Branching fam => Matrix Double
expand = build (famSize @fam) (famSize @fam) mkElem
  where mkElem r c = foldr1 (<->) (row <$> eta' @fam (r-1) (c-1))

levels :: forall fam. Branching fam => FamIx -> [Matrix Double]
levels ix = scanl Matrix.multStd2 (initial @fam ix) (repeat (mean @fam))

level :: forall fam. Branching fam => FamIx -> Level -> Matrix Double
level ix lvl = levels @fam ix !! lvl

branchingLevels :: forall fam. Branching fam => FamIx -> QCSize -> Matrix Double
branchingLevels ix size = foldr1 (+) (take size (levels @fam ix))

lastLevel :: forall fam. Branching fam => FamIx -> QCSize -> Matrix Double
lastLevel ix size = level @fam ix (size - 1)
                  * mean0 @fam

-- | Predict the representation distribution
predictRep' :: forall fam. Branching fam => FamIx -> QCSize -> Matrix Double
predictRep' ix size = branchingLevels @fam ix size + lastLevel @fam ix size

-- | Predict the original distribution by expanding the representation
predict' :: forall fam. Branching fam => FamIx -> QCSize -> Matrix Double
predict' ix size = predictRep' @fam ix size * expand @fam


predictRep :: forall fam. Branching fam => FamIx -> QCSize -> Hist
predictRep ix size = Map.fromList $ zip
                     (Vector.toList (foldr1 (<>) (names @fam)))
                     (Matrix.toList (predictRep' @fam ix size))

predict :: forall fam. Branching fam => FamIx -> QCSize -> Hist
predict ix size = Map.fromList $ zip
                  (Vector.toList (foldr1 (<>) (atomicNames @fam)))
                  (Matrix.toList (predict' @fam ix size))

----------------------------------------
-- | Families of mutually recursive branching types

-- data Nil      :: Type -> Type
data (f <> g) :: Type -> Type

type family Fam (fam :: [Type -> Type]) :: Type -> Type where
  Fam '[] = TypeError ('Text "Fam: empty family")
  Fam (t ': '[]) = t -- <> Nil
  Fam (t ':  ts) = t <> (Fam ts)

instance (Branching f, Branching g) => Branching (f <> g) where
  names  = names  @f <> names  @g
  atomic = atomic @f <> atomic @g
  probs  = probs  @f <> probs  @g
  probs0 = probs0 @f <> probs0 @g
  beta   = beta   @f <> beta   @g
  eta    = eta    @f <> eta    @g

type family Length (fam :: Type -> Type) :: Nat where
  Length (_ <> xs) = 1 + Length xs
  Length _         = 1

-- | Get the value of a type level frequency tag.
lengthVal :: forall xs n. (Length xs ~ n, Reifies n Integer) => Int
lengthVal = fromInteger (reflect (Proxy @n))


----------------------------------------
-- | Prediction confirmation
confirm :: forall a. (Countable a, Arbitrary a) => Int -> IO ConsAvg
confirm size = do
  let samples = 50000
      gen = arbitrary @a
  values <- sequence (replicate samples (generate (resize size gen)))
  return (consAvg (count <$> values))
