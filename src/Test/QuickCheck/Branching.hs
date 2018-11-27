{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.QuickCheck.Branching where

import Data.Bool
import Data.Kind

import Test.QuickCheck

import GHC.Generics.Countable

import Data.Matrix (Matrix)
import qualified Data.Matrix as Matrix

import Data.Vector (Vector)
import qualified Data.Vector as Vector


type Hist = Vector (String, Double)

(.+.), (.*.) :: Vector Double -> Vector Double -> Vector Double
(.+.) = Vector.zipWith (+)
(.*.) = Vector.zipWith (*)

col, row :: Vector a -> Matrix a
col = Matrix.colVector
row = Matrix.rowVector

vec :: Matrix a -> Vector a
vec = Matrix.getRow 1


class Branching (f :: Type -> Type) where
  -- | The constructors aliases in order
  alias :: Vector String
  -- | Terminal constructors
  terminals :: Vector Bool
  -- | The associated probability of each constructor
  probs :: Vector Double
  -- | The "branching factor" of every constructor
  beta :: Vector Double
  -- | The "dispatching probability" of every constructor
  sigma :: Vector Double
  -- | Histogram lower-bounds prediction
  predict :: Int -> Hist
  predict n = Vector.zip (alias @f) (firstLevels .+. lastLevel)
    where
      -- | First n-1 levels
      firstLevels = foldr1 (.+.) (Vector.generate n level)

      e0 = probs @f .*. sigma @f
      mean = col (beta @f) * row e0

      level 0 = e0
      level k = vec (row e0 * (mean ^ k))

      -- | Last level
      lastLevel = countTerms <$> terms

      countTerms cp = prevLevelHoles * cp / pTerms
      terms = Vector.zipWith (bool 0) (probs @f) (terminals @f)
      prevLevelHoles = Vector.sum (beta @f .*. level (n-1))
      pTerms = Vector.sum terms


confirm :: Countable a => Gen a -> Int -> IO ConsAvg
confirm gen size = do
  let samples = 10000
  values <- sequence (replicate samples (generate (resize size gen)))
  return (consAvg (count <$> values))
