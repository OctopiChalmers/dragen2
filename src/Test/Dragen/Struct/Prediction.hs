module Test.Dragen.Struct.Prediction where

import Data.Proxy
import GHC.TypeLits

import Data.Vector (Vector, (!))
import Data.Matrix (Matrix, (<->), (<|>))
import qualified Data.Vector as Vector
import qualified Data.Matrix as Matrix

import Test.Dragen.Struct.BoundedArbitrary
import Test.Dragen.Struct.Branching
import Test.Dragen.Struct.Rep
import Test.Dragen.Struct.TypeLevel



-- | A synonym to hide annoying KnownNat constraints
type Predictable fam
  = ( BranchingFam fam
    , KnownNat   (Length fam)
    , KnownNatss (FamFreqsList fam))

----------------------------------------
-- | Vanilla prediction

initialLevel
  :: forall fam. Predictable fam
  => FamIx -> Matrix Double
initialLevel ix = row (foldr1 (<>) (Vector.imap nullify (famBranchingProbs @fam)))
  where nullify ix' | ix == ix' = id
        nullify _               = fmap (const 0)

branchingMean
  :: forall fam. Predictable fam
  => Matrix Double
branchingMean = build (lengthVal @fam) (lengthVal @fam) mkElem
  where mkElem r c = col (beta  @fam (r-1) (c-1))
                   * row (branchingProbs @fam (c-1))

terminalMean
  :: forall fam. Predictable fam
  => Matrix Double
terminalMean = build (lengthVal @fam) (lengthVal @fam) mkElem
  where mkElem r c = col (beta   @fam (r-1) (c-1))
                   * row (terminalProbs @fam (c-1))

allLevels
  :: forall fam. Predictable fam
  => FamIx -> [Matrix Double]
allLevels ix
  = scanl Matrix.multStd2
    (initialLevel @fam ix)
    (repeat (branchingMean @fam))

nthLevel
  :: forall fam. Predictable fam
  => FamIx -> Int -> Matrix Double
nthLevel ix lvl
  = allLevels @fam ix !! lvl

branchingLevels
  :: forall fam. Predictable fam
  => FamIx -> MaxDepth -> Matrix Double
branchingLevels ix size
  = foldr1 (+) (take size (allLevels @fam ix))

lastLevel
  :: forall fam. Predictable fam
  => FamIx -> MaxDepth -> Matrix Double
lastLevel ix size
  = accumLast (0 :: Int) emptyAcc prevLvl
  where
    prevLvl = nthLevel @fam ix (size - 1)
    emptyAcc = const 0 <$> prevLvl
    branch = (* (terminalMean @fam))

    accumLast n acc prev
      | acc == acc' = acc
      | n   == 50   = acc
      | otherwise   = accumLast (n + 1) acc' (branch prev)
      where acc' = acc + branch prev

-- | Predict the representation distribution
predictFam
  :: forall fam. Predictable fam
  => FamIx -> MaxDepth -> Matrix Double
predictFam ix size
  = branchingLevels @fam ix size
    + lastLevel @fam ix size

-- | Predict the original distribution by expanding the representation
predictFamExpanded
  :: forall fam. Predictable fam
  => FamIx -> MaxDepth -> Matrix Double
predictFamExpanded ix size
  = predictFam @fam ix size
    * expandPatterns @fam

expandPatterns
  :: forall fam. Predictable fam
  => Matrix Double
expandPatterns
  = build (lengthVal @fam) (lengthVal @fam) mkElem
  where mkElem r c = foldr1 (<->) (row <$> eta @fam (r-1) (c-1))

----------------------------------------
-- | Prediction with mutated frequencies (used during optimization)

applyNewFreqs :: Vector2 Double -> [[Integer]] -> [[Integer]] -> Vector2 Double
applyNewFreqs ogProbs ogFreqs freqs
  | ogProbs `sameSize` newFreqs = newProbs
  | otherwise = error
    $ "applyNewFreqs: sizes don't match:\n"
    ++ "* " ++ show ogProbs ++ "\n"
    ++ "* " ++ show newFreqs
  where
    newFreqs = Vector.fromList (Vector.fromList <$> freqs)
    newProbs = normalize <$> Vector.zipWith3 transform ogProbs newFreqs ratios

    transform ogPs newFs r = Vector.zipWith (transform' r) ogPs newFs
    transform' r ogP newF = r * ogP * (fromIntegral newF)

    ratios   = ogSums ./. newSums
    ogSums   = Vector.fromList (fromIntegral . sum <$> ogFreqs)
    newSums  = fromIntegral . sum <$> newFreqs

famBranchingProbsWith
  :: forall fam freqs.
     (Predictable fam, KnownNatss freqs, freqs ~ FamFreqsList fam)
  => [[Integer]] -> Vector2 Double
famBranchingProbsWith
  = applyNewFreqs (famBranchingProbs @fam) (natValss (Proxy @freqs))

famTerminalProbsWith
  :: forall fam freqs.
     (Predictable fam, KnownNatss freqs, freqs ~ FamFreqsList fam)
  => [[Integer]] -> Vector2 Double
famTerminalProbsWith
  = applyNewFreqs (famTerminalProbs @fam) (natValss (Proxy @freqs))

branchingProbsWith
  :: forall fam. Predictable fam
  => [[Integer]] -> FamIx -> Vector Double
branchingProbsWith newFreqs ix
  = famBranchingProbsWith @fam newFreqs ! ix

terminalProbsWith
  :: forall fam. Predictable fam
  => [[Integer]] -> FamIx -> Vector Double
terminalProbsWith newFreqs ix
  = famTerminalProbsWith @fam newFreqs ! ix

initialLevelWith
  :: forall fam. Predictable fam
  => [[Integer]] -> FamIx -> Matrix Double
initialLevelWith newFreqs ix
  = row (foldr1 (<>) (Vector.imap nullify (famBranchingProbsWith @fam newFreqs)))
  where nullify ix' | ix == ix' = id
        nullify _               = fmap (const 0)

branchingMeanWith
  :: forall fam. Predictable fam
  => [[Integer]] -> Matrix Double
branchingMeanWith newFreqs
  = build (lengthVal @fam) (lengthVal @fam) mkElem
  where mkElem r c = col (beta  @fam (r-1) (c-1))
                   * row (branchingProbsWith @fam newFreqs (c-1))

terminalMeanWith
  :: forall fam. Predictable fam
  => [[Integer]] -> Matrix Double
terminalMeanWith newFreqs
  = build (lengthVal @fam) (lengthVal @fam) mkElem
  where mkElem r c = col (beta  @fam (r-1) (c-1))
                   * row (terminalProbsWith @fam newFreqs (c-1))

allLevelsWith
  :: forall fam. Predictable fam
  => [[Integer]] -> FamIx -> [Matrix Double]
allLevelsWith newFreqs ix
  = scanl Matrix.multStd2
    (initialLevelWith @fam newFreqs ix)
    (repeat (branchingMeanWith @fam newFreqs))

nthLevelWith
  :: forall fam. Predictable fam
  => [[Integer]] -> FamIx -> Int -> Matrix Double
nthLevelWith newFreqs ix lvl
  = allLevelsWith @fam newFreqs ix !! lvl

branchingLevelsWith
  :: forall fam. Predictable fam
  => [[Integer]] -> FamIx -> MaxDepth -> Matrix Double
branchingLevelsWith newFreqs ix size
  = foldr1 (+) (take size (allLevelsWith @fam newFreqs ix))

lastLevelWith
  :: forall fam. Predictable fam
  => [[Integer]] -> FamIx -> MaxDepth -> Matrix Double
lastLevelWith newFreqs ix size
  = accumLast (0 :: Int) emptyAcc prevLvl
  where
    prevLvl = nthLevelWith @fam newFreqs ix (size - 1)
    emptyAcc = const 0 <$> prevLvl
    branch = (* (terminalMeanWith @fam newFreqs))
    accumLast n acc prev
      | acc == acc' = acc
      | n   == 50   = acc
      | otherwise   = accumLast (n + 1) acc' (branch prev)
      where acc' = acc + branch prev

-- | Predict the representation distribution
predictFamWith
  :: forall fam. Predictable fam
  => [[Integer]] -> FamIx -> MaxDepth -> Matrix Double
predictFamWith newFreqs ix size
  = branchingLevelsWith @fam newFreqs  ix size
  + lastLevelWith @fam newFreqs ix size

-- | Predict the original distribution by expanding the representation
predictFamExpandedWith
  :: forall fam. Predictable fam
  => [[Integer]] -> FamIx -> MaxDepth -> Matrix Double
predictFamExpandedWith newFreqs ix size
  = predictFamWith @fam newFreqs ix size
  * expandPatterns @fam

----------------------------------------
-- | Vector and Matrix utilities

(.+.), (.*.), (./.) :: Vector Double -> Vector Double -> Vector Double
(.+.) = Vector.zipWith (+)
(.*.) = Vector.zipWith (*)
(./.) = Vector.zipWith (/)

col, row :: Vector a -> Matrix a
col = Matrix.colVector
row = Matrix.rowVector

vec :: Matrix a -> Vector a
vec = Matrix.getRow 1

build :: Int -> Int -> (Int -> Int -> Matrix a) -> Matrix a
build rn cn mkElem = foldr1 (<->) (mkRow <$> [1..rn])
  where mkRow r = foldr1 (<|>) (mkElem r <$> [1..cn])


normalize :: Vector Double -> Vector Double
normalize v = fmap (/ vsum) v
  where vsum = foldr (+) 0 v

sameSize :: Vector2 a -> Vector2 b -> Bool
sameSize v1 v2
  | length v1 == length v2
  = all (uncurry (==)) (Vector.zip (length <$> v1) (length <$> v2))
  | otherwise = False
