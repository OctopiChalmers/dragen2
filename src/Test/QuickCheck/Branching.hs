{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Test.QuickCheck.Branching where

import Data.Maybe
import Data.List
import Data.Ord

import Data.Kind
import Data.Proxy
import Data.Reflection

import GHC.TypeLits
import GHC.Generics.Countable

import Test.QuickCheck
import Test.QuickCheck.HRep

import Data.Matrix (Matrix, (<->), (<|>))
import qualified Data.Matrix as Matrix

import Data.Vector (Vector, (!))
import qualified Data.Vector as Vector

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import System.IO.Unsafe
import System.IO

import Debug.Trace

----------------------------------------
-- | Some type synonyms

type FamIx  = Int
type Level  = Int
type QCSize = Int

type Vector2 a = Vector (Vector a)
type Vector3 a = Vector (Vector (Vector a))
type Vector4 a = Vector (Vector (Vector (Vector a)))

type Hist = Map String Double

----------------------------------------
-- | BranchingType type class

class BranchingType (ty :: Type -> Type) where
  -- | The constructor or pattern name
  typeNames :: Vector String
  -- | Is the the type representing a single constructor?
  typeAtomic :: Vector Bool
  -- | The generation frequency when size > 0
  typeProbs :: Vector Double
  -- | The generation frequency when size = 0
  typeProbs' :: Vector Double
  -- | The "branching factor" to each member of the mutually recursive family
  typeBeta :: Vector2 Double
  -- | The "expansion factor" to each member of the mutually recursive family
  typeEta :: Vector3 Double

instance BranchingType f => BranchingType (Freq f n) where
  typeNames = typeNames @f
  typeAtomic = typeAtomic @f
  typeProbs = typeProbs @f
  typeProbs' = typeProbs' @f
  typeBeta = typeBeta @f
  typeEta = typeEta @f

instance (BranchingType f) => BranchingType (Term f) where
  typeNames = typeNames @f
  typeAtomic = typeAtomic @f
  typeProbs = typeProbs @f
  typeProbs' = typeProbs @f
  typeBeta = typeBeta @f
  typeEta = typeEta @f

instance (BranchingType f, BranchingType g, f #> ff, f @> ff', g #> gg, g @> gg')
  => BranchingType (Sum f g) where
  typeNames = typeNames @f <> typeNames @g
  typeAtomic = typeAtomic @f <> typeAtomic @g
  typeProbs = fmap (* (ff/tot)) (typeProbs @f) <> fmap (* (gg/tot)) (typeProbs @g)
    where ff = numVal @ff; gg = numVal @gg; tot = ff + gg
  typeProbs' = if tot' == 0
    then fmap (*0) (typeProbs' @f <> typeProbs' @g)
    else fmap (* (ff'/tot')) (typeProbs' @f) <> fmap (* (gg'/tot')) (typeProbs' @g)
    where ff' = numVal @ff'; gg' = numVal @gg'; tot' = ff' + gg'
  typeBeta = typeBeta @f <> typeBeta @g
  typeEta  = typeEta  @f <> typeEta  @g

instance (forall a. BranchingType (f a)) => BranchingType (Some1 f) where
  typeNames  = typeNames  @(f ())
  typeAtomic = typeAtomic @(f ())
  typeProbs  = typeProbs  @(f ())
  typeProbs' = typeProbs' @(f ())
  typeBeta   = typeBeta   @(f ())
  typeEta    = typeEta    @(f ())

instance (forall a b. BranchingType (f a b)) => BranchingType (Some2 f) where
  typeNames  = typeNames  @(f () ())
  typeAtomic = typeAtomic @(f () ())
  typeProbs  = typeProbs  @(f () ())
  typeProbs' = typeProbs' @(f () ())
  typeBeta   = typeBeta   @(f () ())
  typeEta    = typeEta    @(f () ())

instance (forall a b c. BranchingType (f a b c)) => BranchingType (Some3 f) where
  typeNames  = typeNames  @(f () () ())
  typeAtomic = typeAtomic @(f () () ())
  typeProbs  = typeProbs  @(f () () ())
  typeProbs' = typeProbs' @(f () () ())
  typeBeta   = typeBeta   @(f () () ())
  typeEta    = typeEta    @(f () () ())

instance (forall a b c d. BranchingType (f a b c d)) => BranchingType (Some4 f) where
  typeNames  = typeNames  @(f () () () ())
  typeAtomic = typeAtomic @(f () () () ())
  typeProbs  = typeProbs  @(f () () () ())
  typeProbs' = typeProbs' @(f () () () ())
  typeBeta   = typeBeta   @(f () () () ())
  typeEta    = typeEta    @(f () () () ())

instance (forall a b c d e. BranchingType (f a b c d e)) => BranchingType (Some5 f) where
  typeNames = typeNames   @(f () () () () ())
  typeAtomic = typeAtomic @(f () () () () ())
  typeProbs = typeProbs   @(f () () () () ())
  typeProbs' = typeProbs' @(f () () () () ())
  typeBeta = typeBeta     @(f () () () () ())
  typeEta = typeEta       @(f () () () () ())

----------------------------------------
-- | BranchingFam type class

class BranchingFam (fam :: [Type -> Type]) where
  famNames :: Vector2 String
  famAtomic :: Vector2 Bool
  famProbs :: Vector2 Double
  famProbs' :: Vector2 Double
  famBeta :: Vector3 Double
  famEta :: Vector4 Double

instance BranchingFam '[] where
  famNames = Vector.empty
  famAtomic = Vector.empty
  famProbs = Vector.empty
  famProbs' = Vector.empty
  famBeta = Vector.empty
  famEta = Vector.empty

instance (BranchingType f, BranchingFam fs) => BranchingFam (f ': fs) where
  famNames = Vector.singleton (typeNames @f) <> famNames @fs
  famAtomic = Vector.singleton (typeAtomic @f) <> famAtomic @fs
  famProbs = Vector.singleton (typeProbs @f) <> famProbs @fs
  famProbs' = Vector.singleton (typeProbs' @f) <> famProbs' @fs
  famBeta = Vector.singleton (typeBeta @f) <> famBeta @fs
  famEta = Vector.singleton (typeEta @f) <> famEta @fs

type Branching fam = (BranchingFam fam
                     ,KnownNat (Length fam)
                     ,KnownNatss (MapRepFreqs fam))


----------------------------------------
-- | Vector dereferences

names :: forall fam. Branching fam => FamIx -> Vector String
names ix = famNames @fam ! ix

atomic :: forall fam. Branching fam => FamIx -> Vector Bool
atomic ix = famAtomic @fam ! ix

probs :: forall fam. Branching fam => FamIx -> Vector Double
probs ix = famProbs @fam ! ix

probs' :: forall fam. Branching fam => FamIx -> Vector Double
probs' ix = famProbs' @fam ! ix

beta :: forall fam. Branching fam => FamIx -> FamIx -> Vector Double
beta from to = (!to) <$> famBeta @fam ! from

eta :: forall fam. Branching fam => FamIx -> FamIx -> Vector2 Double
eta from to = (!to) <$> famEta @fam ! from

atomicNames :: forall fam. Branching fam => Vector2 String
atomicNames = flip Vector.imap (famNames @fam)
  (\fix -> Vector.ifilter (\cix  -> const ((! cix) (atomic @fam fix))))


----------------------------------------
-- | Prediction

famSize :: forall xs n a. (Length xs ~ n, Reifies n Integer, Num a) => a
famSize = fromIntegral (reflect (Proxy @n))

initial :: forall fam. Branching fam => FamIx -> Matrix Double
initial ix = row (foldr1 (<>) (Vector.imap nullify (famProbs @fam)))
  where nullify ix' | ix == ix' = id
        nullify _               = fmap (const 0)

mean :: forall fam. Branching fam => Matrix Double
mean = build (famSize @fam) (famSize @fam) mkElem
  where mkElem r c = col (beta  @fam (r-1) (c-1))
                   * row (probs @fam (c-1))

mean' :: forall fam. Branching fam => Matrix Double
mean' = build (famSize @fam) (famSize @fam) mkElem
  where mkElem r c = col (beta   @fam (r-1) (c-1))
                   * row (probs' @fam (c-1))

expand :: forall fam. Branching fam => Matrix Double
expand = build (famSize @fam) (famSize @fam) mkElem
  where mkElem r c = foldr1 (<->) (row <$> eta @fam (r-1) (c-1))

levels :: forall fam. Branching fam => FamIx -> [Matrix Double]
levels ix = scanl Matrix.multStd2 (initial @fam ix) (repeat (mean @fam))

level :: forall fam. Branching fam => FamIx -> Level -> Matrix Double
level ix lvl = levels @fam ix !! lvl

branchingLevels :: forall fam. Branching fam => FamIx -> QCSize -> Matrix Double
branchingLevels ix size = foldr1 (+) (take size (levels @fam ix))

lastLevel :: forall fam. Branching fam => FamIx -> QCSize -> Matrix Double
lastLevel ix size = accumLast (0 :: Int) emptyAcc prevLvl
  where
    prevLvl = level @fam ix (size - 1)
    emptyAcc = const 0 <$> prevLvl
    branch = (* (mean' @fam))

    accumLast n acc prev
      -- | n == 10    = trace "lastLevel: could not reach a fixed point!" acc
      | n == 10     = acc
      | acc == acc' = acc
      | otherwise   = accumLast (n + 1) acc' (branch prev)
      where acc' = acc + branch prev

-- | Predict the representation distribution
predictRep' :: forall fam. Branching fam => FamIx -> QCSize -> Matrix Double
predictRep' ix size = branchingLevels @fam ix size + lastLevel @fam ix size

-- | Predict the original distribution by expanding the representation
predict' :: forall fam. Branching fam => FamIx -> QCSize -> Matrix Double
predict' ix size = predictRep' @fam ix size * expand @fam

----------------------------------------
-- | Prediction with mutated frequencies

applyFreqsToProbs :: Vector2 Double -> [[Integer]] -> [[Integer]] ->  Vector2 Double
applyFreqsToProbs ogProbs ogFreqs freqs
  | matchSize ogProbs newFreqs = newProbs
  | otherwise = error $ "applyFreqsToProbs: sized don't match:\n"
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


famProbsWith :: forall fam freqs.
                ( Branching fam
                , freqs ~ MapRepFreqs fam
                , KnownNatss freqs
                ) => [[Integer]] -> Vector2 Double
famProbsWith = applyFreqsToProbs (famProbs @fam) (natValss (Proxy @freqs))


famProbs'With :: forall fam freqs.
                ( Branching fam
                , freqs ~ MapRepFreqs fam
                , KnownNatss freqs
                ) => [[Integer]] -> Vector2 Double
famProbs'With = applyFreqsToProbs (famProbs' @fam) (natValss (Proxy @freqs))


probsWith :: forall fam. Branching fam => [[Integer]] -> FamIx -> Vector Double
probsWith newFreqs ix = famProbsWith @fam newFreqs ! ix


probs'With :: forall fam. Branching fam => [[Integer]] -> FamIx -> Vector Double
probs'With newFreqs ix = famProbs'With @fam newFreqs ! ix

initialWith :: forall fam. Branching fam
            => [[Integer]] -> FamIx -> Matrix Double
initialWith newFreqs ix
  = row (foldr1 (<>) (Vector.imap nullify (famProbsWith @fam newFreqs)))
  where nullify ix' | ix == ix' = id
        nullify _               = fmap (const 0)

meanWith :: forall fam. Branching fam
         => [[Integer]] -> Matrix Double
meanWith newFreqs = build (famSize @fam) (famSize @fam) mkElem
  where mkElem r c = col (beta  @fam (r-1) (c-1))
                   * row (probsWith @fam newFreqs (c-1))

mean'With :: forall fam. Branching fam
         => [[Integer]] -> Matrix Double
mean'With newFreqs = build (famSize @fam) (famSize @fam) mkElem
  where mkElem r c = col (beta  @fam (r-1) (c-1))
                   * row (probs'With @fam newFreqs (c-1))

levelsWith :: forall fam. Branching fam => [[Integer]] -> FamIx -> [Matrix Double]
levelsWith newFreqs ix = scanl Matrix.multStd2
                (initialWith @fam newFreqs ix)
                (repeat (meanWith @fam newFreqs))

levelWith :: forall fam. Branching fam => [[Integer]] -> FamIx -> Level -> Matrix Double
levelWith newFreqs ix lvl = levelsWith @fam newFreqs ix !! lvl

branchingLevelsWith :: forall fam. Branching fam
                    => [[Integer]] -> FamIx -> QCSize -> Matrix Double
branchingLevelsWith newFreqs ix size
  = foldr1 (+) (take size (levelsWith @fam newFreqs ix))

lastLevelWith :: forall fam. Branching fam
              => [[Integer]] -> FamIx -> QCSize -> Matrix Double
lastLevelWith newFreqs ix size = accumLast (0 :: Int) emptyAcc prevLvl
  where
    prevLvl = levelWith @fam newFreqs ix (size - 1)
    emptyAcc = const 0 <$> prevLvl
    branch = (* (mean'With @fam newFreqs))

    accumLast n acc prev
      | n == 10    = trace "lastLevelWith: could not reach a fixed point!" acc
      | n == 10     = acc
      | acc == acc' = acc
      | otherwise   = accumLast (n + 1) acc' (branch prev)
      where acc' = acc + branch prev

-- | Predict the representation distribution
predictRep'With :: forall fam. Branching fam
                => [[Integer]] -> FamIx -> QCSize -> Matrix Double
predictRep'With newFreqs ix size
  = branchingLevelsWith @fam newFreqs  ix size
  + lastLevelWith @fam newFreqs ix size

-- | Predict the original distribution by expanding the representation
predict'With :: forall fam. Branching fam
             => [[Integer]] -> FamIx -> QCSize -> Matrix Double
predict'With newFreqs ix size
  = predictRep'With @fam newFreqs ix size
  * expand @fam

----------------------------------------
-- | Specifications prediction and confirmation

type Spec = [(Symbol, Type -> Type)]

type HasSpec (spec :: Spec) (root :: Symbol)
  = ( Branching (Values spec)
    , KnownNat (Length (Values spec))
    , KnownNat (Ix spec root))

predictRep :: forall spec root fam ix.
              ( HasSpec spec root
              , fam ~ Values spec
              , ix ~ Ix spec root
              ) => QCSize -> Hist
predictRep size = Map.fromList $ zip
                  (Vector.toList (foldr1 (<>) (famNames @fam)))
                  (Matrix.toList (predictRep' @fam (numVal @ix) size))


predict :: forall spec root fam ix.
           ( HasSpec spec root
           , fam ~ Values spec
           , ix  ~ Ix spec root
           ) => QCSize -> Hist
predict size = Map.fromList $ zip
               (Vector.toList (foldr1 (<>) (atomicNames @fam)))
               (Matrix.toList (predict' @fam (numVal @ix) size))

predictRepWith :: forall spec root fam ix.
                  ( HasSpec spec root
                  , fam ~ Values spec
                  , ix ~ Ix spec root
                  ) => [[Integer]] -> QCSize -> Hist
predictRepWith newFreqs size
  = Map.fromList $ zip
    (Vector.toList (foldr1 (<>) (famNames @fam)))
    (Matrix.toList (predictRep'With @fam newFreqs (numVal @ix) size))


predictWith :: forall spec root fam ix.
           ( HasSpec spec root
           , fam ~ Values spec
           , ix  ~ Ix spec root
           ) => [[Integer]] -> QCSize -> Hist
predictWith newFreqs size
  = Map.fromList $ zip
    (Vector.toList (foldr1 (<>) (atomicNames @fam)))
    (Matrix.toList (predict'With @fam newFreqs (numVal @ix) size))

confirmRep :: forall spec root hrep target.
  ( HasSpec spec root
  , hrep ~ Lookup spec root
  , HasFixArbitrary hrep target
  , Countable (Fix hrep)
  ) => QCSize -> IO ConsAvg
confirmRep size = do
  let samples = 50000
      gen = genFix @hrep
  values <- sequence (replicate samples (generate (resize size gen)))
  return (consAvg (count <$> values))

confirm :: forall spec root hrep target.
  ( HasSpec spec root
  , hrep ~ Lookup spec root
  , HasFixArbitrary hrep target
  , Countable target
  ) => QCSize -> IO ConsAvg
confirm size = do
  let samples = 50000
      gen = genEval @hrep
  values <- sequence (replicate samples (generate (resize size gen)))
  return (consAvg (count <$> values))

----------------------------------------
-- | Specifications optimization

data Mode = Rep | Target

type DistFun = forall (spec :: Spec) (root :: Symbol). HasSpec spec root
  => Proxy spec -> Proxy root -> Mode -> Int -> [[Integer]] -> Double

chiSquareVec :: Floating a => [a] -> [a] -> a
chiSquareVec expected observed
  = sum (zipWith (\o e -> (o - e)^2 / e) observed expected)

chiSquare :: Floating a => a -> [a] -> a
chiSquare expected observed = chiSquareVec (repeat expected) observed

uniform :: DistFun
uniform (Proxy :: Proxy spec) (Proxy :: Proxy root) mode size freqs
  = chiSquare (fromIntegral size) observed
  where observed = Map.elems (predictRepWith @spec @root freqs size)

weighted :: [(String, Int)] -> DistFun
weighted weights (Proxy :: Proxy spec) (Proxy :: Proxy root) mode size freqs
  = chiSquareVec expected observed
  where
    prediction = predictRepWith @spec @root freqs size
    (cnames, observed) = unzip (Map.toList (Map.filterWithKey hasWeight prediction))
    hasWeight cn _ = isJust (lookup cn weights)
    expected = multWeight <$> cnames
    multWeight cn = fromIntegral (fromJust (lookup cn weights) * size)

takeEvery :: Int -> [a] -> [a]
takeEvery n xs
  | length xs >= n = xs !! (n-1) : takeEvery n (drop n xs)
  | otherwise      = []

epsilon = 0.001

dot :: a -> a
dot x = unsafePerformIO (putStr "*" >> hFlush stdout >> return x)

optimizeFreqs :: forall spec root. HasSpec spec root
  => Mode -> QCSize -> DistFun -> [[Integer]] -> [[Integer]]
optimizeFreqs mode size dist freqs
  = localSearch @spec @root mode size (fromIntegral size) dist freqs []

localSearch :: forall spec root. HasSpec spec root
            => Mode -> QCSize -> Int -> DistFun
            -> [[Integer]] -> [[[Integer]]] -> [[Integer]]
localSearch mode size heat dist focus visited
  | null newNeighbors
  = focus
  | delta <= epsilon && heat == 1
  = focus
  | delta <= epsilon
  = dot $ localSearch @spec @root mode size 1 dist bestNeighbor newFrontier
  | otherwise
  = dot $ localSearch @spec @root mode size newHeat dist bestNeighbor newFrontier
  where
    delta = focusDist - bestNeighborDist
    focusDist = dist (Proxy @spec) (Proxy @root) mode size focus
    (bestNeighbor, bestNeighborDist) = minimumBy (comparing snd) neighborsDists
    neighborsDists = zip newNeighbors (dist (Proxy @spec) (Proxy @root) mode size <$> newNeighbors)
    newNeighbors = mutate (fromIntegral heat) focus \\ (focus:visited)
    newHeat = floor (max 1 ((fromIntegral heat / (1 + 0.001 * (gainRatio / fromIntegral size)))))
    gainRatio = bestNeighborDist / focusDist
    newFrontier = newNeighbors ++ (take (sum (length <$> focus) ^ 2)) visited


type family
  MkSpec (spec :: Spec) :: Spec where
  MkSpec spec = Flatten spec


type family
  ApplySpec (a :: Type) (ts :: Spec) :: Spec where
  ApplySpec _ '[] = '[]
  ApplySpec a ('(k, t) ': ts) = '(k, Apply a t) ': ApplySpec a ts


type family
  Flatten (spec :: Spec) :: Spec where
  Flatten '[] = '[]
  Flatten ('(k, t) ': ts) = '(k, List2Rep (Rep2List t)) ': Flatten ts

type family
  Rep2List (rep :: Type -> Type) :: [Type -> Type] where
  Rep2List (Sum f g) = Rep2List f ++ Rep2List g
  Rep2List t = '[t]

type family
  List2Rep (xs :: [Type -> Type]) :: Type -> Type where
  List2Rep '[t] = t
  List2Rep (x ': xs) = Sum x (List2Rep xs)


-- | Extract the frequencies from a spec
type family
  SpecFreqs (spec :: Spec) :: [[Nat]] where
  SpecFreqs '[] = '[]
  SpecFreqs ('(k, x) ': xs) = RepFreqs x ': SpecFreqs xs

type family
  RepFreqs (rep :: Type -> Type) :: [Nat] where
  RepFreqs (Sum f g) = RepFreqs f ++ RepFreqs g
  RepFreqs f = '[Frequency f]

type family
  MapRepFreqs (reps :: [Type -> Type]) :: [[Nat]] where
  MapRepFreqs '[] = '[]
  MapRepFreqs (x ': xs) = RepFreqs x ': MapRepFreqs xs

-- | Update the frequencies of a spec
type family
  SetSpecFreqs (spec :: Spec) (freqs :: [[Nat]]) :: Spec where
  SetSpecFreqs '[] '[] = '[]
  SetSpecFreqs ('(k, t) ': ts) (f ': fs) = '(k, SetRepFreqs t f) ': SetSpecFreqs ts fs
  SetSpecFreqs _ _ = TypeError ('Text "SetFamFreqs: mismatched sizes")

type family
  SetRepFreqs (rep :: Type -> Type) (freqsL :: [Nat]) :: Type -> Type where
  SetRepFreqs (Sum f g) (ff ': gg) = Sum (SetFreq f ff) (SetRepFreqs g gg)
  SetRepFreqs t '[f] = SetFreq t f
  SetRepFreqs _ _ = TypeError ('Text "SetRepFreqs: mismatched sizes")

type family
  SetFreq (rep :: Type -> Type) (freq :: Nat) :: Type -> Type where
  SetFreq (Freq t n) m = Freq t (n * m)
  SetFreq t          n = Freq t n

-- type family Optimized (spec :: Symbol) (alias :: Symbol) :: Spec
type family Optimized (alias :: Symbol) :: Spec

----------------------------------------
-- | Nested lists reflection

class KnownNats (ns :: [Nat]) where
  natVals  :: Proxy ns -> [Integer]

instance KnownNats '[] where
  natVals  _ = []

instance (KnownNat n, KnownNats ns) => KnownNats (n ': ns) where
  natVals  _ = natVal  (Proxy @n)
             : natVals (Proxy @ns)

class KnownNatss (ns :: [[Nat]]) where
  natValss :: Proxy ns -> [[Integer]]

instance KnownNatss '[] where
  natValss  _ = []

instance (KnownNats n, KnownNatss ns) => KnownNatss (n ': ns) where
  natValss _ = natVals  (Proxy @n)
             : natValss (Proxy @ns)

----------------------------------------
-- | Vector and Matrix utilities

mutate :: Integer -> [[Integer]] -> [[[Integer]]]
mutate n xss = map (mutateAt n xss) [0.. sum (length <$> xss) - 1]

mutateAt :: Integer -> [[Integer]] -> Int -> [[Integer]]
mutateAt n (xs : xss) ix
  | ix < length xs
  = (take ix xs ++ [(xs !! ix) + n]  ++ drop (ix+1) xs) : xss
  | otherwise
  = xs : mutateAt n xss (ix - length xs)

  -- take ix xss
  --                 ++ concatMap (mutateType n (xss !! ix)) [0 .. length (xss !! ix)]
  --                 ++ drop (ix + 1) xss





mutateType :: Integer -> [Integer] -> Integer -> [Integer]
mutateType = undefined


-- mutate :: Integer -> [[Integer]] -> [[[Integer]]]
-- mutate _ [] = [[]]
-- mutate n (x : xs) = ((:) <$> mutate' n x) <*> mutate n xs

-- mutate' :: Integer -> [Integer] -> [[Integer]]
-- mutate' _ [] = [[]]
-- mutate' n (x : xs) = [(x:), ((x+n):)] <*> mutate' n xs

normalize :: Vector Double -> Vector Double
normalize v = Vector.map (/ vsum) v
  where vsum = Vector.foldr (+) 0 v

matchSize :: Vector2 a -> Vector2 b -> Bool
matchSize v1 v2
  | Vector.length v1 == Vector.length v2
  = all (uncurry (==))
    (Vector.zip (Vector.length <$> v1) (Vector.length <$> v2))
  | otherwise = False

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

----------------------------------------
-- | Type families

type family
  (f :: [k]) ++ (g :: [k]) :: [k] where
  '[] ++ g       = g
  (f ': fs) ++ g = f ': (fs ++ g)

type family
  Length (xs :: [k]) :: Nat where
  Length '[]       = 0
  Length (_ ': xs) = 1 + Length xs

type family
  Lookup (map :: [(k, v)]) (key :: k) :: v where
  Lookup ('(k, v) ': m) k = v
  Lookup (_       ': m) k = Lookup m k
  Lookup '[]            k = TypeError
    ('Text "Lookup: key not found" ':<>: 'ShowType k)

type family
  Ix (map :: [(k, v)]) (key :: k) :: Nat where
  Ix ('(k,  _) ': m) k = 0
  Ix ('(k', _) ': m) k = 1 + Ix m k
  Ix '[]         k = TypeError
    ('Text "Ix: key not found" ':<>: 'ShowType k)

type family
  Keys (map :: [(k, v)]) :: [k] where
  Keys '[] = '[]
  Keys ('(k, _) ': kvs) = k ': Keys kvs

type family
  Values (map :: [(k, v)]) :: [v] where
  Values '[] = '[]
  Values ('(_, v) ': kvs) = v ': Values kvs

type family
  All (c :: k -> Constraint) (xs :: [k]) :: Constraint where
  All c '[] = ()
  All c (x ': xs) = (c x, All c xs)

----------------------------------------

-- type family DoubleL (xs :: [Nat]) :: [Nat] where
--   DoubleL '[] = '[]
--   DoubleL (x ': xs) = x + x ': DoubleL xs


-- newtype MagicNatL r = MagicNatL (forall (xs :: [Nat]). All KnownNat xs => Proxy xs -> r)

-- reifyNatL :: forall r. [Integer]
--          -> (forall (xs :: [Nat]). All KnownNat xs => Proxy xs -> r)
--          -> r
-- reifyNatL xs k = unsafeCoerce (MagicNatL k :: MagicNatL r) xs Proxy

-- instance Reifies '[] [Integer] where
--   reflect _ = []

-- instance ( Reifies x Integer
--          , Reifies xs [Integer]
--          ) => Reifies (x ': xs) [Integer]
--   where
--     reflect _ = reflect (undefined :: Proxy x)
--               : reflect (undefined :: Proxy xs)


-- predictWithFreqs :: forall spec root freqs spec'.
--                 ( spec' ~ SetSpecFreqs spec freqs
--                 , HasSpec spec' root
--                 ) => QCSize -> Hist
-- predictWithFreqs size = predict @spec' @root size



-- predictWithFreqs :: forall spec root. (HasSpec spec root)
--                  => Integer -> [Integer] -> QCSize -> Hist
-- predictWithFreqs ix freqs
--   = reifyNat ix $ \(Proxy :: Proxy ix')
--   -> reifyNatL freqs $ \(Proxy :: Proxy freqs')
--   -> predict @(SetFamIxFreqs spec ix' freqs') @root

----------------------------------------

-- test :: [Integer] -> [Integer]
-- test xs = reifyNatL xs $ \(Proxy :: Proxy xs')
--   -> let proxy = Proxy :: xs'' ~ Proxy (DoubleL xs') => xs''
--      in reflect proxy

-- type family SetFreqs spec freqs where
--   SetFreqs spec freqs = SetSpecFreqs (Flatten spec) freqs

-- type family AltRepFreq (rep :: [Type -> Type])
--   (ix :: Nat) (f :: Nat)
--   :: [Type -> Type] where
--   AltRepFreq (t ': ts) 0  f = SetFreq t f ': ts
--   AltRepFreq (t ': ts) ix f = t ': AltRepFreq ts (ix - 1) f
--   AltRepFreq _         _  _ = TypeError ('Text "AltRepFreq: index out of bounds")

-- type family AltSpecLFreq
--   (spec :: [(k, [Type -> Type])])
--   (famIx :: Nat) (tyIx :: Nat) (freq :: Nat)
--   :: [(k, [Type -> Type])] where
--   AltSpecLFreq ('(k, t) ': ts) 0 tix f
--     = '(k, AltRepFreq t tix f) ': ts
--   AltSpecLFreq ('(k, t) ': ts) fix tix f
--     = '(k, t) ': AltSpecLFreq ts (fix - 1) tix f
--   AltSpecLFreq _ _ _ _
--     = TypeError ('Text "AltSpecLFreq: index out of bounds")

-- type family AltSpecFreq
--   (fam :: [[Type -> Type]])
--   (famIx :: Nat) (tyIx :: Nat) (freq :: Nat)
--   :: [[Type -> Type]] where
--   AltSpecFreq (t ': ts) 0   tix f = AltRepFreq t tix f ': ts
--   AltSpecFreq (t ': ts) fix tix f = t ': AltSpecFreq ts (fix - 1) tix f
--   AltSpecFreq _         _   _   _ = TypeError ('Text "AltSpecFreq: index out of bounds")

  -- SetFreq (Sum (Freq t _) ts) 0 n = Sum (Freq t n) ts
  -- SetFreq (Sum t          ts) 0 n = Sum (Freq t n) ts
  -- SetFreq (Sum t          ts) i n = Sum t (SetFreq ts (i - 1) n)
  -- SetFreq _                   _ _ = TypeError ('Text "SetFreq: index out of bounds")

-- type family (xs :: [k]) !! (n :: Nat) :: k where
--   (x ':  _) !! 0 = x
--   (_ ': xs) !! n = xs !! (n - 1)
--   x         !! n = TypeError ('Text "!!: index out of bounds")

-- type family
--   SpecToList (spec :: Spec) :: [(Symbol, [Type -> Type])]
--   where
--   SpecToList '[] = '[]
--   SpecToList ('(k, t) ': ts) = '(k, RepToList t) ': SpecToList ts

-- type family
--   ListToSpec (xs :: [(Symbol, [Type -> Type])]) :: Spec
--   where
--   ListToSpec '[] = '[]
--   ListToSpec ('(k, t) ': ts) = '(k, ListToRep t) ': ListToSpec ts

-- type family
--   SetFamIxFreqs (spec :: Spec) (ix :: Nat) (freqs :: [Nat]) :: Spec
--   where
--   SetFamIxFreqs ('(k, x) ': xs) 0 freqs = '(k, SetRepFreqs x freqs) ': xs
--   SetFamIxFreqs ('(k, x) ': xs) n freqs = '(k, x) : SetFamIxFreqs xs (n - 1) freqs
--   SetFamIxFreqs _               _ _ = TypeError ('Text "SetFamIxFreqs: index out of bounds")


-- type family
--   Mutations (xs :: [Nat]) :: [[Nat]]
--   where
--   Mutations xs = Mutations' '[] xs

-- type family
--   Mutations' (hs :: [[Nat]]) (xs :: [Nat])
--   where
--   Mutations' hs '[] = hs
--   Mutations' hs (x ': xs) = Snoc hs x xs
