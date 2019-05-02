module Test.Dragen2.Spec where

import Data.Kind
import GHC.TypeLits

import Data.Map.Strict (Map)
import qualified Data.Matrix as Matrix
import qualified Data.Vector as Vector
import qualified Data.Map.Strict as Map

import Test.QuickCheck

import Test.Dragen2.Algebra
import Test.Dragen2.BoundedArbitrary
import Test.Dragen2.Branching
import Test.Dragen2.Countable
import Test.Dragen2.Prediction
import Test.Dragen2.Rep
import Test.Dragen2.TypeLevel


----------------------------------------
-- | Generation specifications

type Spec = [(Symbol, Type -> Type)]

-- | Synonym to hide annoying KnownNats constraints
type StartingFrom (spec :: Spec) (root :: Symbol)
  = ( KnownNat (Length (Values spec))
    , KnownNat (Ix spec root)
    , KnownNatss (SpecFreqs (MkSpec spec))
    , Predictable (Values spec))


-- | Extract the frequencies of a Spec
type family
  SpecFreqs (spec :: Spec) :: [[Nat]] where
  SpecFreqs '[] = '[]
  SpecFreqs ('(k, x) : xs) = RepFreqs x : SpecFreqs xs

type family
  RepFreqs (rep :: Type -> Type) :: [Nat] where
  RepFreqs (Sum f g) = RepFreqs f ++ RepFreqs g
  RepFreqs f = '[BranchingFreq f]


-- | Set the frequencies of a Spec
type (spec <<< freqs) = SetSpecFreqs (MkSpec spec) freqs

type family
  SetSpecFreqs (spec :: Spec) (freqs :: [[Nat]]) :: Spec where
  SetSpecFreqs '[] '[] = '[]
  SetSpecFreqs ('(k, t) ': ts) (f ': fs)
    = '(k, SetRepFreqs t f) ': SetSpecFreqs ts fs
  SetSpecFreqs _ _
    = TypeError ('Text "SetFamFreqs: mismatched sizes")

type family
  SetRepFreqs (rep :: Type -> Type) (freqsL :: [Nat]) :: Type -> Type where
  SetRepFreqs (Sum f g) (ff ': gg) = Sum (SetFreq f ff) (SetRepFreqs g gg)
  SetRepFreqs t '[f] = SetFreq t f
  SetRepFreqs _ _ = TypeError ('Text "SetRepFreqs: mismatched sizes")

type family
  SetFreq (rep :: Type -> Type) (freq :: Nat) :: Type -> Type where
  SetFreq (Freq t n) m = Freq t (n * m)
  SetFreq t          n = Freq t n


-- | Build a normalized spec
type family
  MkSpec (spec :: Spec) :: Spec where
  MkSpec spec = Flatten spec

type family
  Flatten (spec :: Spec) :: Spec where
  Flatten '[] = '[]
  Flatten ('(k, t) : ts) = '(k, Balance (List2Rep (Rep2List t))) : Flatten ts

type family
  Rep2List (rep :: Type -> Type) :: [Type -> Type] where
  Rep2List (Sum f g) = Rep2List f ++ Rep2List g
  Rep2List t = '[t]

type family
  List2Rep (xs :: [Type -> Type]) :: Type -> Type where
  List2Rep '[t] = t
  List2Rep (x : xs) = Sum x (List2Rep xs)


----------------------------------------
-- | Predict the distribution of a given spec

type Hist = Map String Double

predictSpec
  :: forall spec root fam ix.
     ( spec `StartingFrom` root
     , fam ~ Values spec
     , ix  ~ Ix spec root
     , Predictable fam)
  => MaxDepth -> Hist
predictSpec maxDepth
  = Map.fromList $ zip
    (Vector.toList (foldr1 (<>) (famNames @fam)))
    (Matrix.toList (predictFam @fam (numVal @ix) maxDepth))

predictSpecExpanded
  :: forall spec root fam ix.
     ( spec `StartingFrom` root
     , fam ~ Values spec
     , ix  ~ Ix spec root
     , Predictable fam)
  => MaxDepth -> Hist
predictSpecExpanded maxDepth
  = Map.fromList $ zip
    (Vector.toList (foldr1 (<>) (atomicNames @fam)))
    (Matrix.toList (predictFamExpanded @fam (numVal @ix) maxDepth))

predictSpecWith
  :: forall spec root fam ix.
     ( spec `StartingFrom` root
     , fam ~ Values spec
     , ix ~ Ix spec root
     , Predictable fam)
  => [[Integer]] -> MaxDepth -> Hist
predictSpecWith newFreqs maxDepth
  = Map.fromList $ zip
    (Vector.toList (foldr1 (<>) (famNames @fam)))
    (Matrix.toList (predictFamWith @fam newFreqs (numVal @ix) maxDepth))

predictSpecExpandedWith
  :: forall spec root fam ix.
     ( spec `StartingFrom` root
     , fam ~ Values spec
     , ix  ~ Ix spec root
     , Predictable fam)
  => [[Integer]] -> MaxDepth -> Hist
predictSpecExpandedWith newFreqs maxDepth
  = Map.fromList $ zip
    (Vector.toList (foldr1 (<>) (atomicNames @fam)))
    (Matrix.toList (predictFamExpandedWith @fam newFreqs (numVal @ix) maxDepth))


----------------------------------------
-- | Sample a bunch of random values and calculate its distribution

sampleSpecHist :: forall spec root rep.
  ( spec `StartingFrom` root
  , rep ~ Lookup spec root
  , BoundedArbitrary1 rep
  , Countable (Fix rep)
  ) => MaxDepth -> Int -> IO Hist
sampleSpecHist maxDepth samples = do
  let gen = genFix @rep
  values <- sequence $ replicate samples $ generate $ gen maxDepth
  return (consAvg (count <$> values))

sampleEvalSpecHist :: forall spec root rep target.
  ( spec `StartingFrom` root
  , rep ~ Lookup spec root
  , BoundedArbitrary1 rep
  , Algebra rep target
  , Countable target)
  => MaxDepth -> Int -> IO Hist
sampleEvalSpecHist maxDepth samples = do
  let gen = genEval @rep
  values <- sequence $ replicate samples $ generate $ gen maxDepth
  return (consAvg (count <$> values))
