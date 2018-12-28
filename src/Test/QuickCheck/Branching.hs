{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.QuickCheck.Branching where

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

type family Length (xs :: [k]) :: Nat where
  Length '[]       = 0
  Length (_ ': xs) = 1 + Length xs

famSize :: forall xs n a. (Length xs ~ n, Reifies n Integer, Num a) => a
famSize = fromIntegral (reflect (Proxy @n))

-- type family (xs :: [k]) !! (n :: Nat) :: k where
--   (x ':  _) !! 0 = x
--   (_ ': xs) !! n = xs !! (n - 1)
--   x         !! n = TypeError ('Text "!!: index out of bounds")

type family Lookup (map :: [(k, v)]) (key :: k) :: v where
  Lookup ('(k, v) ': m) k = v
  Lookup (_       ': m) k = Lookup m k
  Lookup '[]            k = TypeError
    ('Text "Lookup: key not found" ':<>: 'ShowType k)

type family Ix (map :: [(k, v)]) (key :: k) :: Nat where
  Ix ('(k,  _) ': m) k = 0
  Ix ('(k', _) ': m) k = 1 + Ix m k
  Ix '[]         k = TypeError
    ('Text "Ix: key not found" ':<>: 'ShowType k)

type family Keys (map :: [(k, v)]) :: [k] where
  Keys '[] = '[]
  Keys ('(k, _) ': kvs) = k ': Keys kvs

type family Values (map :: [(k, v)]) :: [v] where
  Values '[] = '[]
  Values ('(_, v) ': kvs) = v ': Values kvs

type family ApplySpec (a :: Type) (ts :: [(k, Type -> Type)])
  :: [(k, Type -> Type)] where
  ApplySpec _ '[] = '[]
  ApplySpec a ('(k, t) ': ts) = '(k, Apply a t) ': ApplySpec a ts


type Branching fam
  = ( BranchingFam fam
    , KnownNat (Length fam))

type HasSpec spec root
  = ( Branching (Values spec)
    , KnownNat (Length (Values spec))
    , KnownNat (Ix spec root))

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
-- | Vector and Matrix utilities

(.+.), (.*.) :: Vector Double -> Vector Double -> Vector Double
(.+.) = Vector.zipWith (+)
(.*.) = Vector.zipWith (*)

col, row :: Vector a -> Matrix a
col = Matrix.colVector
row = Matrix.rowVector

vec :: Matrix a -> Vector a
vec = Matrix.getRow 1

build :: Int -> Int -> (Int -> Int -> Matrix a) -> Matrix a
build rn cn mkElem = foldr1 (<->) (mkRow <$> [1..rn])
  where mkRow r = foldr1 (<|>) (mkElem r <$> [1..cn])

----------------------------------------
-- | Prediction

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
      | n == 100    = trace "lastLevel: could not reach a fixed point!" acc
      | acc == acc' = acc
      | otherwise   = accumLast (n + 1) acc' (branch prev)
      where acc' = acc + branch prev

-- | Predict the representation distribution
predictRep' :: forall fam. Branching fam => FamIx -> QCSize -> Matrix Double
predictRep' ix size = branchingLevels @fam ix size + lastLevel @fam ix size

-- | Predict the original distribution by expanding the representation
predict' :: forall fam. Branching fam => FamIx -> QCSize -> Matrix Double
predict' ix size = predictRep' @fam ix size * expand @fam


predictRep :: forall spec root fam ix.
  ( HasSpec spec root
  , fam ~ Values spec
  , ix ~ Ix spec root
  ) => QCSize -> Hist
predictRep size
  = Map.fromList $ zip
    (Vector.toList (foldr1 (<>) (famNames @fam)))
    (Matrix.toList (predictRep' @fam (numVal @ix) size))

predict :: forall spec root fam ix.
  ( HasSpec spec root
  , fam ~ Values spec
  , ix  ~ Ix spec root
  ) => QCSize -> Hist
predict size
  = Map.fromList $ zip
    (Vector.toList (foldr1 (<>) (atomicNames @fam)))
    (Matrix.toList (predict' @fam (numVal @ix) size))


----------------------------------------
-- | Prediction confirmation

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
-- | Optimization

-- type family All (c :: k -> Constraint) (xs :: [k]) :: Constraint where
--   All c '[] = ()
--   All c (x ': xs) = (c x, All c xs)


class KnownNatL (ns :: [Nat]) where
  natLVal  :: proxy ns -> [Integer]

instance KnownNatL '[] where
  natLVal  _ = []

instance (KnownNat n, KnownNatL ns) => KnownNatL (n ': ns) where
  natLVal  _ = natVal (Proxy :: Proxy n) : natLVal (Proxy :: Proxy ns)

class KnownNatLL (ns :: [[Nat]]) where
  natLLVal :: proxy ns -> [[Integer]]

instance KnownNatLL '[] where
  natLLVal  _ = []

instance (KnownNatL n, KnownNatLL ns) => KnownNatLL (n ': ns) where
  natLLVal  _ = natLVal (Proxy :: Proxy n) : natLLVal (Proxy :: Proxy ns)

type family (f :: [k]) ++ (g :: [k]) :: [k] where
  '[] ++ g       = g
  (f ': fs) ++ g = f ': (fs ++ g)



type family RepToList (rep :: Type -> Type) :: [Type -> Type] where
  RepToList (Sum f g) = RepToList f ++ RepToList g
  RepToList t = '[t]

type family SpecToList (spec :: [(k, Type -> Type)]) :: [(k, [Type -> Type])] where
  SpecToList '[] = '[]
  SpecToList ('(k, t) ': ts) = '(k, RepToList t) ': SpecToList ts

type family ListToRep (xs :: [Type -> Type]) :: Type -> Type where
  ListToRep '[] = TypeError ('Text "ListToRep: empty list")
  ListToRep '[t] = t
  ListToRep (x ': xs) = Sum x (ListToRep xs)


type family ListToSpec (xs :: [(k, [Type -> Type])]) :: [(k, Type -> Type)] where
  ListToSpec '[] = '[]
  ListToSpec ('(k, t) ': ts) = '(k, ListToRep t) ': ListToSpec ts

type family FlattenRep (rep :: Type -> Type) :: Type -> Type where
  FlattenRep rep = ListToRep (RepToList rep)

type family FlattenSpec (spec :: [(k, Type -> Type)]) :: [(k, Type -> Type)] where
  FlattenSpec '[] = '[]
  FlattenSpec ('(k, t) ': ts) = '(k, FlattenRep t) ': FlattenSpec ts



type family RepFreqList (elem :: Type -> Type) :: [Nat] where
  RepFreqList (Sum f g) = RepFreqList f ++ RepFreqList g
  RepFreqList f = '[Frequency f]

type family FamFreqList (elem :: [Type -> Type]) :: [[Nat]] where
  FamFreqList '[] = '[]
  FamFreqList (x ': xs) = RepFreqList x ': FamFreqList xs



type family SetFreq (rep :: Type -> Type) (freq :: Nat) :: Type -> Type where
  SetFreq (Freq t _) n = Freq t n
  SetFreq t          n = Freq t n

type family SetRepFreqs (rep :: Type -> Type) (freqsL :: [Nat]) :: Type -> Type where
  SetRepFreqs (Sum f g) (ff ': gg) = Sum (SetFreq f ff) (SetRepFreqs g gg)
  SetRepFreqs t '[f] = Freq t f
  SetRepFreqs _ _ = TypeError ('Text "SetRepFreqs: mismatched sizes")

type family SetSpecFreqs (spec :: [(k, Type -> Type)]) (freqs :: [[Nat]])
  :: [(k, Type -> Type)] where
  SetSpecFreqs '[] '[] = '[]
  SetSpecFreqs ('(k, t) ': ts) (f ': fs) = '(k, SetRepFreqs t f) ': SetSpecFreqs ts fs
  SetSpecFreqs _ _ = TypeError ('Text "SetFamFreqs: mismatched sizes")


type family Spec (spec :: [(k, Type -> Type)]) :: [(k, Type -> Type)] where
  Spec spec = FlattenSpec spec

-- type family SetFreqs spec freqs where
--   SetFreqs spec freqs = SetSpecFreqs (FlattenSpec spec) freqs

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

predictWithFreqs :: forall spec root freqs spec'.
                ( spec' ~ SetSpecFreqs spec freqs
                , HasSpec spec' root
                ) => QCSize -> Hist
predictWithFreqs size = predict @spec' @root size
  -- =  reifyNat fix $ \(Proxy :: Proxy fix')
  -- -> reifyNat tix $ \(Proxy :: Proxy tix')
  -- -> reifyNat f   $ \(Proxy :: Proxy f')


  -- SetFreq (Sum (Freq t _) ts) 0 n = Sum (Freq t n) ts
  -- SetFreq (Sum t          ts) 0 n = Sum (Freq t n) ts
  -- SetFreq (Sum t          ts) i n = Sum t (SetFreq ts (i - 1) n)
  -- SetFreq _                   _ _ = TypeError ('Text "SetFreq: index out of bounds")
