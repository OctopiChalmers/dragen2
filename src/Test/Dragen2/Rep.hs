module Test.Dragen2.Rep where

import GHC.TypeLits
import GHC.Generics

import Data.Kind

import Test.QuickCheck hiding (Fun)

import Test.Dragen2.Algebra
import Test.Dragen2.BoundedArbitrary
import Test.Dragen2.Branching
import Test.Dragen2.TypeLevel

----------------------------------------
-- | Type-level combinators

newtype Freq (f :: Type -> Type) (n :: Nat)          a = Freq (f a)
newtype Term (f :: Type -> Type)                     a = Term (f a)
data    Sum  (f :: Type -> Type) (g :: Type -> Type) a = InL  (f a) | InR (g a)

----------------------------------------
-- | Derived instances

deriving instance (Show (f a))             => Show (Freq f n a)
deriving instance (Show (f a))             => Show (Term f a)
deriving instance (Show (f a), Show (g a)) => Show (Sum f g a)

deriving instance (Functor f)            => Functor (Freq f n)
deriving instance (Functor f)            => Functor (Term f)
deriving instance (Functor f, Functor g) => Functor (Sum f g)

deriving instance (Generic (f a))                => Generic (Freq f n a)
deriving instance (Generic (f a))                => Generic (Term f a)
deriving instance (Generic (f a), Generic (g a)) => Generic (Sum f g a)

----------------------------------------
-- | Algebra instances

instance Algebra f a => Algebra (Freq f n) a where
  alg (Freq f) = alg f

instance Algebra f a => Algebra (Term f) a where
  alg (Term f) = alg f

instance (Algebra f a, Algebra g a) => Algebra (Sum f g) a where
  alg (InL f) = alg f
  alg (InR g) = alg g

----------------------------------------
-- | Generation frequency of a given type

-- | Branching frequencies in a sum type
-- Defaults to 1
type family
  BranchingFreq (f :: Type -> Type) :: Nat where
  BranchingFreq (Freq f n) = n * BranchingFreq f
  BranchingFreq (Term f)   = BranchingFreq f
  BranchingFreq (Sum f g)  = BranchingFreq f + BranchingFreq g
  BranchingFreq _          = 1

-- | Terminal frequencies in a sum type.
-- Defaults to 0
type family
  TerminalFreq (f :: Type -> Type) :: Nat where
  TerminalFreq (Freq f n) = n * TerminalFreq f
  TerminalFreq (Term f)   = BranchingFreq f
  TerminalFreq (Sum f g)  = TerminalFreq f + TerminalFreq g
  TerminalFreq _          = 0

-- | Check if a representation has at least a single terminal construction
type family
  HasTerminals (f :: Type -> Type) :: Constraint where
  HasTerminals f = FailWhen (TerminalFreq f == 0)
                     f "does not has any terminal constructions"

-- | Type level frequency equality constraint
type HasBranchingFreq t f = (KnownNat f, BranchingFreq t ~ f)
type HasTerminalFreq  t f = (KnownNat f, TerminalFreq  t ~ f)


type family
  FreqList (rep :: Type -> Type) :: [Nat] where
  FreqList (Sum f g) = FreqList f ++ FreqList g
  FreqList f         = '[BranchingFreq f]

type family
  FamFreqsList (reps :: [Type -> Type]) :: [[Nat]] where
  FamFreqsList '[]      = '[]
  FamFreqsList (x : xs) = FreqList x : FamFreqsList xs

----------------------------------------
-- | BoundedArbitrary1 instances

instance BoundedArbitrary1 f => BoundedArbitrary1 (Freq f n) where
  liftBoundedGen gen depth = Freq <$> liftBoundedGen gen depth

instance BoundedArbitrary1 f => BoundedArbitrary1 (Term f) where
  liftBoundedGen gen depth = Term <$> liftBoundedGen gen depth

instance
  ( BoundedArbitrary1 f
  , f `HasBranchingFreq` ff
  , f `HasTerminalFreq`  ff0
  , BoundedArbitrary1 g
  , g `HasBranchingFreq` gg
  , g `HasTerminalFreq`  gg0
  ) => BoundedArbitrary1 (Sum f g)
  where
    liftBoundedGen gen depth =
      if depth == 0
      then case (numVal @ff0, numVal @gg0) of
        (_, 0) -> InL <$> liftBoundedGen gen depth
        (0, _) -> InR <$> liftBoundedGen gen depth
        (ff0, gg0) -> frequency
           [ (ff0, InL <$> liftBoundedGen gen depth)
           , (gg0, InR <$> liftBoundedGen gen depth) ]
      else frequency
           [ (numVal @ff, InL <$> liftBoundedGen gen depth)
           , (numVal @gg, InR <$> liftBoundedGen gen depth) ]


----------------------------------------
-- | BranchingType instances

instance BranchingType f => BranchingType (Freq f n) where
  typeNames          = typeNames @f
  typeAtomic         = typeAtomic @f
  typeBranchingProbs = typeBranchingProbs @f
  typeTerminalProbs  = typeTerminalProbs @f
  typeBeta           = typeBeta @f
  typeEta            = typeEta @f

instance BranchingType f => BranchingType (Term f) where
  typeNames          = typeNames @f
  typeAtomic         = typeAtomic @f
  typeBranchingProbs = typeBranchingProbs @f
  typeTerminalProbs  = typeTerminalProbs @f
  typeBeta           = typeBeta @f
  typeEta            = typeEta @f

instance
  ( BranchingType f
  , f `HasBranchingFreq` ff
  , f `HasTerminalFreq` ff'
  , BranchingType g
  , g `HasBranchingFreq` gg
  , g `HasTerminalFreq` gg'
  ) => BranchingType (Sum f g)
  where
    typeNames
      = typeNames @f <> typeNames @g
    typeAtomic
      = typeAtomic @f <> typeAtomic @g
    typeBranchingProbs
      = fmap (* (ff/tot)) (typeBranchingProbs @f)
        <> fmap (* (gg/tot)) (typeBranchingProbs @g)
      where ff = numVal @ff; gg = numVal @gg; tot = ff + gg
    typeTerminalProbs
      = if tot' == 0
        then fmap (*0) (typeTerminalProbs @f <> typeTerminalProbs @g)
        else fmap (* (ff'/tot')) (typeTerminalProbs @f)
             <> fmap (* (gg'/tot')) (typeTerminalProbs @g)
      where ff' = numVal @ff'; gg' = numVal @gg'; tot' = ff' + gg'
    typeBeta
      = typeBeta @f <> typeBeta @g
    typeEta
      = typeEta  @f <> typeEta  @g

----------------------------------------
-- | Balancing representations

type family
  Multiply (n :: Nat) (fs :: [(Type -> Type,Nat)]) :: [(Type -> Type,Nat)] where
  Multiply _ '[] = '[]
  Multiply x ('(f, n) ': fs) = '(f, x * n) ': Multiply x fs

type family
  SetTerm (fs :: [(Type -> Type, Nat)]) :: [(Type -> Type, Nat)] where
  SetTerm '[] = '[]
  SetTerm ('(f, n) ': fs) = '(Term f, n) : SetTerm fs

type family
  ToFreqList (rep :: Type -> Type) :: [(Type -> Type, Nat)] where
  ToFreqList (Sum f g) = ToFreqList f ++ ToFreqList g
  ToFreqList (Freq f n) = Multiply n (ToFreqList f)
  ToFreqList (Term f) = SetTerm (ToFreqList f)
  ToFreqList f = '[ '(f, 1)]

type family
  BuildTree (fs :: [(Type -> Type, Nat)]) :: Type -> Type where
  BuildTree '[ '(Term f, n)] = Term (BuildTree '[ '(f, n)])
  BuildTree '[ '(f, 1)] = f
  BuildTree '[ '(f, n)] = Freq f n
  BuildTree xs = Sum (BuildTree (FirstHalf xs)) (BuildTree (SecondHalf xs))

type family
  Balance (rep :: Type -> Type) :: Type -> Type where
  Balance f = BuildTree (ToFreqList f)

genRep :: forall f a.
  ( BoundedArbitrary1 (Balance f)
  , Algebra (Balance f) a
  ) => BoundedGen a
genRep depth = genEval @(Balance f) depth

----------------------------------------
-- | Existential types to hide type parameters

data Some1
  (f :: Type -> Type -> Type)
  (r :: Type)
  = forall (a :: Type)
  . Some1 (f a r)

data Some2
  (f :: Type -> Type -> Type -> Type)
  (r :: Type)
  = forall (b :: Type) (a :: Type)
  . Some2 (f a b r)

data Some3
  (f :: Type -> Type -> Type -> Type -> Type)
  (r :: Type)
  = forall (c :: Type) (b :: Type) (a :: Type)
  . Some3 (f a b c r)

data Some4
  (f :: Type -> Type -> Type -> Type -> Type -> Type)
  (r :: Type)
  = forall (d :: Type) (c :: Type) (b :: Type) (a :: Type)
  . Some4 (f a b c d r)

data Some5
  (f :: Type -> Type -> Type -> Type -> Type -> Type -> Type)
  (r :: Type)
  = forall (e :: Type) (d :: Type) (c :: Type) (b :: Type) (a :: Type)
  . Some5 (f a b c d e r)


-- | Apply a type to a hidden type parameter
type family
  Apply (a :: Type) (t :: Type -> Type) :: Type -> Type where
  Apply a (Freq t n) = Freq (Apply a t) n
  Apply a (Term t)   = Term (Apply a t)
  Apply a (Sum l r)  = Sum (Apply a l) (Apply a r)
  Apply a (Some1 t)  = t a
  Apply a (Some2 t)  = Some1 (t a)
  Apply a (Some3 t)  = Some2 (t a)
  Apply a (Some4 t)  = Some3 (t a)
  Apply a (Some5 t)  = Some4 (t a)
  Apply a t          = t


instance (forall a. BranchingType (f a))
       => BranchingType (Some1 f) where
  typeNames          = typeNames           @(f ())
  typeAtomic         = typeAtomic          @(f ())
  typeBranchingProbs = typeBranchingProbs  @(f ())
  typeTerminalProbs  = typeTerminalProbs   @(f ())
  typeBeta           = typeBeta            @(f ())
  typeEta            = typeEta             @(f ())

instance (forall a b. BranchingType (f a b))
      => BranchingType (Some2 f) where
  typeNames           = typeNames           @(f () ())
  typeAtomic          = typeAtomic          @(f () ())
  typeBranchingProbs  = typeBranchingProbs  @(f () ())
  typeTerminalProbs   = typeTerminalProbs   @(f () ())
  typeBeta            = typeBeta            @(f () ())
  typeEta             = typeEta             @(f () ())

instance (forall a b c. BranchingType (f a b c))
      => BranchingType (Some3 f) where
  typeNames           = typeNames           @(f () () ())
  typeAtomic          = typeAtomic          @(f () () ())
  typeBranchingProbs  = typeBranchingProbs  @(f () () ())
  typeTerminalProbs   = typeTerminalProbs   @(f () () ())
  typeBeta            = typeBeta            @(f () () ())
  typeEta             = typeEta             @(f () () ())

instance (forall a b c d. BranchingType (f a b c d))
      => BranchingType (Some4 f) where
  typeNames           = typeNames           @(f () () () ())
  typeAtomic          = typeAtomic          @(f () () () ())
  typeBranchingProbs  = typeBranchingProbs  @(f () () () ())
  typeTerminalProbs   = typeTerminalProbs   @(f () () () ())
  typeBeta            = typeBeta            @(f () () () ())
  typeEta             = typeEta             @(f () () () ())

instance (forall a b c d e. BranchingType (f a b c d e))
     => BranchingType (Some5 f) where
  typeNames           = typeNames           @(f () () () () ())
  typeAtomic          = typeAtomic          @(f () () () () ())
  typeBranchingProbs  = typeBranchingProbs  @(f () () () () ())
  typeTerminalProbs   = typeTerminalProbs   @(f () () () () ())
  typeBeta            = typeBeta            @(f () () () () ())
  typeEta             = typeEta             @(f () () () () ())


----------------------------------------
-- | Type families to hide TH unique names

-- | Whole types, functions or interface call
type family Rep (t :: Symbol) :: Type -> Type

-- | A single constructor
type family Con (c :: Symbol) :: Type -> Type
type Con' a = Term (Con a)

-- | A single function call
type family Fun (t :: Symbol) :: Type -> Type
type Fun' a = Term (Fun a)

-- | A single pattern matching
type family Pat (p :: Symbol) (n :: Nat) :: Type -> Type
type Pat' a n = Term (Pat a n)
