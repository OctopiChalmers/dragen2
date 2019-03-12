module Test.Dragen2.Branching where

import Data.Kind

import Data.Vector (Vector, (!))
import qualified Data.Vector as Vector


-- | Nested vectors
type Vector2 a = Vector (Vector a)
type Vector3 a = Vector (Vector (Vector a))
type Vector4 a = Vector (Vector (Vector (Vector a)))

----------------------------------------
-- | BranchingType type class

class BranchingType (ty :: Type -> Type) where
  -- | The construction name
  typeNames :: Vector String
  -- | Is this construction representing a single constructor?
  typeAtomic :: Vector Bool
  -- | The generation frequency when size > 0
  typeBranchingProbs :: Vector Double
  -- | The generation frequency when size = 0
  typeTerminalProbs :: Vector Double
  -- | The "branching factor" to each member of the mutually recursive family
  typeBeta :: Vector2 Double
  -- | The "expansion factor" to each member of the mutually recursive family
  typeEta :: Vector3 Double


----------------------------------------
-- | BranchingFam type class

class BranchingFam (fam :: [Type -> Type]) where
  famNames          :: Vector2 String
  famAtomic         :: Vector2 Bool
  famBranchingProbs :: Vector2 Double
  famTerminalProbs  :: Vector2 Double
  famBeta           :: Vector3 Double
  famEta            :: Vector4 Double


instance BranchingFam '[] where
  famNames          = Vector.empty
  famAtomic         = Vector.empty
  famBranchingProbs = Vector.empty
  famTerminalProbs  = Vector.empty
  famBeta           = Vector.empty
  famEta            = Vector.empty

instance (BranchingType f, BranchingFam fs) => BranchingFam (f ': fs) where
  famNames          = Vector.singleton (typeNames @f)
                      <> famNames @fs
  famAtomic         = Vector.singleton (typeAtomic @f)
                      <> famAtomic @fs
  famBranchingProbs = Vector.singleton (typeBranchingProbs @f)
                      <> famBranchingProbs @fs
  famTerminalProbs  = Vector.singleton (typeTerminalProbs @f)
                      <> famTerminalProbs @fs
  famBeta           = Vector.singleton (typeBeta @f)
                      <> famBeta @fs
  famEta            = Vector.singleton (typeEta @f)
                      <> famEta @fs

----------------------------------------
-- | Vector dereferences

-- | The index of a type within a family of mutually recursive types
type FamIx  = Int

names :: forall fam. BranchingFam fam => FamIx -> Vector String
names ix = famNames @fam ! ix

atomic :: forall fam. BranchingFam fam => FamIx -> Vector Bool
atomic ix = famAtomic @fam ! ix

branchingProbs :: forall fam. BranchingFam fam => FamIx -> Vector Double
branchingProbs ix = famBranchingProbs @fam ! ix

terminalProbs :: forall fam. BranchingFam fam => FamIx -> Vector Double
terminalProbs ix = famTerminalProbs @fam ! ix

beta :: forall fam. BranchingFam fam => FamIx -> FamIx -> Vector Double
beta from to = (!to) <$> famBeta @fam ! from

eta :: forall fam. BranchingFam fam => FamIx -> FamIx -> Vector2 Double
eta from to = (!to) <$> famEta @fam ! from

atomicNames :: forall fam. BranchingFam fam => Vector2 String
atomicNames = flip Vector.imap (famNames @fam) $ \fix ->
  Vector.ifilter (\cix  -> const ((atomic @fam fix) ! cix))
