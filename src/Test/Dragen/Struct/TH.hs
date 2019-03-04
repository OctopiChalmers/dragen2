{-# LANGUAGE NamedFieldPuns #-}

module Test.Dragen.Struct.TH where

import Data.Proxy

import Control.Monad.Extra

import Language.Haskell.TH
import Language.Haskell.TH.Desugar

import Test.QuickCheck
import Test.Dragen.Struct.Rep
import Test.Dragen.Struct.Spec
import Test.Dragen.Struct.Optimization
import Test.Dragen.Struct.BoundedArbitrary
import Test.Dragen.Struct.TypeLevel

import Test.Dragen.Struct.TH.Util
import Test.Dragen.Struct.TH.TypeDef
import Test.Dragen.Struct.TH.TypeInt
import Test.Dragen.Struct.TH.FunPats

----------------------------------------
-- | Derivation targets and dispatcher

type MutRecFam = [Name]
type Blacklist = [Name]

data Target
  = TypeDef
    { typeName_  :: Name
    , blacklist_ :: Blacklist
    , typeFam_   :: MutRecFam }
  | TypeInt
    { typeName_  :: Name
    , alias_     :: String
    , blacklist_ :: Blacklist
    , path_      :: Maybe FilePath
    , typeFam_   :: MutRecFam }
  | FunPats
    { funName_ :: Name
    , argNum_  :: Int
    , path_    :: Maybe FilePath
    , typeFam_ :: MutRecFam }


-- | Simple smart constructors
constructors :: Name -> Target
constructors tname = TypeDef tname [] []

interface :: Name -> Target
interface tname = TypeInt tname ("(-> " ++ nameBase tname ++ ")") [] Nothing []

patterns :: Name -> Target
patterns fname = FunPats fname 1 Nothing []

-- | Simple target modifiers
(|>) :: Target -> (Target -> Target) -> Target
(|>) t m = m t

infixl |>

blacklist :: Blacklist -> Target -> Target
blacklist b t = t { blacklist_ = blacklist_ t ++ b }

alias :: String -> Target -> Target
alias a t = t { alias_ = a }

argNum :: Int -> Target -> Target
argNum n t = t { argNum_ = n }

path :: FilePath -> Target -> Target
path p t = t { path_ = Just p }


-- | TH target dispatcher
deriveTarget :: Target -> Q [Dec]
deriveTarget (TypeDef typeName _blacklist typeFam)
  = sweeten <$> deriveTypeDef typeName _blacklist typeFam
deriveTarget (TypeInt typeName _alias _blacklist _path typeFam)
  = sweeten <$> deriveTypeInt typeName _alias _blacklist _path typeFam
deriveTarget (FunPats funName _argNum _path typeFam)
  = sweeten <$> deriveFunPats funName _argNum _path typeFam


-- | Derive multiple target using the same family of mutually recursive types
derive :: MutRecFam -> [Target] -> Q [Dec]
derive fam targets
  = concatMapM deriveTarget (setFam <$> targets)
  where setFam target = target { typeFam_ = fam }

----------------------------------------
-- | Derive BoundedArbitrary instances using a generation specification

deriveBoundedArbitrary :: [Name] -> Name -> Q [Dec]
deriveBoundedArbitrary typeFam spec
  = concatMapM deriveInstance typeFam
  where
    deriveInstance typeName = do

      -- Reify the original data definition
      (vs, _) <- getDataD (nameBase typeName) typeName
      freeTypeVars <- mapM desugar vs

      -- Create the appropriate BoundedArbitrary instances based on the given
      -- generation specification
      let arbIns = DInstanceD Nothing arbCxt arbTy [arbLetDec]
          arbCxt = mkCxt <$> freeTypeVars
          arbTy  = ''BoundedArbitrary <<# [typeName <<* freeTypeVars]
          arbTyApp = foldl (\t v -> DConT ''Apply `DAppT` v `DAppT` t)
                     arbTyAppBase
                     (dTyVarBndrToDType <$> freeTypeVars)
          arbTyAppBase = DConT ''Lookup
                         `DAppT` DConT spec
                         `DAppT` thNameTyLit typeName
          arbLetDec = DLetDec (DFunD 'boundedArbitrary [arbClause])
          arbClause = DClause [] arbBody
          arbBody = DAppTypeE (DVarE 'genEval) arbTyApp

          mkCxt v = DAppPr (DConPr ''Arbitrary) (dTyVarBndrToDType v)

      -- Return all the stuff
      dragenMsg "derived BoundedArbitrary instance:" [arbIns]
      return (sweeten [arbIns])


----------------------------------------
-- | Optimize the frequencies of a specification

optimize
  :: forall spec root.
     spec `StartingFrom` root
  => DistFun -> MaxDepth -> Q Type
optimize dist depth = do

  dragenMsg' "optimizing frequencies"

  let oldFreqs = map (const 1) <$> natValss (Proxy @(SpecFreqs (MkSpec spec)))
      newFreqs = optimizeFreqs @spec @root depth dist oldFreqs

      promoteSpec = flip foldr promotedNilT $ \t ->
        appT (appT promotedConsT (promoteList t))
      promoteList = flip foldr promotedNilT $ \n ->
        appT (appT promotedConsT (litT (numTyLit n)))

  promoteSpec newFreqs
