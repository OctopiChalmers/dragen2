{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE BangPatterns #-}

module Test.Dragen2.TH where

import Data.Maybe
import Data.Proxy

import Control.Monad.Extra

import Language.Haskell.TH
import Language.Haskell.TH.Desugar

import Test.QuickCheck
import Test.Dragen2.Rep
import Test.Dragen2.Spec
import Test.Dragen2.Optimization
import Test.Dragen2.BoundedArbitrary
import Test.Dragen2.TypeLevel

import Test.Dragen2.TH.Util
import Test.Dragen2.TH.TypeDef
import Test.Dragen2.TH.TypeInt
import Test.Dragen2.TH.FunPats

----------------------------------------
-- | Derivation targets and dispatcher

type MutRecFam = [Name]
type Blacklist = [Name]

data Target
  = TypeDef
    { typeName_  :: Name
    , blacklist_ :: Blacklist
    , typeFam_   :: MutRecFam
    , branching_ :: Bool }
  | TypeInt
    { typeName_  :: Name
    , alias_     :: String
    , blacklist_ :: Blacklist
    , path_      :: Maybe FilePath
    , typeFam_   :: MutRecFam
    , branching_ :: Bool }
  | FunPats
    { funName_   :: Name
    , argNum_    :: Int
    , path_      :: Maybe FilePath
    , typeFam_   :: MutRecFam
    , branching_ :: Bool }


-- | Simple smart constructors
constructors :: Name -> Target
constructors tname
  = TypeDef tname [] [] False

interface :: Name -> Target
interface tname
  = TypeInt tname ("(-> " ++ nameBase tname ++ ")") [] Nothing [] False

patterns :: Name -> Target
patterns fname
  = FunPats fname 1 Nothing [] False

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

branching :: Target -> Target
branching t = t { branching_ = True }

-- | TH target dispatcher
deriveTarget :: Target -> Q [Dec]
deriveTarget (TypeDef typeName _blacklist typeFam branching)
  = sweeten <$> deriveTypeDef typeName _blacklist typeFam branching
deriveTarget (TypeInt typeName _alias _blacklist _path typeFam branching)
  = sweeten <$> deriveTypeInt typeName _alias _blacklist _path typeFam branching
deriveTarget (FunPats funName _argNum _path typeFam branching)
  = sweeten <$> deriveFunPats funName _argNum _path typeFam branching


-- | Derive multiple target using the same family of mutually recursive types
derive :: MutRecFam -> [Target] -> Q [Dec]
derive fam targets
  = concatMapM deriveTarget (setFam <$> targets)
  where setFam target = target { typeFam_ = fam }

----------------------------------------
-- | Derive BoundedArbitrary instances using a generation specification

deriveBoundedArbitrary :: [(Name, [Maybe Name])] -> Name -> Q [Dec]
deriveBoundedArbitrary typeFam spec
  = concatMapM deriveInstance typeFam
  where
    deriveInstance (typeName, typeCxt) = do

      -- Reify the original data definition
      (vs, _) <- getDataD (nameBase typeName) typeName
      freeTypeVars <- mapM desugar vs

      -- Create the constraints from the user provided context
      let extCxt = catMaybes (zipWith applyCxt typeCxt freeTypeVars)
          applyCxt (Just c) v = Just (DAppPr (DConPr c) (dTyVarBndrToDType v))
          applyCxt _ _        = Nothing

      -- Create the appropriate BoundedArbitrary instances based on the given
      -- generation specification
      let arbIns = DInstanceD Nothing (arbCxt ++ extCxt) arbTy [arbLetDec]
          arbCxt = mkArbCxt <$> freeTypeVars
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

          mkArbCxt v = DAppPr (DConPr ''Arbitrary) (dTyVarBndrToDType v)

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

  dragenMsg' "optimizing frequencies:"

  let !oldFreqs = map (const 1) <$> natValss (Proxy @(SpecFreqs (MkSpec spec)))
      !newFreqs = optimizeFreqs @spec @root depth dist oldFreqs

      promoteSpec = flip foldr promotedNilT $ \t ->
        appT (appT promotedConsT (promoteList t))
      promoteList = flip foldr promotedNilT $ \n ->
        appT (appT promotedConsT (litT (numTyLit n)))

  dragenMsg "optimized frequencies:" [show newFreqs]
  promoteSpec newFreqs
