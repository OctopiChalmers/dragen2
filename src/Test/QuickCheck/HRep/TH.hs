{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module Test.QuickCheck.HRep.TH where

import Data.Reflection

import Control.Monad.Extra

import Language.Haskell.TH
import Language.Haskell.TH.Desugar

import Test.QuickCheck.HRep.TH.TypeRep
import Test.QuickCheck.HRep.TH.FunPatsRep
import Test.QuickCheck.HRep.TH.ModIntRep

import Test.QuickCheck.HRep.TH.Common

import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.HRep as HRep
import qualified Test.QuickCheck.Branching as Branching

----------------------------------------
-- Derivation target and dispatcher

data Target
  = TypeDefinition
    { ty :: Name
    , fam :: [Name] }
  | FunctionPatterns
    { fun :: Name
    , arg :: Int
    , fam :: [Name] }
  | ModuleInterface
    { ty :: Name
    , alias :: String
    , fam :: [Name] }

type_ :: Name -> Target
type_ tyName = TypeDefinition tyName [tyName]

patterns_ :: Name -> Target
patterns_ funName = FunctionPatterns funName 1 []

module_ :: Name -> Target
module_ tyName = ModuleInterface tyName ("<" ++ nameBase tyName ++ ">") []

derive :: Target -> Q [Dec]
derive (TypeDefinition tyName tyFam)
  = deriveTypeDefinitionRep tyName tyFam
derive (FunctionPatterns funName funArgNr tyFam)
  = deriveFunctionPatternsRep funName funArgNr tyFam
derive (ModuleInterface tyName modAlias _)
  = deriveModuleInterfaceRep tyName modAlias

deriveHRep :: [Name] -> [Target] -> Q [Dec]
deriveHRep fam' targets = concatMapM derive
  (setFam <$> ((type_ <$> fam') ++ targets))
  where setFam target = target { fam = fam' }


----------------------------------------
-- | Derive Arbitrary instances using a generation specification

deriveArbitrary :: [Name] -> Name -> Q [Dec]
deriveArbitrary tys spec = concatMapM go tys
  where
    go :: Name -> Q [Dec]
    go tyName = do
      (vs, _) <- getDataD mempty tyName
      tyVars <- mapM desugar vs

      let arbIns = DInstanceD Nothing arbCxt arbTy [arbLetDec]
          arbCxt = mkCxt <$> tyVars
          arbTy  = ''QC.Arbitrary <<| [tyName <<* tyVars]
          arbTyApp = foldl (\t v -> DConT ''HRep.Apply `DAppT` v `DAppT` t)
                     arbTyAppBase
                     (dTyVarBndrToDType <$> tyVars)
          arbTyAppBase = DConT ''Branching.Lookup
                         `DAppT` DConT spec
                         `DAppT` DConT tyName
          arbLetDec = DLetDec (DFunD 'QC.arbitrary [arbClause])
          arbClause = DClause [] arbBody
          arbBody = DAppTypeE (DVarE 'HRep.genEval) arbTyApp

          mkCxt v = DAppPr (DConPr ''QC.Arbitrary) (dTyVarBndrToDType v)

      return (sweeten [arbIns])



-- ----------------------------------------
-- -- | Derive all the stuff
-- deriveAll :: Name -> [(Name, Int)] -> Bool -> Q [Dec]
-- deriveAll ogTyName funcsNameArgs reducePatSize = do
--   ogTyRep <- deriveTypeRep ogTyName
--   let derivePat = deriveFunRep reducePatSize
--   funPatsReps <- concatMapM (uncurry derivePat) funcsNameArgs
--   return (ogTyRep ++ funPatsReps)
