{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Test.QuickCheck.HRep.TH where

import Data.Proxy

import Control.Monad.Extra

import Language.Haskell.TH
import Language.Haskell.TH.Desugar

import Test.QuickCheck.HRep.TH.TypeRep
import Test.QuickCheck.HRep.TH.FunPatsRep
import Test.QuickCheck.HRep.TH.ModIntRep
import Test.QuickCheck.Branching

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
    , fam :: [Name]
    , blacklist :: [Name]
    } deriving Show


type_ :: Name -> Target
type_ tyName = TypeDefinition tyName [tyName]

patterns :: Name -> Target
patterns funName = FunctionPatterns funName 1 []

interface :: Name -> Target
interface tyName = ModuleInterface tyName ("[" ++ nameBase tyName ++ "]") [] []


derive :: Target -> Q [Dec]
derive (TypeDefinition tyName tyFam)
  = deriveTypeRep tyName tyFam
derive (FunctionPatterns funName funArgNr tyFam)
  = deriveFunPatsRep funName funArgNr tyFam
derive (ModuleInterface tyName modAlias tyFam blacklist)
  = deriveModIntRep tyName modAlias tyFam blacklist


deriveHRep :: [Name] -> [Target] -> Q [Dec]
deriveHRep fam_ targets = concatMapM derive
  (setFam <$> ((type_ <$> fam_) ++ targets))
  where setFam target = target { fam = fam_ }


----------------------------------------
-- | Derive Arbitrary instances using a generation specification

deriveArbitrary :: Name -> Name -> Q [Dec]
deriveArbitrary tyName spec = do
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
                     `DAppT` DLitT (StrTyLit (nameBase tyName))
      arbLetDec = DLetDec (DFunD 'QC.arbitrary [arbClause])
      arbClause = DClause [] arbBody
      arbBody = DAppTypeE (DVarE 'HRep.genEval) arbTyApp

      mkCxt v = DAppPr (DConPr ''QC.Arbitrary) (dTyVarBndrToDType v)

  return (sweeten [arbIns])


deriveArbitraries :: [Name] -> Name -> Q [Dec]
deriveArbitraries tyFam spec = concatMapM (flip deriveArbitrary spec) tyFam

----------------------------------------
-- | Derive all the stuff

deriveAll :: [Name] -> [Target] -> Name -> Q [Dec]
deriveAll tyFam targets specName = do
  typeReps <- concatMapM (\tn -> derive (TypeDefinition tn tyFam)) tyFam
  arbIns   <- concatMapM (\tn -> deriveArbitrary tn specName) tyFam
  tgtReps  <- concatMapM (\target -> derive (target {fam = tyFam})) targets
  return (concat [typeReps, arbIns, tgtReps])

----------------------------------------
-- | Optimize the frequencies of a specification

optimizeSpec :: forall spec root. HasSpec spec root
         => Name -> DistFun -> QCSize -> Q Type
optimizeSpec specName dist size = do
  let !newFreqs = optimize @spec @root size dist

      promoteList = foldr (\n -> appT (appT promotedConsT (litT (numTyLit n)))) promotedNilT
      promoteSpec = foldr (\t -> appT (appT promotedConsT (promoteList t))) promotedNilT

  [t| SetSpecFreqs (MkSpec $(conT specName)) $(promoteSpec newFreqs) |]
  -- [t| type instance Optimized $(litT (strTyLit specAlias))

type WithFreqs spec freqs = SetSpecFreqs (MkSpec spec) freqs

liftFreqs :: [[Integer]] -> Q Type
liftFreqs freqs = promoteSpec freqs
  where
    promoteList = foldr (\n -> appT (appT promotedConsT (litT (numTyLit n)))) promotedNilT
    promoteSpec = foldr (\t -> appT (appT promotedConsT (promoteList t))) promotedNilT


----------------------------------------
-- | Optimize the frequencies of a specification
deriveTySyn :: Name -> [[Integer]] -> Q Type
deriveTySyn specName freqs = do

  let promoteList = foldr (\n -> appT (appT promotedConsT (litT (numTyLit n)))) promotedNilT
      promoteSpec = foldr (\t -> appT (appT promotedConsT (promoteList t))) promotedNilT

  [t| SetSpecFreqs (MkSpec $(conT specName)) $(promoteSpec freqs) |]
