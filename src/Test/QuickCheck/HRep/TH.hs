{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module Test.QuickCheck.HRep.TH where

import Data.Reflection

import Control.Monad.Extra

import Language.Haskell.TH

import Test.QuickCheck.HRep.TH.TypeRep
import Test.QuickCheck.HRep.TH.FunPatsRep
import Test.QuickCheck.HRep.TH.ModIntRep

----------------------------------------
-- Derivation target and dispatcher

data Target
  = TypeRep
    { ty :: Name
    , fam   :: [Name] }
  | PatsRep
    { fun :: Name
    , arg :: Int
    , fam :: [Name] }
  | ModRep
    { type_ :: Name
    , alias :: String
    , fam :: [Name] }

typeRep :: Name -> Target
typeRep tyName = TypeRep tyName [tyName]

patsRep :: Name -> Target
patsRep funName = PatsRep funName 1 []

modRep :: Name -> Target
modRep tyName = ModRep tyName ("<" ++ nameBase tyName ++ ">") []

derive :: Target -> Q [Dec]
derive (TypeRep tyName tyFam)
  = deriveTypeRep tyName tyFam
derive (PatsRep  funName funArgNr tyFam)
  = deriveFunPatsRep funName funArgNr tyFam
derive (ModRep tyName modAlias _)
  = deriveModIntRep tyName modAlias

deriveHRep :: [Name] -> [Target] -> Q [Dec]
deriveHRep fam' targets = concatMapM derive
  (setFam <$> ((typeRep <$> fam') ++ targets))
  where setFam target = target { fam = fam' }


-- ----------------------------------------
-- -- | Derive all the stuff
-- deriveAll :: Name -> [(Name, Int)] -> Bool -> Q [Dec]
-- deriveAll ogTyName funcsNameArgs reducePatSize = do
--   ogTyRep <- deriveTypeRep ogTyName
--   let derivePat = deriveFunRep reducePatSize
--   funPatsReps <- concatMapM (uncurry derivePat) funcsNameArgs
--   return (ogTyRep ++ funPatsReps)
