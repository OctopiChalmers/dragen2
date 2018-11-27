{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module Test.QuickCheck.HRep.TH where

import Language.Haskell.TH

import Test.QuickCheck.HRep.TH.TypeRep
import Test.QuickCheck.HRep.TH.FunPatsRep
import Test.QuickCheck.HRep.TH.ModIntRep

----------------------------------------
-- Derivation target and dispatcher

data Target
  = TypeRep
    { type_ :: Name }
  | FunPatsRep
    { fun :: Name
    , arg :: Int
    , rps :: Bool }
  | ModIntRep
    { type_ :: Name
    , alias :: String }

data Void

typeRep :: Target
typeRep = TypeRep ''Void

funPatsRep :: Target
funPatsRep = FunPatsRep 'undefined 1 False

modIntRep :: Target
modIntRep = ModIntRep ''Void mempty

derive :: Target -> Q [Dec]
derive (TypeRep tyName)
  = deriveTypeRep tyName
derive (FunPatsRep  funName funArgNr redPatSize)
  = deriveFunPatsRep redPatSize funName funArgNr
derive (ModIntRep tyName modAlias)
  = deriveModIntRep tyName modAlias

-- ----------------------------------------
-- -- | Derive all the stuff
-- deriveAll :: Name -> [(Name, Int)] -> Bool -> Q [Dec]
-- deriveAll ogTyName funcsNameArgs reducePatSize = do
--   ogTyRep <- deriveTypeRep ogTyName
--   let derivePat = deriveFunRep reducePatSize
--   funPatsReps <- concatMapM (uncurry derivePat) funcsNameArgs
--   return (ogTyRep ++ funPatsReps)
