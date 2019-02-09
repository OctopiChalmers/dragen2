{-# LANGUAGE TemplateHaskell #-}
module Test.QuickCheck.HRep.TH.ModIntRep where

import Data.List
import Data.Foldable
import Control.Monad.Extra
import Control.Monad.IO.Class

import Language.Haskell.TH
import Language.Haskell.TH.Desugar
import qualified Language.Haskell.Exts as Ext

import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.HRep as HRep
import qualified Test.QuickCheck.Branching as Branching

import Test.QuickCheck.HRep.TH.Common

----------------------------------------
-- | Derive the complete representation of every combinator of a module that
-- returns the desired type, plus the module interface representation as a sum
-- of each combinator.
deriveModIntRep :: Name -> String -> [Name] -> [Name] -> Q [Dec]
deriveModIntRep tyName modAlias tyFam blacklist = do

  -- | Convert the module alias to a safe identifier
  let modAliasId = toIdentStr modAlias
      shortBlacklist = nameBase <$> blacklist

  -- | Extract the combinator names from the current module
  intNames <- filterM (returnsType tyName) =<< reifyModNames
  let combNames = filter (not . (flip elem shortBlacklist) . nameBase) intNames

  -- | Create the representation for each combinator
  combsRep <- concatMapM (deriveCombRep tyName modAliasId tyFam) combNames

  -- | Create the default HRep type instance
  let repTyIns = DTySynInstD ''HRep.HRep repTyInsEqn
      repTyInsEqn = DTySynEqn [DLitT (StrTyLit modAlias)] repTyInsType
      repTyInsType = foldr1 mkSumType (mkFunTy <$> combNames)

      mkFunTy n = DConT ''HRep.Fun `DAppT` DLitT (StrTyLit (nameBase n))

  -- | Return all the generated stuff, converted again to TH
  return $ sweeten $ repTyIns : combsRep


returnsType :: Name -> Name -> Q Bool
returnsType tyName funName
  = checkRetTy <$> reifyOrFail funName
  where
    checkRetTy (DVarI _ ty _)
      | tyName == tyHead (retType ty) = True
    checkRetTy _                      = False

----------------------------------------
-- | Derive the complete representation of a single value of the abstract
-- interface of a module.
deriveCombRep :: Name -> String -> [Name] -> Name -> Q [DDec]
deriveCombRep tyName modAlias tyFam funName = do

  -- | Some "fresh" names
  repName    <- newName ("HRep_Comb_" ++ toIdentStr modAlias ++ "_" ++ nameBase funName)
  repConName <- newName ("Comb_"  ++ toIdentStr modAlias ++ "_" ++ nameBase funName)
  rv  <- DPlainTV <$> newName "self"
  gen <- newName "_gen"

  -- | Retrieve the function type signature
  DVarI _ funTy _ <- reifyOrFail funName
  let funSig = splitSignature funTy
      (funArgTys, funRetTy) = (init funSig, last funSig)
      funRetTyInsVars = tyArgs funRetTy

  -- | Retrieve the original type definition
  (vs, _) <- getDataD mempty tyName
  ogVars <- mapM desugar vs

  let extVars = ogVars ++ [rv]
      repConTy = repName <<* extVars
      repConTy2Ty = repName <<| funRetTyInsVars

  -- | Representation data declaration
  let repDataDec = DDataD Data [] repName extVars
                     Nothing [singleCon] derivingClauses
      singleCon = DCon extVars [] repConName conRepFields repConTy
      conRepFields = DNormalC False (mkPatRepField <$> funArgTys)

      mkPatRepField ty = (defaultBang, replaceTyForTV funRetTy rv ty)
      defaultBang = Bang NoSourceUnpackedness NoSourceStrictness

  -- | Representation Algebra instance
  let repAlgIns = DInstanceD Nothing [] repAlgTy [repAlgLetDec]
      repAlgTy = ''HRep.Algebra <<| [repConTy2Ty, funRetTy]
      repAlgLetDec = DLetDec (DFunD 'HRep.alg [repAlgClause])
      repAlgClause = DClause [repAlgPat] repAlgRhs
      repAlgPat = DConPa repConName (DVarPa <$> repAlgVars)
      repAlgRhs = applyDExp (DVarE funName) (DVarE <$> repAlgVars)
      repAlgVars = take (length funArgTys) varNames

  -- | Representation FixArbitrary instance
  conFieldsGens <- mapM (deriveGen (DVarE gen) funRetTy) funArgTys

  let repArbIns = DInstanceD Nothing repArbCxt repArbTy [repArbLetDec]
      repArbCxt = mkCxt <$> toList (fvDType funRetTy)
      repArbTy = ''HRep.FixArbitrary <<| [repConTy2Ty, funRetTy]
      repArbLetDec = DLetDec (DFunD 'HRep.liftFix [repArbClause])
      repArbClause = DClause [DVarPa gen] repArbBody
      repArbBody = mkAppExp repConName conFieldsGens

      mkCxt v = DAppPr (DConPr ''QC.Arbitrary) (DVarT v)

  -- | Representation HRep type instance
  let repFunTyIns = DTySynInstD ''HRep.Fun repFunInsEqn
      repFunInsEqn = DTySynEqn [DLitT (StrTyLit (nameBase funName))] someTy
      someTy | null ogVars
             = DConT repName
             | otherwise
             = someTH (length ogVars) (DConT repName)

  -- | Representation BranchingType instance
  let repBrIns = DInstanceD Nothing [] repBrTy repBrLetDecs
      repBrTy = ''Branching.BranchingType <<| [repConTy2Ty]
      repBrLetDecs = uncurry mkBranchingDec <$> zip branchingFunNames brFunExps

      mkBranchingDec brFun funExp
        = DLetDec (DFunD brFun [DClause [] funExp])

      brFunExps = singletonTH <$>
        [ stringLit (nameBase funName)
        , DConE 'False
        , intLit 1
        , intLit 1
        , vectorTH  (intLit . beta <$> tyFam)
        , DAppE (DVarE 'error) (DLitE (StringL "unsuported operation!"))
        ]

      beta tn = sum (bf tn <$> funArgTys)

      bf target (DAppT (DConT f) t)
        | f == ''[] = listBF * (bf target t)
      bf target ty
        | tyHead ty == target = 1
        | otherwise = 0

  return [repDataDec, repAlgIns, repArbIns, repFunTyIns, repBrIns]

----------------------------------------
-- | Extract a list of top-level names from a module using an external parser.

reifyModNames :: Q [Name]
reifyModNames = currentFile >>= extractModNames

defaultExts :: [Ext.Extension]
defaultExts = Ext.parseExtension <$>
  [ "AllowAmbiguousTypes"
  , "DataKinds"
  , "DeriveFunctor"
  , "DeriveGeneric"
  , "ExistentialQuantification"
  , "FlexibleContexts"
  , "FlexibleContexts"
  , "FlexibleInstances"
  , "GADTs"
  , "MultiParamTypeClasses"
  , "PolyKinds"
  , "Rank2Types"
  , "ScopedTypeVariables"
  , "StandaloneDeriving"
  , "TemplateHaskell"
  , "TypeApplications"
  , "TypeFamilies"
  , "TypeOperators"
  , "UndecidableInstances"
  ]

extractModNames :: FilePath -> Q [Name]
extractModNames path = do
  parsed <- liftIO (Ext.parseFileWithExts defaultExts path)
  case parsed of
    Ext.ParseOk (Ext.Module _ _ _ _ decs) -> do
      let srcNames = concat (foldr extractVarNames [] decs)
      if (null srcNames)
      then error ("extractModNames: no names found while reifying " ++ show path)
      else return (nub srcNames)
    err -> error ("extractModNames: cannot parse " ++ show path ++ "\n" ++ show err)

extractVarNames :: Ext.Decl l -> [[Name]] -> [[Name]]
extractVarNames (Ext.FunBind _ ms) = ((:) (funBindName <$> ms))
extractVarNames (Ext.PatBind _ ps@(Ext.PVar {}) _ _) = ((:) [patBindName ps])
extractVarNames _ = id

funBindName :: Ext.Match l -> Name
funBindName (Ext.Match      _ n _ _ _)   = mkName (Ext.prettyPrint n)
funBindName (Ext.InfixMatch _ _ n _ _ _) = mkName (Ext.prettyPrint n)

patBindName :: Ext.Pat l -> Name
patBindName (Ext.PVar _ n) = mkName (Ext.prettyPrint n)
patBindName p = unsupported 'patBindName (Ext.prettyPrint p)
