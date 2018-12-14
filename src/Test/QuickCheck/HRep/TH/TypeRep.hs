{-# LANGUAGE TemplateHaskell #-}

module Test.QuickCheck.HRep.TH.TypeRep where

import Data.List
import Control.Monad.Extra

import Language.Haskell.TH
import Language.Haskell.TH.Desugar

import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.HRep as HRep
import qualified Test.QuickCheck.Branching as Branching

import Test.QuickCheck.HRep.TH.Common

----------------------------------------
-- | Derive the complete representation for every constructor of a type, plus
-- the type representation as a sized sum of each constructor.
deriveTypeRep :: Name -> [Name] -> Q [Dec]
deriveTypeRep tyName tyFam = do

  -- | Reify the original data declaration name and desugar it
  (vs, cons) <- getDataD mempty tyName
  tyVars <- mapM desugar vs
  let ty = simplifyDType (tyName <<* tyVars)
  ogCons <- concatMapM (dsCon tyVars ty) cons

  -- | Create the representation for each constructor
  conReps <- concatMapM (deriveConRep tyFam) ogCons

  -- | Create the default Rep type instance
  let repTyIns = DTySynInstD ''HRep.HRep (DTySynEqn [DConT tyName] rhs)
      rhs = foldr1 mkSumType (mkCon <$> ogCons)

      mkCon c@(DCon _ _ conName _ _)
        | isTerminalDCon tyFam c = term' `DAppT` con'
        | otherwise = con'
        where con' = DConT ''HRep.Con `DAppT` DConT conName
              term' = DConT ''HRep.Term

  -- | Return all the generated stuff, converted again to TH
  return $ sweeten $ repTyIns : conReps

----------------------------------------
-- | Derive the complete representation for a single constructor of a type.
deriveConRep :: [Name] -> DCon -> Q [DDec]
deriveConRep tyFam (DCon conTyVars conCxt conName conFields conTy) = do

  -- | Some "fresh" names
  repName <- newName ("Rep_" ++ nameBase conName)
  repConName <- newName ("Mk_" ++ nameBase conName)
  rv  <- DPlainTV <$> newName "self"
  gen <- newName "_gen"

  let extVars = conTyVars ++ [rv]
      repConTy = repName <<* extVars
      repConTy2Ty = repName <<* conTyVars

  -- | Representation data declararion
  let repDataDec = DDataD Data [] repName extVars
                     Nothing [singleCon] derivingClauses
      singleCon = DCon extVars conCxt repConName conRepFields repConTy
      conRepFields = mkConRepFields conFields

      mkConRepFields (DNormalC ifx bts) = DNormalC ifx (replaceBts <$> bts)
        where replaceBts = fmap (replaceTyForTV conTy rv)
      mkConRepFields (DRecC vbts) = DNormalC False (replaceVbts <$> vbts)
        where replaceVbts (_,b,t) = (b, replaceTyForTV conTy rv t)

  -- | Representation Algebra instance
  let repAlgIns = DInstanceD Nothing [] repAlgTy [repAlgLetDec]
      repAlgTy = ''HRep.Algebra <<| [repConTy2Ty, conTy]
      repAlgLetDec = DLetDec (DFunD 'HRep.alg [repAlgClause])
      repAlgClause = DClause [repAlgPat] repAlgRhs
      repAlgPat = DConPa repConName (DVarPa <$> conPatVars)
        where conPatVars = take (dConFieldsNr conFields) varNames
      repAlgRhs = applyDExp (DConE conName) (DVarE <$> conVarExprs)
        where conVarExprs = take (dConFieldsNr conFields) varNames

  -- | Representation FixArbitrary instance
  conFieldsGens <- mapM (deriveGen (DVarE gen) conTy)
                        (dConFieldsTypes conFields)

  let repArbIns = DInstanceD Nothing repArbCxt repArbTy [repArbLetDec]
      repArbCxt = mkCxt <$> conTyVars
      repArbTy = ''HRep.FixArbitrary <<| [repConTy2Ty, conTy]
      repArbLetDec = DLetDec (DFunD 'HRep.liftFix [repArbClause])
      repArbClause = DClause [DVarPa gen] repArbBody
      repArbBody = mkAppExp repConName conFieldsGens

      mkCxt v = DAppPr (DConPr ''QC.Arbitrary) (dTyVarBndrToDType v)

  -- | Representation Branching instance
  tyFamCons <- getFamConNames tyFam

  let repBrIns = DInstanceD Nothing [] repBrTy repBrLetDecs
      repBrTy = ''Branching.Branching <<| [repConTy2Ty]
      repBrLetDecs = mkBranchingDec <$> zip branchingFunNames brFunExps

      mkBranchingDec (funName, funExp)
        = DLetDec (DFunD funName [DClause [] funExp])

      brFunExps = singletonTH . singletonTH <$>
        [ stringLit (nameBase conName)
        , DConE 'True
        , intLit 1
        , intLit 1
        , vectorTH  (      intLit . beta <$> tyFam)
        , vector2TH (fmap (intLit . eta) <$> tyFamCons)
        ]

      beta tn = length (filter ((tn ==) . tyHead) (dConFieldsTypes conFields))
      eta  cn = if cn == conName then 1 else 0


  -- | Representation Con type family instance
  let repConTyIns = DTySynInstD ''HRep.Con repConInsEqn
      repConInsEqn = DTySynEqn [DConT conName] someTy
      someTy | null conTyVars = DConT repName
             | otherwise      = someTH (length conTyVars) (DConT repName)

  -- | Return all the stuff
  return [repDataDec, repAlgIns, repArbIns, repBrIns, repConTyIns]
