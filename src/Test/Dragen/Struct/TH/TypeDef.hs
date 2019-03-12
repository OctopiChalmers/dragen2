{-# LANGUAGE OverloadedStrings #-}
module Test.Dragen.Struct.TH.TypeDef where

import Data.Bool
import Data.Ord
import Data.List
import Control.Monad.Extra

import Language.Haskell.TH
import Language.Haskell.TH.Desugar

import Test.Dragen.Struct.TH.Util

import qualified Test.QuickCheck as QC
import qualified Test.Dragen.Struct.Rep as Rep
import qualified Test.Dragen.Struct.Algebra as Algebra
import qualified Test.Dragen.Struct.BoundedArbitrary as BoundedArb
import qualified Test.Dragen.Struct.Branching as Branching


----------------------------------------
-- | Derive a complete representation for every constructor of a type, plus
-- the type representation as a sized sum of each constructor.
deriveTypeDef :: Name -> [Name] -> [Name] -> Q [DDec]
deriveTypeDef typeName blacklist typeFam = do

  -- Reify the data constructors of the target data type
  allCons <- getDCons typeName
  dragenMsg "reified data constructors:" [allCons]

  -- Filter the target data constructors from the blacklist
  let isBlacklisted con = dConName con `elem` blacklist
      (droppedCons, targetCons) = partition isBlacklisted allCons

  when (not (null droppedCons)) $ do
    dragenMsg "ignored constructors:" [droppedCons]

  when (null targetCons) $ do
    dragenError "nothing to derive" [typeName]

  -- Derive all the stuff for each target data constructor
  consReps <- concatMapM (deriveConRep typeFam) targetCons

  -- Create the default `Rep` type instance
  repTypeIns <- deriveRepTypeIns typeFam typeName targetCons

  -- Return all the stuff
  return $ consReps ++ repTypeIns


----------------------------------------
-- | Derive the complete representation for a single constructor of a type
deriveConRep :: [Name] -> DCon -> Q [DDec]
deriveConRep typeFam (DCon conTyVars conCxt conName conFields conType) = do

  -- Create the new names of the representation and single constructor
  repTypeName <- newName $ toValidIdent "Rep_Con" (nameBase conName)
  repConName  <- newName $ toValidIdent "Mk_Con"  (nameBase conName)

  -- Create a new type variable for the recursive holes
  rv <- newRecVar
  let extTypeVars = conTyVars ++ [rv]

  -- Create the types we need for the new representation
  let repType     = repTypeName <<* extTypeVars
      repTypeNoRv = repTypeName <<* conTyVars
      conFieldsTypes = dConFieldsTypes conFields

  -- Create the representation data declaration
  let repDataDec = DDataD Data [] repTypeName extTypeVars
                   Nothing [singleCon] derivingClause
      singleCon = DCon extTypeVars conCxt repConName repConFields repType
      repConFields = mkRepConFields conFields

      mkRepConFields (DNormalC ifx bts) = DNormalC ifx (replaceBts <$> bts)
        where replaceBts = fmap (replaceTyForTV conType rv)
      mkRepConFields (DRecC vbts) = DNormalC False (replaceVbts <$> vbts)
        where replaceVbts (_,b,t) = (b, replaceTyForTV conType rv t)

  -- Create the representation Algebra instance
  patVars <- newPatVars (dConFieldsNum conFields)
  let repAlgIns = DInstanceD Nothing [] repAlgTy [repAlgLetDec]
      repAlgTy = ''Algebra.Algebra <<# [repTypeNoRv, conType]
      repAlgLetDec = DLetDec (DFunD 'Algebra.alg [repAlgClause])
      repAlgClause = DClause [repAlgPat] repAlgRhs
      repAlgPat = DConPa repConName (DVarPa <$> patVars)
      repAlgRhs = applyDExp (DConE conName) (DVarE <$> patVars)

  -- Create the representation BoundedArbitrary instance
  gen_   <- newName_ "gen"
  depth_ <- newName_ "depth"
  conFieldsGens <- mapM (mkBoundedGen typeFam conType gen_ depth_)
                        conFieldsTypes

  let repGenIns = DInstanceD Nothing repGenCxt repGenType [repGenLetDec]
      repGenCxt = mkCxt <$> conTyVars
      repGenType = ''BoundedArb.BoundedArbitrary1 <<# [repTypeNoRv]
      repGenLetDec = DLetDec (DFunD 'BoundedArb.liftBoundedGen [repGenClause])
      repGenClause = DClause [DVarPa gen_, DVarPa depth_] repGenBody
      repGenBody = thApplicativeExp repConName conFieldsGens

      mkCxt v = DAppPr (DConPr ''QC.Arbitrary) (dTyVarBndrToDType v)

  -- Create the representation BranchingType instance
  typeFamCons <- getFamDConNames typeFam

  let repBrIns = DInstanceD Nothing [] repBrType repBrLetDecs
      repBrType = ''Branching.BranchingType <<# [repTypeNoRv]
      repBrLetDecs = mkBranchingDec <$> repBrBindings

      mkBranchingDec (methodName, methodExp)
        = DLetDec (DFunD methodName [DClause [] methodExp])

      repBrBindings
        = thSingleton <$$>
        [ ('Branching.typeNames
          , thString (nameBase conName))
        , ('Branching.typeAtomic
          , thTrue)
        , ('Branching.typeBranchingProbs
          , thRational 1)
        , ('Branching.typeTerminalProbs
          , thRational 1)
        , ('Branching.typeBeta
          , thVector (thRational . toRational <$>
                      branchingFactor typeFam conFieldsTypes))
        , ('Branching.typeEta
          , thVector2 (thRational . bool 0 1 . (conName ==) <$$> typeFamCons))
        ]

  -- Create the function Rep type instance
  let repConTyIns = DTySynInstD ''Rep.Con repInsEqn
      repInsEqn = DTySynEqn [thNameTyLit conName] someTy
      someTy | null conTyVars = DConT repTypeName
             | otherwise      = thSome (length conTyVars) (DConT repTypeName)

  -- Return all the stuff
  let conRep = [repDataDec, repAlgIns, repGenIns, repBrIns, repConTyIns]
  dragenMsg "derived data constructor representation:" [conRep]

  return conRep

----------------------------------------
-- | Derive a default `Rep` type instace for the target data type
deriveRepTypeIns :: [Name] -> Name -> [DCon] -> Q [DDec]
deriveRepTypeIns typeFam typeName cons = do

  let repTypeIns = DTySynInstD ''Rep.Rep (DTySynEqn [repTyLit] rhs)
      repTyLit = thNameTyLit typeName
      rhs = foldr1 thSum (mkConExp <$> cons)

      mkConExp con
        -- If the constructor is terminal, tag it accordingly
        | isTerminalDCon typeFam con
        = thTerm (thCon (dConNameTyLit con))
        -- If there are no terminal constructors and `con`
        -- is the "smallest" one, tag it as terminal
        | noTerminals && con == smallest cons
        = thTerm (thCon (dConNameTyLit con))
        -- Otherwise, treat the constructor as non-terminal
        | otherwise
        = thCon (dConNameTyLit con)

      dConNameTyLit = thNameTyLit . dConName
      noTerminals = not (any (isTerminalDCon typeFam) cons)
      smallest = head . sortBy (comparing bf)
      bf = sum . branchingFactor typeFam . dConFieldsTypes . dConFields


  when noTerminals $ do
    dragenWarning "couldn't find any terminal construction:" [cons]

  dragenMsg "derived type instance:" [repTypeIns]

  return [repTypeIns]
