module Test.Dragen2.TH.TypeInt where

import Data.List
import Data.Foldable
import Control.Monad.Extra

import Language.Haskell.TH
import Language.Haskell.TH.Desugar

import Test.Dragen2.TH.Util
import Test.Dragen2.TH.Extract

import qualified Test.QuickCheck as QC
import qualified Test.Dragen2.Rep as Rep
import qualified Test.Dragen2.Algebra as Algebra
import qualified Test.Dragen2.BoundedArbitrary as BoundedArb
import qualified Test.Dragen2.Branching as Branching

----------------------------------------
-- | Derive a complete representation for every function in a module returning
-- the target type, plus the api representation as a sized sum of each function.
deriveTypeInt :: Name -> String -> [Name] -> Maybe FilePath
              -> [Name] -> Bool -> Q [DDec]
deriveTypeInt typeName alias blacklist path typeFam branching = do

  -- Parse the appropriate file to obtain interface function names
  modulePath <- maybeM currentFile pure (pure path)
  moduleNames <- extractVarNames =<< parseModule modulePath

  -- Filter the interface functions from the blacklist
  interfaceFuncs <- filterM (returnsTargetType typeName) moduleNames
  let isBlacklisted name = nameBase name `elem` (nameBase <$> blacklist)
      (droppedFuncs, targetFuncs) = partition isBlacklisted interfaceFuncs

  when (not (null droppedFuncs)) $ do
    dragenMsg "ignored constructors:" [droppedFuncs]

  -- Derive all the stuff for each target interface function
  funReps <- concatMapM (deriveFunRep typeFam branching) targetFuncs

  -- Create the default `Rep` type instance
  repTypeIns <- deriveRepTypeIns typeFam alias targetFuncs

  return $ funReps ++ repTypeIns

returnsTargetType :: Name -> Name -> Q Bool
returnsTargetType typeName funName = do
  checkType <$> reifyName funName
  where checkType (DVarI _ ty _)
          | typeName == typeHead (returnType ty) = True
        checkType _                              = False


----------------------------------------
-- | Derive the complete representation for a single abstract interface function
deriveFunRep :: [Name] -> Bool -> Name -> Q [DDec]
deriveFunRep typeFam branching funName = do

  -- Create the new names of the representation and single constructor
  repTypeName <- newName $ toValidIdent "Rep_Fun" (nameBase funName)
  repConName  <- newName $ toValidIdent "Mk_Fun"  (nameBase funName)

  -- Reify the type signature of the function
  (_, funCxt, funArgTypes, funReturnType) <- reifyFunSig funName
  let funRetTypeInsVars = typeArgs funReturnType

  -- Reify the type variables of the target type
  let funRetTypeFreeVars = DPlainTV <$> concat
        (toList . fvDType <$> funRetTypeInsVars)

  -- Create a new type variable for the recursive holes
  rv <- newRecVar
  let extTypeVars = funRetTypeFreeVars ++ [rv]

  -- Create the types we need for the new representation
  let repType     = repTypeName <<* extTypeVars
      repTypeNoRv = repTypeName <<# funRetTypeInsVars

  -- Create the representation data declaration
  let repDataDec = DDataD Data [] repTypeName extTypeVars
                     Nothing [singleCon] (derivingClauses branching)
      singleCon = DCon extTypeVars [] repConName conRepFields repType
      conRepFields = DNormalC False (mkPatRepField <$> funArgTypes)

      mkPatRepField ty = (defaultBang, replaceTyForTV funReturnType rv ty)
      defaultBang = Bang NoSourceUnpackedness NoSourceStrictness

  -- Create the representation Algebra instance
  patVars <- newPatVars (length funArgTypes)
  let repAlgIns = DInstanceD Nothing funCxt repAlgTy [repAlgLetDec]
      repAlgTy = ''Algebra.Algebra <<# [repTypeNoRv, funReturnType]
      repAlgLetDec = DLetDec (DFunD 'Algebra.alg [repAlgClause])
      repAlgClause = DClause [repAlgPat] repAlgRhs
      repAlgPat = DConPa repConName (DVarPa <$> patVars)
      repAlgRhs = applyDExp (DVarE funName) (DVarE <$> repAlgVars)
      repAlgVars = take (length funArgTypes) patVars

  -- Create the representation BoundedArbitrary instance
  gen_   <- newName_ "gen"
  depth_ <- newName_ "depth"
  funArgsGens <- mapM (mkBoundedGen typeFam funReturnType gen_ depth_)
                        funArgTypes

  let repGenIns = DInstanceD Nothing repGenCxt repGenType [repGenLetDec]
      repGenCxt = mkCxt <$> toList (fvDType funReturnType)
      repGenType = ''BoundedArb.BoundedArbitrary1 <<# [repTypeNoRv]
      repGenLetDec = DLetDec (DFunD 'BoundedArb.liftBoundedGen [repGenClause])
      repGenClause = DClause [DVarPa gen_, DVarPa depth_] repGenBody
      repGenBody = thApplicativeExp repConName funArgsGens

      mkCxt v = DAppPr (DConPr ''QC.Arbitrary) (DVarT v)

  -- Create the function Rep type instance
  let repFunTyIns = DTySynInstD ''Rep.Fun repInsEqn
      repInsEqn = DTySynEqn [thNameTyLit funName] someTy
      someTy | null funRetTypeFreeVars = DConT repTypeName
             | otherwise = thSome (length funRetTypeFreeVars) (DConT repTypeName)

  -- Create the representation BranchingType instance
  repBrIns <- deriveBranchingTypeIns typeFam funName funArgTypes repTypeNoRv

  -- Return all the stuff
  let repDecs = [repDataDec, repAlgIns, repGenIns, repFunTyIns]
  let funRep | branching = repBrIns : repDecs
             | otherwise = repDecs

  dragenMsg "derived interface function representation:" [funRep]

  return funRep

----------------------------------------
-- | Derive the `BranchingType` instance for an interface function
deriveBranchingTypeIns :: [Name] -> Name -> [DType] -> DType -> Q DDec
deriveBranchingTypeIns typeFam funName funArgTypes repTypeNoRv = do
  let repBrIns = DInstanceD Nothing [] repBrType repBrLetDecs
      repBrType = ''Branching.BranchingType <<# [repTypeNoRv]
      repBrLetDecs = mkBranchingDec <$> repBrBindings

      mkBranchingDec (methodName, methodExp)
        = DLetDec (DFunD methodName [DClause [] methodExp])

      repBrBindings
        = thSingleton <$$>
        [ ('Branching.typeNames
          , thString (nameBase funName))
        , ('Branching.typeAtomic
          , thTrue)
        , ('Branching.typeBranchingProbs
          , thRational 1)
        , ('Branching.typeTerminalProbs
          , thRational 1)
        , ('Branching.typeBeta
          , thVector (thRational . toRational <$>
                      branchingFactor typeFam funArgTypes))
        , ('Branching.typeEta
          , DAppE (DVarE 'error)
            (thString "cannot expand constructors for arbitrary functions"))
        ]

  return repBrIns

----------------------------------------
-- | Derive a default `Rep` type instace for the abstract interface of the
-- target type
deriveRepTypeIns :: [Name] -> String -> [Name] -> Q [DDec]
deriveRepTypeIns typeFam alias funcsNames = do

  -- Reify the type signature of the function
  funcsArgsTypes <- fmap (\(_,_,t,_) -> t) <$> mapM reifyFunSig funcsNames

  let repTypeIns = DTySynInstD ''Rep.Rep (DTySynEqn [repTyLit] rhs)
      repTyLit = thStrTyLit alias
      rhs = foldr1 thSum (uncurry mkFunExp <$> zip funcsNames funcsArgsTypes)

      mkFunExp funName funArgsTypes
        -- If the function doesn't has any argument from the recursive family,
        -- then is safe (modulo non-termination) to consider it terminal.
        | bf funArgsTypes == 0
        = thTerm (thFun (thNameTyLit funName))
        -- Otherwise, treat the function as non-terminal.
        | otherwise
        = thFun (thNameTyLit funName)

      bf = sum . branchingFactor typeFam

  dragenMsg "derived type instance:" [repTypeIns]

  return [repTypeIns]
