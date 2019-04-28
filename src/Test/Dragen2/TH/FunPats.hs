module Test.Dragen2.TH.FunPats where

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
-- | Derive the complete representation for a every pattern of a function, plus
-- the function representation as a sum of each pattern.
deriveFunPats :: Name -> Int -> Maybe FilePath -> [Name] -> Bool -> Q [DDec]
deriveFunPats funName argNum path typeFam branching = do

  -- Parse the appropriate file to obtain the target function pattern matching
  modulePath <- maybeM currentFile pure (pure path)
  funPats <- extractDPats funName =<< parseModule modulePath

  -- Extract the patterns from the function for the given argument
  (_, _, funArgsTypes, _) <- reifyFunSig funName
  let funArgType = funArgsTypes !! (argNum - 1)
      funArgPats = dropTrivialPats ((!! (argNum - 1))  <$> funPats)

  -- Retrieve the uninstatiated type vars of the function argument type
  let (funArgTypeName, funArgInsTypeVars) = unapply funArgType
  (vs, _) <- getDataD mempty funArgTypeName
  funArgDefTypeVars <- mapM desugar vs

  -- Replace the type variables in the instantiated function argument type to
  -- match the ones in the type definition. This is kind of annoying, but it
  -- works ¯\_(ツ)_/¯
  let funArgType' = funArgTypeName <<# replacedTyVars
      replacedTyVars = zipWith pickTypeVars funArgDefTypeVars funArgInsTypeVars

      pickTypeVars (DPlainTV v)    (DVarT _) = DVarT v
      pickTypeVars (DKindedTV v _) (DVarT _) = DVarT v
      pickTypeVars _               t         = t

  -- Collect the type of every pattern variable.
  -- We don't care about their depth for now, so we just drop that info.
  let collectPatTypes pat = snd <$$> collectPatVarsDepthsTypes funArgType' pat
  patsVarsTypes <- mapM collectPatTypes funArgPats

  -- Create the representation for each pattern matching of the function
  let derivePatRep'
        = derivePatRep funName typeFam funArgType' funArgDefTypeVars branching
  patReps <- concatMapM (uncurry3 derivePatRep')
                        (zip3 patsVarsTypes [1..] funArgPats)

  -- Create the default `Rep` type instance
  repTypeIns <- deriveRepTypeIns typeFam funName patsVarsTypes

  return $ patReps ++ repTypeIns

----------------------------------------
-- | Derive the complete representation for a single pattern of a function.
derivePatRep :: Name -> [Name] -> DType -> [DTyVarBndr] -> Bool
             -> [DType] -> Int -> DPat -> Q [DDec]
derivePatRep funName typeFam funArgType funArgDefTypeVars branching
             funArgPatVarsTypes patNum targetPat = do

  -- Create the new names of the representation and single constructor
  repTypeName <- newName $ toValidIdent "Rep_Pat"
                 (nameBase funName ++ "_" ++ show patNum)
  repConName  <- newName $ toValidIdent "Mk_Pat"
                 (nameBase funName ++ "_" ++ show patNum)

  -- Create a new type variable for the recursive holes
  rv <- newRecVar
  let extTypeVars = funArgDefTypeVars ++ [rv]

  -- Create the types we need for the new representation
  let repType     = repTypeName <<* extTypeVars
      repTypeNoRv = repTypeName <<# typeArgs funArgType

  -- Create the representation data declaration
  let repDataDec = DDataD Data [] repTypeName extTypeVars
                     Nothing [singleCon] derivingClause
      singleCon = DCon extTypeVars [] repConName conRepFields repType
      conRepFields = DNormalC False (mkPatRepField <$> funArgPatVarsTypes)

      mkPatRepField ty = (defaultBang, replaceTyForTV funArgType rv ty)
      defaultBang = Bang NoSourceUnpackedness NoSourceStrictness

  -- Create the representation Algebra instance
  patVars <- newPatVars (length funArgPatVarsTypes)
  let repAlgIns = DInstanceD Nothing [] repAlgTy [repAlgLetDec]
      repAlgTy = ''Algebra.Algebra <<# [repTypeNoRv, funArgType]
      repAlgLetDec = DLetDec (DFunD 'Algebra.alg [repAlgClause])
      repAlgClause = DClause [repAlgPat] repAlgRhs
      repAlgPat = DConPa repConName (DVarPa <$> patVars)
      repAlgRhs = dPatToDExpWithVars patVars targetPat

  -- Create the representation BoundedArbitrary instance
  gen_   <- newName_ "gen"
  depth_ <- newName_ "depth"
  patVarsGens <- mapM (mkBoundedGen typeFam funArgType gen_ depth_)
                        funArgPatVarsTypes

  let repGenIns = DInstanceD Nothing repGenCxt repGenType [repGenLetDec]
      repGenCxt = mkCxt <$> toList (fvDType funArgType)
      repGenType = ''BoundedArb.BoundedArbitrary1 <<# [repTypeNoRv]
      repGenLetDec = DLetDec (DFunD 'BoundedArb.liftBoundedGen [repGenClause])
      repGenClause = DClause [DVarPa gen_, DVarPa depth_] repGenBody
      repGenBody = thApplicativeExp repConName patVarsGens

      mkCxt v = DAppPr (DConPr ''QC.Arbitrary) (DVarT v)

  -- Create the representation BranchingType instance

  -- Create the function Rep type instance
  let repPatTyIns = DTySynInstD ''Rep.Pat repInsEqn
      repInsEqn = DTySynEqn [thNameTyLit funName, thNumTyLit patNum] someTy
      someTy
        | null funArgDefTypeVars = DConT repTypeName
        | otherwise = thSome (length funArgDefTypeVars) (DConT repTypeName)

  -- Create the representation BranchingType instance
  repBrIns <- deriveBranchingTypeIns typeFam funName patNum targetPat
                funArgPatVarsTypes repTypeNoRv

  -- Return all the stuff
  let repDecs = [repDataDec, repAlgIns, repGenIns, repPatTyIns]
  let conRep | branching = repBrIns : repDecs
             | otherwise = repDecs

  dragenMsg "derived function pattern representation:" [conRep]

  return conRep

----------------------------------------
-- | Derive the `BranchingType` instance for a function pattern matching
deriveBranchingTypeIns :: [Name] -> Name -> Int -> DPat -> [DType] -> DType -> Q DDec
deriveBranchingTypeIns typeFam funName patNum targetPat
  funArgPatVarsTypes repTypeNoRv = do

  typeFamCons <- getFamDConNames typeFam
  let targetPatCons = collectPatCons targetPat

  let repBrIns = DInstanceD Nothing [] repBrType repBrLetDecs
      repBrType = ''Branching.BranchingType <<# [repTypeNoRv]
      repBrLetDecs = mkBranchingDec <$> repBrBindings

      mkBranchingDec (methodName, methodExp)
        = DLetDec (DFunD methodName [DClause [] methodExp])

      repBrBindings
        = thSingleton <$$>
        [ ('Branching.typeNames
          , thString (nameBase funName ++ "#" ++ show patNum))
        , ('Branching.typeAtomic
          , thFalse)
        , ('Branching.typeBranchingProbs
          , thRational 1)
        , ('Branching.typeTerminalProbs
          , thRational 1)
        , ('Branching.typeBeta
          , thVector (thRational . toRational <$>
                      branchingFactor typeFam funArgPatVarsTypes))
        , ('Branching.typeEta
          , thVector2 (thRational . toRational . eta <$$> typeFamCons))
        ]

      eta cn = maybe 0 id (lookup cn targetPatCons)

  return repBrIns

----------------------------------------
-- | Derive a default `Rep` type instace for the target data type
deriveRepTypeIns :: [Name] -> Name -> [[DType]] -> Q [DDec]
deriveRepTypeIns typeFam funName patsVarsTypes = do

  let repTypeIns = DTySynInstD ''Rep.Rep (DTySynEqn [repTyLit] rhs)
      repTyLit = thNameTyLit funName
      rhs = foldr1 thSum (uncurry mkPatExp <$> zip [1..] patsVarsTypes)

      mkPatExp patNum patVarTypes
        -- If the pattern doesn't has any pattern variable from the recursive
        -- family, then is safe to consider it terminal.
        | bf patVarTypes == 0
        = thTerm (thPat (thNameTyLit funName) patNum)
        -- Otherwise, treat the pattern as non-terminal.
        | otherwise
        = thPat (thNameTyLit funName) patNum

      bf = sum . branchingFactor typeFam

  dragenMsg "derived type instance:" [repTypeIns]

  return [repTypeIns]
