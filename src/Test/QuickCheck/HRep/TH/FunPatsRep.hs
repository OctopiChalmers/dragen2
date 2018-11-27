{-# LANGUAGE TemplateHaskell #-}

module Test.QuickCheck.HRep.TH.FunPatsRep where

import Data.List
import Data.Foldable
import Control.Monad.Extra
import Control.Monad.IO.Class

import Language.Haskell.TH
import Language.Haskell.TH.Desugar
import Language.Haskell.TH.Desugar.Utils
import qualified Language.Haskell.Exts as Ext

import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.HRep as HRep
import qualified Test.QuickCheck.Branching as Branching

import Test.QuickCheck.HRep.TH.Common

----------------------------------------
-- | Derive the complete representation for a every pattern of a function,
-- plus the function representation as a sum of each pattern.
deriveFunPatsRep :: Bool -> Name -> Int -> Q [Dec]
deriveFunPatsRep redPatSize funName argNr = do

  -- | Retrieve the LHS of the target function
  FunLHS _ funSig funPats <- reifyFunLHS funName
  let (_, _, funArgTys, _) = unravel funSig

  -- | Pick the right argument to extract its patterns
  let funArgTy = funArgTys !! (argNr - 1)
      funArgPats = dropTrivialPats (map (!! (argNr - 1)) funPats)
      funArgPatRejects = init (inits funArgPats)

  -- | Retrieve the uninstatiated type vars of the function argument type
  let (funArgTyName, funArgInsTyVars) = unapply funArgTy
  (vs, _) <- getDataD mempty funArgTyName
  funArgDefTyVars <- mapM desugar vs

  -- | Replace the type variables in the instantiated function argument type
  -- to match the ones in the type definition
  let funArgTy' = applyDType (DConT funArgTyName) replacedTyVars
      replacedTyVars = zipWith pickTyVars funArgDefTyVars funArgInsTyVars
      pickTyVars (DPlainTV v)    (DVarT _) = DVarT v
      pickTyVars (DKindedTV v _) (DVarT _) = DVarT v
      pickTyVars _               t         = t

  -- | Create the representation for each pattern matching of the function
  let derivePatRep' = derivePatRep funName redPatSize funArgTy' funArgDefTyVars
  patReps <- concatMapM (uncurry3 derivePatRep')
                        (zip3 [1..] funArgPats funArgPatRejects)

  -- | Create the default HRep type instance
  let repTyIns = DTySynInstD ''HRep.HRep repTyInsEqn
      repTyInsEqn = DTySynEqn [DLitT (StrTyLit (nameBase funName))] repTyInsType
      repTyInsType = foldr1 mkSumType (mkPatTy <$> [1..(length funArgPats)])

      mkPatTy n = DConT ''HRep.Pat `DAppT` mkSymbol n
      mkSymbol n = DLitT (StrTyLit (nameBase funName ++ "#" ++ show n))

  -- | Return all the generated stuff, converted again to TH
  return $ sweeten $ repTyIns : concat [patReps]


----------------------------------------
-- | Derive the complete representation for a single pattern of a function.
derivePatRep :: Name -> Bool -> DType -> [DTyVarBndr]
             -> Int -> DPat -> [DPat] -> Q [DDec]
derivePatRep funName redPatSize funArgTy funArgDefTyVars
             patNr targetPat rejectsPats = do

  -- | Create fresh names for the data types
  repName <- newName ("Pat_" ++ nameBase funName ++ "_" ++ show patNr)
  repConName <- newName ("Mk_" ++ nameBase funName ++ "_" ++ show patNr)
  gen <- newName "_gen"
  pat <- newName "pat"
  rv <- mkRecVar

  let patAlias = nameBase funName ++ "#" ++ show patNr
      rvTy = dTyVarBndrToDType rv

  let collectPatInfo = collectPatVarDepthsTys funArgTy
      replaceArgTyForRv = map (\(d, t) -> (d, replaceTyForTV funArgTy rv t))
  patVarsDepthsTys <- replaceArgTyForRv <$> collectPatInfo targetPat

  let patVarsTys = snd <$> patVarsDepthsTys

  let (_, funArgInsTyVars) = unapply funArgTy
      extVars = funArgDefTyVars ++ [rv]
      repConTy = repName <<* extVars
      repConTy2Ty = repName <<| funArgInsTyVars

  -- | Representation data declaration
  let repDataDec = DDataD Data [] repName extVars
                     Nothing [singleCon] derivingClauses
      singleCon = DCon extVars [] repConName conRepFields repConTy
      conRepFields = DNormalC False (mkPatRepField <$> patVarsTys)

      mkPatRepField ty = (defaultBang, ty)
      defaultBang = Bang NoSourceUnpackedness NoSourceStrictness

  -- | Representation Algebra instance
  let repAlgIns = DInstanceD Nothing [] repAlgTy [repAlgLetDec]
      repAlgTy = ''HRep.Algebra <<| [repConTy2Ty, funArgTy]
      repAlgLetDec = DLetDec (DFunD 'HRep.alg [repAlgClause])
      repAlgClause = DClause [repAlgPat] repAlgRhs
      repAlgPat = DConPa repConName (DVarPa <$> conPatVars)
        where conPatVars = take (length patVarsTys) varNames
      repAlgRhs = dPatToDExpWithVars targetPat

  -- | Representation FixArbitrary instance
  let repArbIns = DInstanceD Nothing repArbCxt repArbTy [repArbLetDec]
      repArbCxt = mkCxt <$> toList (fvDType funArgTy)
      repArbTy = ''HRep.FixArbitrary <<| [repConTy2Ty, funArgTy]
      repArbLetDec = DLetDec (DFunD 'HRep.liftFix [repArbClause])
      repArbClause = DClause [DVarPa gen] repArbBody
      repArbBody = mkAppExp repConName
                   (uncurry mkGen <$> patVarsDepthsTys)
                   `rejecting` rejectsPats

      mkCxt v = DAppPr (DConPr ''QC.Arbitrary) (DVarT v)

      mkGen depth ty | ty == rvTy
        = (if redPatSize then reduceTH depth else smallerTH) (DVarE gen)
      mkGen depth (DAppT (DAppT (DConT _) t1) t2)
        = liftArbitrary2TH (mkGen depth t1) (mkGen depth t2)
      mkGen depth (DAppT (DConT _) r)
        = liftArbitraryTH (mkGen depth r)
      mkGen _ _ = arbitraryTH

      rejecting genExp patExps
        = satisfyTH patAlias .: mkMatchReject patExps .: genExp

      mkMatchReject pats
        = DLamE [pat] (DCaseE converted (badClauses ++ [lastClause]))
        where converted   = stepTH .: DVarE pat
              badClauses = flip DMatch (DConE 'False) <$> pats
              lastClause = DMatch DWildPa (DConE 'True)

  -- | Representation Branching instance
  let repBrIns = DInstanceD Nothing [] repBrTy repBrLetDecs
      repBrTy = ''Branching.Branching <<| [repConTy2Ty]
      repBrLetDecs = uncurry mkBranchingDec <$> zip branchingFunNames brFunExps

      mkBranchingDec brFun funExp
        = DLetDec (DFunD brFun [DClause [] funExp])

      brFunExps = singletonTH <$>
        [ DLitE (StringL patAlias)
        , if rvTy `occursInTypes` patVarsTys then DConE 'False else DConE 'True
        , DLitE (IntegerL 1)
        , DLitE (IntegerL (sum (branchFactor rvTy <$> patVarsTys)))
        , DLitE (IntegerL 1)
        ]

  -- | Representation Rep type family instance
  let repHashTyIns = DTySynInstD ''HRep.Hash repHashInsEqn
      repHashInsEqn = DTySynEqn
                      [ DLitT (StrTyLit (nameBase funName))
                      , DLitT (NumTyLit (fromIntegral patNr)) ]
                      (DLitT (StrTyLit patAlias))

  -- | Representation Pat type family instance
  let repPatTyIns = DTySynInstD ''HRep.Pat repPatInsEqn
      repPatInsEqn = DTySynEqn [DLitT (StrTyLit (patAlias))] someTy
      someTy | null funArgDefTyVars
             = DConT repName
             | otherwise
             = someTH (length funArgDefTyVars) (DConT repName)

  -- | Return all the stuff
  return [repDataDec, repAlgIns, repArbIns, repBrIns, repPatTyIns, repHashTyIns]


-- | Collect the variables of a pattern in left to right order.
-- Since the function defining the pattern can be using an instantiated type, we
-- need to carry it around to make the proper substitutions.
collectPatVarDepthsTys :: DType -> DPat -> Q [(Integer, DType)]
collectPatVarDepthsTys = collect 0
  where
    collect _ _ (DLitPa _) = return []
    collect d t (DVarPa _) = return [(d, t)]
    collect d t (DTildePa p) = collect d t p
    collect d t (DBangPa p) = collect d t p
    collect d t DWildPa = return [(d, t)]
    collect d t (DConPa conName conFieldsPats)
      = collectCon (d+1) t conName conFieldsPats
    collect _ _ p = unsupported 'collectPatVarDepthsTys (show p)

    -- | Calculate the instatiated types of each field and call recursively.
    collectCon d t conName conFieldsPats = do
      conFieldsTys <- getConFieldTypes conName t
      let conFieldsTysPats = zip conFieldsTys conFieldsPats
      concatMapM (uncurry (collect d)) conFieldsTysPats


-- | Get the field types of a constructor, instantiated against a concrete type
getConFieldTypes :: Name -> DType -> Q [DType]
getConFieldTypes conName insTy = do
  -- | Obtain the original data definition where conName is declared
  ogTyName <- dataConNameToDataName conName
  (vs, _) <- getDataD mempty ogTyName
  ogVars <- mapM desugar vs
  -- | Calculate variable substitutions with the concrete type
  let ogTy = ogTyName <<* ogVars
      Just subst = matchTy YesIgnore ogTy (simplifyDType insTy)
  -- | Get the original types of the fields definitions (maybe parametric)
  con <- dataConNameToCon conName
  DCon _ _ _ conFields _ <- head <$> dsCon ogVars ogTy con
  let conFieldsTys = dConFieldsTypes conFields
  -- | Return the field types instantiated with the concrete type
  mapM (substTy subst) conFieldsTys


----------------------------------------
-- | Extract function left hand side using an external parser.

-- The left hand side of a function
data FunLHS = FunLHS Name DType [[DPat]] deriving Show

reifyFunLHS :: Name -> Q FunLHS
reifyFunLHS funName = do
  here <- currentFile
  DVarI _ fsig _ <- reifyOrFail funName
  fpats <- extractDPats here funName
  return (FunLHS funName fsig fpats)

extractDPats :: FilePath -> Name -> Q [[DPat]]
extractDPats path funName = do
  parsed <- liftIO (Ext.parseFile path)
  case parsed of
    Ext.ParseOk (Ext.Module _ _ _ _ decs) -> do
      let extractFunBinds (Ext.FunBind _ ms) = (ms:)
          extractFunBinds _ = id
          srcDefs = concat (foldr extractFunBinds [] decs)
          funDefs = filter (matchName funName) srcDefs
      dpats <- mapM toDPats funDefs
      if (null dpats)
      then error ("extractDPats: no patterns while reifying " ++ show funName)
      else return dpats
    err -> error ("extractDPats: cannot parse " ++ show path ++"\n" ++ show err)

matchName :: Name -> Ext.Match l -> Bool
matchName f (Ext.Match      _ n _ _ _)   = Ext.prettyPrint n == nameBase f
matchName f (Ext.InfixMatch _ _ n _ _ _) = Ext.prettyPrint n == nameBase f

toDPats :: Ext.Match l -> Q [DPat]
toDPats (Ext.Match _ _ p _ _)
  = mapM toTHDPat p
toDPats (Ext.InfixMatch _ p _ ps _ _)
  = (:) <$> toTHDPat p <*> mapM toTHDPat ps

toTHDPat :: Ext.Pat l -> Q DPat
toTHDPat (Ext.PLit _ sign l)
  = pure (DLitPa (toTHLit l sign))
toTHDPat (Ext.PVar _ n)
  = DVarPa <$> toTHDataName n
toTHDPat (Ext.PApp _ cn ps)
  = DConPa <$> toTHDataName cn <*> mapM toTHDPat ps
toTHDPat (Ext.PIrrPat _ pat)
  = DTildePa <$> toTHDPat pat
toTHDPat (Ext.PBangPat _ pat)
  = DBangPa <$> toTHDPat pat
toTHDPat (Ext.PWildCard _)
  = pure DWildPa
toTHDPat (Ext.PParen _ pat)
  = toTHDPat pat
toTHDPat p
  = unsupported 'toTHDPat (Ext.prettyPrint p)

toTHLit :: Ext.Literal l -> Ext.Sign l -> Lit
toTHLit (Ext.Char _ c _)     _                = CharL c
toTHLit (Ext.String _ str _) _                = StringL str
toTHLit (Ext.Int _ n _)      (Ext.Negative _) = IntegerL (-n)
toTHLit (Ext.Int _ n _)      _                = IntegerL n
toTHLit (Ext.Frac _ f _)     (Ext.Negative _) = RationalL (-f)
toTHLit (Ext.Frac _ f _)     _                = RationalL f
toTHLit l _ = unsupported 'toTHLit (Ext.prettyPrint l)

toTHDataName :: Ext.Pretty a => a -> Q Name
toTHDataName = mkDataNameWithLocals . Ext.prettyPrint
