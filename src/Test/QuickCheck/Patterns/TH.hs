{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}

module Test.QuickCheck.Patterns.TH
  ( module Test.QuickCheck.Patterns.TH
  , Name
  ) where

import Data.Foldable

import System.Directory
import System.FilePath

import Control.Monad.Extra
import Control.Monad.IO.Class

import Language.Haskell.TH
import Language.Haskell.TH.Desugar
import qualified Language.Haskell.Exts as Ext

import qualified Test.QuickCheck.Patterns.Rep as Rep
import Test.QuickCheck.FreqArbitrary


deriving instance Eq DTyVarBndr
deriving instance Eq DPred
deriving instance Eq DType

----------------------------------------
-- | Function match clauses

deriveAll :: Name -> [Name] -> [(Name, Int)] -> Q [Dec]
deriveAll t_name t_inst f_names_args = do
  pf <- derivePF t_name
  fun_pfs <- concatMapM (deriveFunPF t_inst) f_names_args
  return (pf ++ fun_pfs)

----------------------------------------
-- | Derive the pattern functor, Algebra instance and PF type instance for a
-- given data type name.
derivePF :: Name -> Q [Dec]
derivePF og_tn = do

  -- | Reify the original data declaration name and desugar it
  (vs, cons) <- getDataD mempty og_tn
  og_vs <- mapM desugar vs
  let og_ty = og_tn <<* og_vs
  og_cons <- concatMapM (dsCon og_vs og_ty) cons

  -- | Create some common internals for the pattern functor
  let pf_tn = mkPFName og_tn
  pf_rv <- mkRecVar

  -- | Generate pattern functor data type
  let pf_dd = DDataD Data [] pf_tn pf_vs Nothing pf_cons derivingClauses
      pf_vs = og_vs ++ [pf_rv]
      pf_ty_ext = pf_tn <<* pf_vs
      pf_cons = map mkPFCon og_cons

      mkPFCon (DCon c_vs c_cxt c_name c_fields _)
        = DCon pfc_vs c_cxt pfc_name pf_fields pf_ty_ext
        where pfc_vs = pf_rv : c_vs
              pfc_name = mkPFName c_name
              pf_fields = mkPFConFields c_fields

      mkPFConFields (DNormalC ifx bts) = DNormalC ifx (map replace_bts bts)
        where replace_bts = fmap (replaceTyForTV og_ty pf_rv)
      mkPFConFields (DRecC vbts) = DRecC (map replace_vbts vbts)
        where replace_vbts (n,b,t) = (mkPFName n,b,replaceTyForTV og_ty pf_rv t)

  -- | Generate PF type family instance
  let pf_ti = DTySynInstD ''Rep.PF (DTySynEqn [og_ty] pf_ty_f)
      pf_ty_f = pf_tn <<* og_vs

  -- | Generate Algebra (PF T) T instance
  let pf_alg_inst = DInstanceD Nothing [] pf_alg_ty [pf_alg_letdec]
      pf_alg_ty = ''Rep.Algebra <<| [pf_ty_f, og_ty]
      pf_alg_letdec = DLetDec (DFunD 'Rep.alg clauses)
        where clauses = map (uncurry mkPFAlgClause) (zip pf_cons og_cons)

      mkPFAlgClause pf_con og_con
        = DClause [mkAlgClausePat pf_con] (mkAlgClauseRhs og_con)

      mkAlgClausePat (DCon _ _ c_name c_fields _)
        = DConPa c_name (map DVarPa fields_pats)
        where fields_pats = take (dConFieldsNr c_fields) patVars

      mkAlgClauseRhs (DCon _ _ c_name c_fields _)
        = applyDExp (DConE c_name) (map DVarE field_exprs)
        where field_exprs = take (dConFieldsNr c_fields) patVars

  -- | Generate FreqArbitrary1 (PF T) instance
  let pf_gen = DInstanceD Nothing pf_gen_cxt pf_gen_ty [pf_gen_letdec]
      pf_gen_ty = ''FreqArbitrary1 <<| [pf_tn <<* og_vs]
      pf_gen_cxt = map mkCxt og_vs
      pf_gen_letdec = DLetDec (DFunD 'liftFreqArbitrary [pf_gen_body])
      pf_gen_body = DClause [] (DVarE 'undefined)

      mkCxt v = DAppPr (DConPr ''FreqArbitrary) (dTyVarBndrToDType v)

  -- | Return all the generated stuff, converted again to TH
  return (sweeten [pf_dd, pf_ti, pf_alg_inst, pf_gen])


----------------------------------------
-- | Derive the function LHS pattern functor, Algebra instance, and Pat type
-- instance for a given function name.
deriveFunPF :: [Name] -> (Name, Int) -> Q [Dec]
deriveFunPF f_inst_vars (f_name, arg_nr) = do

  FunLHS _ f_sig f_pats <- reifyFunLHS f_name
  let (_, _, f_arg_tys, _) = unravel f_sig

  -- | Pick the right argument to extract its patterns
  let pats  = dropTrivialPats (map (!! (arg_nr - 1)) f_pats)
      ty    = f_arg_tys !! (arg_nr - 1)
      pf_fv = map DPlainTV (toList (fvDType ty))
      pf_tn = mkFunPFName f_name

  -- | Create some common internals for the pattern functor
  pf_rv <- mkRecVar
  pats_vs_tys <- mapM (collectPatVarTypes ty) pats
  let pats_vs_tys' = map (map (replaceTyForTV ty pf_rv)) pats_vs_tys
      pf_cons_names = zip pats_vs_tys' [1..]

  -- | Create function LHS pattern functor data definition
  let pf_dd = DDataD Data [] pf_tn pf_vs Nothing pf_cons derivingClauses
      pf_vs = pf_fv ++ [pf_rv]
      pf_ty = pf_tn <<* pf_vs
      pf_cons = map (uncurry mkFunPFCon) pf_cons_names

      mkFunPFCon c_fields_tys c_idx
        = DCon pf_vs [] c_name (DNormalC False c_fields) pf_ty
        where c_name = mkFunPFConName f_name c_idx
              c_fields = map mkBangType c_fields_tys

      mkBangType t = (defaultBang, replaceTyForTV pf_ty pf_rv t)
      defaultBang = Bang NoSourceUnpackedness NoSourceStrictness

  -- | Create Pat type family instance
  -- There is currently a problem here: we cannot use existentially polymorphic
  -- types on type instance RHS.
  let pf_ti = DTySynInstD ''Rep.Pat pf_eqns
      pf_eqns = DTySynEqn [f_name_ty_lit] pf_rhs
      pf_rhs = pf_tn <<| pf_rhs_args
      pf_rhs_args = DConT <$> take (length pf_fv) f_inst_vars
      f_name_ty_lit = DLitT (StrTyLit (nameBase f_name))

  -- | Create Algebra (Pat T) T instance
  let alg_inst = DInstanceD Nothing [] alg_ty [alg_letdec]
      alg_ty = ''Rep.Algebra <<| [ty_f, ty]
      ty_f = pf_tn <<* pf_fv
      alg_letdec = DLetDec (DFunD 'Rep.alg alg_clauses)
      alg_clauses = map (uncurry mkPFAlgClause) (zip pf_cons pf_pats_exps)
      pf_pats_exps = map dPatToDExpWithVars pats

      mkPFAlgClause pf_con pat_exp
        = DClause [mkAlgClausePat pf_con] pat_exp

      mkAlgClausePat (DCon _ _ c_name c_fields _)
        = DConPa c_name (map DVarPa fields_pats)
        where fields_pats = take (dConFieldsNr c_fields) patVars

  -- | Return all the generated stuff, converted again to TH
  return (sweeten [pf_dd, pf_ti, alg_inst])

-- | Collect the variables of a pattern in left to right order.
-- Since the function defining the pattern can be using an instantiated type, we
-- need to carry it around to make the proper substitutions.
collectPatVarTypes :: DType -> DPat -> Q [DType]
collectPatVarTypes _ (DLitPa _) = return []
collectPatVarTypes t (DVarPa _) = return [t]
collectPatVarTypes t (DTildePa p) = collectPatVarTypes t p
collectPatVarTypes t (DBangPa p) = collectPatVarTypes t p
collectPatVarTypes t DWildPa = return [t]
collectPatVarTypes t (DConPa c_name c_fields_pats)
  = collectConPatVarTypes t c_name c_fields_pats
collectPatVarTypes _ p = unsupported "collectPatVarTypes" (show p)

-- | Calculate the instatiated types of each field and call recursively.
collectConPatVarTypes :: DType -> Name -> DPats -> Q [DType]
collectConPatVarTypes t c_name c_fields_pats = do
  c_fields_tys <- getConFieldTypes c_name t
  let c_fields_tys_pats = zip c_fields_tys c_fields_pats
  concatMapM (uncurry collectPatVarTypes) c_fields_tys_pats

-- | Get the field types of a constructor, instantiated against a concrete type
getConFieldTypes :: Name -> DType -> Q [DType]
getConFieldTypes c_name ins_ty = do
  -- | Obtain the original data definition where c_name is declared
  og_tn <- dataConNameToDataName c_name
  (vs, _) <- getDataD mempty og_tn
  -- | Calculate variable substitutions with the concrete type
  og_vs <- mapM desugar vs
  let og_ty = og_tn <<* og_vs
      Just subst = matchTy YesIgnore og_ty (simplifyType ins_ty)
  -- | Get the original types of the fields definitions (maybe parametric)
  con <- dataConNameToCon c_name
  DCon _ _ _ c_fields _ <- head <$> dsCon og_vs og_ty con
  let c_fields_tys = dConFieldsTypes c_fields
  -- | Return the field types instantiated with the concrete type
  mapM (substTy subst) c_fields_tys

----------------------------------------
-- | Derive pattern matching evaluation functions.
deriveMatchReject :: DPats -> Q DExp
deriveMatchReject pats = do
  x <- newName "x"
  let bad_clauses = map (flip DMatch (DConE 'False)) pats
      last_clause = DMatch DWildPa (DConE 'True)
  return (DLamE [x] (DCaseE (DVarE x) (bad_clauses ++ [last_clause])))


----------------------------------------
-- | Extract function left hand side using an external parser.
-- I know, this is nasty workaround.

data FunLHS
  = FunLHS Name DType [DPats]
  deriving Show

type DPats = [DPat]

reifyFunLHS :: Name -> Q FunLHS
reifyFunLHS fname = do
  here <- currentFile
  DVarI _ fsig _ <- reifyOrFail fname
  fpats <- extractDPats here fname
  return (FunLHS fname fsig fpats)

exts :: [Ext.Extension]
exts = map Ext.parseExtension
  [ "DataKinds"
  , "TypeOperators"
  , "MultiParamTypeClasses"
  , "TypeFamilies"
  ]

extractDPats :: FilePath -> Name -> Q [DPats]
extractDPats path fun = do
  parsed <- liftIO (Ext.parseFileWithExts exts path)
  case parsed of
    Ext.ParseOk (Ext.Module _ _ _ _ decs) -> do
      let extractFunBinds (Ext.FunBind _ ms) = (ms:)
          extractFunBinds _ = id
          srcDefs = concat (foldr extractFunBinds [] decs)
          funDefs = filter (matchName fun) srcDefs
      dpats <- mapM toDPats funDefs
      if (null dpats)
      then error ("extractDPats: found no patterns while reifying " ++ show fun)
      else return dpats
    err -> error ("extractDPats: cannot parse " ++ show path ++"\n" ++ show err)

matchName :: Name -> Ext.Match l -> Bool
matchName f (Ext.Match      _ n _ _ _)   = Ext.prettyPrint n == nameBase f
matchName f (Ext.InfixMatch _ _ n _ _ _) = Ext.prettyPrint n == nameBase f

toDPats :: Ext.Match l -> Q DPats
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
  = unsupported "toTHDPat" (Ext.prettyPrint p)

toTHLit :: Ext.Literal l -> Ext.Sign l -> Lit
toTHLit (Ext.Char _ c _)     _                = CharL c
toTHLit (Ext.String _ str _) _                = StringL str
toTHLit (Ext.Int _ n _)      (Ext.Negative _) = IntegerL (-n)
toTHLit (Ext.Int _ n _)      _                = IntegerL n
toTHLit (Ext.Frac _ f _)     (Ext.Negative _) = RationalL (-f)
toTHLit (Ext.Frac _ f _)     _                = RationalL f
toTHLit l _ = unsupported "toTHLit" (Ext.prettyPrint l)

dropTrivialPats :: [DPat] -> [DPat]
dropTrivialPats [] = []
dropTrivialPats (DVarPa _ : _) = []
dropTrivialPats (DWildPa  : _) = []
dropTrivialPats (p : ps) = p : dropTrivialPats ps

----------------------------------------
-- | Types manipulations

(.==.) :: DType -> DType -> Bool
t1 .==. t2 = removeSigs t1 == removeSigs t2

simplifyType :: DType -> DType
simplifyType (DForallT _ _ t) = simplifyType t
simplifyType (DSigT t _) = simplifyType t
simplifyType (DAppT l r) = DAppT (simplifyType l) (simplifyType r)
simplifyType t = t

removeSigs :: DType -> DType
removeSigs (DForallT v c t) = DForallT v c (removeSigs t)
removeSigs (DSigT t _) = t
removeSigs (DAppT l r) = DAppT (removeSigs l) (removeSigs r)
removeSigs t = t

-- | Replace a given type by a type var within a type
replaceTyForTV :: DType -> DTyVarBndr -> DType -> DType
replaceTyForTV target tv ty | ty .==. target
  = dTyVarBndrToDType tv
replaceTyForTV target tv (DAppT l r)
  = DAppT (replaceTyForTV target tv l) (replaceTyForTV target tv r)
replaceTyForTV target tv (DSigT ty kind)
  = DSigT (replaceTyForTV target tv ty) kind
replaceTyForTV _  _ fa@(DForallT _ _ _)
  = unsupported "replaceTyForTV" (show fa)
replaceTyForTV _  _  ty = ty

replaceHeadTy :: Name -> DType -> DType
replaceHeadTy n (DConT _)   = DConT n
replaceHeadTy n (DVarT _)   = DConT n
replaceHeadTy n (DAppT l r) = DAppT (replaceHeadTy n l) r
replaceHeadTy n (DSigT t k) = DSigT (replaceHeadTy n t) k
replaceHeadTy n (DForallT vs c t) = DForallT vs c (replaceHeadTy n t)
replaceHeadTy _ t = t

litToDType :: Lit -> DType
litToDType (IntegerL _) = DConT ''Int
litToDType (StringL _) = DConT ''String
litToDType (CharL _) = DConT ''Char
litToDType (RationalL _) = DConT ''Rational
litToDType l = unsupported "litToDType" (show l)

dPatToDExpWithVars :: DPat -> DExp
dPatToDExpWithVars = fst . go patVars
  where
    go vs (DLitPa l) = (DLitE l, vs)
    go vs (DVarPa _) = (DVarE (head vs), tail vs)
    go vs (DConPa cn pats) = (applyDExp (DConE cn) pats', vs')
      where (pats', vs') = mapListDPatsToDExp (pats, vs)
    go vs (DTildePa pat) = go vs pat
    go vs (DBangPa pat) = go vs pat
    go vs (DSigPa pat kind) = (DSigE pat' kind, vs')
      where (pat', vs') = go vs pat
    go vs DWildPa = (DVarE (head vs), tail vs)

    mapListDPatsToDExp :: (DPats, [Name]) -> ([DExp], [Name])
    mapListDPatsToDExp ([], vs) = ([], vs)
    mapListDPatsToDExp (p:ps, vs) = (p':ps', vs'')
      where (p', vs') = go vs p
            (ps', vs'') = mapListDPatsToDExp (ps, vs')


mkDType, (<<|) :: Name -> [DType] -> DType
mkDType tn ts = DConT tn `applyDType` ts
(<<|) = mkDType

mkDTypeWithTVs, (<<*) :: Name -> [DTyVarBndr] -> DType
mkDTypeWithTVs tn vs = mkDType tn (map dTyVarBndrToDType vs)
(<<*) = mkDTypeWithTVs


----------------------------------------
-- | Name manipulations

toTHTypeName :: Ext.Pretty a => a -> Q Name
toTHTypeName = mkTypeNameWithLocals . Ext.prettyPrint

toTHDataName :: Ext.Pretty a => a -> Q Name
toTHDataName = mkDataNameWithLocals . Ext.prettyPrint

mkPFName :: Name -> Name
mkPFName n = mkName (nameBase n ++ "F")

mkFunPFName :: Name -> Name
mkFunPFName n = mkName ("Pat_" ++ nameBase n)

mkFunPFConName :: Name -> Int -> Name
mkFunPFConName n i = mkName ("Pat_" ++ nameBase n ++ "_" ++ show i)

----------------------------------------
-- | Utilities

dConFieldsNr :: DConFields -> Int
dConFieldsNr (DNormalC _ bts) = length bts
dConFieldsNr (DRecC bts)      = length bts

dConFieldsTypes :: DConFields -> [DType]
dConFieldsTypes (DNormalC _ bts) = map snd bts
dConFieldsTypes (DRecC bts)      = map (\(_,_,t) -> t) bts

mkTypeKindedVar :: Name -> DTyVarBndr
mkTypeKindedVar n = DKindedTV n (DConT typeKindName)

mkRecVar :: Q DTyVarBndr
mkRecVar = DPlainTV <$> newName "self"

patVars :: [Name]
patVars = map (mkName . ("v"++) . show) [1 :: Integer ..]

isVarT :: DType -> Bool
isVarT (DVarT {}) = True
isVarT (DSigT v _) = isVarT v
isVarT _ = False

derivingClauses :: [DDerivClause]
derivingClauses = [DDerivClause Nothing [DConPr ''Functor, DConPr ''Show]]

currentFile :: Q FilePath
currentFile = do
  dir  <- liftIO getCurrentDirectory
  file <- location
  return (dir </> loc_filename file)

reifyOrFail :: Name -> Q DInfo
reifyOrFail n = dsReify n >>= maybe err expand
  where err = error ("dsReify: error while reifiying " ++ show n)

unsupported :: Show a => String -> a -> any
unsupported fname val = error (fname ++ ": not yet supported " ++ show val)

putStrLnQ :: String -> Q ()
putStrLnQ = liftIO . putStrLn

debugQ :: Show a => a -> Q ()
debugQ v = do
  putStrLnQ "\n=== Debug ==="
  putStrLnQ (show v)
  putStrLnQ "=== Debug ==="

decorate :: Q a -> Q a
decorate action = do
  putStrLnQ "\n=== Template Haskell begin ==="
  res <- action
  putStrLnQ "===  Template Haskell end  ===\n"
  return res

qq :: Show a => Q a -> Q Exp
qq a = a >>= return . sweeten . DLitE . StringL . show
