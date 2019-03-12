module Test.Dragen.Struct.TH.Extract where

import Data.List

import Control.Monad.Extra
import Control.Monad.IO.Class

import Language.Haskell.Exts
import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Desugar as THD

import Test.Dragen.Struct.TH.Util


----------------------------------------
-- | Parse a module or die gracefully
parseModule :: FilePath -> TH.Q (Module SrcSpanInfo)
parseModule path = do
  parsed <- liftIO (parseFileWithExts defaultExts path)
  case parsed of
    ParseOk m -> return m
    parseError -> dragenError "cannot parse file" [path, show parseError]

defaultExts :: [Extension]
defaultExts = parseExtension <$>
  [ "AllowAmbiguousTypes"
  , "DataKinds"
  , "DeriveFunctor"
  , "DeriveGeneric"
  , "ExistentialQuantification"
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


----------------------------------------
-- | Extract a list of top-level variable identifiers from a module
extractVarNames :: Module SrcSpanInfo -> TH.Q [TH.Name]
extractVarNames (Module _ mbModHead _ _ decs) = do

  let srcNames = foldr extractBinds [] decs

      extractBinds (PatBind _ ps@(PVar {}) _ _) xs = patBindName ps : xs
      extractBinds (FunBind _ ms) xs               = map funBindName ms ++ xs
      extractBinds _ xs = xs

      funBindName (Match _ n _ _ _)        = TH.mkName (qualify mbModName n)
      funBindName (InfixMatch _ _ n _ _ _) = TH.mkName (qualify mbModName n)

      patBindName (PVar _ n) = TH.mkName (qualify mbModName n)
      patBindName p          = unsupported 'extractVarNames p

      mbModName = case mbModHead of
        (Just (ModuleHead _ modName _ _)) -> Just modName
        _                                 -> Nothing

      qualify (Just modName) n = prettyPrint modName ++ "." ++ prettyPrint n
      qualify _              n = prettyPrint n

      printModName (Just modName) = prettyPrint modName
      printModName _              = "<unnamed module>"

  when (null srcNames) $ do
    dragenError "couldn't find any variable names" [printModName mbModName]

  let varNames = nub srcNames
  dragenMsg
    ("extracted names from module " ++ printModName mbModName ++ ":") [varNames]

  return (nub srcNames)

extractVarNames m = unsupported 'extractVarNames m

----------------------------------------
-- | Extract a list of top-level function patterns from a module
extractDPats :: TH.Name -> Module SrcSpanInfo -> TH.Q [[THD.DPat]]
extractDPats funName (Module _ _ _ _ decs) = do

  let extractFunBinds (FunBind _ ms) = (ms:)
      extractFunBinds _              = id

      srcDefs = concat (foldr extractFunBinds [] decs)
      funDefs = filter (matchName funName) srcDefs

  dpats <- mapM toDPats funDefs
  when (null dpats) $ do
    dragenError "found no patterns" [funName]

  return dpats

extractDPats m _ = unsupported 'extractDPats m

matchName :: TH.Name -> Match l -> Bool
matchName f (Match      _ n _ _ _)   = prettyPrint n == TH.nameBase f
matchName f (InfixMatch _ _ n _ _ _) = prettyPrint n == TH.nameBase f

toDPats :: Match l -> TH.Q [THD.DPat]
toDPats (Match _ _ p _ _)
  = mapM toTHDPat p
toDPats (InfixMatch _ p _ ps _ _)
  = (:) <$> toTHDPat p <*> mapM toTHDPat ps

toTHDPat :: Pat l -> TH.Q THD.DPat
toTHDPat (PLit _ sign l)
  = pure (THD.DLitPa (toTHLit l sign))
toTHDPat (PVar _ _)
  = pure THD.DWildPa
toTHDPat (PApp _ cn ps)
  = THD.DConPa <$> toTHDataName cn <*> mapM toTHDPat ps
toTHDPat (PIrrPat _ pat)
  = THD.DTildePa <$> toTHDPat pat
toTHDPat (PBangPat _ pat)
  = THD.DBangPa <$> toTHDPat pat
toTHDPat (PWildCard _)
  = pure THD.DWildPa
toTHDPat (PParen _ pat)
  = toTHDPat pat
toTHDPat (PList _ pats)
  = go pats
  where
    go [] = return $ THD.DConPa '[] []
    go (h : t) = do
      h' <- toTHDPat h
      t' <- go t
      return $ THD.DConPa '(:) [h', t']
toTHDPat p
  = unsupported 'toTHDPat (prettyPrint p)

toTHLit :: Literal l -> Sign l -> TH.Lit
toTHLit (Char _ c _)     _            = TH.CharL c
toTHLit (String _ str _) _            = TH.StringL str
toTHLit (Int _ n _)      (Negative _) = TH.IntegerL (-n)
toTHLit (Int _ n _)      _            = TH.IntegerL n
toTHLit (Frac _ f _)     (Negative _) = TH.RationalL (-f)
toTHLit (Frac _ f _)     _            = TH.RationalL f
toTHLit l _ = unsupported 'toTHLit (prettyPrint l)

toTHDataName :: Pretty a => a -> TH.Q TH.Name
toTHDataName = THD.mkDataNameWithLocals . prettyPrint
