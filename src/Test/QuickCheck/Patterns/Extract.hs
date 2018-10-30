{-# LANGUAGE LambdaCase #-}
module Test.QuickCheck.Patterns.Extract where

import Control.Monad.IO.Class

import qualified Language.Haskell.Exts as Ext
import Language.Haskell.TH
import Language.Haskell.TH.Desugar

-- import Test.QuickCheck.Patterns.Types

-- exts :: [Extension]
-- exts = [ EnableExtension DeriveFunctor
--        , EnableExtension TypeOperators
--        , EnableExtension TypeFamilies
--        , EnableExtension DataKinds
--        , EnableExtension MultiParamTypeClasses
--        ]


reifyFunLHS :: DsMonad q => Name -> q FunLHS
reifyFunLHS fname = do
  reifyOrFail


extractDPats :: DsMonad q => FilePath -> Name -> q [DPats]
extractDPats path fun = liftIO $ Ext.parseFile path >>= \case
  Ext.ParseOk (Ext.Module _ _ _ _ decs) -> do
    let extractFunBinds (Ext.FunBind _ ms) = (ms:)
        extractFunBinds _ = id

        srcDefs = concat (foldr extractFunBinds [] decs)
        funDefs = filter (matchName fun) srcDefs

    return (map toDPats funDefs)

  err -> error $ "extractDPats: cannot parse " ++ show path ++ "\n" ++ show err

matchName :: Name -> Ext.Match l -> Bool
matchName f (Ext.Match      _ n _ _ _)   = Ext.prettyPrint n == nameBase f
matchName f (Ext.InfixMatch _ _ n _ _ _) = Ext.prettyPrint n == nameBase f

toDPats :: Ext.Match l -> [DPat]
toDPats (Ext.Match _ _ pats _ _) = map toTHDPat pats
toDPats (Ext.InfixMatch _ p _ ps _ _) = toTHDPat p : map toTHDPat ps

toTHName :: Ext.Pretty a => a -> Name
toTHName = mkName . Ext.prettyPrint

toTHDPat :: Ext.Pat l -> DPat
toTHDPat (Ext.PLit _ sign l) = DLitPa (toTHLit l sign)
toTHDPat (Ext.PVar _ n) = DVarPa (toTHName n)
toTHDPat (Ext.PApp _ cn ps) = DConPa (toTHName cn) (map toTHDPat ps)
toTHDPat (Ext.PIrrPat _ pat) = DTildePa (toTHDPat pat)
toTHDPat (Ext.PBangPat _ pat) = DBangPa (toTHDPat pat)
toTHDPat (Ext.PWildCard _) = DWildPa
toTHDPat (Ext.PParen _ pat) = toTHDPat pat
toTHDPat p = unsupported "toTHDPat" (Ext.prettyPrint p)

toTHLit :: Ext.Literal l -> Ext.Sign l -> Lit
toTHLit (Ext.Char _ c _)     _                = CharL c
toTHLit (Ext.String _ str _) _                = StringL str
toTHLit (Ext.Int _ n _)      (Ext.Negative _) = IntegerL (-n)
toTHLit (Ext.Int _ n _)      _                = IntegerL n
toTHLit (Ext.Frac _ f _)     (Ext.Negative _) = RationalL (-f)
toTHLit (Ext.Frac _ f _)     _                = RationalL f
toTHLit l _ = unsupported "toTHLit" (Ext.prettyPrint l)

-- | Usefull unsupported messages
unsupported :: Show a => String -> a -> any
unsupported fname val = error $ fname ++ ": not yet supported " ++ show val
