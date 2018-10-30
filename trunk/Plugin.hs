{-# LANGUAGE ViewPatterns #-}
module Test.QuickCheck.Patterns.Plugin where

import Data.List.Split

import Control.Monad.IO.Class

import GHC
import GHC.Paths (libdir)
import Outputable
import HscTypes
import Plugins

-- import Test.QuickCheck.Patterns.Pattern

plugin :: Plugin
plugin = defaultPlugin { parsedResultAction = run }

run :: [CommandLineOption] -> ModSummary -> HsParsedModule -> Hsc HsParsedModule
run opts _ parsed = do

  let funcs = concatMap (splitOn ",") opts

  putStrLnHsc "--------------------------"
  putStrLnHsc "Plugin running!"
  putStrLnHsc (show funcs)
  putStrLnHsc "--------------------------"
  return (procHsParsedModule parsed)

procHsParsedModule :: HsParsedModule -> HsParsedModule
procHsParsedModule parsed@(hpm_module -> L loc hsMod) = parsed'
  where
    parsed' = parsed { hpm_module = L loc hsMod' }
    hsMod' = hsMod { hsmodDecls = procLHsDecls (hsmodDecls hsMod) }

procLHsDecls :: [LHsDecl GhcPs] -> [LHsDecl GhcPs]
procLHsDecls decls = patDataDecls ++ decls
  where
    patDataDecls = debug decls $ []


putStrLnHsc :: String -> Hsc ()
putStrLnHsc = liftIO . putStrLn

debug :: Outputable a => a -> b -> b
debug = trace . showSDocUnsafe . ppr

dynPrint :: Outputable a => a -> IO ()
dynPrint x = runGhc (Just libdir) $ do
  dflags <- getSessionDynFlags
  liftIO $ putStrLn $ showSDoc dflags $ ppr x
