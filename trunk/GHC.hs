{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}

module Test.QuickCheck.Patterns.GHC where

import GHC
import GHC.Paths (libdir)

import Outputable
import DynFlags

import Control.Monad.IO.Class

-- target, target' :: String
-- target  = "Test.QuickCheck.Patterns.Expr"
-- target' = "Expr"

-- main :: IO ()
-- main = parseSource target >>= dynPrint


-- parseSource :: String -> IO ParsedSource
-- parseSource target =
--     defaultErrorHandler defaultFatalMessager defaultFlushOut $ do
--       runGhc (Just libdir) $ do

--         dflags <- getSessionDynFlags

--         setSessionDynFlags dflags
--           { includePaths = ["src/Test/QuickCheck/Patterns"] ++ includePaths dflags
--           , packageFlags = [ExposePackage "ghc" (PackageArg "ghc") (ModRenaming True [])]
--           }

--         guessTarget target' Nothing >>= setTargets . pure
--         load LoadAllTargets
--         modSum <- getModSummary (mkModuleName target)
--         parsedSource <$> parseModule modSum

-- dynPrint :: Outputable a => a -> IO ()
-- dynPrint x = runGhc (Just libdir) $ do
--   dflags <- getSessionDynFlags
--   liftIO $ putStrLn $ showSDoc dflags $ ppr x
