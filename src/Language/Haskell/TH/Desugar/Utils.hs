{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}

module Language.Haskell.TH.Desugar.Utils where

import Data.Char

import Control.Monad.IO.Class

import Language.Haskell.TH
import Language.Haskell.TH.Desugar

import System.Directory
import System.FilePath
