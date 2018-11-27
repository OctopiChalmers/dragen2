{-# LANGUAGE TemplateHaskell #-}

module Test.QuickCheck.HRep.TH.Common where


import Language.Haskell.TH
import Language.Haskell.TH.Desugar
import Language.Haskell.TH.Desugar.Utils

import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Gen.Utils as QC
import qualified Test.QuickCheck.HRep as HRep
import qualified Test.QuickCheck.Branching as Branching

import qualified GHC.Generics as Generics
import qualified Data.Vector as Vector

----------------------------------------
-- | Borrowed names

someTH :: Int -> DType -> DType
someTH n = DAppT (DConT (mkName ("Some" ++ show n)))

smallerTH :: DExp -> DExp
smallerTH = DAppE (DVarE 'QC.smaller)

reduceTH :: Integer -> DExp -> DExp
reduceTH n = DAppE (DAppE (DVarE 'QC.reduce) (DLitE (IntegerL n)))

liftArbitraryTH :: DExp -> DExp
liftArbitraryTH = DAppE (DVarE 'QC.liftArbitrary)

liftArbitrary2TH :: DExp -> DExp -> DExp
liftArbitrary2TH e1 e2 = DAppE (DAppE (DVarE 'QC.liftArbitrary2) e1) e2

mkSumType :: DType -> DType -> DType
mkSumType t1 t2 = ''HRep.Sum <<| [t1, t2]

mkSizedSumType :: DType -> DType -> DType
mkSizedSumType t1 t2 = ''HRep.SizedSum <<| [t1, t2]

arbitraryTH :: DExp
arbitraryTH = DVarE 'QC.arbitrary

satisfyTH :: String -> DExp
satisfyTH str = DAppE (DVarE 'QC.satisfy) (DLitE (StringL str))

stepTH :: DExp
stepTH = DVarE 'HRep.step

singletonTH :: DExp -> DExp
singletonTH = DAppE (DVarE 'Vector.singleton)

branchingFunNames :: [Name]
branchingFunNames = [ 'Branching.alias
                    , 'Branching.terminals
                    , 'Branching.probs
                    , 'Branching.beta
                    , 'Branching.sigma
                    ]

derivingClauses :: [DDerivClause]
derivingClauses = [ DDerivClause Nothing
                    [ DConPr ''Functor
                    , DConPr ''Show
                    , DConPr ''Generics.Generic
                    ] ]
