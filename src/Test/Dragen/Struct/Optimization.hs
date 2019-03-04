module Test.Dragen.Struct.Optimization where

import Data.Proxy
import Data.Ord
import Data.List
import Data.Maybe

import System.IO
import System.IO.Unsafe

import qualified Data.Map.Strict as Map

import Test.Dragen.Struct.BoundedArbitrary
import Test.Dragen.Struct.Spec

----------------------------------------
-- | Distance functions

type DistFun
  = forall spec root.
  spec `StartingFrom` root
  => Proxy spec -> Proxy root
  -> MaxDepth -> [[Integer]] -> Double

uniform :: DistFun
uniform (_ :: Proxy spec) (_ :: Proxy root) maxDepth freqs
  = chiSquareConst (fromIntegral maxDepth) observed
  where observed = Map.elems (predictSpecWith @spec @root freqs maxDepth)

weighted :: [(String, Int)] -> DistFun
weighted weights (_ :: Proxy spec) (_ :: Proxy root) maxDepth freqs
  = chiSquare expected observed
  where
    prediction = predictSpecWith @spec @root freqs maxDepth
    withWeight = Map.filterWithKey hasWeight prediction
    (cnames, observed) = unzip (Map.toList withWeight)
    hasWeight cn _ = isJust (lookup cn weights)
    expected = multWeight <$> cnames
    multWeight cn = fromIntegral (fromJust (lookup cn weights) *  maxDepth)

chiSquare :: Floating a => [a] -> [a] -> a
chiSquare expected observed
  = sum (zipWith f observed expected)
  where
    f o e =  (o - e)**2 / e -- + 0.2 * (1/o)

chiSquareConst :: Floating a => a -> [a] -> a
chiSquareConst expected observed
  = chiSquare (repeat expected) observed


----------------------------------------
-- | Simulation-based optimization

epsilon :: Double
epsilon = 0.00001

heatDecay :: Double
heatDecay = 0.999

neighborsCount :: Int
neighborsCount = 300


mutate :: Integer -> [[Integer]] -> [[[Integer]]]
mutate n xss = map (mutateAt (+n) xss) [0.. sum (length <$> xss) - 1]

mutateAt :: (Integer -> Integer) -> [[Integer]] -> Int -> [[Integer]]
mutateAt f (xs : xss) ix
  | ix < length xs
  = (take ix xs ++ [f (xs !! ix)]  ++ drop (ix+1) xs) : xss
  | otherwise
  = xs : mutateAt f xss (ix - length xs)
mutateAt _ _ _ = error "mutateAt: empty list"

localSearch
  :: forall spec root.
     spec `StartingFrom` root
  => MaxDepth -> Double -> DistFun
  -> [[Integer]] -> [[[Integer]]] -> [[Integer]]
localSearch  maxDepth heat dist focus visited
  | null newNeighbors || delta <= epsilon
  = focus
  | delta <= epsilon
  = dot delta heat bestNeighborDist
    $ localSearch @spec @root
    maxDepth (heat/heatDecay) dist bestNeighbor newFrontier
  | otherwise
  = dot delta heat bestNeighborDist
    $ localSearch @spec @root
    maxDepth newHeat dist bestNeighbor newFrontier
  where
    delta         = abs (focusDist - bestNeighborDist)
    focusDist     = dist (Proxy @spec) (Proxy @root) maxDepth focus
    (bestNeighbor, bestNeighborDist)
      = minimumBy (comparing snd) neighborsDists
    neighborsDists = zip newNeighbors
      (dist (Proxy @spec) (Proxy @root) maxDepth <$> newNeighbors)
    newNeighbors  = mutate (floor heat) focus \\ (focus:visited)
    newHeat       = max 1 (heat*heatDecay)
    newFrontier   = newNeighbors ++ take neighborsCount visited


dot :: Double -> Double -> Double ->  a -> a
dot delta heat dist x
  = unsafePerformIO $ do
  putStrLn
    $ "> delta:" ++ show delta
    ++ "\theat:" ++ show heat
    ++ "\tdist:" ++ show dist
  hFlush stdout
  return x


optimizeFreqs
  :: forall spec root.
     spec `StartingFrom` root
  => MaxDepth -> DistFun -> [[Integer]] -> [[Integer]]
optimizeFreqs maxDepth dist freqs
  = localSearch @spec @root maxDepth heat dist freqs []
  where heat = fromIntegral maxDepth
