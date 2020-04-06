{-# LANGUAGE TypeFamilies #-}

module PrimeTest where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Set as S
import qualified Data.List as L
import Data.Function
import PdsReachability.Reachability
import PdsReachability.Specification
import PdsReachability.Structure

data PrimeTest

data State
  = Number Int
  | Count Int
  deriving (Eq, Ord, Show)

data StackElm
  = Bottom Char
  | Prime Int
  deriving (Eq, Ord, Show)

data PrimeDynPop
  = PopAnythingBut StackElm

data PrimeUntDynPop

type instance Node PrimeTest = State
type instance Element PrimeTest = StackElm
type instance TargetedDynPop PrimeTest = PrimeDynPop
type instance UntargetedDynPop PrimeTest = PrimeUntDynPop

-- doDynPopPrime :: PrimeDynPop -> Element PrimeTest -> [Path PrimeTest]
-- doDynPopPrime dpf element =
--   case dpf of
--     PopAnythingBut se ->
--       if (element == se) then [] else [Path []]
--
-- doUntargetedDynPopPrime :: PrimeUntDynPop -> Element PrimeTest -> [(Path PrimeTest, Terminus PrimeTest)]
-- doUntargetedDynPopPrime _ _ = []
--
-- -- primeFactorCountTest :: ?
-- primeFactorCountTest =
--   let isPrime n =
--         let divide k =
--               if (k <= 1) then True else
--                 case (n mod k) of 0 -> False
--                                   otherwise -> divide (k-1)
--             in
--         let isFactor n k =
--               if (n mod k == 0) then True else False in
--         let start = Number 12 in
--         let analysis =
--               emptyAnalysis doDynPopPrime doUntargetedDynPopPrime
--               & addEdgeFunction (\state ->
--                                     case state of
--                                       Number n ->
--                                         let leqState = [1..n] in
--                                         let primesLeqState = L.filter isPrime leqState in
--                                         let primeFactors = L.filter (isFactor n) primesLeqState in
--                                         L.map (\k -> ([Push (Prime k)], StaticTerminus (Number (n/k)))) primeFactors
--                                       Count _ -> []
--                                 )
--               & addEdge (Edge (UserNode (Number 1)) Nop (UserNode (Count 0)))
--               & addEdgeFunction (\state ->
--                             case state of
--                               Count c -> [([DynamicPop (PopAnythingBut(Bottom '$'))], StaticTerminus (Count (c+1)))]
--                               Number _ -> []
--                         )
--               & addStart start [Push (Bottom '$')]
--               & fullClosure
--         in
--         undefined -- TODO
--   in
--   undefined -- TODO
