module Main where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Set as S
import Data.Function
import PdsReachability.Reachability
import PdsReachability.Structure

import qualified Spec
import qualified PrimeTest

main :: IO ()
main = do
  defaultMain (testGroup "all tests" [Spec.tests, PrimeTest.tests])
