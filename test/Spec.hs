module Main where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Set as S
import PdsReachability.Reachability
import PdsReachability.Structure

type TestGraph = Graph String String

main :: IO ()
main = do
  defaultMain (testGroup "Our Library Tests"
    [pushPopTest,
     pushPopTest2,
     pushNopTest,
     popNopTest,
     nopNopTest,
     biggerTest1])



-- First test: Push + Pop matching stack element
pushPopTestSet :: S.Set (Edge String String)
pushPopTestSet =
  S.fromList
    [Edge ("a", Push "x", "b"), Edge ("b", Pop "x", "c"), Edge ("a", Nop, "c")]

pushPopTestRes :: Graph String String
pushPopTestRes = graphFromEdges pushPopTestSet

pushPopTestSetInit :: S.Set (Edge String String)
pushPopTestSetInit =
  S.fromList
    [Edge ("a", Push "x", "b"), Edge ("b", Pop "x", "c")]

pushPopTestInit :: Graph String String
pushPopTestInit = graphFromEdges pushPopTestSetInit

pushPopTest :: TestTree
pushPopTest = testCase "Testing push + pop (matching stack element)"
  (assertEqual "Should have a nop edge" pushPopTestRes (graphClosure pushPopTestInit))

-- Second Test: Push + Pop non-matching stack element
pushPopTestSet2 :: S.Set (Edge String String)
pushPopTestSet2 =
  S.fromList
    [Edge ("a", Push "x", "b"), Edge ("b", Pop "y", "c")]

pushPopTestRes2 :: Graph String String
pushPopTestRes2 = graphFromEdges pushPopTestSet2

pushPopTestSetInit2 :: S.Set (Edge String String)
pushPopTestSetInit2 =
  S.fromList
    [Edge ("a", Push "x", "b"), Edge ("b", Pop "y", "c")]

pushPopTestInit2 :: Graph String String
pushPopTestInit2 = graphFromEdges pushPopTestSetInit2

pushPopTest2 :: TestTree
pushPopTest2 = testCase "Testing push + pop (non-matching stack element)"
  (assertEqual "Should not have a nop edge" pushPopTestRes2 (graphClosure pushPopTestInit2))

-- Third Test: Push + Nop
pushNopTestSet :: S.Set (Edge String String)
pushNopTestSet =
  S.fromList
    [Edge ("a", Push "x", "b"), Edge ("b", Nop, "c"), Edge ("a", Push "x", "c")]

pushNopTestRes :: Graph String String
pushNopTestRes = graphFromEdges pushNopTestSet

pushNopTestSetInit :: S.Set (Edge String String)
pushNopTestSetInit =
  S.fromList
    [Edge ("a", Push "x", "b"), Edge ("b", Nop, "c")]

pushNopTestInit :: Graph String String
pushNopTestInit = graphFromEdges pushNopTestSetInit

pushNopTest :: TestTree
pushNopTest = testCase "Testing push + nop"
  (assertEqual "Should have form a nop edge" pushNopTestRes (graphClosure pushNopTestInit))

-- Third Test: Pop + Nop
popNopTestSet :: S.Set (Edge String String)
popNopTestSet =
  S.fromList
    [Edge ("a", Pop "x", "b"), Edge ("b", Nop, "c")]

popNopTestRes :: Graph String String
popNopTestRes = graphFromEdges popNopTestSet

popNopTestSetInit :: S.Set (Edge String String)
popNopTestSetInit =
  S.fromList
    [Edge ("a", Pop "x", "b"), Edge ("b", Nop, "c")]

popNopTestInit :: Graph String String
popNopTestInit = graphFromEdges popNopTestSetInit

popNopTest :: TestTree
popNopTest = testCase "Testing pop + nop"
  (assertEqual "Should not have new edges" popNopTestRes (graphClosure popNopTestInit))

-- Fourth Test: Nop + Nop
nopNopTestSet :: S.Set (Edge String String)
nopNopTestSet =
  S.fromList
    [Edge ("a", Nop, "b"), Edge ("b", Nop, "c"), Edge ("a", Nop, "c")]

nopNopTestRes :: Graph String String
nopNopTestRes = graphFromEdges nopNopTestSet

nopNopTestSetInit :: S.Set (Edge String String)
nopNopTestSetInit =
  S.fromList
    [Edge ("a", Nop, "b"), Edge ("b", Nop, "c")]

nopNopTestInit :: Graph String String
nopNopTestInit = graphFromEdges nopNopTestSetInit

nopNopTest :: TestTree
nopNopTest = testCase "Testing nop + nop"
  (assertEqual "Should have a new edge" nopNopTestRes (graphClosure nopNopTestInit))

-- Fifth Test: Complex 1
biggerTestSet1 :: S.Set (Edge String String)
biggerTestSet1 =
  S.fromList
    [Edge ("a", Push "x", "b"),
     Edge ("b", Pop "y", "c"),
     Edge ("b", Nop, "c"),
     Edge ("c", Nop, "d"),
     Edge ("a", Push "x", "c"),
     Edge ("b", Nop, "d"),
     Edge ("a", Push "x", "d")]

biggerTestRes1 :: Graph String String
biggerTestRes1 = graphFromEdges biggerTestSet1

biggerTestSetInit1 :: S.Set (Edge String String)
biggerTestSetInit1 =
  S.fromList
    [Edge ("a", Push "x", "b"),
     Edge ("b", Pop "y", "c"),
     Edge ("b", Nop, "c"),
     Edge ("c", Nop, "d")]

biggerTestInit1 :: Graph String String
biggerTestInit1 = graphFromEdges biggerTestSetInit1

biggerTest1 :: TestTree
biggerTest1 = testCase "Testing bigger test case"
  (assertEqual "Should have multiple new edges" biggerTestRes1 (graphClosure biggerTestInit1))
