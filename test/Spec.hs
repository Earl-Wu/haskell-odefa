module Main where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Set as S
import PdsReachability.Reachability
import PdsReachability.Structure

type TestGraph = Graph String String DynPopFun
type TestEdge = Edge String String DynPopFun
type TestNode = Node String String DynPopFun
type TestPath = Path String DynPopFun

data DynPopFun
  = DynPopFun1
  | DynPopFun2 deriving (Eq, Ord, Show)

doDynPop :: DynPopFun -> String -> [TestPath]
doDynPop dpf se =
  case dpf of
    DynPopFun1 -> [[Push "II", Push "IV", Push "VI", Push se, Push "I"]]
    DynPopFun2 -> [[Push "1", Push "1", Push "1"]]

main :: IO ()
main = do
  defaultMain (testGroup "Our Library Tests"
    [pushPopTest,
     pushPopTest2,
     pushNopTest,
     popNopTest,
     nopNopTest,
     biggerTest1,
     dynPopTest1,
     dynPopTest2])

graphClosure :: TestGraph -> TestGraph
graphClosure g =
  let edges = getEdges g in
  let initialAnalysis = S.foldl (\acc -> \e -> updateAnalysis e acc) emptyAnalysis edges in
  let fullAnalysis = performClosure doDynPop initialAnalysis in
  getGraph fullAnalysis

-- First test: Push + Pop matching stack element
pushPopTestSet :: S.Set TestEdge
pushPopTestSet =
  S.fromList
    [Edge (UserNode "a", Push "x", UserNode "b"),
     Edge (UserNode "b", Pop "x", UserNode "c"),
     Edge (UserNode "a", Nop, UserNode "c")]

pushPopTestRes :: TestGraph
pushPopTestRes = graphFromEdges pushPopTestSet

pushPopTestSetInit :: S.Set TestEdge
pushPopTestSetInit =
  S.fromList
    [Edge (UserNode "a", Push "x", UserNode "b"),
     Edge (UserNode "b", Pop "x", UserNode "c")]

pushPopTestInit :: TestGraph
pushPopTestInit = graphFromEdges pushPopTestSetInit

pushPopTest :: TestTree
pushPopTest = testCase "Testing push + pop (matching stack element)"
  (assertEqual "Should have a nop edge" pushPopTestRes (graphClosure pushPopTestInit))

-- Second Test: Push + Pop non-matching stack element
pushPopTestSet2 :: S.Set TestEdge
pushPopTestSet2 =
  S.fromList
    [Edge (UserNode "a", Push "x", UserNode "b"),
     Edge (UserNode "b", Pop "y", UserNode "c")]

pushPopTestRes2 :: TestGraph
pushPopTestRes2 = graphFromEdges pushPopTestSet2

pushPopTestSetInit2 :: S.Set TestEdge
pushPopTestSetInit2 =
  S.fromList
    [Edge (UserNode "a", Push "x", UserNode "b"),
     Edge (UserNode "b", Pop "y", UserNode "c")]

pushPopTestInit2 :: TestGraph
pushPopTestInit2 = graphFromEdges pushPopTestSetInit2

pushPopTest2 :: TestTree
pushPopTest2 = testCase "Testing push + pop (non-matching stack element)"
  (assertEqual "Should not have a nop edge" pushPopTestRes2 (graphClosure pushPopTestInit2))

-- Third Test: Push + Nop
pushNopTestSet :: S.Set TestEdge
pushNopTestSet =
  S.fromList
    [Edge (UserNode "a", Push "x", UserNode "b"),
     Edge (UserNode "b", Nop, UserNode "c"),
     Edge (UserNode "a", Push "x", UserNode "c")]

pushNopTestRes :: TestGraph
pushNopTestRes = graphFromEdges pushNopTestSet

pushNopTestSetInit :: S.Set TestEdge
pushNopTestSetInit =
  S.fromList
    [Edge (UserNode "a", Push "x", UserNode "b"),
     Edge (UserNode "b", Nop, UserNode "c")]

pushNopTestInit :: TestGraph
pushNopTestInit = graphFromEdges pushNopTestSetInit

pushNopTest :: TestTree
pushNopTest = testCase "Testing push + nop"
  (assertEqual "Should have form a nop edge" pushNopTestRes (graphClosure pushNopTestInit))

-- Third Test: Pop + Nop
popNopTestSet :: S.Set TestEdge
popNopTestSet =
  S.fromList
    [Edge (UserNode "a", Pop "x", UserNode "b"),
     Edge (UserNode "b", Nop, UserNode "c")]

popNopTestRes :: TestGraph
popNopTestRes = graphFromEdges popNopTestSet

popNopTestSetInit :: S.Set TestEdge
popNopTestSetInit =
  S.fromList
    [Edge (UserNode "a", Pop "x", UserNode "b"),
     Edge (UserNode "b", Nop, UserNode "c")]

popNopTestInit :: TestGraph
popNopTestInit = graphFromEdges popNopTestSetInit

popNopTest :: TestTree
popNopTest = testCase "Testing pop + nop"
  (assertEqual "Should not have new edges" popNopTestRes (graphClosure popNopTestInit))

-- Fourth Test: Nop + Nop
nopNopTestSet :: S.Set TestEdge
nopNopTestSet =
  S.fromList
    [Edge (UserNode "a", Nop, UserNode "b"),
     Edge (UserNode "b", Nop, UserNode "c"),
     Edge (UserNode "a", Nop, UserNode "c")]

nopNopTestRes :: TestGraph
nopNopTestRes = graphFromEdges nopNopTestSet

nopNopTestSetInit :: S.Set TestEdge
nopNopTestSetInit =
  S.fromList
    [Edge (UserNode "a", Nop, UserNode "b"),
     Edge (UserNode "b", Nop, UserNode "c")]

nopNopTestInit :: TestGraph
nopNopTestInit = graphFromEdges nopNopTestSetInit

nopNopTest :: TestTree
nopNopTest = testCase "Testing nop + nop"
  (assertEqual "Should have a new edge" nopNopTestRes (graphClosure nopNopTestInit))

-- Fifth Test: Complex 1
biggerTestSet1 :: S.Set TestEdge
biggerTestSet1 =
  S.fromList
    [Edge (UserNode "a", Push "x", UserNode "b"),
     Edge (UserNode "b", Pop "y", UserNode "c"),
     Edge (UserNode "b", Nop, UserNode "c"),
     Edge (UserNode "c", Nop, UserNode "d"),
     Edge (UserNode "a", Push "x", UserNode "c"),
     Edge (UserNode "b", Nop, UserNode "d"),
     Edge (UserNode "a", Push "x", UserNode "d")]

biggerTestRes1 :: TestGraph
biggerTestRes1 = graphFromEdges biggerTestSet1

biggerTestSetInit1 :: S.Set TestEdge
biggerTestSetInit1 =
  S.fromList
    [Edge (UserNode "a", Push "x", UserNode "b"),
     Edge (UserNode "b", Pop "y", UserNode "c"),
     Edge (UserNode "b", Nop, UserNode "c"),
     Edge (UserNode "c", Nop, UserNode "d")]

biggerTestInit1 :: TestGraph
biggerTestInit1 = graphFromEdges biggerTestSetInit1

biggerTest1 :: TestTree
biggerTest1 = testCase "Testing bigger test case"
  (assertEqual "Should have multiple new edges" biggerTestRes1 (graphClosure biggerTestInit1))


-- Sixth Test: DynamicPop 1
dynPopTestSet1 :: S.Set TestEdge
dynPopTestSet1 =
  S.fromList
    [Edge (UserNode "a", Push "NULLA", UserNode "b"),
     Edge (UserNode "b", DynamicPop DynPopFun1, UserNode "c"),
     Edge (UserNode "a", Push "II",
            IntermediateNode ([Push "IV", Push "VI", Push "NULLA", Push "I"], UserNode "c")),
     Edge (IntermediateNode ([Push "IV", Push "VI", Push "NULLA", Push "I"], UserNode "c"),
            Push "IV", IntermediateNode ([Push "VI", Push "NULLA", Push "I"], UserNode "c")),
     Edge (IntermediateNode ([Push "VI", Push "NULLA", Push "I"], UserNode "c"),
            Push "VI", IntermediateNode ([Push "NULLA", Push "I"], UserNode "c")),
     Edge (IntermediateNode ([Push "NULLA", Push "I"], UserNode "c"),
            Push "NULLA", IntermediateNode ([Push "I"], UserNode "c")),
     Edge (IntermediateNode ([Push "I"], UserNode "c"), Push "I", UserNode "c")
    ]

dynPopTestRes1 :: TestGraph
dynPopTestRes1 = graphFromEdges dynPopTestSet1

dynPopTestSetInit1 :: S.Set TestEdge
dynPopTestSetInit1 =
  S.fromList
    [Edge (UserNode "a", Push "NULLA", UserNode "b"),
     Edge (UserNode "b", DynamicPop DynPopFun1, UserNode "c")]

dynPopTestInit1 :: TestGraph
dynPopTestInit1 = graphFromEdges dynPopTestSetInit1

dynPopTest1 :: TestTree
dynPopTest1 = testCase "Testing push + dynpop"
  (assertEqual "Should have many new edges" dynPopTestRes1 (graphClosure dynPopTestInit1))

-- Seventh Test: DynamicPop 2
dynPopTestSet2 :: S.Set TestEdge
dynPopTestSet2 =
  S.fromList
    [Edge (UserNode "a", Push "5", UserNode "b"),
     Edge (UserNode "b", DynamicPop DynPopFun2, UserNode "c"),
     Edge (UserNode "c", Pop "1", UserNode "d"),
     Edge (UserNode "a", Push "1", IntermediateNode ([Push "1", Push "1"], UserNode "c")),
     Edge (IntermediateNode ([Push "1", Push "1"], UserNode "c"), Push "1", IntermediateNode ([Push "1"], UserNode "c")),
     Edge (IntermediateNode ([Push "1"], UserNode "c"), Push "1", UserNode "c"),
     Edge (IntermediateNode ([Push "1"], UserNode "c"), Nop, UserNode "d"),
     Edge (IntermediateNode ([Push "1", Push "1"], UserNode "c"), Push "1", UserNode "d")
    ]

dynPopTestRes2 :: TestGraph
dynPopTestRes2 = graphFromEdges dynPopTestSet2

dynPopTestSetInit2 :: S.Set TestEdge
dynPopTestSetInit2 =
  S.fromList
    [Edge (UserNode "a", Push "5", UserNode "b"),
     Edge (UserNode "b", DynamicPop DynPopFun2, UserNode "c"),
     Edge (UserNode "c", Pop "1", UserNode "d")]

dynPopTestInit2 :: TestGraph
dynPopTestInit2 = graphFromEdges dynPopTestSetInit2

dynPopTest2 :: TestTree
dynPopTest2 = testCase "Testing push + dynpop (2)"
  (assertEqual "Should have many new edges" dynPopTestRes2 (graphClosure dynPopTestInit2))
