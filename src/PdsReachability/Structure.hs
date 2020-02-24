{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}

module PdsReachability.Structure
(
  StackAction(..),
  Edge(..),
  Node(..),
  Graph,
  emptyGraph,
  graphFromEdges,
  addEdge,
  getEdges,
  findPopEdgesBySourceAndElement,
  findNopEdgesBySource,
  findNopEdgesByDest,
  findPushEdgesByDestAndElement,
  findPushEdgesByDest,
  findDynPopEdgesBySource
) where

import AST.Ast
import Data.Function
import qualified Data.Set as S
import qualified Data.Map as M

data Graph nt element dynPopFun where
   Graph :: (Ord nt, Ord element, Ord dynPopFun, Eq nt, Eq element, Eq dynPopFun) =>
            { -- A dictionary stroing all the edges in the graph
              allEdges :: S.Set (Edge nt element dynPopFun),
              -- A dictionary storing pop edges, key - edge src and pop element, val - edge dest)
              popEdgesBySourceAndElement :: M.Map (Node nt element dynPopFun, element) (S.Set (Node nt element dynPopFun)),
              -- A dictionary storing nop edges, key - edge src, val - edge dest)
              nopEdgesBySource :: M.Map (Node nt element dynPopFun) (S.Set (Node nt element dynPopFun)),
              -- A dictionary string nop edges, key - edge dest, val - edge src
              nopEdgesByDest :: M.Map (Node nt element dynPopFun) (S.Set (Node nt element dynPopFun)),
              -- A dictionary string push edges, key - (edge dest, push element), val - edge src
              pushEdgesByDestAndElement :: M.Map ((Node nt element dynPopFun), element) (S.Set (Node nt element dynPopFun)),
              -- A dictionary string push edges, key - edge dest, val - (edge src, push element)
              pushEdgesByDest :: M.Map (Node nt element dynPopFun) (S.Set ((Node nt element dynPopFun), element)),
              -- A dictionary string dynamic pop edges, key - edge src, val - (edge dest, dynamic action)
              dynPopEdgesBySource :: M.Map (Node nt element dynPopFun) (S.Set ((Node nt element dynPopFun), dynPopFun))
            } -> Graph nt element dynPopFun
deriving instance (Show nt, Show element, Show dynPopFun) => (Show (Graph nt element dynPopFun))
deriving instance (Eq (Graph nt element dynPopFun))
deriving instance (Ord (Graph nt element dynPopFun))

data Node nt element dynPopFun
  = UserNode nt
  | IntermediateNode [StackAction element dynPopFun] (Node nt element dynPopFun) deriving (Show, Eq, Ord)

data Edge nt element dynPopFun
  = Edge (Node nt element dynPopFun) (StackAction element dynPopFun) (Node nt element dynPopFun) deriving (Show, Eq, Ord)

data StackAction element dynPopFun
  = Push element
  | Pop element
  | DynamicPop dynPopFun
  | Nop deriving (Show, Eq, Ord)

-- This function unpacks the GADT so that the functions required by the
-- constraints are exposed
withGraph ::
  Graph nt element dynPopFun ->
  ((Eq nt, Eq element, Eq dynPopFun, Ord nt, Ord element, Ord dynPopFun) => () -> a) ->
  a
withGraph g f =
  case g of
    Graph {} -> f ()

emptyGraph ::
  (Ord nt, Ord element, Ord dynPopFun, Eq nt, Eq element, Eq dynPopFun) =>
  Graph nt element dynPopFun
emptyGraph
  = Graph { allEdges = S.empty,
            popEdgesBySourceAndElement = M.empty,
            nopEdgesBySource = M.empty,
            nopEdgesByDest = M.empty,
            pushEdgesByDestAndElement = M.empty,
            pushEdgesByDest = M.empty,
            dynPopEdgesBySource = M.empty
          }

graphFromEdges :: (Ord nt, Ord element, Ord dynPopFun) =>
  S.Set (Edge nt element dynPopFun) -> Graph nt element dynPopFun
graphFromEdges edgeSet =
  S.foldl (\acc -> \e -> addEdge e acc) emptyGraph edgeSet

alterMap :: (Ord k, Ord v) =>
  M.Map k (S.Set v) -> (k, v) ->  M.Map k (S.Set v)
alterMap m (k, v) =
  if (M.member k m)
    then M.adjust (\s -> S.insert v s) k m
    else M.insert k (S.singleton v) m

addEdge ::
  Edge nt element dynPopFun ->
  Graph nt element dynPopFun ->
  Graph nt element dynPopFun
addEdge (e@(Edge n1 sa n2)) g =
  withGraph g $ \() ->
  let newEdges = S.insert e (allEdges g) in
  case sa of
    Push se ->
      let ogMap = pushEdgesByDestAndElement g in
      let newMap = alterMap ogMap ((n2, se), n1) in
      let ogMap' = pushEdgesByDest g in
      let newMap' = alterMap ogMap' (n2, (n1, se)) in
      let newGraph = g { allEdges = newEdges,
                         pushEdgesByDestAndElement = newMap,
                         pushEdgesByDest = newMap' }
      in
      newGraph
    Pop se ->
      let ogMap = popEdgesBySourceAndElement g in
      let newMap = alterMap ogMap ((n1, se), n2) in
      let newGraph = g { allEdges = newEdges,
                         popEdgesBySourceAndElement = newMap }
      in
      newGraph
    Nop ->
      let ogMap = nopEdgesBySource g in
      let newMap = alterMap ogMap (n1, n2) in
      let ogMap' = nopEdgesByDest g in
      let newMap' = alterMap ogMap' (n2, n1) in
      let newGraph = g { allEdges = newEdges,
                         nopEdgesBySource = newMap,
                         nopEdgesByDest = newMap' }
      in
      newGraph
    DynamicPop f ->
      let ogMap = dynPopEdgesBySource g in
      let newMap = alterMap ogMap (n1, (n2, f)) in
      let newGraph = g { allEdges = newEdges,
                         dynPopEdgesBySource = newMap }
      in
      newGraph


getEdges :: Graph nt element dynPopFun -> S.Set (Edge nt element dynPopFun)
getEdges g =
  allEdges g

findPopEdgesBySourceAndElement ::
  (Node nt element dynPopFun, element) -> Graph nt element dynPopFun -> S.Set (Node nt element dynPopFun)
findPopEdgesBySourceAndElement (n, e) g =
  withGraph g $ \() ->
  let entry = M.lookup (n, e) (popEdgesBySourceAndElement g) in
  case entry of
    Just s -> s
    Nothing -> S.empty

findNopEdgesBySource ::
  (Node nt element dynPopFun) -> Graph nt element dynPopFun -> S.Set (Node nt element dynPopFun)
findNopEdgesBySource n g =
  withGraph g $ \() ->
  let entry = M.lookup n (nopEdgesBySource g) in
  case entry of
    Just s -> s
    Nothing -> S.empty

findNopEdgesByDest ::
  (Node nt element dynPopFun) -> Graph nt element dynPopFun -> S.Set (Node nt element dynPopFun)
findNopEdgesByDest n g =
  withGraph g $ \() ->
  let entry = M.lookup n (nopEdgesByDest g) in
  case entry of
    Just s -> s
    Nothing -> S.empty

findPushEdgesByDestAndElement ::
  (Node nt element dynPopFun, element) -> Graph nt element dynPopFun -> S.Set (Node nt element dynPopFun)
findPushEdgesByDestAndElement (n, e) g =
  withGraph g $ \() ->
  let entry = M.lookup (n, e) (pushEdgesByDestAndElement g) in
  case entry of
    Just s -> s
    Nothing -> S.empty

findPushEdgesByDest ::
  (Node nt element dynPopFun) -> Graph nt element dynPopFun -> S.Set (Node nt element dynPopFun, element)
findPushEdgesByDest n g =
  withGraph g $ \() ->
  let entry = M.lookup n (pushEdgesByDest g) in
  case entry of
    Just s -> s
    Nothing -> S.empty

findDynPopEdgesBySource ::
  (Node nt element dynPopFun) -> Graph nt element dynPopFun -> S.Set (Node nt element dynPopFun, dynPopFun)
findDynPopEdgesBySource n g =
  withGraph g $ \() ->
  let entry = M.lookup n (dynPopEdgesBySource g) in
  case entry of
    Just s -> s
    Nothing -> S.empty
