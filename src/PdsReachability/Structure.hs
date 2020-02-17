{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}

module PdsReachability.Structure
(
  StackAction(..),
  Edge(..),
  Graph,
  emptyGraph,
  graphFromEdges,
  addEdge,
  getEdges,
  findPopEdgesBySourceAndElement,
  findNopEdgesBySource,
  findNopEdgesByDest,
  findPushEdgesByDestAndElement,
  findPushEdgesByDest
) where

import AST.Ast
import Data.Function
import qualified Data.Set as S
import qualified Data.Map as M

data Graph node element where
   Graph :: (Ord node, Ord element, Eq node, Eq element) =>
            { -- A dictionary stroing all the edges in the graph
              allEdges :: S.Set (Edge node element),
              -- A dictionary storing pop edges, key - edge src and pop element, val - edge dest)
              popEdgesBySourceAndElement :: M.Map (node, element) (S.Set node),
              -- A dictionary storing nop edges, key - edge src, val - edge dest)
              nopEdgesBySource :: M.Map node (S.Set node),
              -- A dictionary string nop edges, key - edge dest, val - edge src
              nopEdgesByDest :: M.Map node (S.Set node),
              -- A dictionary string push edges, key - (edge dest, push element), val - edge src
              pushEdgesByDestAndElement :: M.Map (node, element) (S.Set node),
              -- A dictionary string push edges, key - edge dest, val - (edge src, push element)
              pushEdgesByDest :: M.Map node (S.Set (node, element))
            } -> Graph node element
deriving instance (Show node, Show element) => (Show (Graph node element))
deriving instance (Eq (Graph node element))
deriving instance (Ord (Graph node element))

data Edge node element
  = Edge (node, StackAction element, node) deriving (Show, Eq, Ord)

data StackAction element
  = Push element
  | Pop element
  -- | DynamicPop 
  | Nop deriving (Show, Eq, Ord)

-- This function unpacks the GADT so that the functions required by the
-- constraints are exposed
withGraph ::
  Graph node element ->
  ((Eq node, Eq element, Ord node, Ord element) => () -> a) ->
  a
withGraph g f =
  case g of
    Graph {} -> f ()

emptyGraph ::
  (Ord node, Ord element, Eq node, Eq element) =>
  Graph node element
emptyGraph
  = Graph { allEdges = S.empty,
            popEdgesBySourceAndElement = M.empty,
            nopEdgesBySource = M.empty,
            nopEdgesByDest = M.empty,
            pushEdgesByDestAndElement = M.empty,
            pushEdgesByDest = M.empty }

graphFromEdges :: (Ord node, Ord element) =>
  S.Set (Edge node element) -> Graph node element
graphFromEdges edgeSet =
  S.foldl (\acc -> \e -> addEdge e acc) emptyGraph edgeSet

alterMap :: (Ord k, Ord v) =>
  M.Map k (S.Set v) -> (k, v) ->  M.Map k (S.Set v)
alterMap m (k, v) =
  if (M.member k m)
    then M.adjust (\s -> S.insert v s) k m
    else M.insert k (S.singleton v) m

addEdge ::
  Edge node element ->
  Graph node element ->
  Graph node element
addEdge (e@(Edge (n1, sa, n2))) g =
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

getEdges :: Graph node element -> S.Set (Edge node element)
getEdges g =
  allEdges g

findPopEdgesBySourceAndElement ::
  (node, element) -> Graph node element -> S.Set node
findPopEdgesBySourceAndElement (n, e) g =
  withGraph g $ \() ->
  let entry = M.lookup (n, e) (popEdgesBySourceAndElement g) in
  case entry of
    Just s -> s
    Nothing -> S.empty

findNopEdgesBySource ::
  node -> Graph node element -> S.Set node
findNopEdgesBySource n g =
  withGraph g $ \() ->
  let entry = M.lookup n (nopEdgesBySource g) in
  case entry of
    Just s -> s
    Nothing -> S.empty

findNopEdgesByDest ::
  node -> Graph node element -> S.Set node
findNopEdgesByDest n g =
  withGraph g $ \() ->
  let entry = M.lookup n (nopEdgesByDest g) in
  case entry of
    Just s -> s
    Nothing -> S.empty

findPushEdgesByDestAndElement ::
  (node, element) -> Graph node element -> S.Set node
findPushEdgesByDestAndElement (n, e) g =
  withGraph g $ \() ->
  let entry = M.lookup (n, e) (pushEdgesByDestAndElement g) in
  case entry of
    Just s -> s
    Nothing -> S.empty

findPushEdgesByDest ::
  node -> Graph node element -> S.Set (node, element)
findPushEdgesByDest n g =
  withGraph g $ \() ->
  let entry = M.lookup n (pushEdgesByDest g) in
  case entry of
    Just s -> s
    Nothing -> S.empty
