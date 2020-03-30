{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}

module PdsReachability.Structure
(
  StackAction(..),
  Edge(..),
  InternalNode(..),
  Graph,
  GeneralEdges(..),
  Terminus(..),
  UntargetedDynPopEdge(..),
  emptyGraph,
  addEdge,
  addUntargetedDynPopEdge,
  getEdges,
  getUntargetedDynPopEdges,
  findPopEdgesBySourceAndElement,
  findNopEdgesBySource,
  findNopEdgesByDest,
  findPushEdgesByDestAndElement,
  findPushEdgesByDest,
  findPushEdgesBySource,
  findTargetedDynPopEdgesBySource,
  findUntargetedDynPopEdgesBySource
) where

import AST.Ast
import Data.Function
import PdsReachability.Specification
import qualified Data.Set as S
import qualified Data.Map as M

-- NOTE: Terminus: InternalNode and UntargetedDynPop

data Graph a =
   Graph
      { -- A dictionary stroing all the edges in the graph
        allEdges :: S.Set (Edge a),
        -- A dictionary stroing all the untargeted pop edges in the graph
        allUntargetedDynPopEdges :: S.Set (UntargetedDynPopEdge a),
        -- A dictionary storing pop edges, key - edge src and pop element, val - edge dest)
        popEdgesBySourceAndElement :: M.Map (InternalNode a, Element a) (S.Set (InternalNode a)),
        -- A dictionary storing nop edges, key - edge src, val - edge dest)
        nopEdgesBySource :: M.Map (InternalNode a) (S.Set (InternalNode a)),
        -- A dictionary storing nop edges, key - edge dest, val - edge src
        nopEdgesByDest :: M.Map (InternalNode a) (S.Set (InternalNode a)),
        -- A dictionary storing push edges, key - (edge dest, push element), val - edge src
        pushEdgesByDestAndElement :: M.Map ((InternalNode a), Element a) (S.Set (InternalNode a)),
        -- A dictionary storing push edges, key - edge dest, val - (edge src, push element)
        pushEdgesByDest :: M.Map (InternalNode a) (S.Set ((InternalNode a), Element a)),
        -- A dictionary storing push edges, key - edge src, val - (edge dest, push element)
        pushEdgesBySource :: M.Map (InternalNode a) (S.Set ((InternalNode a), Element a)),
        -- A dictionary storing dynamic(UntargetedDynPop a) pop edges, key - edge src, val - (edge dest, dynamic action)
        dynPopEdgesBySource :: M.Map (InternalNode a) (S.Set ((InternalNode a), TargetedDynPop a)),
        -- A dictionary storing untargeted pop edges, key - edge src, val - Untargeted Pop action
        untargetedDynPopBySrc :: M.Map (InternalNode a) (S.Set (UntargetedDynPop a))
      }
deriving instance (SpecIs Eq a) => Eq (Graph a)
deriving instance (SpecIs Ord a) => Ord (Graph a)
deriving instance (SpecIs Show a) => Show (Graph a)

data InternalNode a
  = UserNode (Node a)
  | IntermediateNode [StackAction a] (Terminus a)
deriving instance (SpecIs Eq a) => (Eq (InternalNode a))
deriving instance (SpecIs Ord a) => (Ord (InternalNode a))
deriving instance (SpecIs Show a) => (Show (InternalNode a))

data Edge a
  = Edge (InternalNode a) (StackAction a) (InternalNode a)
deriving instance (SpecIs Eq a) => (Eq (Edge a))
deriving instance (SpecIs Ord a) => (Ord (Edge a))
deriving instance (SpecIs Show a) => (Show (Edge a))

data UntargetedDynPopEdge a
  = UntargetedDynPopEdge (InternalNode a) (UntargetedDynPop a)
deriving instance (SpecIs Eq a) => (Eq (UntargetedDynPopEdge a))
deriving instance (SpecIs Ord a) => (Ord (UntargetedDynPopEdge a))
deriving instance (SpecIs Show a) => (Show (UntargetedDynPopEdge a))

data Terminus a
  = StaticTerminus (InternalNode a)
  | DynamicTerminus (UntargetedDynPop a)
deriving instance (SpecIs Eq a) => (Eq (Terminus a))
deriving instance (SpecIs Ord a) => (Ord (Terminus a))
deriving instance (SpecIs Show a) => (Show (Terminus a))

data GeneralEdges a
  = RegularEdge (Edge a)
  | UntargetedEdge (UntargetedDynPopEdge a)
deriving instance (SpecIs Eq a) => (Eq (GeneralEdges a))
deriving instance (SpecIs Ord a) => (Ord (GeneralEdges a))
deriving instance (SpecIs Show a) => (Show (GeneralEdges a))

data StackAction a
  = Push (Element a)
  | Pop (Element a)
  | DynamicPop (TargetedDynPop a)
  | Nop
deriving instance (TargetedSpecIs Eq a) => (Eq (StackAction a))
deriving instance (TargetedSpecIs Ord a) => (Ord (StackAction a))
deriving instance (TargetedSpecIs Show a) => (Show (StackAction a))

emptyGraph :: Graph a
emptyGraph
  = Graph { allEdges = S.empty,
            allUntargetedDynPopEdges = S.empty,
            popEdgesBySourceAndElement = M.empty,
            nopEdgesBySource = M.empty,
            nopEdgesByDest = M.empty,
            pushEdgesByDestAndElement = M.empty,
            pushEdgesByDest = M.empty,
            pushEdgesBySource = M.empty,
            dynPopEdgesBySource = M.empty,
            untargetedDynPopBySrc = M.empty
          }

-- graphFromEdges :: (SpecIs Ord a) => S.Set (Edge a) -> Graph a
-- graphFromEdges edgeSet =
--   S.foldl (\acc -> \e -> addEdge e acc) emptyGraph edgeSet

alterMap :: (Ord k, Ord v) => M.Map k (S.Set v) -> (k, v) ->  M.Map k (S.Set v)
alterMap m (k, v) =
  if (M.member k m)
    then M.adjust (\s -> S.insert v s) k m
    else M.insert k (S.singleton v) m

addEdge :: (Spec a) => Edge a -> Graph a -> Graph a
addEdge (e@(Edge n1 sa n2)) g =
  let newEdges = S.insert e (allEdges g) in
  case sa of
    Push se ->
      let ogMap = pushEdgesByDestAndElement g in
      let newMap = alterMap ogMap ((n2, se), n1) in
      let ogMap' = pushEdgesByDest g in
      let newMap' = alterMap ogMap' (n2, (n1, se)) in
      let ogMap'' = pushEdgesBySource g in
      let newMap'' = alterMap ogMap'' (n1, (n2, se)) in
      let newGraph = g { allEdges = newEdges,
                         pushEdgesByDestAndElement = newMap,
                         pushEdgesByDest = newMap',
                         pushEdgesBySource = newMap'' }
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

addUntargetedDynPopEdge ::
  (Spec a) => UntargetedDynPopEdge a -> Graph a -> Graph a
addUntargetedDynPopEdge (upe@(UntargetedDynPopEdge n upa)) g =
  let newEdges = S.insert upe (allUntargetedDynPopEdges g) in
  let ogMap = untargetedDynPopBySrc g in
  let newMap = alterMap ogMap (n, upa) in
  let newGraph = g { allUntargetedDynPopEdges = newEdges,
                     untargetedDynPopBySrc = newMap }
  in
  newGraph

getEdges :: Graph a -> S.Set (Edge a)
getEdges g =
  allEdges g

getUntargetedDynPopEdges :: Graph a -> S.Set (UntargetedDynPopEdge a)
getUntargetedDynPopEdges g =
  allUntargetedDynPopEdges g

findPopEdgesBySourceAndElement ::
  (SpecIs Ord a) =>
  (InternalNode a, Element a) -> Graph a -> S.Set (InternalNode a)
findPopEdgesBySourceAndElement (n, e) g =
  let entry = M.lookup (n, e) (popEdgesBySourceAndElement g) in
  case entry of
    Just s -> s
    Nothing -> S.empty

findNopEdgesBySource ::
  (SpecIs Ord a) =>
  (InternalNode a) -> Graph a -> S.Set (InternalNode a)
findNopEdgesBySource n g =
  let entry = M.lookup n (nopEdgesBySource g) in
  case entry of
    Just s -> s
    Nothing -> S.empty

findNopEdgesByDest ::
  (SpecIs Ord a) =>
  (InternalNode a) -> Graph a -> S.Set (InternalNode a)
findNopEdgesByDest n g =
  let entry = M.lookup n (nopEdgesByDest g) in
  case entry of
    Just s -> s
    Nothing -> S.empty

findPushEdgesByDestAndElement ::
  (SpecIs Ord a) =>
  (InternalNode a, Element a) -> Graph a -> S.Set (InternalNode a)
findPushEdgesByDestAndElement (n, e) g =
  let entry = M.lookup (n, e) (pushEdgesByDestAndElement g) in
  case entry of
    Just s -> s
    Nothing -> S.empty

findPushEdgesByDest ::
  (SpecIs Ord a) =>
  (InternalNode a) -> Graph a -> S.Set (InternalNode a, Element a)
findPushEdgesByDest n g =
  let entry = M.lookup n (pushEdgesByDest g) in
  case entry of
    Just s -> s
    Nothing -> S.empty

findPushEdgesBySource ::
  (SpecIs Ord a) =>
  (InternalNode a) -> Graph a -> S.Set (InternalNode a, Element a)
findPushEdgesBySource n g =
  let entry = M.lookup n (pushEdgesBySource g) in
  case entry of
    Just s -> s
    Nothing -> S.empty

findTargetedDynPopEdgesBySource ::
  (SpecIs Ord a) =>
  (InternalNode a) -> Graph a -> S.Set (InternalNode a, TargetedDynPop a)
findTargetedDynPopEdgesBySource n g =
  let entry = M.lookup n (dynPopEdgesBySource g) in
  case entry of
    Just s -> s
    Nothing -> S.empty

findUntargetedDynPopEdgesBySource ::
  (SpecIs Ord a) =>
  (InternalNode a) -> Graph a -> S.Set (UntargetedDynPop a)
findUntargetedDynPopEdgesBySource n g =
  let entry = M.lookup n (untargetedDynPopBySrc g) in
  case entry of
    Just s -> s
    Nothing -> S.empty
