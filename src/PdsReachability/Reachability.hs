{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
module PdsReachability.Reachability where

import AST.Ast
import Data.Function
import PdsReachability.Structure
import qualified Data.Either as E
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Maybe as MB
import qualified Data.Dequeue as Q

type WorkQueue node element = Q.BankersDequeue (Edge node element)

data Analysis node element where
   Analysis :: (Ord node, Ord element, Eq node, Eq element) =>
    (Graph node element, WorkQueue node element) -> Analysis node element
deriving instance (Show node, Show element) => (Show (Analysis node element))

-- This function unpacks the GADT so that the functions required by the
-- constraints are exposed
withAnalysis ::
  Analysis node element ->
  ((Eq node, Eq element, Ord node, Ord element) => () -> a) ->
  a
withAnalysis g f =
  case g of
    Analysis _ -> f ()

emptyAnalysis :: (Ord node, Ord element) => Analysis node element
emptyAnalysis =
  Analysis (emptyGraph, Q.empty)

getGraph :: Analysis node element -> Graph node element
getGraph (Analysis (g, _)) = g

getWorkQueue :: Analysis node element -> WorkQueue node element
getWorkQueue (Analysis (_, wq)) = wq

closureStep :: Analysis node element -> Analysis node element
closureStep analysis =
  withAnalysis analysis $ \() ->
  let wq = getWorkQueue analysis in
  if (null wq) then analysis
    else
      let g = getGraph analysis in
      let (e@(Edge (n1, sa, n2)), wq') = MB.fromJust (Q.popFront wq) in
      let g' = addEdge e g in
            case sa of
              Push se ->
                let popDests = findPopEdgesBySourceAndElement (n2, se) g in
                let nopDests = findNopEdgesBySource n2 g in
                let wq'' = S.foldl (\acc -> \dest -> Q.pushBack acc (Edge (n1, Nop, dest))) wq' popDests in
                let finalWq = S.foldl (\acc -> \dest -> Q.pushBack acc (Edge (n1, sa, dest))) wq'' nopDests in
                Analysis (g', finalWq)
              Pop se ->
                let pushSrcs = findPushEdgesByDestAndElement (n1, se) g in
                let finalWq = S.foldl (\acc -> \src -> Q.pushBack acc (Edge (src, Nop, n2))) wq' pushSrcs in
                Analysis (g', finalWq)
              Nop ->
                let nopDests = findNopEdgesBySource n2 g in
                let wq1 = S.foldl (\acc -> \dest -> Q.pushBack acc (Edge (n1, Nop, dest))) wq' nopDests in
                let nopSrcs = findNopEdgesByDest n1 g in
                let wq2 = S.foldl (\acc -> \src -> Q.pushBack acc (Edge (src, Nop, n2))) wq1 nopSrcs in
                let pushSrcsAndElms = findPushEdgesByDest n1 g in
                let finalWq = S.foldl (\acc -> \(src, elm) -> Q.pushBack acc (Edge (src, Push elm, n2))) wq2 pushSrcsAndElms in
                Analysis (g', finalWq)

fullClosure :: Analysis node element -> Analysis node element
fullClosure analysis =
  withAnalysis analysis $ \() ->
  let analysis' = closureStep analysis in
  let wq' = getWorkQueue analysis' in
  if (null wq') then analysis' else fullClosure analysis'

updateAnalysis :: Edge node element -> Analysis node element -> Analysis node element
updateAnalysis e (analysis) =
  withAnalysis analysis $ \() ->
  let g' = addEdge e (getGraph analysis) in
  Analysis (g', getWorkQueue analysis)
