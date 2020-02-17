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

type WorkQueue nt element dynPopFun = Q.BankersDequeue (Edge nt element dynPopFun)

data Analysis nt element dynPopFun where
   Analysis :: (Ord nt, Ord element, Ord dynPopFun, Eq nt, Eq element, Eq dynPopFun) =>
    (Graph nt element dynPopFun, WorkQueue nt element dynPopFun) -> Analysis nt element dynPopFun
deriving instance (Show nt, Show element, Show dynPopFun) => (Show (Analysis nt element dynPopFun))

-- This function unpacks the GADT so that the functions required by the
-- constraints are exposed
withAnalysis ::
  Analysis nt element dynPopFun ->
  ((Eq nt, Eq element, Eq dynPopFun, Ord nt, Ord element, Ord dynPopFun) => () -> a) ->
  a
withAnalysis g f =
  case g of
    Analysis _ -> f ()

-- TODO: assume the dynamicalPopActions function exist
emptyAnalysis :: (Ord nt, Ord element, Ord dynPopFun) => Analysis nt element dynPopFun
emptyAnalysis =
  Analysis (emptyGraph, Q.empty)

getGraph :: Analysis nt element dynPopFun -> Graph nt element dynPopFun
getGraph (Analysis (g, _)) = g

getWorkQueue :: Analysis nt element dynPopFun -> WorkQueue nt element dynPopFun
getWorkQueue (Analysis (_, wq)) = wq

closureStep :: Analysis nt element dynPopFun -> Analysis nt element dynPopFun
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

fullClosure :: Analysis nt element dynPopFun -> Analysis nt element dynPopFun
fullClosure analysis =
  withAnalysis analysis $ \() ->
  let analysis' = closureStep analysis in
  let wq' = getWorkQueue analysis' in
  if (null wq') then analysis' else fullClosure analysis'

updateAnalysis :: Edge nt element dynPopFun -> Analysis nt element dynPopFun -> Analysis nt element dynPopFun
updateAnalysis e (analysis) =
  withAnalysis analysis $ \() ->
  let g' = addEdge e (getGraph analysis) in
  Analysis (g', getWorkQueue analysis)
