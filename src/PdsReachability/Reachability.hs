{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
module PdsReachability.Reachability where

import AST.Ast
import Data.Function
import PdsReachability.Structure
import Utils.NondeterminismMonad as ND
import qualified Data.Either as E
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Maybe as MB
import qualified Data.Dequeue as Q

type WorkQueue nt element dynPopFun = Q.BankersDequeue (Edge nt element dynPopFun)

type Path element dynPopFun = [StackAction element dynPopFun]

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

pathToEdges ::
  Path element dynPopFun ->
  Node nt element dynPopFun ->
  Node nt element dynPopFun ->
  [Edge nt element dynPopFun]
pathToEdges path src dest =
  case path of
    [] -> [Edge (src, Nop, dest)]
    hd : [] -> [Edge (src, hd, dest)]
    hd : tl ->
      let loop lst acc prevSrc =
            case lst of
              hd' : [] -> acc ++ [Edge (prevSrc, hd', dest)]
              hd' : tl' ->
                let newImdNode = IntermediateNode (tl', dest) in
                let newAcc = acc ++ [Edge (prevSrc, hd', newImdNode)] in
                loop tl' newAcc newImdNode
      in
      let firstImdNode = IntermediateNode (tl, dest) in
      loop tl [Edge (src, hd, firstImdNode)] firstImdNode

closureStep ::
  (dynPopFun -> element -> [Path element dynPopFun]) ->
  Analysis nt element dynPopFun ->
  Analysis nt element dynPopFun
closureStep doDynPop analysis =
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
                let dynPopDests = findDynPopEdgesBySource n2 g in
                let wq1 = S.foldl (\acc -> \dest -> Q.pushBack acc (Edge (n1, Nop, dest))) wq' popDests in
                let wq2 = S.foldl (\acc -> \dest -> Q.pushBack acc (Edge (n1, sa, dest))) wq1 nopDests in
                let dynPopDestsMnd = pick $ S.toList $ dynPopDests in
                let rawEdgesLsts =
                      do
                        (dest, f) <- dynPopDestsMnd
                        let pathLst = doDynPop f se
                        singlePath <- ND.pick pathLst
                        return $ pathToEdges singlePath n1 dest
                in
                let newEdgesSet = S.fromList $ concat $ ND.toList rawEdgesLsts in
                let finalWq = S.foldl Q.pushBack wq2 newEdgesSet in
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
              DynamicPop f ->
                let pushSrcsAndElms = S.toList $ findPushEdgesByDest n1 g in
                let pushSrcsAndElmsMnd = ND.pick pushSrcsAndElms in
                let rawEdgesLsts =
                      do
                        (src, elm) <- pushSrcsAndElmsMnd
                        let pathLst = doDynPop f elm
                        singlePath <- ND.pick pathLst
                        return $ pathToEdges singlePath src n2
                in
                let newEdgesSet = S.fromList $ concat $ ND.toList rawEdgesLsts in
                let finalWq = S.foldl Q.pushBack wq' newEdgesSet in
                Analysis (g', finalWq)

fullClosure ::
  (dynPopFun -> element -> [Path element dynPopFun]) ->
  Analysis nt element dynPopFun ->
  Analysis nt element dynPopFun
fullClosure doDynPop analysis =
  withAnalysis analysis $ \() ->
  let analysis' = closureStep doDynPop analysis in
  let wq' = getWorkQueue analysis' in
  if (null wq') then analysis' else fullClosure doDynPop analysis'

performClosure ::
  (dynPopFun -> element -> [Path element dynPopFun]) ->
  Analysis nt element dynPopFun ->
  Analysis nt element dynPopFun
performClosure doDynPop analysis =
  withAnalysis analysis $ \() ->
  let initG = getGraph analysis in
  let initWorkQ = Q.fromList $ S.toList $ getEdges $ initG in
  fullClosure doDynPop $ Analysis (initG, initWorkQ)

updateAnalysis :: Edge nt element dynPopFun -> Analysis nt element dynPopFun -> Analysis nt element dynPopFun
updateAnalysis e (analysis) =
  withAnalysis analysis $ \() ->
  let g' = addEdge e (getGraph analysis) in
  Analysis (g', getWorkQueue analysis)
