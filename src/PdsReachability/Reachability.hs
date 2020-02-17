{-# LANGUAGE ScopedTypeVariables #-}

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

newtype Analysis node element = Analysis (Graph node element, WorkQueue node element)

getGraph :: Analysis node element -> Graph node element
getGraph (Analysis (g, _)) = g

getWorkQueue :: Analysis node element -> WorkQueue node element
getWorkQueue (Analysis (_, wq)) = wq

-- checkEdgePair :: Edge -> Edge -> Maybe Edge
-- checkEdgePair (Edge (s1, a1, t1)) (Edge (s2, a2, t2)) =
--   if (t1 == s2) then
--     case a1 of
--       Push sa1 ->
--         case a2 of
--           Pop sa2 ->
--             if (sa1 == sa2)
--               then Just $ Edge (s1, Nop, t2)
--               else Nothing
--           Nop ->
--             Just $ Edge (s1, a1, t2)
--           otherwise -> Nothing
--       Nop ->
--         case a2 of
--           Nop -> Just $ Edge (s1, Nop, s2)
--           otherwise -> Nothing
--       otherwise -> Nothing
--   else Nothing
--
-- addEdge :: Graph -> Edge -> WorkQueue -> (WorkQueue, Graph)
-- addEdge (Graph g) e q =
--   let foldFun =
--           \acc -> \elm ->
--           let mbe1 = checkEdgePair e elm in
--           let mbe2 = checkEdgePair elm e in
--           let acc' = if MB.isJust mbe1 then Q.pushBack acc (MB.fromJust mbe1) else acc
--           in
--           if MB.isJust mbe2 then Q.pushBack acc' (MB.fromJust mbe2) else acc'
--   in
--   let q' = S.foldl foldFun q g in
--   (q', Graph (S.insert e g))

closureStep :: (Ord node, Ord element) => Analysis node element -> Analysis node element
closureStep analysis =
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

fullClosure :: (Ord node, Ord element) => Analysis node element -> Analysis node element
fullClosure analysis =
  let analysis' = closureStep analysis in
  let wq' = getWorkQueue analysis' in
  if (null wq') then analysis' else fullClosure analysis'

graphClosure :: (Ord node, Ord element) => Graph node element -> Graph node element
graphClosure g =
  let g' = emptyGraph in
  let initWorkQ = Q.fromList $ S.toList $ getEdges g in
  let res = fullClosure $ Analysis (g', initWorkQ) in
  getGraph res

-- graphClosure :: Graph -> Graph
-- graphClosure (Graph g) =
--   let g' = Graph S.empty in
--   let initWorkQ = Q.fromList $ S.toList g in
--   let (res, _) = fullClosure g' initWorkQ in
--   res
