{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
module PdsReachability.Reachability where

import AST.Ast
import Data.Function
import PdsReachability.Structure
import PdsReachability.Specification
import qualified Data.Either as E
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Maybe as MB
import qualified Data.Dequeue as Q

data WorkQueue a = WorkQueue (Q.BankersDequeue (Edge a))
deriving instance (SpecIs Show a) => (Show (WorkQueue a))

data Path a = Path [StackAction a]
deriving instance (SpecIs Show a) => (Show (Path a))

data History a = History (S.Set (Edge a))
deriving instance (SpecIs Show a) => (Show (History a))

data ActiveNodes a = ActiveNodes (S.Set (InternalNode a))
deriving instance (SpecIs Show a) => (Show (ActiveNodes a))

data EdgeFunction a = EdgeFunction (InternalNode a -> [(Path a, InternalNode a)])

data Waitlist a = Waitlist (M.Map (InternalNode a) (S.Set (Edge a)))

data Analysis a =
  Analysis
    { doDynPop :: (DynPop a -> Element a -> [Path a]),
      -- TODO: add the untargeted version of the doDynPop
      -- doTargetlessDynPop :: (targetlessDynPopFun -> element -> ([(Path, InternalNode a)]))
      graph :: Graph a,
      workQueue :: WorkQueue a,
      activeNodes :: ActiveNodes a,
      history :: History a,
      waitlist :: Waitlist a,
      edgeFunctions :: [EdgeFunction a]
    }

-- Cannot derive show for doDynPop so have to manually roll out this function
instance (SpecIs Show a) => Show (Analysis a) where
  show a = "Analysis Graph: " ++ show (graph a) ++ ";\n" ++
    "WorkQueue: " ++ show (workQueue a) ++ ";\n" ++
    "ActiveNodes: " ++ show (activeNodes a) ++ ";\n"

getGraph :: Analysis a -> Graph a
getGraph analysis = graph analysis

getWorkQueue :: Analysis a -> WorkQueue a
getWorkQueue analysis = workQueue analysis

getDynPop :: Analysis a -> (DynPop a -> Element a -> [Path a])
getDynPop analysis = doDynPop analysis

getActiveNodes :: Analysis a -> ActiveNodes a
getActiveNodes analysis = activeNodes analysis

getHistory :: Analysis a -> History a
getHistory analysis = history analysis

getWaitlist :: Analysis a -> Waitlist a
getWaitlist analysis = waitlist analysis

getEdgeFunctions :: Analysis a -> [EdgeFunction a]
getEdgeFunctions analysis = edgeFunctions analysis

emptyAnalysis :: (DynPop a -> Element a -> [Path a]) -> Analysis a
emptyAnalysis doDynPop =
  Analysis { doDynPop = doDynPop,
             graph = emptyGraph,
             workQueue = WorkQueue Q.empty,
             activeNodes = ActiveNodes S.empty,
             history = History S.empty,
             waitlist = Waitlist M.empty,
             edgeFunctions = []
           }

addEdgeFunction :: (Spec a) => EdgeFunction a -> Analysis a -> Analysis a
addEdgeFunction (rawEf@(EdgeFunction ef)) analysis =
  let WorkQueue wq = getWorkQueue analysis in
  let History history = getHistory analysis in
  let ActiveNodes activeSet = getActiveNodes analysis in
  let actives = S.toList activeSet in
  let newEdges = L.concat $
        do
          node <- actives
          (path, dest) <- ef node
          return $ pathToEdges path node dest
  in
  let newActives = S.fromList $
        MB.mapMaybe (\(Edge src _ _) ->
                       case src of IntermediateNode _ _ -> Just src
                                   otherwise -> Nothing
                    ) newEdges in
  let newEdgesSet = S.fromList newEdges in
  let (finalWq, finalHistory) =
        S.foldl (\(accWq, accHistory) -> \e ->
          if S.member e accHistory then (accWq, accHistory) else
            (Q.pushBack accWq e, S.insert e accHistory)) (wq, history) newEdgesSet
  in analysis { workQueue = WorkQueue finalWq,
                history = History finalHistory,
                activeNodes = ActiveNodes (S.union newActives activeSet),
                edgeFunctions = rawEf : (getEdgeFunctions analysis)
              }

addActiveNode :: (Spec a) => InternalNode a -> Analysis a -> Analysis a
addActiveNode newNode analysis =
  let ActiveNodes activeNodes = getActiveNodes analysis in
  let WorkQueue wq = getWorkQueue analysis in
  let History history = getHistory analysis in
  let Waitlist waitlist = getWaitlist analysis in
  -- Check whether the node is already active; if it is, we don't have to do anything
  if S.member newNode activeNodes then analysis else
    -- If not, then we need to empty the waitlist corresponding to this node,
    -- call the edge functions, and propagate liveness from it
    let activeNodes' = S.insert newNode activeNodes in
    let waitedWork = M.findWithDefault S.empty newNode waitlist in
    let waitlist' = M.delete newNode waitlist in
    let edgesFromEf = S.fromList $ L.concat $
          do
            (EdgeFunction ef) <- getEdgeFunctions analysis
            (path, dest) <- ef newNode
            return $ pathToEdges path newNode dest
    in
    let newWork = S.union waitedWork edgesFromEf in
    let history' = S.foldl (\acc -> \e -> S.insert e acc) history newWork in
    let wq' = S.foldl Q.pushBack wq newWork in
    let analysis' = analysis { workQueue = WorkQueue wq',
                               activeNodes = ActiveNodes activeNodes',
                               history = History history',
                               waitlist = Waitlist waitlist'
                             }
    in
    propagateLiveness newNode analysis'

pathToEdges :: Path a -> InternalNode a -> InternalNode a -> [Edge a]
pathToEdges (Path path) src dest =
  case path of
    [] -> [Edge src Nop dest]
    hd : [] -> [Edge src hd dest]
    hd : tl ->
      let loop lst acc prevSrc =
            case lst of
              hd' : [] -> acc ++ [Edge prevSrc hd' dest]
              hd' : tl' ->
                let newImdNode = IntermediateNode tl' dest in
                let newAcc = acc ++ [Edge prevSrc hd' newImdNode] in
                loop tl' newAcc newImdNode
      in
      let firstImdNode = IntermediateNode tl dest in
      loop tl [Edge src hd firstImdNode] firstImdNode

-- TODO: Leave comments to explain the algorithm
propagateLiveness :: (Spec a) => InternalNode a -> Analysis a -> Analysis a
propagateLiveness node analysis =
  let g = getGraph analysis in
  let ActiveNodes activeNodes = getActiveNodes analysis in
  -- Liveness is only propagated through push and nop edges
  let connectedNonActiveNodes =
        S.union
          (S.map fst $ findPushEdgesBySource node g) (findNopEdgesBySource node g)
        & S.filter (\e -> S.notMember e activeNodes)
  in
  S.foldl (\acc -> \n -> addActiveNode n acc) analysis connectedNonActiveNodes

closureStep :: (Spec a) => Analysis a -> Analysis a
closureStep analysis =
  -- If the workqueue is empty, we can simply return the analysis unchanged
  let WorkQueue wq = getWorkQueue analysis in
  if (null wq) then analysis
    else
      -- Extracting basic information from the analysis
      let g = getGraph analysis in
      let History history = getHistory analysis in
      let doDynPop = getDynPop analysis in
      let ActiveNodes ogActives = getActiveNodes analysis in
      -- If the edge is in the workqueue, we have not done work on it
      let (e@(Edge n1 sa n2), wq') = MB.fromJust (Q.popFront wq) in
      -- It's true that all edges in the workqueue should have active sources,
      -- but we never explicitly change the active status of IntermediateNodes
      -- I think we can either change the activeness here or when we are creating
      -- the path. I don't know which one is the correct move
      -- Maybe for the sake of invariance, we should change it in the path
      -- creation phase?
      {-- NOTE: Change activeness upon encoutering an edge in the workQueue --}
      -- let actives = if (S.member n1 ogActives) then ogActives else (S.insert n1 ogActives) in
      -- let analysis' = analysis { activeNodes = actives } in
      {-- NOTE: Edges in workQueue always have active sources --}
      let analysis' = analysis in
      let g' = if (S.member e (getEdges g)) then g else (addEdge e g) in
            case sa of
              Push se ->
                -- Push edge propagates liveness
                let analysis'' = propagateLiveness n2 analysis' in
                let popDests = findPopEdgesBySourceAndElement (n2, se) g in
                let nopDests = findNopEdgesBySource n2 g in
                let dynPopDests = findDynPopEdgesBySource n2 g in
                -- Since the source of the new edges will definitely be
                let (wq1, history1) = S.foldl
                      (\(accWq, accHistory) -> \dest ->
                        let newEdge = Edge n1 Nop dest in
                        if S.member newEdge accHistory then (accWq, accHistory) else
                          (Q.pushBack accWq newEdge, S.insert newEdge accHistory))
                      (wq', history) popDests in
                let (wq2, history2) = S.foldl
                      (\(accWq, accHistory) -> \dest ->
                        let newEdge = Edge n1 sa dest in
                        if S.member newEdge accHistory then (accWq, accHistory) else
                          (Q.pushBack accWq newEdge, S.insert newEdge accHistory))
                      (wq1, history1) nopDests in
                -- having live source nodes (or can we assume the path will always be alive?)
                let dynPopDestsMnd = S.toList $ dynPopDests in
                let rawEdgesLsts =
                      do
                        (dest, f) <- dynPopDestsMnd
                        let pathLst = doDynPop f se
                        singlePath <- pathLst
                        return $ pathToEdges singlePath n1 dest
                in
                {-- NOTE: Marking the IntermediateNodes as active --}
                let fullEdgesLst = concat rawEdgesLsts in
                let newActives = S.fromList $
                      MB.mapMaybe (\(Edge src _ _) ->
                                     case src of IntermediateNode _ _ -> Just src
                                                 otherwise -> Nothing
                                  ) fullEdgesLst in
                let newEdgesSet = S.fromList fullEdgesLst in
                {-- NOTE: Not marking the IntermediateNodes as active --}
                -- let newEdgesSet = S.fromList $ concat $ ND.toList rawEdgesLsts in
                let (finalWq, finalHistory) = S.foldl
                      (\(accWq, accHistory) -> \e ->
                        if S.member e accHistory then (accWq, accHistory) else
                          (Q.pushBack accWq e, S.insert e accHistory)) (wq2, history2) newEdgesSet
                in
                let ActiveNodes actives = getActiveNodes analysis'' in
                analysis'' { graph = g',
                             workQueue = WorkQueue finalWq,
                             history = History finalHistory,
                             activeNodes = ActiveNodes (S.union newActives actives)
                           }
              Pop se ->
                let pushSrcs = findPushEdgesByDestAndElement (n1, se) g in
                let ActiveNodes activeNodes = getActiveNodes analysis' in
                let History history = getHistory analysis' in
                let activepushSrcs = S.filter (\s -> S.member s activeNodes) pushSrcs in
                let (finalWq, finalHistory) = S.foldl
                      (\(accWq, accHistory) -> \src ->
                        let newEdge = Edge src Nop n2 in
                        if (S.member newEdge accHistory) then (accWq, accHistory) else
                          (Q.pushBack accWq newEdge, S.insert newEdge accHistory))
                      (wq', history) activepushSrcs in
                analysis' { graph = g',
                            workQueue = WorkQueue finalWq,
                            history = History finalHistory
                           }
              Nop ->
                -- Nop edge propagates liveness
                let analysis'' = propagateLiveness n2 analysis' in
                let ActiveNodes activeNodes = getActiveNodes analysis'' in
                let nopDests = findNopEdgesBySource n2 g in
                let wq1 = S.foldl
                      (\acc -> \dest ->
                        let newEdge = Edge n1 Nop dest in
                        if (S.member newEdge history) then acc else
                          Q.pushBack acc newEdge)
                      wq' nopDests in
                let nopSrcs = findNopEdgesByDest n1 g in
                let activenopSrcs = S.filter (\s -> S.member s activeNodes) nopSrcs in
                let wq2 = S.foldl
                      (\acc -> \src ->
                        let newEdge = Edge src Nop n2 in
                        if (S.member newEdge history) then acc else
                          Q.pushBack acc newEdge)
                      wq1 activenopSrcs in
                let pushSrcsAndElms = findPushEdgesByDest n1 g in
                let activePushSrcsAndElms = S.filter (\(s, _) -> S.member s activeNodes) pushSrcsAndElms in
                let finalWq = S.foldl
                      (\acc -> \(src, elm) ->
                        let newEdge = Edge src (Push elm) n2 in
                        if (S.member newEdge history) then acc else
                          Q.pushBack acc newEdge)
                      wq2 activePushSrcsAndElms in
                analysis'' { graph = g',
                             workQueue = WorkQueue finalWq }
              DynamicPop f ->
                let pushSrcsAndElms = S.toList $ findPushEdgesByDest n1 g in
                let rawEdgesLsts =
                      do
                        (src, elm) <- pushSrcsAndElms
                        let pathLst = doDynPop f elm
                        singlePath <- pathLst
                        return $ pathToEdges singlePath src n2
                in
                {-- NOTE: Marking the IntermediateNodes as active --}
                let fullEdgesLst = concat rawEdgesLsts in
                let newActives = S.fromList $
                      MB.mapMaybe (\(Edge src _ _) ->
                                     case src of IntermediateNode _ _ -> Just src
                                                 otherwise -> Nothing
                                  ) fullEdgesLst in
                let newEdgesSet = S.fromList fullEdgesLst in
                {-- NOTE: Not marking the IntermediateNodes as active --}
                -- let newEdgesSet = S.fromList $ concat $ ND.toList rawEdgesLsts in
                let finalWq = S.foldl Q.pushBack wq' newEdgesSet in
                let ActiveNodes activeNodes = getActiveNodes analysis in
                analysis { graph = g',
                           workQueue = WorkQueue finalWq,
                           activeNodes = ActiveNodes (S.union newActives activeNodes)
                         }

fullClosure :: (Spec a) => Analysis a -> Analysis a
fullClosure analysis =
  let doDynPop = getDynPop analysis in
  let analysis' = closureStep analysis in
  let WorkQueue wq' = getWorkQueue analysis' in
  if (null wq') then analysis' else fullClosure analysis'

-- TODO: Yet another dictionary keeping track of edges in the graph with inactive
-- sources so that we can dump them into workQueue when their source becomes active
updateAnalysis :: (Spec a) => Edge a -> Analysis a -> Analysis a
updateAnalysis (e@(Edge src sa dest)) (analysis) =
  -- Check whether the "new" edge is already seen
  let g = getGraph analysis in
  -- If it's already in the graph, it means we have already processed the edge, so skip
  if S.member e (getEdges g) then analysis else
    -- If it's not present in the graph, we need to check for its active status
    let WorkQueue wq = getWorkQueue analysis in
    let ActiveNodes activeNodes = getActiveNodes analysis in
    -- We will need to add it to the graph either way, so construct the new graph upfront
    let g' = addEdge e g in
    -- If the source of new edge is active, we add it to the workqueue
    if (S.member src activeNodes) then
      let History history = getHistory analysis in
      let history' = S.insert e history in
      let wq' = Q.pushBack wq e in
      analysis { graph = g',
                 workQueue = WorkQueue wq',
                 history = History history' }
    -- If the source is inactive, we only add it to the graph, and will wake
    -- it up later on demand
    else
      let Waitlist waitlist = getWaitlist analysis in
      let waitlist' =
            if M.member src waitlist
            then
              let curEntry = M.findWithDefault S.empty src waitlist in
              let newEntry = S.insert e curEntry in
              M.adjust (\_ -> newEntry) src waitlist
            else
              M.insert src (S.singleton e) waitlist
      in
      analysis { graph = g',
                 waitlist = Waitlist waitlist' }
