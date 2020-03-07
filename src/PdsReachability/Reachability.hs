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

-- TODO: Next step: Edge functions?
-- Adding edge function requires calling this particular function with all
-- currently active nodes
-- When a node becomes active, call every edge function with this node as the
-- argument.
-- Edge functions: Node -> [Path]

type WorkQueue nt element dynPopFun = Q.BankersDequeue (Edge nt element dynPopFun)

type Path element dynPopFun = [StackAction element dynPopFun]

type History nt element dynPopFun = S.Set (Edge nt element dynPopFun)

type ActiveNodes nt element dynPopFun = S.Set (Node nt element dynPopFun)

type EdgeFunction nt element dynPopFun =
  Node nt element dynPopFun -> [Edge nt element dynPopFun]

type Waitlist nt element dynPopFun
  = M.Map (Node nt element dynPopFun) (S.Set (Edge nt element dynPopFun))

data Analysis nt element dynPopFun where
   Analysis ::
    (Ord nt, Ord element, Ord dynPopFun, Eq nt, Eq element, Eq dynPopFun) =>
    {
      doDynPop :: (dynPopFun -> element -> [Path element dynPopFun]),
      graph :: Graph nt element dynPopFun,
      workQueue :: WorkQueue nt element dynPopFun,
      activeNodes :: ActiveNodes nt element dynPopFun,
      history :: History nt element dynPopFun,
      waitlist :: Waitlist nt element dynPopFun,
      edgeFunctions :: [EdgeFunction nt element dynPopFun]
    } -> Analysis nt element dynPopFun

-- Cannot derive show for doDynPop so have to manually roll out this function
instance (Show nt, Show element, Show dynPopFun) =>
  Show (Analysis nt element dynPopFun) where
  show a = "Analysis Graph: " ++ show (graph a) ++ ";\n" ++
    "WorkQueue: " ++ show (workQueue a) ++ ";\n" ++
    "ActiveNodes: " ++ show (activeNodes a) ++ ";\n"

-- This function unpacks the GADT so that the functions required by the
-- constraints are exposed
withAnalysis ::
  Analysis nt element dynPopFun ->
  ((Eq nt, Eq element, Eq dynPopFun, Ord nt, Ord element, Ord dynPopFun) => () -> a) ->
  a
withAnalysis g f =
  case g of
    Analysis {} -> f ()

getGraph :: Analysis nt element dynPopFun -> Graph nt element dynPopFun
getGraph analysis = graph analysis

getWorkQueue :: Analysis nt element dynPopFun -> WorkQueue nt element dynPopFun
getWorkQueue analysis = workQueue analysis

getDynPopFun ::
  Analysis nt element dynPopFun ->
  (dynPopFun -> element -> [Path element dynPopFun])
getDynPopFun analysis = doDynPop analysis

getActiveNodes ::
  Analysis nt element dynPopFun ->
  ActiveNodes nt element dynPopFun
getActiveNodes analysis = activeNodes analysis

getHistory ::
  Analysis nt element dynPopFun ->
  History nt element dynPopFun
getHistory analysis = history analysis

getWaitlist ::
  Analysis nt element dynPopFun ->
  Waitlist nt element dynPopFun
getWaitlist analysis = waitlist analysis

getEdgeFunctions ::
  Analysis nt element dynPopFun ->
  [EdgeFunction nt element dynPopFun]
getEdgeFunctions analysis = edgeFunctions analysis

emptyAnalysis :: (Ord nt, Ord element, Ord dynPopFun) =>
  (dynPopFun -> element -> [Path element dynPopFun]) ->
  Analysis nt element dynPopFun
emptyAnalysis doDynPop =
  Analysis { doDynPop = doDynPop,
             graph = emptyGraph,
             workQueue = Q.empty,
             activeNodes = S.empty,
             history = S.empty,
             waitlist = M.empty,
             edgeFunctions = []
           }

addEdgeFunction ::
  EdgeFunction nt element dynPopFun ->
  Analysis nt element dynPopFun ->
  Analysis nt element dynPopFun
addEdgeFunction ef analysis =
  withAnalysis analysis $ \() ->
  let wq = getWorkQueue analysis in
  let history = getHistory analysis in
  let actives = S.toList $ getActiveNodes analysis in
  let activeMND = ND.pick actives in
  let newEdges = L.concat $ ND.toList $
        do
          node <- activeMND
          return $ ef node
  in
  let newActives = S.fromList $
        MB.mapMaybe (\(Edge src _ _) ->
                       case src of IntermediateNode _ _ -> Just src
                                   otherwise -> Nothing
                    ) newEdges in
  let newEdgesSet = S.fromList newEdges in
  let finalWq = S.foldl
        (\acc -> \e ->
          if S.member e history then acc else
            Q.pushBack acc e) wq newEdgesSet
  in
  let finalHistory = S.foldl
        (\acc -> \e -> S.insert e acc) history newEdgesSet
  in
  analysis { workQueue = finalWq,
             history = finalHistory,
             activeNodes = S.union newActives (getActiveNodes analysis),
             edgeFunctions = ef : (getEdgeFunctions analysis)
            }

addActiveNode ::
  Node nt element dynPopFun ->
  Analysis nt element dynPopFun ->
  Analysis nt element dynPopFun
addActiveNode newNode analysis =
  withAnalysis analysis $ \() ->
  let activeNodes = getActiveNodes analysis in
  -- Check whether the node is already active; if it is, we don't have to do anything
  if S.member newNode activeNodes then analysis else
    -- If not, then we need to empty the waitlist corresponding to this node,
    -- call the edge functions, and propagate liveness from it
    let activeNodes' = S.insert newNode activeNodes in
    let waitedWork = M.findWithDefault S.empty newNode (getWaitlist analysis) in
    let waitlist' = M.delete newNode (getWaitlist analysis) in
    let history' = S.foldl (\acc -> \e -> S.insert e acc) (getHistory analysis) waitedWork in
    let wq' = S.foldl Q.pushBack (getWorkQueue analysis) waitedWork in
    let analysis' = analysis { workQueue = wq',
                               activeNodes = activeNodes',
                               history = history',
                               waitlist = waitlist'
                             }
    in
    propagateLiveness newNode analysis'

pathToEdges ::
  Path element dynPopFun ->
  Node nt element dynPopFun ->
  Node nt element dynPopFun ->
  [Edge nt element dynPopFun]
pathToEdges path src dest =
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
propagateLiveness ::
  Node nt element dynPopFun ->
  Analysis nt element dynPopFun ->
  Analysis nt element dynPopFun
propagateLiveness node analysis =
  withAnalysis analysis $ \() ->
  let g = getGraph analysis in
  let activeNodes = getActiveNodes analysis in
  -- Liveness is only propagated through push and nop edges
  let connectedNonActiveNodes =
        S.union
          (S.map fst $ findPushEdgesBySource node g) (findNopEdgesBySource node g)
        & S.filter (\e -> S.notMember e activeNodes)
  in
  S.foldl (\acc -> \n -> addActiveNode n acc) analysis connectedNonActiveNodes

closureStep ::
  Analysis nt element dynPopFun ->
  Analysis nt element dynPopFun
closureStep analysis =
  withAnalysis analysis $ \() ->
  -- If the workqueue is empty, we can simply return the analysis unchanged
  let wq = getWorkQueue analysis in
  if (null wq) then analysis
    else
      -- Extracting basic information from the analysis
      let g = getGraph analysis in
      let history = getHistory analysis in
      let doDynPop = getDynPopFun analysis in
      let ogActives = getActiveNodes analysis in
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
                let dynPopDestsMnd = pick $ S.toList $ dynPopDests in
                let rawEdgesLsts =
                      do
                        (dest, f) <- dynPopDestsMnd
                        let pathLst = doDynPop f se
                        singlePath <- ND.pick pathLst
                        return $ pathToEdges singlePath n1 dest
                in
                {-- NOTE: Marking the IntermediateNodes as active --}
                let fullEdgesLst = concat $ ND.toList rawEdgesLsts in
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
                analysis'' { graph = g',
                             workQueue = finalWq,
                             -- history = finalHistory,
                             activeNodes = S.union newActives (getActiveNodes analysis'')
                           }
              Pop se ->
                let pushSrcs = findPushEdgesByDestAndElement (n1, se) g in
                let activeNodes = getActiveNodes analysis' in
                let history = getHistory analysis' in
                let activepushSrcs = S.filter (\s -> S.member s activeNodes) pushSrcs in
                let (finalWq, finalHistory) = S.foldl
                      (\(accWq, accHistory) -> \src ->
                        let newEdge = Edge src Nop n2 in
                        if (S.member newEdge accHistory) then (accWq, accHistory) else
                          (Q.pushBack accWq newEdge, S.insert newEdge accHistory))
                      (wq', history) activepushSrcs in
                analysis' { graph = g',
                            workQueue = finalWq,
                            history = finalHistory
                           }
              Nop ->
                -- Nop edge propagates liveness
                let analysis'' = propagateLiveness n2 analysis' in
                let activeNodes = getActiveNodes analysis'' in
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
                           workQueue = finalWq }
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
                {-- NOTE: Marking the IntermediateNodes as active --}
                let fullEdgesLst = concat $ ND.toList rawEdgesLsts in
                let newActives = S.fromList $
                      MB.mapMaybe (\(Edge src _ _) ->
                                     case src of IntermediateNode _ _ -> Just src
                                                 otherwise -> Nothing
                                  ) fullEdgesLst in
                let newEdgesSet = S.fromList fullEdgesLst in
                {-- NOTE: Not marking the IntermediateNodes as active --}
                -- let newEdgesSet = S.fromList $ concat $ ND.toList rawEdgesLsts in
                let finalWq = S.foldl Q.pushBack wq' newEdgesSet in
                analysis { graph = g',
                           workQueue = finalWq,
                           activeNodes = S.union newActives (getActiveNodes analysis)
                         }

fullClosure ::
  Analysis nt element dynPopFun ->
  Analysis nt element dynPopFun
fullClosure analysis =
  withAnalysis analysis $ \() ->
  let doDynPop = getDynPopFun analysis in
  let analysis' = closureStep analysis in
  let wq' = getWorkQueue analysis' in
  if (null wq') then analysis' else fullClosure analysis'

-- TODO: Yet another dictionary keeping track of edges in the graph with inactive
-- sources so that we can dump them into workQueue when their source becomes active
updateAnalysis ::
  Edge nt element dynPopFun ->
  Analysis nt element dynPopFun ->
  Analysis nt element dynPopFun
updateAnalysis (e@(Edge src sa dest)) (analysis) =
  withAnalysis analysis $ \() ->
  -- Check whether the "new" edge is already seen
  let g = getGraph analysis in
  -- If it's already in the graph, it means we have already processed the edge, so skip
  if S.member e (getEdges g) then analysis else
    -- If it's not present in the graph, we need to check for its active status
    let wq = getWorkQueue analysis in
    let activeNodes = getActiveNodes analysis in
    -- We will need to add it to the graph either way, so construct the new graph upfront
    let g' = addEdge e g in
    -- If the source of new edge is active, we add it to the workqueue
    if (S.member src activeNodes) then
      let history = getHistory analysis in
      let history' = S.insert e history in
      let wq' = Q.pushBack wq e in
      analysis { graph = g',
                 workQueue = wq',
                 history = history' }
    -- If the source is inactive, we only add it to the graph, and will wake
    -- it up later on demand
    else
      let waitlist = getWaitlist analysis in
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
                 waitlist = waitlist' }
