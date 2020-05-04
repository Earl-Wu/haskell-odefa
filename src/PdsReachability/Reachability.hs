{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
module PdsReachability.Reachability where

import AST.Ast
import Control.Monad
import Data.Function
import PdsReachability.Structure
import PdsReachability.Specification
import qualified Data.Either as E
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Maybe as MB
import qualified Data.Multimap as MM
import qualified Data.Dequeue as Q

-- NOTE: TODO List
-- Getting rid of the constructors
-- Creating a PdsReachability module file for user interface
--   Creating an internal file PdsReachability.UserTypes for user data types
-- Implementing the edge fuctions
--

data WorkQueue a = WorkQueue (Q.BankersDequeue (GeneralEdges a))
deriving instance (SpecIs Show a) => (Show (WorkQueue a))

data History a = History (S.Set (GeneralEdges a))
deriving instance (SpecIs Show a) => (Show (History a))

data ActiveNodes a = ActiveNodes (S.Set (InternalNode a))
deriving instance (SpecIs Show a) => (Show (ActiveNodes a))
deriving instance (SpecIs Eq a) => (Eq (ActiveNodes a))

-- USER
data Path a = Path [StackAction a]
deriving instance (SpecIs Show a) => (Show (Path a))

-- USER
data EdgeFunction a = EdgeFunction (Node a -> [(Path a, Terminus a)])

-- USER
data Question a = Question (Node a) [StackAction a]
deriving instance (SpecIs Show a) => (Show (Question a))
deriving instance (SpecIs Eq a) => (Eq (Question a))
deriving instance (SpecIs Ord a) => (Ord (Question a))

data Questions a = Questions (S.Set (Question a))
deriving instance (SpecIs Show a) => (Show (Questions a))
deriving instance (SpecIs Eq a) => (Eq (Questions a))

data Waitlist a = Waitlist (M.Map (InternalNode a) (S.Set (GeneralEdges a)))

-- USER (black box)
data Analysis a =
  Analysis
    { doClassify :: (Node a -> NodeClass a),
      doTargetedDynPop :: (TargetedDynPop a -> Element a -> [Path a]),
      doUntargetedDynPop ::
        (UntargetedDynPop a -> Element a -> [(Path a, Terminus a)]),
      graph :: Graph a,
      workQueue :: WorkQueue a,
      activeNodes :: ActiveNodes a,
      activeUserNodes :: S.Set (Node a),
      activeNodesByClass :: MM.Multimap S.Set (NodeClass a) (Node a),
      questions :: Questions a,
      history :: History a,
      waitlist :: Waitlist a,
      edgeFunctions :: MM.Multimap [] (Maybe (NodeClass a)) (EdgeFunction a)
    }

-- Cannot derive show for doTargetedDynPop so have to manually roll out this function
instance (SpecIs Show a) => Show (Analysis a) where
  show a = "Analysis Graph: " ++ show (graph a) ++ ";\n" ++
    "WorkQueue: " ++ show (workQueue a) ++ ";\n" ++
    "ActiveNodes: " ++ show (activeNodes a) ++ ";\n"

getGraph :: Analysis a -> Graph a
getGraph analysis = graph analysis

getWorkQueue :: Analysis a -> WorkQueue a
getWorkQueue analysis = workQueue analysis

getTargetedDynPop :: Analysis a -> (TargetedDynPop a -> Element a -> [Path a])
getTargetedDynPop analysis = doTargetedDynPop analysis

getUntargetedDynPop ::
  Analysis a -> (UntargetedDynPop a -> Element a -> [(Path a, Terminus a)])
getUntargetedDynPop analysis = doUntargetedDynPop analysis

getActiveNodes :: Analysis a -> ActiveNodes a
getActiveNodes analysis = activeNodes analysis

getActiveUserNodes :: Analysis a -> S.Set (Node a)
getActiveUserNodes analysis = activeUserNodes analysis

getActiveNodesByClass ::
  (Ord (Node a), Ord (NodeClass a)) =>
  NodeClass a -> Analysis a -> S.Set (Node a)
getActiveNodesByClass nodeClass analysis =
  MM.find nodeClass (activeNodesByClass analysis)

getQuestions :: Analysis a -> Questions a
getQuestions analysis = questions analysis

getHistory :: Analysis a -> History a
getHistory analysis = history analysis

getWaitlist :: Analysis a -> Waitlist a
getWaitlist analysis = waitlist analysis

getEdgeFunctionsByClass ::
  Ord (NodeClass a) =>
  NodeClass a -> Analysis a -> [EdgeFunction a]
getEdgeFunctionsByClass nodeClass analysis =
  MM.find (Just nodeClass) (edgeFunctions analysis) `mappend`
  MM.find Nothing (edgeFunctions analysis)

-- TODO: How do we count number of nodes?
-- getSize :: Analysis a -> (Int, Int)
-- getSize analysis =
--   let g = getGraph analysis in
--   -- let nodeCount = countNodes (S.toList edges) in
--   let edgeCount = S.size (getEdges g) + S.size (getUntargetedDynPopEdges g) in
--   (0, edgeCount)

terminusToDestination :: Terminus a -> Destination a
terminusToDestination terminus =
  case terminus of
    StaticTerminus node -> StaticDestination (UserNode node)
    DynamicTerminus action -> DynamicDestination action

-- USER
emptyAnalysis ::
  (Node a -> NodeClass a) ->
  (TargetedDynPop a -> Element a -> [Path a]) ->
  (UntargetedDynPop a ->  Element a -> ([(Path a, Terminus a)])) ->
  Analysis a
emptyAnalysis classifier doTargetedDynPop doUntargetedDynPop =
  Analysis { doClassify = classifier,
             doTargetedDynPop = doTargetedDynPop,
             doUntargetedDynPop = doUntargetedDynPop,
             graph = emptyGraph,
             workQueue = WorkQueue Q.empty,
             activeNodes = ActiveNodes S.empty,
             activeUserNodes = S.empty,
             activeNodesByClass = MM.empty,
             questions = Questions S.empty,
             history = History S.empty,
             waitlist = Waitlist M.empty,
             edgeFunctions = MM.empty
           }

-- USER
addEdge ::
  forall a. (Spec a) =>
  Node a -> Path a -> Terminus a -> Analysis a -> Analysis a
addEdge source path terminus analysis =
  let destination = terminusToDestination terminus in
  let generalEdges = pathToEdges path (UserNode source) destination in
  addAnalysisEdges generalEdges analysis

-- USER
addEdgeFunction ::
  forall a. (Spec a) =>
  Maybe (NodeClass a) -> EdgeFunction a -> Analysis a -> Analysis a
addEdgeFunction maybeNodeClass (rawEf@(EdgeFunction ef)) analysis =
  let WorkQueue wq = getWorkQueue analysis in
  let History history = getHistory analysis in
  let ActiveNodes activeSet = getActiveNodes analysis in
  let newEdges =
        let actives =
              case maybeNodeClass of
                Just nodeClass ->
                  S.toList $ getActiveNodesByClass nodeClass analysis
                Nothing ->
                  S.toList $ getActiveUserNodes analysis
        in
        L.concat $ do
          node <- actives
          (path, terminus) <- ef node
          let dest = terminusToDestination terminus
          return $ pathToEdges path (UserNode node) dest
  in
  let newIntermediateActives = S.fromList $
        MB.mapMaybe (\e ->
                       case e of RegularEdge (Edge src _ _) ->
                                   case src of IntermediateNode _ _ -> Just src
                                               otherwise -> Nothing
                                 UntargetedEdge (UntargetedDynPopEdge src _) ->
                                   case src of IntermediateNode _ _ -> Just src
                                               otherwise -> Nothing
                    ) newEdges
  in
  let newEdgesSet = S.fromList newEdges in
  let (finalWq, finalHistory) =
        S.foldl (\(accWq, accHistory) -> \e ->
          if S.member e accHistory then (accWq, accHistory) else
            (Q.pushBack accWq e, S.insert e accHistory)) (wq, history) newEdgesSet
  in analysis { workQueue = WorkQueue finalWq,
                history = History finalHistory,
                activeNodes =
                  ActiveNodes (S.union newIntermediateActives activeSet),
                edgeFunctions =
                  MM.append maybeNodeClass rawEf $ edgeFunctions analysis
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
    let (activeNodesByClass', activeUserNodes', edgesFromEf) =
          case newNode of
            IntermediateNode _ _ ->
              ( activeNodesByClass analysis
              , getActiveUserNodes analysis
              , S.empty)
            UserNode n ->
              let classification = doClassify analysis n in
              let activeNodesByClass' =
                    MM.append classification n $ activeNodesByClass analysis
              in
              let edgesFromEf =
                    S.fromList $ L.concat $
                    do
                      (EdgeFunction ef) <-
                          getEdgeFunctionsByClass classification analysis
                      (path, terminus) <- ef n
                      let dest = terminusToDestination terminus
                      return $ pathToEdges path newNode dest
              in
              ( activeNodesByClass'
              , (S.insert n (getActiveUserNodes analysis))
              , edgesFromEf)
    in
    let waitedWork = M.findWithDefault S.empty newNode waitlist in
    let waitlist' = M.delete newNode waitlist in
    let newWork = S.union waitedWork edgesFromEf in
    let history' = S.foldl (\acc -> \e -> S.insert e acc) history newWork in
    let wq' = S.foldl Q.pushBack wq newWork in
    let analysis' = analysis { workQueue = WorkQueue wq',
                               activeNodes = ActiveNodes activeNodes',
                               activeUserNodes = activeUserNodes',
                               activeNodesByClass = activeNodesByClass',
                               history = History history',
                               waitlist = Waitlist waitlist'
                             }
    in
    propagateLiveness newNode analysis'

-- USER
addQuestion :: (Spec a) => Question a -> Analysis a -> Analysis a
addQuestion question analysis =
  let Question node actions = question in
  let internalTarget = UserNode node in
  let Questions ogQuestions = getQuestions analysis in
  let newQuestions = Questions $ S.insert question ogQuestions in
  let destination = StaticDestination internalTarget in
  let internalSource =
        if L.null actions then
          internalTarget
        else
          IntermediateNode actions destination
  in
  let edges = pathToEdges (Path actions) internalSource destination in
  let analysis' =
        analysis
        & addActiveNode internalSource
        & addAnalysisEdges edges
  in analysis' { questions = newQuestions }

-- USER
getReachableNodes :: (Spec a) => Question a -> Analysis a -> Maybe [Node a]
getReachableNodes question analysis =
  let Question node actions = question in
  let lookupNode = IntermediateNode actions (StaticDestination (UserNode node)) in
  -- Look up Nop edges in the analysis graph and filter out the IntermediateNodes
  let Questions qs = getQuestions analysis in
  let g = getGraph analysis in
  if (S.member question qs) then
    let rawRes = findNopEdgesBySource lookupNode g in
    S.filter (\n -> case n of UserNode _ -> True
                              IntermediateNode _ _ -> False
             ) rawRes
    & S.map (\n -> case n of UserNode res -> res)
    & S.toList
    & return
  else Nothing

pathToEdges :: Path a -> InternalNode a -> Destination a -> [GeneralEdges a]
pathToEdges (Path path) src dest =
  case path of
    [] ->
      case dest of
        StaticDestination destNode ->
          [RegularEdge $ Edge src Nop destNode]
        DynamicDestination upAction ->
          [UntargetedEdge $ UntargetedDynPopEdge src upAction]
    hd : [] ->
      case dest of
        StaticDestination destNode ->
          [RegularEdge $ Edge src hd destNode]
        DynamicDestination upAction ->
          let newDest = IntermediateNode [] dest in
          [RegularEdge $ Edge src hd newDest]
    hd : tl ->
      let loop lst acc prevSrc =
            case lst of
              hd' : [] ->
                case dest of
                  StaticDestination destNode ->
                    acc ++ [RegularEdge $ Edge prevSrc hd' destNode]
                  DynamicDestination upAction ->
                    let newDest = IntermediateNode [] dest in
                    acc ++ [RegularEdge $ Edge prevSrc hd' newDest]
              hd' : tl' ->
                let newImdNode = IntermediateNode tl' dest in
                let newAcc = acc ++ [RegularEdge $ Edge prevSrc hd' newImdNode] in
                loop tl' newAcc newImdNode
      in
      let firstImdNode = IntermediateNode tl dest in
      loop tl [RegularEdge $ Edge src hd firstImdNode] firstImdNode

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

-- USER
isClosed :: Analysis a -> Bool
isClosed analysis =
  let WorkQueue wq = getWorkQueue analysis in
  null wq

-- USER
closureStep ::
  (Spec a) => Analysis a -> (Analysis a, Maybe (Question a, Node a))
closureStep analysis =
  -- If the workqueue is empty, we can simply return the analysis unchanged
  let WorkQueue wq = getWorkQueue analysis in
  if (null wq) then (analysis, Nothing)
    else
      -- Extracting basic information from the analysis
      let g = getGraph analysis in
      let History history = getHistory analysis in
      let doTargetedDynPop = getTargetedDynPop analysis in
      let doUntargetedDynPop = getUntargetedDynPop analysis in
      let ActiveNodes ogActives = getActiveNodes analysis in
      -- If the edge is in the workqueue, we have not done work on it
      let work = MB.fromJust (Q.popFront wq) in
      let resultAnalysis =
            case work of
              (RegularEdge (e@(Edge n1 sa n2)), wq') ->
                {- It's true that all edges in the workqueue should have active
                   sources, but we never explicitly change the active status of
                   IntermediateNodes.  I think we can either change the
                   activeness here or when we are creating the path. I don't
                   know which one is the correct move.  Maybe for the sake of
                   invariance, we should change it in the path creation phase?
                -}
                {-- NOTE: Edges in workQueue always have active sources --}
                let analysis' = analysis { workQueue = WorkQueue wq' } in
                {-- NOTE: It's ok to use the original graph g in the following
                          computation because the edge does not close with
                          itself --}
                let g' =
                      if (S.member e (getEdges g)) then
                        g
                      else
                        (PdsReachability.Structure.addEdge e g)
                in
                case sa of
                  Push se ->
                    -- Push edge propagates liveness
                    let analysis'' =
                          propagateLiveness n2 (addActiveNode n2 analysis')
                    in
                    -- NOTE: here we need to get the latest work queue,
                    -- because propagateLiveness might alter the it
                    let WorkQueue curWq = getWorkQueue analysis'' in
                    let popDests = findPopEdgesBySourceAndElement (n2, se) g in
                    let nopDests = findNopEdgesBySource n2 g in
                    let dynPopDests = findTargetedDynPopEdgesBySource n2 g in
                    let untargetedDynPops =
                          findUntargetedDynPopEdgesBySource n2 g
                    in
                    -- Closure rule: push + pop ==> nop
                    let (wq1, history1) = S.foldl
                          (\(accWq, accHistory) -> \dest ->
                            let newEdge = RegularEdge $ Edge n1 Nop dest in
                            if S.member newEdge accHistory then
                              (accWq, accHistory)
                            else
                              ( Q.pushBack accWq newEdge
                              , S.insert newEdge accHistory
                              )
                          )
                          (curWq, history) popDests
                    in
                    -- Closure rule: push + nop ==> push
                    let (wq2, history2) = S.foldl
                          (\(accWq, accHistory) -> \dest ->
                            let newEdge = RegularEdge $ Edge n1 sa dest in
                            if S.member newEdge accHistory then
                              (accWq, accHistory)
                            else
                              ( Q.pushBack accWq newEdge
                              , S.insert newEdge accHistory
                              )
                          )
                          (wq1, history1) nopDests
                    in
                    -- Closure rule: push + untargeted pop ==> ...
                    let untargetedDynPopsMnd = S.toList untargetedDynPops in
                    let rawUntargetedEdgesLsts =
                          do
                            f <- untargetedDynPopsMnd
                            (singlePath, terminus) <- doUntargetedDynPop f se
                            let destination = terminusToDestination terminus
                            return $ pathToEdges singlePath n1 destination
                    in
                    -- Closure rule: push + targeted pop ==> ...
                    let dynPopDestsMnd =
                          S.toList $
                          S.map (\(dest, f) ->
                                    (StaticDestination dest, f)) dynPopDests
                    in
                    let rawTargetedEdgesLsts =
                          do
                            (dest, f) <- dynPopDestsMnd
                            let pathLst = doTargetedDynPop f se
                            singlePath <- pathLst
                            return $ pathToEdges singlePath n1 dest
                    in
                    -- Concatenate all of the paths from dynamic pops
                    let fullEdgesLst =
                          concat rawTargetedEdgesLsts ++
                          concat rawUntargetedEdgesLsts
                    in
                    {-- NOTE: Marking the IntermediateNodes as active --}
                    -- Since the source of the new edges will definitely be
                    -- having live source nodes (or can we assume the path will
                    -- always be alive?)
                    let newIntermediateActives = S.fromList $
                          MB.mapMaybe
                            (\e ->
                              case e of
                                RegularEdge (Edge src _ _) ->
                                  case src of
                                    IntermediateNode _ _ -> Just src
                                    otherwise -> Nothing
                                UntargetedEdge (UntargetedDynPopEdge src _) ->
                                  case src of
                                    IntermediateNode _ _ -> Just src
                                    otherwise -> Nothing)
                          fullEdgesLst
                    in
                    let newEdgesSet = S.fromList fullEdgesLst in
                    {-- NOTE: Not marking the IntermediateNodes as active --}
                    let (finalWq, finalHistory) =
                          S.foldl
                            (\(accWq, accHistory) -> \e ->
                              if S.member e accHistory then
                                (accWq, accHistory)
                              else
                                (Q.pushBack accWq e, S.insert e accHistory)
                            )
                            (wq2, history2) newEdgesSet
                    in
                    let ActiveNodes actives = getActiveNodes analysis'' in
                    analysis'' { graph = g',
                                 workQueue = WorkQueue finalWq,
                                 history = History finalHistory,
                                 activeNodes =
                                    ActiveNodes (S.union newIntermediateActives
                                                         actives)
                               }
                  Pop se ->
                    let pushSrcs = findPushEdgesByDestAndElement (n1, se) g in
                    let ActiveNodes activeNodes = getActiveNodes analysis' in
                    let History history = getHistory analysis' in
                    let activepushSrcs =
                          S.filter (\s -> S.member s activeNodes) pushSrcs
                    in
                    let (finalWq, finalHistory) = S.foldl
                          (\(accWq, accHistory) -> \src ->
                            let newEdge = RegularEdge $ Edge src Nop n2 in
                            if (S.member newEdge accHistory) then
                              (accWq, accHistory)
                            else
                              ( Q.pushBack accWq newEdge
                              , S.insert newEdge accHistory))
                          (wq', history) activepushSrcs
                    in
                    analysis' { graph = g',
                                workQueue = WorkQueue finalWq,
                                history = History finalHistory
                               }
                  Nop ->
                    -- Nop edge propagates liveness
                    let analysis'' =
                          propagateLiveness n2 (addActiveNode n2 analysis')
                    in
                    let WorkQueue curWq = getWorkQueue analysis'' in
                    let ActiveNodes activeNodes = getActiveNodes analysis'' in
                    let nopDests = findNopEdgesBySource n2 g in
                    let wq1 = S.foldl
                          (\acc -> \dest ->
                            let newEdge = RegularEdge $ Edge n1 Nop dest in
                            if (S.member newEdge history) then acc else
                              Q.pushBack acc newEdge)
                          curWq nopDests in
                    let nopSrcs = findNopEdgesByDest n1 g in
                    let activenopSrcs =
                          S.filter (\s -> S.member s activeNodes) nopSrcs
                    in
                    let wq2 = S.foldl
                          (\acc -> \src ->
                            let newEdge = RegularEdge $ Edge src Nop n2 in
                            if (S.member newEdge history) then acc else
                              Q.pushBack acc newEdge)
                          wq1 activenopSrcs in
                    let pushSrcsAndElms = findPushEdgesByDest n1 g in
                    let activePushSrcsAndElms =
                          S.filter
                            (\(s, _) -> S.member s activeNodes)
                            pushSrcsAndElms
                    in
                    let finalWq = S.foldl
                          (\acc -> \(src, elm) ->
                            let newEdge = RegularEdge $ Edge src (Push elm) n2 in
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
                            let pathLst = doTargetedDynPop f elm
                            singlePath <- pathLst
                            return $
                              pathToEdges singlePath src (StaticDestination n2)
                    in
                    {-- NOTE: Marking the IntermediateNodes as active --}
                    let fullEdgesLst = concat rawEdgesLsts in
                    let newIntermediateActives = S.fromList $
                          MB.mapMaybe
                            (\e ->
                              case e of
                                RegularEdge (Edge src _ _) ->
                                  case src of
                                    IntermediateNode _ _ -> Just src
                                    otherwise -> Nothing
                                UntargetedEdge (UntargetedDynPopEdge src _) ->
                                  case src of
                                    IntermediateNode _ _ -> Just src
                                    otherwise -> Nothing
                            )
                            fullEdgesLst
                    in
                    let newEdgesSet = S.fromList fullEdgesLst in
                    {-- NOTE: Not marking the IntermediateNodes as active --}
                    let finalWq = S.foldl Q.pushBack wq' newEdgesSet in
                    let ActiveNodes activeNodes = getActiveNodes analysis in
                    analysis { graph = g',
                               workQueue = WorkQueue finalWq,
                               activeNodes =
                                 ActiveNodes (S.union newIntermediateActives
                                                      activeNodes)
                             }
              (UntargetedEdge (e@(UntargetedDynPopEdge n1 pa)), wq') ->
                let g' = if (S.member e (getUntargetedDynPopEdges g)) then
                           g
                         else
                           addUntargetedDynPopEdge e g
                in
                let pushSrcsAndElms = S.toList $ findPushEdgesByDest n1 g in
                let rawEdgesLsts =
                      do
                        (src, elm) <- pushSrcsAndElms
                        let pathTerminusLst = doUntargetedDynPop pa elm
                        (singlePath, singleTerminus) <- pathTerminusLst
                        let destination = terminusToDestination singleTerminus
                        return $ pathToEdges singlePath src destination
                in
                {-- NOTE: Marking the IntermediateNodes as active --}
                let fullEdgesLst = concat rawEdgesLsts in
                let newIntermediateActives = S.fromList $
                      MB.mapMaybe
                        (\e ->
                          case e of
                            RegularEdge (Edge src _ _) ->
                              case src of
                                IntermediateNode _ _ -> Just src
                                otherwise -> Nothing
                            UntargetedEdge (UntargetedDynPopEdge src _) ->
                              case src of
                                IntermediateNode _ _ -> Just src
                                otherwise -> Nothing
                        )
                        fullEdgesLst
                in
                let newEdgesSet = S.fromList fullEdgesLst in
                {-- NOTE: Not marking the IntermediateNodes as active --}
                let finalWq = S.foldl Q.pushBack wq' newEdgesSet in
                let ActiveNodes activeNodes = getActiveNodes analysis in
                analysis { graph = g',
                           workQueue = WorkQueue finalWq,
                           activeNodes =
                             ActiveNodes (S.union newIntermediateActives
                                                  activeNodes)
                         }
      in
      let maybeAnswerEdge = do
            let (RegularEdge (Edge n1 sa n2), _) = work
            guard $ sa == Nop
            let maybeQuestionFromInternalNode internalNode =
                  case internalNode of
                    UserNode n -> return $ Question n []
                    IntermediateNode actionList (StaticDestination dest) ->
                      do
                        Question n' actions <-
                          maybeQuestionFromInternalNode dest
                        return $ Question n' (actionList ++ actions)
                    IntermediateNode _ (DynamicDestination _) -> mzero
            question <- maybeQuestionFromInternalNode n1
            let Questions qs = getQuestions analysis
            guard $ S.member question qs
            let UserNode dest = n2
            return (question, dest)
      in
      (resultAnalysis, maybeAnswerEdge)

-- USER
fullClosure :: (Spec a) => Analysis a -> Analysis a
fullClosure analysis =
  let doTargetedDynPop = getTargetedDynPop analysis in
  let (analysis', _) = closureStep analysis in
  let WorkQueue wq' = getWorkQueue analysis' in
  if (null wq') then analysis' else fullClosure analysis'

-- TODO: Yet another dictionary keeping track of edges in the graph with inactive
-- sources so that we can dump them into workQueue when their source becomes active
addAnalysisEdge :: (Spec a) => GeneralEdges a -> Analysis a -> Analysis a
addAnalysisEdge edge analysis =
  -- Check whether the "new" edge is already seen
  let g = getGraph analysis in
  case edge of
    RegularEdge (e@(Edge src sa dest)) ->
  -- If it's already in the graph, it means we have already processed the edge, so skip
      if S.member e (getEdges g) then analysis else
        -- If it's not present in the graph, we need to check for its active status
        let WorkQueue wq = getWorkQueue analysis in
        let ActiveNodes activeNodes = getActiveNodes analysis in
        -- We will need to add it to the graph either way, so construct the new graph upfront
        let g' = PdsReachability.Structure.addEdge e g in
        -- If the source of new edge is active, we add it to the workqueue
        if (S.member src activeNodes) then
          let History history = getHistory analysis in
          let history' = S.insert edge history in
          let wq' = Q.pushBack wq edge in
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
                  let newEntry = S.insert edge curEntry in
                  M.adjust (\_ -> newEntry) src waitlist
                else
                  M.insert src (S.singleton edge) waitlist
          in
          analysis { graph = g',
                     waitlist = Waitlist waitlist' }
    UntargetedEdge (e@(UntargetedDynPopEdge src pa)) ->
      if S.member e (getUntargetedDynPopEdges g) then analysis else
        -- If it's not present in the graph, we need to check for its active status
        let WorkQueue wq = getWorkQueue analysis in
        let ActiveNodes activeNodes = getActiveNodes analysis in
        -- We will need to add it to the graph either way, so construct the new graph upfront
        let g' = addUntargetedDynPopEdge e g in
        -- If the source of new edge is active, we add it to the workqueue
        if (S.member src activeNodes) then
          let History history = getHistory analysis in
          let history' = S.insert edge history in
          let wq' = Q.pushBack wq edge in
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
                  let newEntry = S.insert edge curEntry in
                  M.adjust (\_ -> newEntry) src waitlist
                else
                  M.insert src (S.singleton edge) waitlist
          in
          analysis { graph = g',
                     waitlist = Waitlist waitlist' }

addAnalysisEdges :: (Spec a) => [GeneralEdges a] -> Analysis a -> Analysis a
addAnalysisEdges edges analysis = L.foldl (flip addAnalysisEdge) analysis edges
