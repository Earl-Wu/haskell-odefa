{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
module PlumeAnalysis.PlumeAnalysis where

import AST.AbstractAstUtils
import AST.Ast
import qualified PlumeAnalysis.Context as C
import PdsReachability.Reachability
import PdsReachability.Specification
import PdsReachability.Structure
import PlumeAnalysis.Pds.PdsEdgeFunctions
import PlumeAnalysis.Pds.PlumePdsStructureTypes
import PlumeAnalysis.PlumeSpecification
import PlumeAnalysis.Types.PlumeGraph
import PlumeAnalysis.Utils.PlumeUtils

import Control.Monad
import Data.Function
import qualified Data.Either as E
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Multimap as MM
import qualified Data.Maybe as MB
import qualified Data.Dequeue as Q

-- TODO: Don't keep this
plumeTargetedDynPop ::
  TargetedDynPop (PlumePds context) ->
  Element (PlumePds context) ->
  [Path (PlumePds context)]
plumeTargetedDynPop targetedDynPop element = undefined

plumeUntargetedDynPop ::
  UntargetedDynPop (PlumePds context) ->
  Element (PlumePds context) ->
  [(Path (PlumePds context), Terminus (PlumePds context))]
plumeUntargetedDynPop untargetedDynPop element = undefined

type Lookup context = (AbstractVar, context, (S.Set Pattern), (S.Set Pattern))

data ArgState context
  = ValueFound
  | ValueNotFound [(PlumeAnalysis context) -> ((PlumeAnalysis context), [CFGEdge context])]

data PlumeAnalysis context =
  PlumeAnalysis
    { plumeGraph :: CFG context
    , pdsReachability :: Analysis (PlumePds context)
    , plumeActiveNodes :: S.Set (CFGNode context)
    , plumeEdgesWorklist :: Q.BankersDequeue (CFGEdge context)
    , plumeArgMap :: M.Map (Lookup context) (ArgState context)
    , plumeWireMap :: M.Map (Lookup context) [AbstractValue -> CFG context -> Maybe ([CFGEdge context], CFGNode context, CFGNode context, CFGNode context)]
    , plumePredsPeerMap :: MM.Multimap S.Set (CFGNode context) (CFGNode context)
    , plumeSuccsPeerMap :: MM.Multimap S.Set (CFGNode context) (CFGNode context)
    -- , plumeLoggingData :: Maybe (PlumeAnalysisLoggingData)
    }

-- getSize ::
--   (C.Context context) =>
--   PlumeAnalysis context -> (Int, Int, Int, Int, Int)
-- getSize analysis =
--   let (pdsNodeCount, pdsEdgeCount) =
--         PdsReachability.Reachability.getSize (pdsReachability analysis)
--   in
--   let filterInferrableNodes nodes =
--         nodes
--         & S.filter
--           (\(CFGNode cls _) -> case cls of
--                   EnterClause _ _ _ -> False
--                   ExitClause _ _ _ -> False
--                   otherwise -> True)
--   in
--   let cfgNodeCount = S.size (filterInferrableNodes (plumeActiveNodes analysis)) in
--   let cfgEdgeCount = S.size (allCFGEdges (plumeGraph analysis)) in
--   (cfgNodeCount, -1, cfgEdgeCount, pdsNodeCount, pdsEdgeCount)

addOneEdge ::
  (C.Context context) =>
  CFGEdge context ->
  PlumeAnalysis context ->
  (PlumeAnalysis context, S.Set (CFGNode context))
addOneEdge edgeIn analysis =
  if hasEdge edgeIn (plumeGraph analysis)
  then (analysis, S.empty)
  else
    let plumeGraph' = PlumeAnalysis.Types.PlumeGraph.addEdge edgeIn (plumeGraph analysis) in
    let CFGEdge n1 n2 = edgeIn in
    let workList' =
          let newEdgesFromPreds =
                MM.find n2 (plumePredsPeerMap analysis)
                & S.map (\n -> CFGEdge n1 n)
          in
          let newEdgesFromSuccs =
                MM.find n2 (plumeSuccsPeerMap analysis)
                & S.map (\n -> CFGEdge n n2)
          in
          S.foldl Q.pushBack (plumeEdgesWorklist analysis) (S.union newEdgesFromPreds newEdgesFromSuccs)
    in
    let targetClass = ProgramPointState n2 in
    let pdsReachability' =
          pdsReachability analysis
          & addEdgeFunction (Just targetClass) (createEdgeFunction edgeIn)
    in
    let findNewActiveNodes fromNodesList resultSoFar =
          case fromNodesList of
            [] -> resultSoFar
            fromNode : fromNodesTail ->
              if S.member fromNode (plumeActiveNodes analysis) ||
                 S.member fromNode resultSoFar
              then findNewActiveNodes fromNodesTail resultSoFar
              else
                let resultSoFar' = S.insert fromNode resultSoFar in
                let fromHere = plumeGraph' & succs fromNode in
                findNewActiveNodes
                  (S.toList fromHere ++ fromNodesTail)
                  resultSoFar'
    in
    let (plumeActiveNodes', plumeActiveNonImmediateNodes') =
          let maybeNewActiveRootNode =
                let (CFGEdge nodeLeft nodeRight) = edgeIn in
                if S.notMember nodeLeft (plumeActiveNodes analysis)
                then Just nodeRight
                else Nothing
          in
          let newActiveNodes =
                case maybeNewActiveRootNode of
                  Nothing -> S.empty
                  Just node -> findNewActiveNodes [node] S.empty
          in
          let isNodeImmediate (CFGNode clause _) = isImmediate clause in
          (
            S.union (plumeActiveNodes analysis) newActiveNodes,
            newActiveNodes & S.filter (not . isNodeImmediate)
          )
    in
    let retAnalysis = PlumeAnalysis
          { plumeGraph = plumeGraph'
          , pdsReachability = pdsReachability'
          , plumeActiveNodes = plumeActiveNodes'
          , plumeEdgesWorklist = workList'
          , plumeArgMap = (plumeArgMap analysis)
          , plumeWireMap = (plumeWireMap analysis)
          , plumePredsPeerMap = (plumePredsPeerMap analysis)
          , plumeSuccsPeerMap = (plumeSuccsPeerMap analysis)
          }
    in (retAnalysis, plumeActiveNonImmediateNodes')

createInitialAnalysis ::
  forall context.
  (C.Context context) =>
  ConcreteExpr -> Either AbstractInterpreterError (PlumeAnalysis context)
createInitialAnalysis e =
  let Expr cls = liftExpr e in
  do
    rx <- rv cls
    let nodes =
          cls
          & L.map (\x -> CFGNode (UnannotatedClause x) C.empty) -- FIXME: What to do with empty contexts?
          & (\tl -> (CFGNode (StartClause rx) C.empty) : tl)
          & flip (++) [CFGNode (EndClause rx) C.empty]
    let edges = edgesFromNodeList nodes
    let initialReachability =
          emptyAnalysis id plumeTargetedDynPop plumeUntargetedDynPop
          & addEdgeFunction Nothing
              (EdgeFunction $ \state ->
                  [(Path [Pop $ BottomOfStack], StaticTerminus state)])
    return $ PlumeAnalysis
          { plumeGraph = emptyCFG
          , pdsReachability = initialReachability
          , plumeActiveNodes = S.singleton (CFGNode (StartClause rx) C.empty)
          , plumeEdgesWorklist = Q.fromList (S.toList edges)
          , plumeArgMap = M.empty
          , plumeWireMap = M.empty
          , plumePredsPeerMap = MM.empty
          , plumeSuccsPeerMap = MM.empty
          }

prepareQuestion ::
  (C.Context context) =>
  AbstractVar ->
  AnnotatedClause ->
  context ->
  S.Set Pattern ->
  S.Set Pattern ->
  PlumeAnalysis context ->
  PlumeAnalysis context
prepareQuestion x acl ctx patsp patsn analysis =
  let startNode = CFGNode acl ctx in
  let startState = ProgramPointState startNode in
  let startActions = [Push BottomOfStack, Push (LookupVar x patsp patsn)] in
  let question = Question startState startActions in
  let reachability = pdsReachability analysis in
  let reachability' =
        addQuestion question reachability
  in
  analysis { pdsReachability = reachability' }

askQuestion ::
  (C.Context context) =>
  AbstractVar ->
  AnnotatedClause ->
  context ->
  S.Set Pattern ->
  S.Set Pattern ->
  PlumeAnalysis context ->
  ([AbsFilteredVal], PlumeAnalysis context)
askQuestion x acl ctx patsp patsn analysis =
  let startNode = CFGNode acl ctx in
  let startState = ProgramPointState startNode in
  let startActions = [Push BottomOfStack, Push (LookupVar x patsp patsn)] in
  let question = Question startState startActions in
  let reachability = pdsReachability analysis in
  let reachableStates = getReachableNodes question reachability in
  let values =
        case reachableStates of
          Nothing -> []
          Just vals -> MB.mapMaybe
                        (\val -> case val of ProgramPointState _ -> Nothing
                                             ResultState v -> Just v) vals
  in (values, analysis)

contextlessRestrictedValuesOfVariableWithoutClosure ::
  (C.Context context) =>
  AbstractVar ->
  AnnotatedClause ->
  S.Set Pattern ->
  S.Set Pattern ->
  PlumeAnalysis context ->
  ([AbsFilteredVal], PlumeAnalysis context)
contextlessRestrictedValuesOfVariableWithoutClosure x acl patsp patsn analysis =
  let analysis' = prepareQuestion x acl C.empty patsp patsn analysis in
  askQuestion x acl C.empty patsp patsn analysis'

analyzeNote ::
  (C.Context context) =>
  (Question (PlumePds context), PdsState context) ->
  Maybe ((AbstractVar, context, S.Set Pattern, S.Set Pattern), AbstractValue)
analyzeNote note =
  let (Question startNode stackActions, endNode) = note in
  do -- Maybe
    -- Note: binding direct returns here to take advantage of Nothing on pattern
    -- match failures.
    (Push BottomOfStack) :
      (Push (LookupVar x patsp patsn)) :
      [] <- return stackActions
    ProgramPointState (CFGNode acl context) <- return startNode
    ResultState filterVarVal <- return endNode
    let AbsFilteredVal varVal _ _ = filterVarVal
    return ((x, context, patsp, patsn), varVal)

handleArgumentMap ::
  (C.Context context) =>
  (Lookup context) ->
  PlumeAnalysis context ->
  (PlumeAnalysis context, [CFGEdge context])
handleArgumentMap relevantPair analysis =
  let argMap = plumeArgMap analysis in
  if M.member relevantPair argMap
  then
    let relevantArgFuns = argMap M.! relevantPair in
    let (argFuns, argMap') =
          case relevantArgFuns of
            ValueFound -> ([], argMap)
            ValueNotFound funList ->
              let newArgMap = M.insert relevantPair ValueFound argMap in
              (funList, newArgMap)
    in
    let analysis' = analysis { plumeArgMap = argMap' } in
    let (resAnalysis, newEdges) =
          L.foldl
            (\acc -> \argFun ->
              let (currAnalysis, edges) = acc in
              let (currAnalysis', edges') = argFun currAnalysis in
              (currAnalysis', edges ++ edges')
            ) (analysis', []) argFuns
    in
    (resAnalysis, newEdges)
  else (analysis, [])

handleWireMap ::
  (C.Context context) =>
  (Lookup context) ->
  AbstractValue ->
  PlumeAnalysis context ->
  ([CFGEdge context], PlumeAnalysis context)
handleWireMap relevantPair varVal analysis =
  let wireMap = plumeWireMap analysis in
  let predsPeerMap = plumePredsPeerMap analysis in
  let succsPeerMap = plumeSuccsPeerMap analysis in
  let g = plumeGraph analysis in
  if M.member relevantPair wireMap
  then
    let relevantWireFuns = wireMap M.! relevantPair in
    let (totalNewEdges, newPredsPeerMap, newSuccsPeerMap) =
          let foldFun acc wireFun =
                let (accEdges, accPredsPeerMap, accSuccsPeerMap) = acc in
                let wireFunRes = wireFun varVal g in
                case wireFunRes of
                  Nothing -> acc
                  Just (wireEdges, wireCurrNode, wirePredsPeer, wireSuccsPeer) ->
                    let accEdges' = accEdges ++ wireEdges in
                    let accPredsPeerMap' =
                          MM.append wireCurrNode wirePredsPeer accPredsPeerMap
                    in
                    let accSuccsPeerMap' =
                          MM.append wireCurrNode wireSuccsPeer accPredsPeerMap
                    in
                    (accEdges', accPredsPeerMap', accSuccsPeerMap')
          in
          L.foldl foldFun ([], predsPeerMap, succsPeerMap) relevantWireFuns
    in
    let analysis' = analysis { plumePredsPeerMap = newPredsPeerMap
                             , plumeSuccsPeerMap = newSuccsPeerMap }
    in (totalNewEdges, analysis')
  else ([], analysis)

pdsClosureStep ::
  (C.Context context) =>
  PlumeAnalysis context ->
  PlumeAnalysis context
pdsClosureStep analysis =
  let reachability = pdsReachability analysis in
  let (reachability', lazyNote) = closureStep reachability in
  let analysis' = analysis { pdsReachability = reachability' } in
  case lazyNote of
    Nothing -> analysis'
    Just note ->
      let contentMb = analyzeNote note in
      case contentMb of
        Just content ->
          let (relevantPair, varVal) = content in
          let (hamAnalysis, argFunEdges) =
                handleArgumentMap relevantPair analysis'
          in
          let (functionFunEdges, hwmAnalysis) =
                handleWireMap relevantPair varVal hamAnalysis
          in
          let totalEdges = argFunEdges ++ functionFunEdges in
          let plumeEdgesWorklist' =
                L.foldl Q.pushBack (plumeEdgesWorklist analysis) totalEdges
          in
          hwmAnalysis { plumeEdgesWorklist = plumeEdgesWorklist' }
        Nothing -> analysis'

pdsClosure ::
  (C.Context context) =>
  PlumeAnalysis context ->
  PlumeAnalysis context
pdsClosure analysis =
  let reachability = pdsReachability analysis in
  if (isClosed reachability) then analysis else pdsClosure $ pdsClosureStep analysis

executeWireFuns ::
  (C.Context context) =>
  PlumeAnalysis context ->
  [AbstractValue] ->
  Lookup context ->
  (PlumeAnalysis context, [CFGEdge context])
executeWireFuns analysis valuesForWire wireLookupKey =
  if (L.null valuesForWire) then (analysis, [])
  else
    let wireFunctions = (plumeWireMap analysis) M.! wireLookupKey in
    let (newEdges, newPreds, newSuccs) =
          wireFunctions
          & L.map
            (\wiringFun ->
                valuesForWire
                & MB.mapMaybe (\valueFound ->
                                  wiringFun valueFound (plumeGraph analysis))
            )
          & L.concat
          & L.foldl
            (\(edgeList, predsPeers, succsPeers) ->
             \(currEdges, currCallSite, currEnter, currExit) ->
                (edgeList ++ currEdges,
                 MM.append currCallSite currEnter predsPeers,
                 MM.append currCallSite currExit succsPeers
                )
            ) ([], plumePredsPeerMap analysis, plumeSuccsPeerMap analysis)
    in
    let analysis' = analysis { plumePredsPeerMap = newPreds
                             , plumeSuccsPeerMap = newSuccs }
    in (analysis', newEdges)
