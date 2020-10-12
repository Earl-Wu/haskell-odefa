{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
module PlumeAnalysis.PlumeAnalysis where

import AST.AbstractAst
import AST.Ast
import AST.AstUtils
import qualified PlumeAnalysis.Context as C
import PdsReachability
import PlumeAnalysis.Pds.PdsEdgeFunctions
import PlumeAnalysis.Pds.PlumePdsDynamicPopHandler
import PlumeAnalysis.Pds.PlumePdsStructureTypes
import PlumeAnalysis.PlumeSpecification
import PlumeAnalysis.Types.PlumeGraph
import PlumeAnalysis.Utils.PlumeUtils

import Control.DeepSeq
import Control.Monad
import Data.Function
import qualified Data.Either as E
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Multimap as MM
import qualified Data.Maybe as MB
import qualified Data.Dequeue as Q

type Lookup context = (AbstractVar, context, (S.Set Pattern), (S.Set Pattern))

type WireFunction context = AbstractValue -> CFG context -> Maybe (S.Set (CFGEdge context), CFGNode context, CFGNode context, CFGNode context)

data ArgState context
  = ValueFound
  | ValueNotFound [(PlumeAnalysis context) -> ((PlumeAnalysis context), S.Set (CFGEdge context))]

data PlumeAnalysis context =
  PlumeAnalysis
    { plumeGraph :: CFG context
    , plumeExpression :: ConcreteExpr
    , pdsReachability :: Analysis (PlumePds context)
    , plumeActiveNodes :: S.Set (CFGNode context)
    , plumeEdgesWorklist :: Q.BankersDequeue (CFGEdge context)
    , plumeArgMap :: M.Map (Lookup context) (ArgState context)
    , plumeWireMap :: MM.Multimap [] (Lookup context) (WireFunction context)
    , plumePredsPeerMap :: MM.Multimap S.Set (CFGNode context) (CFGNode context)
    , plumeSuccsPeerMap :: MM.Multimap S.Set (CFGNode context) (CFGNode context)
    -- , plumeLoggingData :: Maybe (PlumeAnalysisLoggingData)
    }

instance NFData (PlumeAnalysis context) where
  rnf plumeAnalysis =
    seq (plumeGraph plumeAnalysis) $
    seq (plumeExpression plumeAnalysis) $
    seq (pdsReachability plumeAnalysis) $
    seq (plumeActiveNodes plumeAnalysis) $
    seq (plumeEdgesWorklist plumeAnalysis) $
    seq (plumeArgMap plumeAnalysis) $
    seq (plumeWireMap plumeAnalysis) $
    seq (plumePredsPeerMap plumeAnalysis) $
    seq (plumeSuccsPeerMap plumeAnalysis) $
    ()

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
                MM.find n1 (plumeSuccsPeerMap analysis)
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
                let fromHere = succs fromNode plumeGraph' in
                findNewActiveNodes
                  (S.toList fromHere ++ fromNodesTail)
                  resultSoFar'
    in
    let (plumeActiveNodes', plumeActiveNonImmediateNodes') =
          let maybeNewActiveRootNode =
                let (CFGEdge nodeLeft nodeRight) = edgeIn in
                if S.notMember nodeRight (plumeActiveNodes analysis)
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
             S.filter (not . isNodeImmediate) newActiveNodes
          )
    in
    let retAnalysis = analysis
          { plumeGraph = plumeGraph'
          , pdsReachability = pdsReachability'
          , plumeActiveNodes = plumeActiveNodes'
          , plumeEdgesWorklist = workList'
          }
    in (retAnalysis, plumeActiveNonImmediateNodes')

createInitialAnalysis ::
  forall context.
  (C.Context context) =>
  context -> ConcreteExpr -> PlumeAnalysis context
createInitialAnalysis emptyCtx e =
  let Expr cls = transform e in
  let rx = rv cls in
  let nodes =
        cls
        & L.map (\x -> CFGNode (UnannotatedClause x) emptyCtx) -- FIXME: What to do with empty contexts?
        & (\tl -> (CFGNode (StartClause rx) emptyCtx) : tl)
        & flip (++) [CFGNode (EndClause rx) emptyCtx]
  in
  let edges = edgesFromNodeList nodes in
  let initialReachability =
        emptyAnalysis id plumeTargetedDynPop plumeUntargetedDynPop
        & addEdgeFunction Nothing
            (EdgeFunction $ \state ->
                [(Path [Pop $ BottomOfStack], StaticTerminus state)])
  in
  PlumeAnalysis
    { plumeGraph = emptyCFG
    , plumeExpression = e
    , pdsReachability = initialReachability
    , plumeActiveNodes = S.singleton (CFGNode (StartClause rx) emptyCtx)
    , plumeEdgesWorklist = Q.fromList (S.toList edges)
    , plumeArgMap = M.empty
    , plumeWireMap = MM.empty
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

restrictedValuesOfVariableInternal ::
  (C.Context context) =>
  AbstractVar ->
  AnnotatedClause ->
  context ->
  S.Set Pattern ->
  S.Set Pattern ->
  PlumeAnalysis context ->
  ([AbsFilteredVal], PlumeAnalysis context)
restrictedValuesOfVariableInternal x acl ctx patsp patsn analysis =
  let analysis' = prepareQuestion x acl ctx patsp patsn analysis in
  askQuestion x acl ctx patsp patsn analysis'

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
  (PlumeAnalysis context, S.Set (CFGEdge context))
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
              (currAnalysis', S.union edges edges')
            ) (analysis', S.empty) argFuns
    in
    (resAnalysis, newEdges)
  else (analysis, S.empty)

handleWireMap ::
  (C.Context context) =>
  (Lookup context) ->
  AbstractValue ->
  PlumeAnalysis context ->
  (S.Set (CFGEdge context), PlumeAnalysis context)
handleWireMap relevantPair varVal analysis =
  let wireMap = plumeWireMap analysis in
  let predsPeerMap = plumePredsPeerMap analysis in
  let succsPeerMap = plumeSuccsPeerMap analysis in
  let g = plumeGraph analysis in
  if MM.member relevantPair wireMap
  then
    let relevantWireFuns = wireMap MM.! relevantPair in
    let (totalNewEdges, newPredsPeerMap, newSuccsPeerMap) =
          let foldFun acc wireFun =
                let (accEdges, accPredsPeerMap, accSuccsPeerMap) = acc in
                let wireFunRes = wireFun varVal g in
                case wireFunRes of
                  Nothing -> acc
                  Just (wireEdges, wireCurrNode, wirePredsPeer, wireSuccsPeer) ->
                    let accEdges' = S.union accEdges wireEdges in
                    let accPredsPeerMap' =
                          MM.append wireCurrNode wirePredsPeer accPredsPeerMap
                    in
                    let accSuccsPeerMap' =
                          MM.append wireCurrNode wireSuccsPeer accSuccsPeerMap
                    in
                    (accEdges', accPredsPeerMap', accSuccsPeerMap')
          in
          L.foldl foldFun (S.empty, predsPeerMap, succsPeerMap) relevantWireFuns
    in
    let analysis' = analysis { plumePredsPeerMap = newPredsPeerMap
                             , plumeSuccsPeerMap = newSuccsPeerMap }
    in (totalNewEdges, analysis')
  else (S.empty, analysis)

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
          let totalEdges = S.union argFunEdges functionFunEdges in
          let plumeEdgesWorklist' =
                S.foldl Q.pushBack (plumeEdgesWorklist analysis) totalEdges
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
  (PlumeAnalysis context, S.Set (CFGEdge context))
executeWireFuns analysis valuesForWire wireLookupKey =
  if (L.null valuesForWire) then (analysis, S.empty)
  else
    let wireFunctions = (plumeWireMap analysis) MM.! wireLookupKey in
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
                (S.union edgeList currEdges,
                 MM.append currCallSite currEnter predsPeers,
                 MM.append currCallSite currExit succsPeers
                )
            ) (S.empty, plumePredsPeerMap analysis, plumeSuccsPeerMap analysis)
    in
    let analysis' = analysis { plumePredsPeerMap = newPreds
                             , plumeSuccsPeerMap = newSuccs }
    in (analysis', newEdges)

addMappingToWireMap ::
  (C.Context context) =>
  MM.Multimap [] (Lookup context) (WireFunction context) ->
  Lookup context ->
  WireFunction context ->
  MM.Multimap [] (Lookup context) (WireFunction context)
addMappingToWireMap currWireMap lookupKey responseFun =
  MM.append lookupKey responseFun currWireMap

cfgClosureStep ::
  (C.Context context) =>
  PlumeAnalysis context ->
  PlumeAnalysis context
cfgClosureStep analysis =
  let workList = plumeEdgesWorklist analysis
  in
  if (Q.null workList) then analysis
  else
    let qFrontMb = Q.popFront workList in
    let (newAnalysis, newNiNodes) =
          case qFrontMb of
            Just (edgeToAdd, worklist') ->
              let preAnalysis = analysis { plumeEdgesWorklist = worklist' } in
              addOneEdge edgeToAdd preAnalysis
            Nothing -> undefined
    in
    let nodeProcessFun accAnalysis node =
          let argMap = plumeArgMap accAnalysis in
          let CFGNode acl ctx = node in
          case acl of
            UnannotatedClause (absCls@(Clause clauseName (ApplBody applFun applArg annots))) ->
              let argumentValueResponse =
                    \currAnalysis ->
                      let functionValueResponse value graph =
                            case value of
                              AbsValueFunction funVal ->
                                let acontextualCall =
                                      case (csaContextuality annots) of
                                        CallSiteContextual -> False
                                        CallSiteAcontextual -> True
                                        CallSiteAcontextualFor vars ->
                                          let FunctionValue (Var param) _ = funVal in
                                          S.member param vars
                                in
                                let newCtx =
                                      if acontextualCall then ctx
                                      else C.add absCls ctx
                                in
                                let wireResult =
                                      wireFun newCtx node funVal applArg clauseName graph
                                in
                                Just wireResult
                              otherwise -> Nothing
                      in
                      let oldWireMap = plumeWireMap currAnalysis in
                      let funLookupKey = (applFun, ctx, S.empty, S.empty) in
                      let newWireMap = addMappingToWireMap oldWireMap funLookupKey functionValueResponse
                      in
                      let (lookupRes, analysis') =
                            restrictedValuesOfVariableInternal applFun acl ctx S.empty S.empty currAnalysis
                      in
                      let valuesOfFun =
                            L.foldl (\currValList -> \currRes ->
                                        case currRes of
                                          AbsFilteredVal v _ _ -> v : currValList
                                    ) [] lookupRes
                      in
                      let analysis'' = analysis' { plumeWireMap = newWireMap } in
                      executeWireFuns analysis'' valuesOfFun funLookupKey
              in
              let argLookupKey = (applArg, ctx, S.empty, S.empty) in
              if (M.member argLookupKey argMap)
              then
                let action = argMap M.! (applArg, ctx, S.empty, S.empty)
                in
                case action of
                  ValueFound ->
                    let (accAnalysis', edgesToAdd) =
                          argumentValueResponse accAnalysis
                    in
                    let newWorklist = S.foldl Q.pushBack (plumeEdgesWorklist accAnalysis) edgesToAdd in
                    let accAnalysis'' = accAnalysis' { plumeEdgesWorklist = newWorklist }
                    in
                    accAnalysis''
                  ValueNotFound fList ->
                    let modifiedArgMap =
                          M.update (\_ -> Just $ ValueNotFound $ argumentValueResponse : fList) argLookupKey argMap
                    in
                    let accAnalysis' = accAnalysis { plumeArgMap = modifiedArgMap }
                    in
                    accAnalysis'
              else
                let (applArgLookupres, accAnalysis') =
                      restrictedValuesOfVariableInternal applArg acl ctx S.empty S.empty accAnalysis
                in
                if (L.null applArgLookupres)
                then
                  let newArgMap =
                        M.insert argLookupKey (ValueNotFound [argumentValueResponse]) argMap
                  in
                  let accAnalysis'' = accAnalysis' { plumeArgMap = newArgMap }
                  in accAnalysis''
                else
                  let (accAnalysis'', edgesToAdd) =
                        argumentValueResponse accAnalysis'
                  in
                  let newWorklist =
                        S.foldl Q.pushBack (plumeEdgesWorklist accAnalysis) edgesToAdd
                  in
                  let newArgMap =
                        M.insert argLookupKey ValueFound argMap
                  in
                  let accAnalysis''' =
                        accAnalysis'' { plumeEdgesWorklist = newWorklist
                                      , plumeArgMap = newArgMap
                                      }
                  in
                  accAnalysis'''
            UnannotatedClause (absCls@(Clause x1 (ConditionalBody subject pattern f1 f2))) ->
              let oldWireMap = plumeWireMap analysis in
              let posmatchLookupKey = (subject, ctx, S.singleton pattern, S.empty)
              in
              let negmatchLookupKey = (subject, ctx, S.empty, S.singleton pattern)
              in
              let condSetPosResponse resVal graph =
                    let _ = resVal in
                    Just $ wireCond node f1 subject x1 graph
              in
              let condSetNegResponse resVal graph =
                    let _ = resVal in
                    Just $ wireCond node f2 subject x1 graph
              in
              let wireMapWPos =
                    addMappingToWireMap oldWireMap posmatchLookupKey condSetPosResponse
              in
              let wireMapWNeg =
                    addMappingToWireMap wireMapWPos negmatchLookupKey condSetNegResponse
              in
              let analysisWNewWireMap = accAnalysis { plumeWireMap = wireMapWNeg }
              in
              let (posLookupRes, posLookupAnalysis) =
                    restrictedValuesOfVariableInternal subject acl ctx (S.singleton pattern) S.empty analysisWNewWireMap
              in
              let valuesOfPosmatch =
                    L.foldl (\currValList -> \currRes ->
                                case currRes of
                                  AbsFilteredVal v _ _ -> v : currValList
                            ) [] posLookupRes
              in
              let (execPosAnalysis, posNewEdges) =
                    executeWireFuns posLookupAnalysis valuesOfPosmatch posmatchLookupKey
              in
              let (patsnLookupRes, patsnLookupAnalysis) =
                    restrictedValuesOfVariableInternal subject acl ctx S.empty (S.singleton pattern) execPosAnalysis
              in
              let valuesOfNegMatch =
                    L.foldl (\currValList -> \currRes ->
                                case currRes of
                                  AbsFilteredVal v _ _ -> v : currValList
                            ) [] patsnLookupRes
              in
              let (execNegAnalysis, negNewEdges) =
                    executeWireFuns patsnLookupAnalysis valuesOfNegMatch negmatchLookupKey
              in
              let totalNewEdges = L.foldl Q.pushBack (plumeEdgesWorklist execNegAnalysis) (S.union posNewEdges negNewEdges)
              in
              execNegAnalysis { plumeEdgesWorklist = totalNewEdges }
            otherwise -> undefined
    in 
    S.foldl nodeProcessFun newAnalysis newNiNodes

performClosureSteps ::
  (C.Context context) =>
  PlumeAnalysis context ->
  PlumeAnalysis context
performClosureSteps analysis =
  let postCfgAnalysis = cfgClosureStep analysis in
  let postPdsStepsAnalysis = pdsClosure postCfgAnalysis in
  postPdsStepsAnalysis

isFullyClosed ::
  (C.Context context) =>
  PlumeAnalysis context ->
  Bool
isFullyClosed analysis =
  Q.null (plumeEdgesWorklist analysis) &&
  isClosed (pdsReachability analysis)

performFullClosure ::
  (C.Context context) =>
  PlumeAnalysis context ->
  PlumeAnalysis context
performFullClosure analysis =
  if isFullyClosed analysis then analysis
  else
    performFullClosure $ performClosureSteps analysis

restrictedValuesOfVariableWithClosure ::
  (C.Context context) =>
  AbstractVar ->
  AnnotatedClause ->
  context ->
  S.Set Pattern ->
  S.Set Pattern ->
  PlumeAnalysis context ->
  ([AbsFilteredVal], PlumeAnalysis context)
restrictedValuesOfVariableWithClosure x acl ctx patsp patsn analysis =
  let analysis' = prepareQuestion x acl ctx patsp patsn analysis in
  let analysis'' = performFullClosure analysis' in
  askQuestion x acl ctx patsp patsn analysis''

valuesOfVariable ::
  (C.Context context) =>
  AbstractVar ->
  AnnotatedClause ->
  PlumeAnalysis context ->
  (S.Set AbsFilteredVal, PlumeAnalysis context)
valuesOfVariable x acl analysis =
  let (valLst, analysis') = restrictedValuesOfVariableWithClosure x acl C.empty S.empty S.empty analysis in
  (S.fromList valLst, analysis')
  
contextualValuesOfVariable ::
  (C.Context context) =>
  AbstractVar ->
  AnnotatedClause ->
  context ->
  PlumeAnalysis context ->
  (S.Set AbsFilteredVal, PlumeAnalysis context)
contextualValuesOfVariable x acl ctx analysis =
  let (valLst, analysis') = restrictedValuesOfVariableWithClosure x acl ctx S.empty S.empty analysis in
  (S.fromList valLst, analysis')
