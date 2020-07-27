module PlumeAnalysis.Pds.PlumePdsDynamicPopHandler where

import Control.Exception
import Control.Monad
import Data.Function
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S

import AST.Ast
import AST.AbstractAst
import PdsReachability
import PlumeAnalysis.Pds.PlumePdsDynamicPopTypes
import PlumeAnalysis.Pds.PlumePdsStructureTypes
import PlumeAnalysis.PlumeSpecification
import PlumeAnalysis.Utils.PlumeUtils
import Utils.Exception

plumeTargetedDynPop ::
  TargetedDynPop (PlumePds context) ->
  PdsContinuation context ->
  [Path (PlumePds context)]
plumeTargetedDynPop action element =
  case action of
    ValueDrop ->
      case element of
        ContinuationValue _ -> []
        otherwise -> mzero
    ValueDiscovery2of2 ->
      case element of
        BottomOfStack -> []
        otherwise -> mzero
    VariableAliasing x2 x1 ->
      case element of
        LookupVar x' patsp patsn ->
          if (x' == x2)
          then return $ Path $ [Push $ LookupVar x1 patsp patsn]
          else mzero
        otherwise -> mzero
    StatelessNonmatchingClauseSkip1of2 x'' ->
      case element of
        LookupVar x _ _ ->
          if (not (x == x''))
          then return $ Path $ [DynamicPop $ StatelessNonmatchingClauseSkip2of2 element]
          else mzero
    StatelessNonmatchingClauseSkip2of2 element' ->
      return $ Path $ [Push element, Push element']
    ValueCapture1of3 ->
      case element of
        ContinuationValue absFilteredVal ->
          return $ Path $ [DynamicPop $ ValueCapture2of3 absFilteredVal]
        otherwise -> mzero
    ValueCapture2of3 fv ->
      case element of
        Capture size ->
          return $ Path $ [DynamicPop $ ValueCapture3of3 fv [] size]
        otherwise -> mzero
    ValueCapture3of3 fv collectedElements size ->
      let CaptureSize n = size in
      if n > 1
      then
        let size' = CaptureSize (n-1) in
        return $ Path $ [DynamicPop $ ValueCapture3of3 fv (element : collectedElements) size']
      else
        let pushes =
              L.map (\x -> Push x) (element : collectedElements)
        in
        return $ Path $ (Push (ContinuationValue fv) : pushes)
    FunctionClosureLookup x'' xf ->
      case element of
        LookupVar x _ _ ->
          if (x == x'')
          then return $ Path $ [Push element, Push $ LookupVar xf S.empty S.empty]
          else mzero
        otherwise -> mzero
    ConditionalClosureLookup x' x1 pat positiveSide ->
      case element of
        LookupVar x patsp patsn ->
          if (not $ x == x' || x == x1)
          then return $ Path $ [Push element]
          else
            let (patsp', patsn') =
                  if positiveSide
                  then (S.insert pat patsp, patsn)
                  else (patsp, S.insert pat patsn)
            in
            return $ Path $ [Push $ LookupVar x1 patsp' patsn']
        otherwise -> mzero
    RecordProjectionLookup x x' l ->
      case element of
        LookupVar x0 patsp patsn ->
          if (x0 == x)
          then return $ Path $ [Push $ Project l patsp patsn, Push $ LookupVar x' S.empty S.empty]
          else mzero
        otherwise -> mzero
    RecordProjection1of2 ->
      case element of
        ContinuationValue fv ->
          case fv of
            AbsFilteredVal (AbsValueRecord r) patsp patsn ->
              return $ Path $ [DynamicPop $ RecordProjection2of2 r patsp patsn]
            otherwise -> mzero
        otherwise -> mzero
    RecordProjection2of2 (r@(RecordValue m)) patsp0 patsn0 ->
      case element of
        Project l patsp1 patsn1 ->
          if (M.member l m)
          then
            let patCheck =
                  L.all (\pat -> not $ S.member pat patsn0)
                    [RecordPattern M.empty, AnyPattern]
            in
            if (not $ isRecordPatternSet patsp0 && patCheck)
            then throw $ InvariantFailureException "Record projection received a value that doesn't satisfy to the record pattern. This might be an error in the record-value-filter-validation rule (7b at the time of this writing)."
            else
              let patsn2 = negativePatternSetSelection r patsn0 in
              let x' = (M.!) m l in
              let patsp' = S.union patsp1 (patternSetProjection patsp0 l) in
              let patsn' = S.union patsn1 (patternSetProjection patsn2 l) in
              return $ Path $ [Push $ LookupVar x' patsp' patsn']
          else mzero
        otherwise -> mzero
    ImmediateFilterValidation x patsLegal v ->
      case element of
        LookupVar x0 patsp patsn ->
          let patCheck =
                L.all (\pat -> not $ S.member pat patsn)
                  [FunPattern, AnyPattern]
          in
          -- NOTE: Check logic here
          if (x == x0 && (patsp `S.isSubsetOf` patsLegal) && S.disjoint patsn patsLegal && patCheck)
          then
            let absFilteredVal = AbsFilteredVal v S.empty S.empty
            in
            return $ Path $ [Push $ ContinuationValue absFilteredVal]
          else mzero
        otherwise -> mzero
    RecordFilterValidation x r n1 ->
      case element of
        LookupVar x0 patsp0 patsn0 ->
          let patCheck =
                L.all (\pat -> not $ S.member pat patsn0)
                  [RecordPattern M.empty, AnyPattern]
          in
          if (x == x0 && (isRecordPatternSet patsp0) && patCheck)
          then
            let patsn2 = negativePatternSetSelection r patsn0 in
            let patternSetLabels = labelsInPatternSet patsp0 in
            let recordLabels = labelsInRecord r in
            let RecordValue m = r in
            if (patternSetLabels `S.isSubsetOf` recordLabels)
            then
              let makeK'' l =
                    let x'' = (M.!) m l in
                    [Push $ LookupVar x'' (patternSetProjection patsp0 l) (patternSetProjection patsn2 l),
                     Push $ Jump n1]
              in
              let firstPushes =
                    [Push $ ContinuationValue $ AbsFilteredVal (AbsValueRecord r) patsp0 patsn2,
                     Push $ Jump n1]
              in
              let allPushes =
                    recordLabels
                    &S.toList
                    & L.map makeK''
                    & L.concat
                    & (++) firstPushes
              in
              return $ Path $ allPushes
            else mzero
          else mzero
        otherwise -> mzero
    EmptyRecordValueDiscovery x ->
      case element of
        LookupVar x0 patsp patsn ->
          if (x == x0)
          then
            let emptyRecord = AbsValueRecord $ RecordValue M.empty in
            let emptyRecordPattern = RecordPattern M.empty in
            let patList = S.fromList [emptyRecordPattern, AnyPattern] in
            let patCheck =
                  L.all (\pat -> not $ S.member pat patsn)
                    [emptyRecordPattern, AnyPattern]
            in
            if ((patsp `S.isSubsetOf` patList) && patCheck)
            then
              return $ Path $ [Push $ ContinuationValue $ AbsFilteredVal emptyRecord S.empty S.empty]
            else mzero
          else mzero
        otherwise -> mzero
    BinaryOperatorLookupInit x1 x2 x3 n1 n0 ->
      case element of
        LookupVar x1' _ _ ->
          if (x1 == x1')
          then
            let captureSize5 = CaptureSize 5 in
            let captureSize2 = CaptureSize 2 in
            let k1'' = [ Capture captureSize5
                       , LookupVar x2 S.empty S.empty
                       ]
            in
            let k2'' = [ Capture captureSize2
                       , LookupVar x3 S.empty S.empty
                       , Jump n1
                       ]
            in
            let k3'' = [ BinaryOperation
                       , Jump n0
                       ]
            in
            let k0 = [element] in
            return $ Path $ L.map (\x -> Push x) $ k0 ++ k3'' ++ k2'' ++ k1''
          else mzero
        otherwise -> mzero
    UnaryOperatorLookupInit x1 x2 n0 ->
      case element of
        LookupVar x1' _ _ ->
          if (x1 == x1')
          then
            let captureSize2 = CaptureSize 2 in
            let k1'' = [ Capture captureSize2
                       , LookupVar x2 S.empty S.empty ]
            in
            let k2'' = [ UnaryOperation
                       , Jump n0 ]
            in
            let k0 = [element] in
            return $ Path $ L.map (\x -> Push x) $ k0 ++ k2'' ++ k1''
          else mzero
        otherwise -> mzero
    BinaryOperatorResolution1of4 x1 op ->
      case element of
        BinaryOperation ->
          return $ Path $ [DynamicPop $ BinaryOperatorResolution2of4 x1 op]
        otherwise -> mzero
    BinaryOperatorResolution2of4 x1 op ->
      case element of
        ContinuationValue (AbsFilteredVal v2 patsp patsn) ->
          if (S.null patsp && S.null patsn)
          then
            return $ Path $ [DynamicPop $ BinaryOperatorResolution3of4 x1 op v2]
          else mzero
        otherwise -> mzero
    BinaryOperatorResolution3of4 x1 op v2 ->
      case element of
        ContinuationValue (AbsFilteredVal v1 patsp patsn) ->
          if (S.null patsp && S.null patsn)
          then
            case (abstractBinaryOperation op v1 v2) of
              Just resultValues ->
                do
                  resultVal <- resultValues
                  return $ Path $ [DynamicPop $ BinaryOperatorResolution4of4 x1 resultVal]
              Nothing -> mzero
          else mzero
        otherwise -> mzero
    BinaryOperatorResolution4of4 x1 resultValue ->
      case element of
        LookupVar x1' patsp patsn ->
          if (x1 == x1')
          then
            case (immediatelyMatchedBy resultValue) of
              Just immediatePatterns ->
                if (patsp `S.isSubsetOf` immediatePatterns) && (S.disjoint immediatePatterns patsn)
                then
                  return $ Path $ [Push $ ContinuationValue $ AbsFilteredVal resultValue S.empty S.empty]
                else mzero
              Nothing -> mzero
          else mzero
        otherwise -> mzero
    UnaryOperatorResolution1of3 x1 op ->
      case element of
        UnaryOperation ->
          return $ Path $ [DynamicPop $ UnaryOperatorResolution2of3 x1 op]
        otherwise -> mzero
    UnaryOperatorResolution2of3 x1 op ->
      case element of
        ContinuationValue (AbsFilteredVal v patsp patsn) ->
          if (S.null patsp) && (S.null patsn)
          then
            case (abstractUnaryOperation op v) of
              Just resultValues ->
                do
                  resultVal <- resultValues
                  return $ Path $ [DynamicPop $ UnaryOperatorResolution3of3 x1 resultVal]
              Nothing -> mzero
          else mzero
        otherwise -> mzero
    UnaryOperatorResolution3of3 x1 resultValue ->
      case element of
        LookupVar x1' patsp patsn ->
          if (x1 == x1')
          then
            case (immediatelyMatchedBy resultValue) of
              Just immediatePatterns ->
                if (patsp `S.isSubsetOf` immediatePatterns) && (S.disjoint immediatePatterns patsn)
                then
                  return $ Path $ [Push $ ContinuationValue $ AbsFilteredVal resultValue S.empty S.empty]
                else mzero
              Nothing -> mzero
          else mzero
        otherwise -> mzero

plumeUntargetedDynPop ::
  UntargetedDynPop (PlumePds context) ->
  Element (PlumePds context) ->
  [(Path (PlumePds context), Terminus (PlumePds context))]
plumeUntargetedDynPop action element =
  case action of
    DoJump ->
      case element of
        Jump n1 ->
          return $ (Path $ [], StaticTerminus $ ProgramPointState n1)
        otherwise -> mzero
    ValueDiscovery1of2 ->
      case element of
        ContinuationValue absFilteredVal ->
          return $ (Path $ [DynamicPop $ ValueDiscovery2of2], StaticTerminus $ ResultState absFilteredVal)
        otherwise -> mzero
