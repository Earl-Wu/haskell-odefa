{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Toploop.Toploop where

import AST.AbstractAst
import AST.Ast
import AST.AstUtils
import AST.AstWellformedness
import qualified PlumeAnalysis.Context as C
import Interpreter.Interpreter
import PlumeAnalysis.PlumeAnalysis
import PlumeAnalysis.Utils.PlumeUtils
import Toploop.ToploopAnalysisTypes
import Toploop.ToploopTypes
import Toploop.ToploopOptions
import Toploop.ToploopUtils
import Utils.Exception

import Control.Exception
import Control.Monad.State.Lazy
import Data.Function
import Data.Functor.Identity
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Maybe as MB
import qualified Data.Set as S

data ToploopSituation m
  = ToploopSituation
      {
        tsExpr :: ConcreteExpr,
        tsConf :: Configuration,
        tsCallbacks :: Callbacks m
      }

valuesOfVariableFrom ::
  (C.Context context) =>
  AbstractVar -> 
  AnnotatedClause -> 
  PlumeAnalysis context -> 
  (S.Set AbsFilteredVal, PlumeAnalysis context)
valuesOfVariableFrom x acl analysis = 
  let a = performFullClosure analysis in
  valuesOfVariable x acl a

contextualValuesOfVariableFrom ::
  (C.Context context) =>
  AbstractVar ->
  AnnotatedClause ->
  context ->
  PlumeAnalysis context ->
  (S.Set (AbsFilteredVal), PlumeAnalysis context)
contextualValuesOfVariableFrom x acl ctx analysis =
  let a = performFullClosure analysis in
  contextualValuesOfVariable x acl ctx a

findErrors :: 
  (C.Context context) =>
  PlumeAnalysis context -> [AnalysisError]
findErrors analysis = 
  let acls = 
        analysis
        & expressionOf
        & transform
        & iterateAbstractClauses
  in do
    acl <- acls
    let (Clause xClause b) = acl
    let lookup x =
          let (valList, _) = valuesOfVariableFrom x (UnannotatedClause acl) analysis in
          S.toList valList
          & L.map (\(filtv@(AbsFilteredVal v _ _)) -> (v, filtv))
    case b of
      ValueBody _ -> []
      VarBody _ -> []
      ConditionalBody _ _ _ _ -> []
      ApplBody xf xa _ -> do
        (v, filtv) <- lookup xf
        case v of
          AbsValueFunction _ -> []
          otherwise ->
            let filtvs = 
                  lookup xa
                  & L.map snd
                  & S.fromList
            in return $ ApplicationOfNonFunction xClause xf filtv filtvs
      ProjectionBody x i -> do
        (v, filtv) <- lookup x
        case v of
          AbsValueRecord (RecordValue m) ->
            if M.member i m then []
            else
            return $ ProjectionOfAbsentLabel xClause x filtv i
          otherwise -> return $ ProjectionOfNonRecord xClause x filtv
      BinaryOperationBody x1 op x2 -> do
        (v1, filtv1) <- lookup x1
        (v2, filtv2) <- lookup x2
        let isValid = MB.isJust (abstractBinaryOperation op v1 v2)
        if isValid then []
        else return $ Toploop.ToploopAnalysisTypes.InvalidBinaryOperation xClause op x1 filtv1 x2 filtv2
      UnaryOperationBody op x -> do
        (v, filtv) <- lookup x
        case (op, v) of
          (UnaOpBoolNot, AbsValueBool _) -> []
          otherwise -> return $ Toploop.ToploopAnalysisTypes.InvalidUnaryOperation xClause op x filtv

analysisStepGeneral :: forall m. (ToploopMonad m)
                    => AnalysisTask
                    -> ToploopSituation m
                    -> m AnalysisResult
analysisStepGeneral analysisTask situation =
  let conf = tsConf situation in
  let callbacks = tsCallbacks situation in
  let e = tsExpr situation in
  let initialAnalysis =
        case analysisTask of
          -- Plume n -> createInitialAnalysis ListContext
          SPLUME -> createInitialAnalysis (C.SetContext S.empty) e
          -- OSKPLUME ->
          -- OSMPLUME ->
  in
  let checkForErrors :: m () = 
        if (runIdentity $ topConfDisableInconsistencyCheck conf) 
        then return $ ()
        else 
          let errors = findErrors initialAnalysis in
          toploopErrors errors
  in
  let standardizedVariableAnalysisRequest =
        case (runIdentity $ topConfAnalyzeVars conf) of
          AnalyzeNoVariables -> Nothing
          AnalyzeToplevelVariables ->
            Just (
              e
              & (\(Expr cls) -> cls)
              & L.map (\(Clause (Var (Ident i)) _) -> Query (LUVar i) END [])
            )
          AnalyzeSpecificVariables lst ->
            Just (
              L.map (\(var, clause, ctx) -> Query var clause ctx) lst
            )
  in
  let analyzeVariableValues :: [Query]
                            -> State
                                (PlumeAnalysis C.SetContext)
                                (m [QnA])
      analyzeVariableValues requests =
        let varnameToClauseMap =
              e
              & flatten
              & L.map transform
              & L.map (\(c@(Clause (Var i) _)) -> (i, c))
              & M.fromList
        in
        let lookupClauseByIdent ident =
              case (varnameToClauseMap M.!? ident) of
                Nothing -> throw $ InvalidVariableAnalysis $ "No such variable: " ++ (show ident)
                Just abscls -> abscls
        in
        let mapQuery :: Query -> State (PlumeAnalysis C.SetContext) (m QnA)
            mapQuery tryQuery = 
              let (Query varName siteName userContext) = tryQuery in
              let LUVar varIdent = varName in
              let lookupVar = Var (Ident varIdent) in
              let site =
                    case siteName of
                      ProgramPoint siteNameStr ->
                        UnannotatedClause (lookupClauseByIdent (Ident siteNameStr))
                      END -> EndClause $ lastVarOf e
              in
              let contextStack =
                    case userContext of
                      [] -> C.empty
                      contextVars ->
                        contextVars
                        & L.map (\(LUVar wrappedContext) -> wrappedContext)
                        & L.foldl
                          (\a -> \e ->
                            let c = lookupClauseByIdent (Ident e) in
                            C.add c a
                          )
                          C.empty
              in
              let analysisName = show analysisTask in
              do 
                curAnalysis <- get
                let (values, analysis') = contextualValuesOfVariableFrom lookupVar site contextStack curAnalysis
                put analysis'
                return $
                  do
                    toploopVariableAnalysis varName siteName userContext values analysisName
                    return $ QnA (Query varName siteName userContext) values
        in
        sequence <$> mapM mapQuery requests
  in
  let errors = findErrors initialAnalysis in do
    analyses <- case standardizedVariableAnalysisRequest of
                  Nothing -> return []
                  Just requests -> 
                    evalState (analyzeVariableValues requests) initialAnalysis
    return $ AnalysisResult analyses errors
    
doAnalysisSteps :: 
  (ToploopMonad m) => 
  ToploopSituation m -> m AnalysisReport
doAnalysisSteps situation = 
  let conf = tsConf situation in
  if (runIdentity $ topConfDisableInconsistencyCheck conf) &&
     (runIdentity $ topConfAnalyzeVars conf) == AnalyzeNoVariables
  then return $ M.empty
  else
    foldM
      (\analysisReport -> \atask ->
          let plumeOrSplume = 
                let model = plumeAnalysisToStack atask in
                let ataskName = show atask in
                do
                  result <- analysisStepGeneral atask situation
                  return $ M.insert atask result analysisReport
          in
          case atask of
            PLUME n -> plumeOrSplume
            SPLUME -> plumeOrSplume
      ) M.empty (runIdentity $ topConfAnalyses conf)

doEvaluation ::
  (ToploopMonad m) =>
  ToploopSituation m -> Bool -> m EvaluationResult
doEvaluation situation hasErrors = 
  let callbacks = tsCallbacks situation in
  let conf = tsConf situation in
  let e = tsExpr situation in
  case (runIdentity $ topConfEvaluationMode conf) of
    NeverEvaluate ->
      do
        toploopEvaluationDisabled ()
        return $ EvaluationDisabled
    SafelyEvaluate ->
      if hasErrors 
      then return $ EvaluationInvalidated
      else 
        case eval (transform e) of
          Right (v, env) ->
            do
              toploopEvaluationResult v env
              return $ EvaluationCompleted v env
          Left str -> return $ EvaluationFailure $ show str
    AlwaysEvaluate -> 
      case eval (transform e) of
          Right (v, env) ->
            do
              toploopEvaluationResult v env
              return $ EvaluationCompleted v env
          Left str -> return $ EvaluationFailure $ show str

handleExpression :: 
  (ToploopMonad m) =>
  Callbacks m -> Configuration -> ConcreteExpr -> m Result
handleExpression cbs conf e =
  case checkWellformedExpr e of
    Left err -> do
      toploopIllformednesses err
      return $ Result { illformednesses = err
      , analysisReport = M.empty
      , evaluationResult = EvaluationInvalidated
      }
    Right _ ->
      let situation = ToploopSituation { tsExpr = e, tsConf = conf, tsCallbacks = cbs } in
      let reportM = doAnalysisSteps situation in
      -- let _ = 
      --       if topConfReportAnalysisTimes conf
      --       then 
      --         do 
      --           time <- analysisTimeInMs
      --           toploopAnalysisTimeReport 0
      --       else return ()
      -- in
      do
        -- Reporting time of analysis
        (report, runtime) <- time reportM
        toploopAnalysisTimeReport runtime
        -- Reporting errors, if any
        let errorFree = 
              M.elems report
              & L.foldl (\acc -> \(AnalysisResult _ errors) -> (L.null errors) && acc) True
        -- Report the result
        evaluationResult <- doEvaluation situation (not errorFree)
        return $ 
          Result { illformednesses = []
                , analysisReport = report
                , evaluationResult = evaluationResult
                } 

