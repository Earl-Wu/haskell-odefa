{-# LANGUAGE ScopedTypeVariables #-}

module AST.AbstractAstUtils where

import AST.Ast
import Data.Function
import qualified Data.Either as E
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Maybe as MB
import qualified Control.Monad as MND
import qualified Utils.NondeterminismMonad as ND

data AbstractInterpreterError
  = InvariantFailure String
  | NonRecordProjection String

rv :: [AbstractCls] -> Either AbstractInterpreterError AbstractVar
rv body =
  case body of
    [] -> Left $ InvariantFailure "Empty function body provided to rv"
    otherwise -> let Clause (x, _) = L.last body in return x

negativePatternSetSelection ::
  AbstractRec ->
  S.Set Pattern ->
  Either AbstractInterpreterError [Pattern]
negativePatternSetSelection recordType patternSet =
  let RecordValue m = recordType in
  let recordLabels = M.keysSet m in
  let (relevantPatterns :: Either AbstractInterpreterError [Pattern]) =
        let patternLst = S.toList patternSet in
        let filterFun = \pattern ->
              case pattern of
                RecordPattern m' ->
                  Right $ S.isSubsetOf (M.keysSet m') recordLabels
                AnyPattern -> Left (InvariantFailure "Shouldn't call `negativePatternSetSelection' with a pattern set that contains `any' patterns.")
                otherwise -> Right False
        in
        MND.filterM filterFun patternLst
  in
  do
    pats <- relevantPatterns
    let pickPattern pattern =
          case pattern of
            RecordPattern m' ->
              do
                (k, v) <- ND.pick $ M.toList m'
                return $ RecordPattern (M.singleton k v)
    let selectedPatterns = (ND.pick pats) >>= pickPattern
    return $ ND.toList selectedPatterns
        -- let filterEitherFn = \plst ->
        --       case plst of
        --         [] -> Right []
        --         hd : tl ->
        --           case hd of
        --             RecordPattern m' ->
        --               if S.isSubsetOf (M.keysSet m') recordLabels
        --                 then
        --                   let filterTail = filterEitherFn tl in
        --                   case filterTail of
        --                     Left err -> Left err
        --                     Right plst' -> Right (hd : plst')
        --                 else filterEitherFn tl
        --             AnyPattern -> Left (InvariantFailure "Shouldn't call `negativePatternSetSelection' with a pattern set that contains `any' patterns.")
        --             otherwise -> filterEitherFn tl
        -- in
        -- filterEitherFn patternLst

  -- case relevantPatterns of
  --   Left err -> Left err
  --   Right pats ->
  --     let pickPattern pattern =
  --           case pattern of
  --             RecordPattern m' ->
  --               do
  --                 (k, v) <- ND.pick $ M.toList m'
  --                 return $ RecordPattern (M.singleton k v)


patternProjection ::
  Pattern ->
  Ident ->
  Either AbstractInterpreterError (Maybe Pattern)
patternProjection pattern label =
  case pattern of
    RecordPattern m ->
      return $ M.lookup label m
    AnyPattern -> return $ Nothing
    -- TODO: Change the file name in the error string
    otherwise -> Left $ NonRecordProjection ("Tried to project out of a non-record pattern" ++ (show pattern) ++ "in `analysis.ml:pattern_projection'.")

patternSetProjection :: S.Set Pattern -> Ident -> Either AbstractInterpreterError (S.Set Pattern)
patternSetProjection set label =
  do
    let patLst = S.toList set
    projectedPatterns <- mapM (flip patternProjection label) patLst
    return $ S.fromList $ MB.catMaybes projectedPatterns
  -- let lst = S.toList set in
  -- case lst of
  --   [] -> Right $ S.empty
  --   hd : tl ->
  --     let hdPat = patternProjection hd label in
  --     case hdPat of
  --       Left err -> Left err
  --       Right pat ->
  --         let tlPat = patternSetProjection (S.fromList tl) label in
  --         case tlPat of
  --           Left err' -> Left err'
  --           Right patSet ->
  --             case pat of
  --               Just patVal -> return $ S.insert patVal patSet
  --               Nothing -> return $ patSet

isRecordPatternSet :: S.Set Pattern -> Bool
isRecordPatternSet set =
  set
  & S.toList
  & L.all (\pat -> case pat of RecordPattern _ -> True
                               AnyPattern -> True
                               otherwise -> False)

labelsInPattern :: Pattern -> Either AbstractInterpreterError (S.Set Ident)
labelsInPattern pattern =
  case pattern of
    RecordPattern m ->
      return $ M.keysSet m
    AnyPattern ->
      return $ S.empty
    otherwise ->
      -- TODO: Change the filename to appropriate
      Left $ NonRecordProjection ("Tried to enumerate labels out of a non-record pattern" ++ (show pattern) ++ "in `analysis.ml:labels_in_pattern'.")

liftExpr :: ConcreteExpr -> AbstractExpr
liftExpr (Expr cls) =
  Expr (L.map liftClause cls)

liftClause :: ConcreteCls -> AbstractCls
liftClause (Clause (x, b)) =
  Clause (x, liftClauseBody b)

liftClauseBody :: ConcreteClsBd -> AbstractClsBd
liftClauseBody b =
  case b of
    ValueBody v -> ValueBody (liftValue v)
    VarBody x -> VarBody x
    ApplBody (x, x', annots) -> ApplBody (x, x', annots)
    ConditionalBody (x, p, f1, f2) ->
      ConditionalBody (x, p, liftFunctionValue f1, liftFunctionValue f2)
    ProjectionBody (x, i) -> ProjectionBody (x, i)
    BinaryOperationBody (x1, op, x2) -> BinaryOperationBody (x1, op, x2)
    UnaryOperationBody (op, x) -> UnaryOperationBody (op, x)

liftValue :: ConcreteVal -> AbstractValue
liftValue v =
  case v of
    ValueRecord r -> AbsValueRecord r
    ValueFunction f -> AbsValueFunction (liftFunctionValue f)
    ValueInt _ -> AbsValueInt
    ValueBool b -> AbsValueBool b
    ValueString _ -> AbsValueString

liftFunctionValue :: ConcreteFun -> AbstractFun
liftFunctionValue (FunctionValue (x, e)) =
  FunctionValue (x, liftExpr e)
