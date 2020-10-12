{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module AST.AbstractAst where

import GHC.Generics (Generic)

import AST.Ast
import AST.AstUtils
import Control.DeepSeq
import Data.Function
import qualified Data.Either as E
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Maybe as MB
import qualified Control.Monad as MND
import Control.Exception
import Utils.Exception
import qualified Utils.NondeterminismMonad as ND

type AbstractVar = Var Ident
type AbstractFun = FunctionValue Ident AbstractValue
type AbstractRec = RecordValue Ident
type AbstractClsBd = ClauseBody Ident AbstractValue
type AbstractCls = Clause Ident AbstractValue
type AbstractExpr = Expr Ident AbstractValue

data AbstractValue
  = AbsValueRecord (RecordValue Ident)
  | AbsValueFunction (FunctionValue Ident AbstractValue)
  | AbsValueInt
  | AbsValueBool Bool
  | AbsValueString deriving (Show, Eq, Ord, Generic, NFData)

data AbsFilteredVal = AbsFilteredVal AbstractValue (S.Set Pattern) (S.Set Pattern) deriving (Show, Eq, Ord, Generic, NFData)

data AnnotatedClause
  = UnannotatedClause AbstractCls
  | EnterClause AbstractVar AbstractVar AbstractCls
  | ExitClause AbstractVar AbstractVar AbstractCls
  | StartClause AbstractVar
  | EndClause AbstractVar deriving (Eq, Ord, Show)

ppAnnotatedClause atc =
  case atc of
    UnannotatedClause (Clause (Var (Ident x)) _) -> x
    EnterClause (Var (Ident x1)) (Var (Ident x2)) (Clause (Var (Ident f)) _) ->
        "Enter " ++ f ++ " with " ++ x1 ++ "=" ++ x2 
    ExitClause (Var (Ident x1)) (Var (Ident x2)) (Clause (Var (Ident f)) _) ->
        "Exit " ++ f ++ " with " ++ x1 ++ "=" ++ x2 
    StartClause (Var (Ident x)) -> "Start block " ++ x
    EndClause (Var (Ident x)) -> "End block " ++ x

instance AstTransform ConcreteVal AbstractValue where
  transform v =
    case v of
      ValueRecord r -> AbsValueRecord (transform r)
      ValueFunction f -> AbsValueFunction (transform f)
      ValueInt _ -> AbsValueInt
      ValueBool b -> AbsValueBool b
      ValueString _ -> AbsValueString

instance AstTransform ConcreteVar AbstractVar where
  transform x = x

negativePatternSetSelection ::
  AbstractRec ->
  S.Set Pattern ->
  S.Set Pattern
negativePatternSetSelection recordType patternSet =
  let RecordValue m = recordType in
  let recordLabels = M.keysSet m in
  let relevantPatterns :: [Pattern] =
        let patternLst = S.toList patternSet in
        let filterFun = \pattern ->
              case pattern of
                RecordPattern m' ->
                  S.isSubsetOf (M.keysSet m') recordLabels
                AnyPattern ->
                  throw $ InvariantFailureException $
                    "Shouldn't call `negativePatternSetSelection' with a pattern set that contains `any' patterns."
                otherwise -> False
        in
        L.filter filterFun patternLst
  in
  S.fromList $ L.concat $
  do
    pat <- relevantPatterns
    let pickPattern :: Pattern -> ND.Nondet Pattern
        pickPattern pattern =
          case pattern of
            RecordPattern m' ->
              do
                (k, v) <- ND.pick $ M.toList m'
                return $ RecordPattern (M.singleton k v)
    let selectedPatterns = pickPattern pat
    return $ ND.toList selectedPatterns

patternProjection :: Pattern -> Ident -> Maybe Pattern
patternProjection pattern label =
  case pattern of
    RecordPattern m ->
      M.lookup label m
    AnyPattern ->
      Nothing
    otherwise ->
      throw $ InvariantFailureException $
        "Tried to project out of a non-record pattern" ++
        (Prelude.show pattern) ++ "in `PlumeAnalysis.hs:pattern_projection'."

patternSetProjection :: S.Set Pattern -> Ident -> S.Set Pattern
patternSetProjection set label =
  let patLst = S.toList set in
  let projectedPatterns = L.map (flip patternProjection label) patLst in
  S.fromList $ MB.catMaybes projectedPatterns

isRecordPatternSet :: S.Set Pattern -> Bool
isRecordPatternSet set =
  set
  & S.toList
  & L.all (\pat -> case pat of RecordPattern _ -> True
                               AnyPattern -> True
                               otherwise -> False)

labelsInPattern :: Pattern -> S.Set Ident
labelsInPattern pattern =
  case pattern of
    RecordPattern m -> M.keysSet m
    AnyPattern -> S.empty
    otherwise ->
      throw $ InvariantFailureException $
        "Tried to enumerate labels out of a non-record pattern" ++
        (Prelude.show pattern) ++ "in `PlumeAnalysis.hs:labels_in_pattern'."

labelsInRecord :: AbstractRec -> S.Set Ident
labelsInRecord (RecordValue record) =
  S.fromList $ M.keys record

labelsInPatternSet :: S.Set Pattern -> S.Set Ident
labelsInPatternSet patSet =
  patSet
  & S.map labelsInPattern
  & S.foldl S.union S.empty
