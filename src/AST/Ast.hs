module AST.Ast where

import qualified Data.Map as M
import qualified Data.Set as S

newtype Ident = Ident String deriving (Show, Eq, Ord)

newtype FresheningStack = FresheningStack [Ident] deriving (Show, Eq, Ord)

newtype Var = Var (Ident, Maybe FresheningStack) deriving (Show, Eq, Ord)

data BinaryOperator = BinOpPlus | BinOpIntMinus | BinOpIntLessThan
  | BinOpIntLessThanOrEqualTo | BinOpEqualTo | BinOpBoolAnd
  | BinOpBoolOr deriving (Show, Eq, Ord)

data UnaryOperator = UnaOpBoolNot deriving (Show, Eq, Ord)

data ContextualityCallSiteAnnot = CallSiteAcontextual
  | CallSiteAcontextualFor (S.Set Ident) | CallSiteContextual deriving (Show, Eq, Ord)

data CallSiteAnnot = CallSiteAnnot { csaContextuality :: ContextualityCallSiteAnnot,
                                     csaUnit :: ()
                                   } deriving (Show, Eq, Ord)

defaultCallSiteAnnot = CallSiteAnnot { csaContextuality = CallSiteContextual, csaUnit = ()}

newtype RecordValue = RecordValue (M.Map Ident Var) deriving (Show, Eq, Ord)

newtype FunctionValue = FunctionValue (Var, Expr) deriving (Show, Eq, Ord)

data Value = ValueRecord RecordValue | ValueFunction FunctionValue
  | ValueInt Int | ValueBool Bool | ValueString String deriving (Show, Eq, Ord)

data ClauseBody = ValueBody Value | VarBody Var
  | ApplBody (Var, Var, CallSiteAnnot)
  | ConditionalBody (Var, Pattern, FunctionValue, FunctionValue)
  | ProjectionBody (Var, Ident) | BinaryOperationBody (Var, BinaryOperator, Var)
  | UnaryOperationBody (UnaryOperator, Var) deriving (Show, Eq, Ord)

newtype Clause = Clause (Var, ClauseBody) deriving (Show, Eq, Ord)

newtype Expr = Expr [Clause] deriving (Show, Eq, Ord)

data Pattern = RecordPattern (M.Map Ident Pattern)
  | FunPattern | IntPattern | BoolPattern Bool
  | StringPattern | AnyPattern deriving (Show, Eq, Ord)
