module AST.Ast where

import qualified Data.Map as M
import qualified Data.Set as S

newtype Ident = Ident String deriving (Show, Eq, Ord)

newtype Var x = Var x deriving (Show, Eq, Ord)

newtype FresheningStack = FresheningStack [Ident] deriving (Show, Eq, Ord)

type FreshIdent = (Ident, Maybe FresheningStack)

type InterpExpr = Expr FreshIdent (ConcreteValue FreshIdent)

type ConcreteVar = Var Ident
type ConcreteVal = ConcreteValue Ident
type ConcreteFun = FunctionValue Ident ConcreteVal
type ConcreteRec = RecordValue Ident
type ConcreteClsBd = ClauseBody Ident ConcreteVal
type ConcreteCls = Clause Ident ConcreteVal
type ConcreteExpr = Expr Ident (ConcreteValue Ident)

type AbstractVar = Var Ident
type AbstractFun = FunctionValue Ident AbstractValue
type AbstractRec = RecordValue Ident
type AbstractClsBd = ClauseBody Ident AbstractValue
type AbstractCls = Clause Ident AbstractValue
type AbstractExpr = Expr Ident AbstractValue

data BinaryOperator
  = BinOpPlus
  | BinOpIntMinus
  | BinOpIntLessThan
  | BinOpIntLessThanOrEqualTo
  | BinOpEqualTo
  | BinOpBoolAnd
  | BinOpBoolOr deriving (Show, Eq, Ord)

data UnaryOperator = UnaOpBoolNot deriving (Show, Eq, Ord)

data ContextualityCallSiteAnnot
  = CallSiteAcontextual
  | CallSiteAcontextualFor (S.Set Ident)
  | CallSiteContextual deriving (Show, Eq, Ord)

data CallSiteAnnot = CallSiteAnnot { csaContextuality :: ContextualityCallSiteAnnot,
                                     csaUnit :: () } deriving (Show, Eq, Ord)

defaultCallSiteAnnot
  = CallSiteAnnot { csaContextuality = CallSiteContextual, csaUnit = ()}

newtype RecordValue x
  = RecordValue (M.Map Ident (Var x)) deriving (Show, Eq, Ord)

newtype FunctionValue x v
  = FunctionValue ((Var x), Expr x v) deriving (Show, Eq, Ord)

data ConcreteValue x
  = ValueRecord (RecordValue x)
  | ValueFunction (FunctionValue x (ConcreteValue x))
  | ValueInt Int
  | ValueBool Bool
  | ValueString String deriving (Show, Eq, Ord)

data AbstractValue
  = AbsValueRecord (RecordValue Ident)
  | AbsValueFunction (FunctionValue Ident AbstractValue)
  | AbsValueInt
  | AbsValueBool Bool
  | AbsValueString deriving (Show, Eq, Ord)

data ClauseBody x v
  = ValueBody v
  | VarBody (Var x)
  | ApplBody (Var x, Var x, CallSiteAnnot)
  | ConditionalBody (Var x, Pattern, FunctionValue x v, FunctionValue x v)
  | ProjectionBody (Var x, Ident)
  | BinaryOperationBody (Var x, BinaryOperator, Var x)
  | UnaryOperationBody (UnaryOperator, Var x) deriving (Show, Eq, Ord)

newtype Clause x v
  = Clause (Var x, ClauseBody x v) deriving (Show, Eq, Ord)

newtype Expr x v = Expr [(Clause x v)] deriving (Show, Eq, Ord)

data Pattern
  = RecordPattern (M.Map Ident Pattern)
  | FunPattern
  | IntPattern
  | BoolPattern Bool
  | StringPattern
  | AnyPattern deriving (Show, Eq, Ord)

newtype AbsFilteredVal = AbsFilteredVal (AbstractValue, S.Set Pattern, S.Set Pattern) deriving (Show, Eq, Ord)

data AnnotatedClause
  = UnannotatedClause AbstractCls
  | EnterClause (AbstractVar, AbstractVar, AbstractCls)
  | ExitClause (AbstractVar, AbstractVar, AbstractCls)
  | StartClause AbstractVar
  | EndClause AbstractVar deriving (Show, Eq, Ord)
