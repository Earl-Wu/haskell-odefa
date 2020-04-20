{-# LANGUAGE ScopedTypeVariables #-}

module PlumeAnalysis.Utils.PlumeUtils where

import AST.Ast
import AST.AbstractAstUtils
import PlumeAnalysis.Types.PlumeGraph

import Data.Function
import qualified Data.Either as E
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Map as M

isImmediate :: AnnotatedClause -> Bool
isImmediate acl =
  case acl of
    UnannotatedClause cls -> isClauseImmediate cls
    otherwise -> True

edgesFromNodeList ::
  (Ord context) => [CFGNode context] -> S.Set (CFGEdge context)
edgesFromNodeList nodes =
  loop S.empty nodes
  where
    loop ::
      (Ord context) =>
      S.Set (CFGEdge context) -> [CFGNode context] -> S.Set (CFGEdge context)
    loop acc nodeList =
      case nodeList of
        [] -> acc
        [_] -> acc
        hd : next : [] -> S.insert (CFGEdge hd next) acc
        hd : next : tl -> loop (S.insert (CFGEdge hd next) acc) (next : tl)

-- TODO: What should the error type be?
wireFun ::
  (Ord context) =>
  context ->
  (CFGNode context) ->
  AbstractFun ->
  AbstractVar ->
  AbstractVar ->
  CFG context ->
  Either AbstractInterpreterError (S.Set (CFGEdge context), CFGNode context, CFGNode context, CFGNode context)
wireFun newContext siteNode func x1 x2 graph =
  let CFGNode acl _ = siteNode in
  case acl of
     UnannotatedClause abcl ->
        let (FunctionValue x0 (Expr body)) = func in
        let wireInNode = CFGNode (EnterClause x0 x1 abcl) newContext in
        do
          endVar <- rv body
          let startNode = CFGNode (StartClause endVar) newContext
          let endNode = CFGNode (EndClause endVar) newContext
          let wireOutNode = CFGNode (ExitClause x2 endVar abcl) newContext
          let predEdges =
                preds siteNode graph
                & S.map (\n -> CFGEdge n wireInNode)
          let succEdges =
                succs siteNode graph
                & S.map (\n -> CFGEdge wireOutNode n)
          let innerEdges =
                L.map (\cl -> CFGNode (UnannotatedClause cl) newContext) body
                & (\lst -> wireInNode : startNode : lst)
                & flip (++) [endNode, wireOutNode]
                & edgesFromNodeList
          let newEdges = S.unions [predEdges, innerEdges, succEdges] -- TODO: Check order
          return (newEdges, siteNode, wireInNode, wireOutNode)
     otherwise -> undefined -- TODO: ... Sorry, I know I'm just avoiding doing work here...

wireCond ::
  (Ord context) =>
  CFGNode context ->
  AbstractFun ->
  AbstractVar ->
  AbstractVar ->
  CFG context ->
  Either AbstractInterpreterError (S.Set (CFGEdge context), CFGNode context, CFGNode context, CFGNode context)
wireCond siteNode func x1 x2 graph =
  let (CFGNode acl ctx) = siteNode in
  case acl of
    UnannotatedClause abcl ->
      let (FunctionValue x0 (Expr body)) = func in
      let wireInNode = CFGNode (EnterClause x0 x1 abcl) ctx in
      do
        endVar <- rv body
        let startNode = CFGNode (StartClause endVar) ctx
        let endNode = CFGNode (EndClause endVar) ctx
        let wireOutNode = CFGNode (ExitClause x2 endVar abcl) ctx
        let predEdges =
              preds siteNode graph
              & S.map (\n -> CFGEdge n wireInNode)
        let succEdges =
              succs siteNode graph
              & S.map (\n -> CFGEdge wireOutNode n)
        let innerEdges =
              L.map (\cl -> CFGNode (UnannotatedClause cl) ctx) body
              & (\lst -> wireInNode : startNode : lst)
              & flip (++) [endNode, wireOutNode]
              & edgesFromNodeList
        let newEdges = S.unions [predEdges, innerEdges, succEdges] -- TODO: Check order
        return (newEdges, siteNode, wireInNode, wireOutNode)
    otherwise -> undefined -- TODO: ... Sorry, I know I'm just avoiding doing work here...

immediatelyMatchedBy :: AbstractValue -> Maybe (S.Set Pattern)
immediatelyMatchedBy v =
  case v of
    AbsValueFunction _ -> Just (S.fromList [AnyPattern, FunPattern])
    AbsValueInt -> Just (S.fromList [AnyPattern, IntPattern])
    AbsValueBool b -> Just (S.fromList [AnyPattern, BoolPattern b])
    AbsValueString -> Just (S.fromList [AnyPattern, StringPattern])
    AbsValueRecord _ -> Nothing

abstractBinaryOperation ::
  BinaryOperator -> AbstractValue -> AbstractValue -> Maybe [AbstractValue]
abstractBinaryOperation binop arg1 arg2 =
  case (binop, arg1, arg2) of
    (BinOpPlus, AbsValueInt, AbsValueInt) -> Just [AbsValueInt]
    (BinOpIntMinus, AbsValueInt, AbsValueInt) -> Just [AbsValueInt]
    (BinOpIntLessThan, AbsValueInt, AbsValueInt) -> Just [AbsValueBool True, AbsValueBool False]
    (BinOpIntLessThanOrEqualTo, AbsValueInt, AbsValueInt) -> Just [AbsValueBool True, AbsValueBool False]
    (BinOpEqualTo, AbsValueInt, AbsValueInt) -> Just [AbsValueBool True, AbsValueBool False]
    (BinOpEqualTo, AbsValueBool b1, AbsValueBool b2) -> Just [AbsValueBool $ b1 == b2]
    (BinOpBoolAnd, AbsValueBool b1, AbsValueBool b2) -> Just [AbsValueBool $ b1 && b2]
    (BinOpBoolOr, AbsValueBool b1, AbsValueBool b2) -> Just [AbsValueBool $ b1 || b2]
    otherwise -> Nothing

abstractUnaryOperation :: UnaryOperator -> AbstractValue -> Maybe [AbstractValue]
abstractUnaryOperation unop arg =
  case (unop, arg) of
    (UnaOpBoolNot, AbsValueBool b) -> Just [AbsValueBool $ not b]
    otherwise -> Nothing
