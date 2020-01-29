module Main where

import AST.Ast
import Interpreter.Interpreter
import Parser.Parser
import Parser.Lexer
import System.Environment
import Control.Monad
import Data.Function
import Data.Char
import System.IO
import qualified Data.Map as M

parseFile :: FilePath -> IO Expr
parseFile f = do
  contents <- readFile f
  let tokenList = alexScanTokens contents
  -- putStrLn (show tokenList)
  let ast = parseProgram tokenList
  -- putStrLn (show ast)
  return ast
-- handleExprs :: [Expr] -> IO ()
-- handleExprs exprs =
--  case exprs of
--    [] -> return ()
--    hd : tl -> handleExpr hd >> handleExprs tl
--
handleExpr :: Expr -> IO ()
handleExpr expr =
  do
    let res = eval expr
    case res of Left err -> putStrLn (show err)
                Right (v, env) -> let val = env M.! v in
                                  putStrLn ("Your environment is:\n" ++ showEnvironment env) >>
                                  putStrLn ("\n") >>
                                  putStrLn ("The evaluation result is:\n" ++ showValue val)

main :: IO ()
main =
 do
  args <- getArgs
  let expr =
        case args of
          [] ->
            do
              text <- getContents
              let tokenList = alexScanTokens text
              -- putStrLn (show tokenList)
              return $ parseProgram tokenList
          hd : _ -> parseFile hd
  expr >>= handleExpr

-- main :: IO ()
-- main = hSetBuffering stdout NoBuffering >>
--  do
--   args <- getArgs
--   case args of
--     [] ->
--       -- (getContents
--       -- & (fmap alexScanTokens)
--       -- -- )
--       -- & (fmap parseExpr) :: IO [Expr])
--       -- -- >>= handleExprs
--       -- & fmap (fmap show)
--       -- & fmap concat
--       -- >>= putStr
--       do
--         text <- getContents
--         let tokenList = alexScanTokens text
--         -- putStrLn (show tokenList)
--         let asts = parseExpr tokenList
--         mapM_ handleExpr asts
--     hd : _ -> parseFile hd
--
-- main :: IO ()
-- main = putStr =<< (fmap (map toUpper) $ getContents)

-- main :: IO ()
-- main = do
--   text <- getLine
--   let tokenList = alexScanTokens text
--   putStrLn (show tokenList)
--   let ast = parseExpr tokenList
--   let test = eval ast
--   case test of Left err -> putStrLn (show err)
--                Right (v, env) -> let val = env M.! v in
--                                  putStrLn (show val)
