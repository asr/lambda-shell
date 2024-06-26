{-
 -   The Lambda Shell, an interactive environment for evaluating pure untyped lambda terms.
 -   Copyright (C) 2005-2011, Robert Dockins
 -
 -   This program is free software; you can redistribute it and/or modify
 -   it under the terms of the GNU General Public License as published by
 -   the Free Software Foundation; either version 2 of the License, or
 -   (at your option) any later version.
 -
 -   This program is distributed in the hope that it will be useful,
 -   but WITHOUT ANY WARRANTY; without even the implied warranty of
 -   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 -   GNU General Public License for more details.
 -
 -   You should have received a copy of the GNU General Public License
 -   along with this program; if not, write to the Free Software
 -   Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
 -}


module LambdaCmdLine
( lambdaCmdLine
) where

import Data.IORef
import Numeric
import Data.Maybe
import Data.List
import Data.Char
import qualified Data.Map as Map
import System.IO
import System.Exit
import System.Console.GetOpt
import Text.ParserCombinators.Parsec (runParser)

-- Local imports
import Lambda
import CPS
import LambdaParser
import LambdaShell
import Version

-----------------------------------------------------------------------
-- Main entry point for the command line tool

-- | Parse command line options and run the lambda shell
lambdaCmdLine :: [String] -> IO ()
lambdaCmdLine argv =
   do st <- parseCmdLine argv
      case (cmd_print st) of
         PrintNothing    -> doCmdLine st
         PrintHelp       -> putStr (printUsage usageNotes)
         PrintVersion    -> putStr versionInfo
         PrintNoWarranty -> putStr noWarranty
         PrintGPL        -> putStr gpl


doCmdLine :: LambdaCmdLineState -> IO ()
doCmdLine st =
   case (cmd_input st) of
       Just expr -> evalInput st expr
       Nothing ->
           if (cmd_stdin st)
              then evalStdin st
              else runShell st

--------------------------------------------------------------
-- Holds important values parsed from the command line

data LambdaCmdLineState
   = LambdaCmdLineState
     { cmd_unfold  :: Bool
     , cmd_stdin   :: Bool
     , cmd_input   :: Maybe String
     , cmd_binds   :: Bindings () String
     , cmd_print   :: PrintWhat
     , cmd_fuel    :: Fuel
     , cmd_trace   :: Maybe (Maybe Int)
     , cmd_red     :: RS
     , cmd_count   :: Bool
     , cmd_extsyn  :: Bool
     , cmd_cps     :: CPS LamParser
     , cmd_history :: Maybe String
     }

initialCmdLineState =
  LambdaCmdLineState
  { cmd_unfold  = False
  , cmd_stdin   = False
  , cmd_input   = Nothing
  , cmd_binds   = Map.empty
  , cmd_print   = PrintNothing
  , cmd_fuel    = maxBound
  , cmd_trace   = Nothing
  , cmd_red     = lamReduceNF
  , cmd_count   = False
  , cmd_extsyn  = True
  , cmd_cps     = simple_cps
  , cmd_history = Just "lambda.history"
  }

data PrintWhat
   = PrintNothing
   | PrintVersion
   | PrintHelp
   | PrintNoWarranty
   | PrintGPL

-------------------------------------------------------------
-- Set up the command line options

data LambdaCmdLineArgs
  = FullUnfold
  | ReadStdIn
  | Program String
  | CFuel String
  | Trace (Maybe String)
  | Print PrintWhat
  | Reduction String
  | Cps String
  | ShowCount
  | NoExtSyn
  | History String
  | NoHistory

options :: [OptDescr LambdaCmdLineArgs]
options =
  [ Option ['u']     ["unfold"]      (NoArg FullUnfold)              "perform full unfolding of let-bound terms"
  , Option ['s']     ["stdin"]       (NoArg ReadStdIn)               "read from standard in"
  , Option ['e']     ["program"]     (ReqArg Program "PROGRAM")      "evaluate statements from command line"
  , Option ['f']     ["fuel"]        (ReqArg CFuel "INT")            "set the maximum number of reductions"
  , Option ['r']     ["trace"]       (OptArg Trace "TRACE_NUM")      "set tracing (and optional trace display length)"
  , Option ['h','?'] ["help"]        (NoArg (Print PrintHelp))       "print this message"
  , Option ['v']     ["version"]     (NoArg (Print PrintVersion))    "print version information"
  , Option ['g']     ["gpl"]         (NoArg (Print PrintGPL))        "print the GNU GPLv2, under which this software is licensed"
  , Option ['w']     ["nowarranty"]  (NoArg (Print PrintNoWarranty)) "print the warranty disclamer"
  , Option ['c']     ["count"]       (NoArg ShowCount)               "turn on printing of reduction counts"
  , Option ['x']     ["extsyn"]      (NoArg NoExtSyn)                "turn off extended syntax"
  , Option ['t']     ["strategy"]    (ReqArg Reduction "REDUCTION_STRATEGY")
           "set the reduction strategy (one of 'whnf', 'hnf', 'nf', 'strict')"
  , Option ['w']     ["history"]     (ReqArg History "HISTORY_FILE")  "set the command history file (default: 'lambda.history')"
  , Option ['q']     ["nohistory"]   (NoArg NoHistory)                "disable command history file"
  , Option ['p']     ["cps"]         (ReqArg Cps "CPS_STRATEGY")      "set the CPS strategy (one of 'simple', 'onepass')"
  ]



-----------------------------------------------------------------
-- Parser for the command line
-- Yeah, I know it's ugly.

parseCmdLine :: [String] -> IO LambdaCmdLineState
parseCmdLine argv =
   case getOpt RequireOrder options argv of
     (opts,files,[]) -> (foldl (>>=) (return initialCmdLineState) $ map applyFlag opts) >>= \st ->
                        (foldl (>>=) (return st)                  $ map loadDefs files)

     (_,_,errs)      -> fail (errMsg errs)

  where errMsg errs = printUsage (concat (intersperse "\n" errs))

        applyFlag :: LambdaCmdLineArgs -> LambdaCmdLineState -> IO LambdaCmdLineState
        applyFlag FullUnfold            st = return st{ cmd_unfold  = True }
        applyFlag ReadStdIn             st = return st{ cmd_stdin   = True }
        applyFlag ShowCount             st = return st{ cmd_count   = True }
        applyFlag NoExtSyn              st = return st{ cmd_extsyn  = False }
        applyFlag NoHistory             st = return st{ cmd_history = Nothing }
        applyFlag (History nm)          st = return st{ cmd_history = Just nm }
        applyFlag (Print printWhat)     st = return st{ cmd_print   = printWhat }
        applyFlag (CFuel f)             st = return st{ cmd_fuel    = read f }
        applyFlag (Trace Nothing)       st = return st{ cmd_trace   = Just Nothing }
        applyFlag (Trace (Just num))    st = case readDec num of
                                                ((n,[]):_) -> return st{ cmd_trace = Just (Just n) }
                                                _          -> fail (errMsg [concat ["'",num,"' must be a positive integer"]])

        applyFlag (Program pgm)         st = case cmd_input st of
                                                Nothing -> return st{ cmd_input = Just pgm }
                                                _       -> fail (errMsg ["'-e' option may only occur once"])

        applyFlag (Cps str) st =
            case map toLower str of
                "simple"  -> return st{ cmd_cps = simple_cps }
                "onepass" -> return st{ cmd_cps = onepass_cps }
                _         -> fail (concat ["'",str,"' is not a valid CPS strategy"])

        applyFlag (Reduction str) st =
            case map toLower str of
                "whnf"   -> return st{ cmd_red = lamReduceWHNF }
                "hnf"    -> return st{ cmd_red = lamReduceHNF }
                "nf"     -> return st{ cmd_red = lamReduceNF }
                "strict" -> return st{ cmd_red = lamStrictNF }
                _        -> fail (concat ["'",str,"' is not a valid reduction strategy"])


-----------------------------------------------------------------------
-- Actually run the shell

mapToShellState :: LambdaCmdLineState -> LambdaShellState
mapToShellState st =
  initialShellState
  { letBindings = cmd_binds st
  , fullUnfold  = cmd_unfold st
  , fuel        = cmd_fuel st
  , trace       = isJust (cmd_trace st)
  , traceNum    = let x = traceNum initialShellState
                  in maybe x (maybe x id) (cmd_trace st)
  , redStrategy = cmd_red st
  , showCount   = cmd_count st
  , cpsStrategy = cmd_cps st
  , histFile    = cmd_history st
  }

runShell :: LambdaCmdLineState -> IO ()
runShell st = do
   lambdaShell (mapToShellState st)
   return ()



--------------------------------------------------------------------------
-- For dealing with input from stdin or the command line

evalStdin :: LambdaCmdLineState -> IO ()
evalStdin st = hGetContents stdin >>= evalInput st

evalInput :: LambdaCmdLineState -> String -> IO ()
evalInput st expr = do
    exitCode <- newIORef ExitSuccess
    let parseSt = LamParseState (cmd_cps st) (cmd_extsyn st)
    case runParser (statementsParser (cmd_binds st)) parseSt "" expr of
       Left msg    -> fail (show msg)
       Right stmts -> foldl (>>=) (return st) $ map (flip (evalStmt exitCode)) $ stmts
    code <- readIORef exitCode
    exitWith code

setSucc :: IORef ExitCode -> IO ()
setSucc ec = writeIORef ec ExitSuccess

setFail :: IORef ExitCode -> IO ()
setFail ec = writeIORef ec (ExitFailure 100)

evalStmt :: IORef ExitCode -> LambdaCmdLineState -> Statement -> IO LambdaCmdLineState
evalStmt ec st (Stmt_eval t)     = evalTerm st t >> setSucc ec >> return st
evalStmt ec st (Stmt_isEq t1 t2) = compareTerms ec st t1 t2 >> return st
evalStmt ec st (Stmt_let name t) = setSucc ec >> return st{ cmd_binds = Map.insert name (Just t) (cmd_binds st) }
evalStmt ec st (Stmt_decl nms)   = setSucc ec >> return st{ cmd_binds = foldr (\x -> Map.insert x Nothing) (cmd_binds st) nms }
evalStmt ec st (Stmt_empty)      = setSucc ec >> return st


evalTerm :: LambdaCmdLineState -> PureLambda () String -> IO ()
evalTerm st t = doEval (unfoldTop (cmd_binds st) t)
 where doEval t =
         case cmd_trace st of
            Nothing       -> putStrLn (printLam (cmd_binds st) (eval t))
            Just Nothing  -> printTrace 50 t
            Just (Just x) -> printTrace x t

       printTrace x t = putStr $ unlines $ map (printLam (cmd_binds st)) $ take x $ trace t

       eval t  = fst $ lamEval (cmd_binds st) (cmd_unfold st) (cmd_red st) (cmd_fuel st) t
       trace t = lamEvalTrace (cmd_binds st) (cmd_unfold st) (cmd_red st) t


compareTerms :: IORef ExitCode
            -> LambdaCmdLineState
            -> PureLambda () String
            -> PureLambda () String
            -> IO ()

compareTerms ec st t1 t2 = do
  if normalEq (cmd_binds st) (cmd_fuel st) t1 t2
     then putStrLn "equal"     >> setSucc ec
     else putStrLn "not equal" >> setFail ec


-------------------------------------------------------------------------
-- Read definitions from a file

loadDefs :: FilePath -> LambdaCmdLineState -> IO LambdaCmdLineState
loadDefs path st = do
  let parseSt = LamParseState (cmd_cps st) (cmd_extsyn st)
  binds <- readDefinitionFile parseSt (cmd_binds st) path
  return st{ cmd_binds = Map.union binds (cmd_binds st) }


-----------------------------------------------------------------------
-- Printing stuff

printUsage :: String -> String
printUsage str = unlines
   [ ""
   , ""
   , usageInfo "usage: lambdaShell {<option>} [{<file>}]\n" options
   , ""
   , ""
   ,str
   , ""
   ]

usageNotes :: String
usageNotes = unlines
   [ "Any files listed after the options will be parsed as a series of"
   , "\"let\" definitions, which will be in scope when the shell starts"
   , "(or when the -e expression is evaluated)"
   ]
