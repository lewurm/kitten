{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Main where

import Control.Monad
import Data.Text (Text)
import System.Console.CmdArgs.Explicit
import System.Exit
import System.IO

import qualified Data.Text.IO as T
import qualified Data.Vector as V

import Kitten.Compile
import Kitten.Error
import Kitten.Interpret
import Kitten.Name (NameGen, mkNameGen)
import Kitten.Tree
import Kitten.Yarn (yarn)

import qualified Kitten.Compile as Compile
import qualified Kitten.HTML as HTML
import qualified Kitten.Infer.Config as Infer
import qualified Kitten.Util.Text as T

data CompileMode
  = CheckMode
  | CompileMode
  | InterpretMode
  | HTMLMode

data Arguments = Arguments
  { argsCompileMode :: CompileMode
  , argsDumpResolved :: Bool
  , argsDumpScoped :: Bool
  , argsEnableImplicitPrelude :: Bool
  , argsEntryPoints :: [FilePath]
  , argsLibraryDirectories :: [FilePath]
  , argsShowHelp :: Bool
  , argsShowVersion :: Bool
  }

main :: IO ()
main = do
  hSetEncoding stdout utf8
  arguments <- parseArguments
  let
    defaultConfig filename program = Compile.Config
      { Compile.dumpResolved = argsDumpResolved arguments
      , Compile.dumpScoped = argsDumpScoped arguments
      , Compile.firstLine = 1
      , Compile.implicitPrelude = argsEnableImplicitPrelude arguments
      , Compile.inferConfig = Infer.Config
        { Infer.enforceBottom = True
        , Infer.fragmentName = filename
        }
      , Compile.libraryDirectories = argsLibraryDirectories arguments
      , Compile.name = filename
      , Compile.predefined = V.empty
      , Compile.source = program
      , Compile.stackTypes = V.empty
      }

  let nameGen = mkNameGen  -- TODO(strager): Use StateT NameGen.
  case argsEntryPoints arguments of
    [] -> return ()  -- TODO runRepl nameGen
    entryPoints -> interpretAll entryPoints
      (argsCompileMode arguments) defaultConfig nameGen

containsCode :: TypedTerm -> Bool
containsCode (Compose _ terms _) = V.any containsCode terms
containsCode _ = True

interpretAll
  :: [FilePath]
  -> CompileMode
  -> (FilePath -> Text -> Compile.Config)
  -> NameGen
  -> IO ()
interpretAll entryPoints compileMode config nameGen
  = mapM_ interpretOne entryPoints
  where
  interpretOne :: FilePath -> IO ()
  interpretOne filename = do
    source <- T.readFileUtf8 filename
    mResult <- compile (config filename source) nameGen
    case mResult of
      Left compileErrors -> do
        printCompileErrors compileErrors
        exitFailure
      Right (_nameGen', result, _type) -> case compileMode of
        CheckMode -> return ()
        CompileMode -> V.mapM_ print $ yarn result
        InterpretMode -> void $ interpret [] (yarn result)
        HTMLMode -> do
          html <- HTML.fromFragmentsM T.readFileUtf8 [result]
          T.putStrLn html

parseArguments :: IO Arguments
parseArguments = do
  arguments <- processArgs argumentsMode

  when (argsShowVersion arguments) $ do
    putStrLn "Kitten version 1.0"
    exitSuccess

  when (argsShowHelp arguments) $ do
    print $ helpText [] HelpFormatDefault argumentsMode
    exitSuccess

  return arguments

argumentsMode :: Mode Arguments
argumentsMode = mode "kitten" defaultArguments
  "Interprets Kitten code." bareArgument options
  where

  defaultArguments :: Arguments
  defaultArguments = Arguments
    { argsCompileMode = InterpretMode
    , argsDumpResolved = False
    , argsDumpScoped = False
    , argsEnableImplicitPrelude = True
    , argsEntryPoints = []
    , argsLibraryDirectories = []
    , argsShowHelp = False
    , argsShowVersion = False
    }

  bareArgument :: Arg Arguments
  bareArgument = flagArg entryPointArgument "entry-point"

  entryPointArgument
    :: FilePath -> Arguments -> Either e Arguments
  entryPointArgument path acc = Right
    $ acc { argsEntryPoints = path : argsEntryPoints acc }

  flagReq'
    :: [Name]
    -> FlagHelp
    -> Help
    -> Update a
    -> Flag a
  flagReq' names sample description option
    = flagReq names option sample description

  flagBool'
    :: [Name]
    -> Help
    -> (Bool -> a -> a)
    -> Flag a
  flagBool' names description option
    = flagBool names option description

  options :: [Flag Arguments]
  options =
    [ flagBool' ["c", "compile"]
      "Compile Yarn assembly."
      $ \flag acc@Arguments{..} -> acc
      { argsCompileMode = if flag then CompileMode else argsCompileMode }

    , flagBool' ["check"]
      "Check syntax and types without compiling or running."
      $ \flag acc@Arguments{..} -> acc
      { argsCompileMode = if flag then CheckMode else argsCompileMode }

    , flagBool' ["dump-resolved"]
      "Output result of name resolution."
      $ \flag acc@Arguments{..} -> acc
      { argsDumpResolved = flag }

    , flagBool' ["dump-scoped"]
      "Output result of scope resolution."
      $ \flag acc@Arguments{..} -> acc
      { argsDumpScoped = flag }

    , flagBool' ["html"]
      "Output an HTML document for viewing the type-checked source code."
      $ \flag acc@Arguments{..} -> acc
      { argsCompileMode = if flag then HTMLMode else argsCompileMode }

    , flagReq' ["L", "library"] "DIR"
      "Add library search directory."
      $ \path acc@Arguments{..} -> Right $ acc
      { argsLibraryDirectories = path : argsLibraryDirectories }

    , flagBool' ["no-implicit-prelude"]
      "Disable implicit inclusion of prelude."
      $ \flag acc@Arguments{..} -> acc
      { argsEnableImplicitPrelude = not flag }

    , flagHelpSimple $ \acc -> acc { argsShowHelp = True }
    , flagVersion $ \acc -> acc { argsShowVersion = True }
    ]
