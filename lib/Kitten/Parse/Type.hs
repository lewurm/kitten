{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Kitten.Parse.Type
  ( signature
  , typeDefType
  ) where

import Control.Applicative
import Data.List
import Data.Text (Text)
import Data.Vector (Vector)

import qualified Data.Vector as V

import Kitten.Parse.Monad
import Kitten.Parsec
import Kitten.Parse.Primitive
import Kitten.Types
import Kitten.Util.Parsec

signature :: Parser Anno
signature = (<?> "type signature") . locate
  $ Anno <$> (quantified sig <|> sig)
  where sig = grouped functionType

typeDefType :: Parser Anno
typeDefType = locate $ Anno <$> baseType

type_ :: Parser AnType
type_ = (<?> "type") $ try functionType <|> baseType

data Variable
  = ScalarVariable !Text
  | StackVariable !Text
  | RowVariable !Text

partitionVariables :: [Variable] -> ([Text], [Text], [Text])
partitionVariables = foldl' go ([], [], [])
  where
  go (stacks, scalars, rows) = \case
    StackVariable name -> (name : stacks, scalars, rows)
    ScalarVariable name -> (stacks, name : scalars, rows)
    RowVariable name -> (stacks, scalars, name : rows)

quantified :: Parser AnType -> Parser AnType
quantified thing = do
  (stacks, scalars, rows) <- partitionVariables <$> between
    (match $ TkBlockBegin NormalBlockHint)
    (match TkBlockEnd)
    (variable `sepEndBy1` match TkComma)
  AnQuantified (V.fromList stacks) (V.fromList scalars) (V.fromList rows)
    <$> thing
  where
  variable :: Parser Variable
  variable = choice
    [ StackVariable <$> (dot *> word)
    , RowVariable <$> (plus *> word)
    , ScalarVariable <$> word
    ]

dot, plus :: Parser Token
dot = match (TkOperator ".")
plus = match (TkOperator "+")

functionType :: Parser AnType
functionType = (<?> "function type") $ choice
  [ AnStackFunction
    <$> (dot *> word) <*> left <*> (dot *> word) <*> right <*> effect
  , AnFunction <$> left <*> right <*> effect
  ]
  where
  left, right :: Parser (Vector AnType)
  left = manyV baseType <* match TkArrow
  right = manyV type_
  effect :: Parser (Vector Text)
  effect = option V.empty $ plus *> (word `sepByV` plus)

baseType :: Parser AnType
baseType = (<?> "base type") $ do
  prefix <- choice
    [ AnVar <$> (notFollowedBy plus *> word)
    , vector
    , try $ grouped type_
    ]
  (<?> "") $ choice
    [ AnChoice prefix
      <$> (match (TkOperator "|") *> baseType)
    , AnOption prefix <$ match (TkOperator "?")
    , AnPair prefix
      <$> (match (TkOperator "&") *> baseType)
    , pure prefix
    ]

vector :: Parser AnType
vector = AnVector <$> between
  (match TkVectorBegin) (match TkVectorEnd) baseType
