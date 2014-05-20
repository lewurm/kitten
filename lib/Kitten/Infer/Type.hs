{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Kitten.Infer.Type
  ( fromAnno
  ) where

import Control.Applicative
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Data.Either
import Data.Map (Map)
import Data.Monoid
import Data.Text (Text)
import Data.Vector (Vector)

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Vector as V

import Kitten.Error
import Kitten.Location
import Kitten.Types
import Kitten.Util.FailWriter
import Kitten.Util.Text (toText)

data Env = Env
  { envAnonStacks :: [KindedId Stack]
  -- ^ Anonymous stacks implicit on both sides of an
  -- 'Anno.Function' constructor.

  , envRow :: !(Type EffRow)
  -- ^ The default implicit row.

  , envRows :: !(Map Text (KindedId EffRow))
  -- ^ Map from effect variable names to effect variables.

  , envStacks :: !(Map Text (KindedId Stack))
  -- ^ Map from stack variable names to stack variables.

  , envScalars :: !(Map Text (KindedId Scalar))
  -- ^ Map from scalar variable names to scalar variables.
  }

type Converted a = StateT Env K a

fromAnno :: Annotated -> Anno -> K (Scheme (Type Scalar))
fromAnno annotated (Anno annoType annoLoc) = do
  row <- TyVar <$> freshRowIdM <*> pure (Origin (HiType annotated) annoLoc)
  (type_, env) <- flip runStateT Env
    { envAnonStacks = []
    , envRow = row
    , envRows = M.empty
    , envStacks = M.empty
    , envScalars = M.empty
    } $ fromAnnoType' (HiType annotated) annoType

  return $ Forall
    (S.fromList (envAnonStacks env <> M.elems (envStacks env)))
    (S.fromList . M.elems $ envScalars env)
    S.empty
    type_
  where

  fromInput, fromOutput :: AnType -> Converted (Type Scalar)
  fromInput = fromAnnoType' (HiFunctionInput annotated)
  fromOutput = fromAnnoType' (HiFunctionOutput annotated)

  fromAnnoType' :: Hint -> AnType -> Converted (Type Scalar)
  fromAnnoType' hint = \case
    AnChoice a b -> (:|)
      <$> fromAnnoType' HiNone a
      <*> fromAnnoType' HiNone b
    AnFunction a b e -> do
      r <- lift freshStackIdM
      let rVar = TyVar r origin
      scheme <- Forall (S.singleton r) S.empty S.empty
        <$> makeFunction origin rVar a rVar b e
      return $ TyQuantified scheme origin
    AnOption a -> (:?)
      <$> fromAnnoType' HiNone a
    AnPair a b -> (:&)
      <$> fromAnnoType' HiNone a
      <*> fromAnnoType' HiNone b
    AnQuantified stacks scalars rows type_ -> do
      stackVars <- V.mapM declareStack stacks
      scalarVars <- V.mapM declareScalar scalars
      rowVars <- V.mapM declareRow rows
      scheme <- Forall
        (S.fromList (V.toList stackVars))
        (S.fromList (V.toList scalarVars))
        (S.fromList (V.toList rowVars))
        <$> fromAnnoType' HiNone type_
      return $ TyQuantified scheme origin
      where
      declareRow name = do
        var <- lift freshRowIdM
        modify $ \env -> env
          { envRows = M.insert name var (envRows env) }
        return var
      declareScalar name = do
        var <- lift freshScalarIdM
        modify $ \env -> env
          { envScalars = M.insert name var (envScalars env) }
        return var
      declareStack name = do
        var <- lift freshStackIdM
        modify $ \env -> env
          { envStacks = M.insert name var (envStacks env) }
        return var
    AnStackFunction leftStack leftScalars rightStack rightScalars effects -> do
      leftStackVar <- annoStackVar leftStack loc annotated
      rightStackVar <- annoStackVar rightStack loc annotated
      makeFunction origin
        leftStackVar leftScalars rightStackVar rightScalars effects
    AnVar name -> annoScalarVar name loc annotated
    AnVector a -> TyVector <$> fromAnnoType' HiNone a <*> pure origin
    where
    origin :: Origin
    origin = Origin hint loc
    loc :: Location
    loc = annoLoc  -- FIXME(strager)

  makeFunction
    :: Origin
    -> Type Stack
    -> Vector AnType
    -> Type Stack
    -> Vector AnType
    -> Vector Text
    -> Converted (Type Scalar)
  makeFunction origin leftStack leftScalars rightStack rightScalars effects = do
    (consts, vars) <- partitionEithers . V.toList <$> V.mapM fromEffect effects
    e <- case vars of
      [] -> gets envRow
      [var] -> return var
      _ -> lift . liftFailWriter . throwMany . (:[]) . ErrorGroup
        $ item Error
          "multiple effect variables on one function"
        : map (item Note . toText) vars  -- TODO More precise source locations.
        where item = CompileError (originLocation origin)
    TyFunction
      <$> (V.foldl' (:.) leftStack <$> V.mapM fromInput leftScalars)
      <*> (V.foldl' (:.) rightStack <$> V.mapM fromOutput rightScalars)
      <*> pure (foldr (:+) e consts)
      <*> pure origin

  fromEffect :: Text -> Converted (Either (Type Eff) (Type EffRow))
  fromEffect name = annoEffectVar name annoLoc annotated

fromAnno _ TestAnno = error "cannot make type from test annotation"

annoEffectVar
  :: Text
  -> Location
  -> Annotated
  -> Converted (Either (Type Eff) (Type EffRow))
annoEffectVar name loc annotated = do
  existing <- gets $ M.lookup name . envRows
  case existing of
    Just var -> return $ Right (TyVar var origin)
    Nothing -> case name of
      "exit" -> return $ Left (TyEff EffExit origin)
      "fail" -> return $ Left (TyEff EffFail origin)
      "io" -> return $ Left (TyEff EffIo origin)
      _ -> unknown name loc
  where origin = Origin (HiVar name annotated) loc

-- | Gets a scalar variable by name from the environment.
annoScalarVar :: Text -> Location -> Annotated -> Converted (Type Scalar)
annoScalarVar name loc annotated = do
  existing <- gets $ M.lookup name . envScalars
  case existing of
    Just var -> return $ TyVar var origin
    Nothing -> case name of
      "bool" -> return $ TyCtor CtorBool origin
      "char" -> return $ TyCtor CtorChar origin
      "float" -> return $ TyCtor CtorFloat origin
      "handle" -> return $ TyCtor CtorHandle origin
      "int" -> return $ TyCtor CtorInt origin
      _ -> unknown name loc
  where origin = Origin (HiVar name annotated) loc

-- | Gets a stack variable by name from the environment.
annoStackVar :: Text -> Location -> Annotated -> Converted (Type Stack)
annoStackVar name loc annotated = do
  existing <- gets $ M.lookup name . envStacks
  case existing of
    Just var -> return $ TyVar var (Origin (HiVar name annotated) loc)
    Nothing -> unknown name loc

unknown :: Text -> Location -> Converted a
unknown name loc = lift . liftFailWriter . throwMany . (:[]) $ ErrorGroup
  [ CompileError loc Error
    $ "unknown type or undeclared type variable " <> name
  ]
