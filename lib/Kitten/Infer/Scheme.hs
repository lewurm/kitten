{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Kitten.Infer.Scheme
  ( Occurrences(..)
  , Simplify(..)
  , Substitute(..)
  , free
  , generalize
  , instantiate
  , instantiateM
  , occurs
  , skolemize
  ) where

import Control.Applicative hiding (Const)
import Control.Monad
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer
import Data.Foldable (foldrM)
import Data.List
import Data.Monoid
import Data.Set (Set)

import qualified Data.Set as S

import Kitten.Id
import Kitten.Infer.Monad
import Kitten.Types
import Kitten.Util.Function
import Kitten.Util.Monad

import qualified Kitten.IdMap as Id

instantiateM :: TypeScheme -> K (Type Scalar)
instantiateM scheme = do
  origin <- getsProgram inferenceOrigin
  liftState $ state (instantiate origin scheme)

instantiate
  :: Origin
  -> TypeScheme
  -> Program
  -> (Type Scalar, Program)
instantiate origin@(Origin _ _) (Forall stacks scalars rows type_) program
  = (sub renamed type_, program')

  where
  (renamed, program') = flip runState program
    $ composeM [renames stacks, renames scalars, renames rows] emptyProgram

  renames
    :: (Declare a, Fresh a)
    => Set (KindedId a)
    -> Program
    -> State Program Program
  renames = flip (foldrM rename) . S.toList

  rename
    :: (Declare a, Fresh a)
    => KindedId a
    -> Program
    -> State Program Program
  rename name local = do
    var <- state (freshVar origin)
    return (declare name var local)

generalize :: K (a, Type Scalar) -> K (a, TypeScheme)
generalize action = do
  before <- getProgram
  (extra, type_) <- action  -- HACK To preserve effect ordering.
  after <- getProgram

  let
    substituted :: Type Scalar
    substituted = sub after type_

    dependent :: (Occurrences a, ReifyKind a, Unbound a) => KindedId a -> Bool
    dependent = dependentBetween before after

    scalars :: [KindedId Scalar]
    stacks :: [KindedId Stack]
    (stacks, scalars, rows) = let
      three
        :: (a -> a') -> (b -> b') -> (c -> c')
        -> (a, b, c) -> (a', b', c')
      three f g h (a, b, c) = (f a, g b, h c)
      d :: (Occurrences a, ReifyKind a, Unbound a) => [KindedId a] -> [KindedId a]
      d = filter dependent
      in three d d d (freeVars substituted)

  return . (,) extra . regeneralize after $ Forall
    (S.fromList stacks)
    (S.fromList scalars)
    (S.fromList rows)
    substituted

-- | Tests whether a variable is dependent between two type
-- environment states.
dependentBetween
  :: forall a. (Occurrences a, ReifyKind a, Unbound a)
  => Program
  -> Program
  -> KindedId a
  -> Bool
dependentBetween before after name
  = any (bound after) (unbound before)
  where
  bound :: Program -> KindedId a -> Bool
  bound env name' = occurs (unkinded name) env
    (TyVar name' (inferenceOrigin env) :: Type a)

-- | Enumerates those type variables in an environment that
-- are allocated but not yet bound to a type.
class Unbound (a :: Kind) where
  unbound :: Program -> [KindedId a]

instance Unbound Scalar where
  unbound env = map KindedId
    $ filter (`Id.notMember` inferenceScalars env)
    $ let n = envMaxScalar env in [n, pred n .. Id 0]
    -- See note [enumerating unbound names].

instance Unbound Stack where
  unbound env = map KindedId
    $ filter (`Id.notMember` inferenceStacks env)
    $ let n = envMaxStack env in [n, pred n .. Id 0]
    -- See note [enumerating unbound names].

instance Unbound EffRow where
  unbound env = map KindedId
    $ filter (`Id.notMember` inferenceRows env)
    $ let n = envMaxRow env in [n, pred n .. Id 0]
    -- See note [enumerating unbound names].

instance Unbound Eff where
  unbound _ = []

-- | The last allocated name in an environment. Relies on
-- the fact that 'NameGen' allocates names sequentially.
envMaxScalar :: Program -> Id TypeSpace
envMaxScalar = unkinded . pred . fst . genKinded . programScalarIdGen

-- | See 'envMaxScalar'.
envMaxStack :: Program -> Id TypeSpace
envMaxStack = unkinded . pred . fst . genKinded . programStackIdGen

-- | See 'envMaxScalar'.
envMaxRow :: Program -> Id TypeSpace
envMaxRow = unkinded . pred . fst . genKinded . programRowIdGen

-- Note [enumerating unbound names]:
--
-- We enumerate unbound names in descending order, with the most recently
-- allocated names appearing first, so that searches for bound names complete
-- faster on average and do fewer allocations.

data TypeLevel = TopLevel | NonTopLevel
  deriving (Eq)

regeneralize :: Program -> TypeScheme -> TypeScheme
regeneralize program (Forall stacks scalars rows wholeType) = let
  (type_, vars) = runWriter $ regeneralize' TopLevel wholeType
  in Forall (foldr S.delete stacks vars) scalars rows type_
  where
  regeneralize'
    :: forall a. TypeLevel -> Type a -> Writer [KindedId Stack] (Type a)
  regeneralize' level type_ = case type_ of
    TyFunction a b _ loc
      | level == NonTopLevel
      , TyVar c _ <- bottommost a
      , TyVar d _ <- bottommost b
      , c == d
      -> do
        -- If this is the only mention of this type variable, then it
        -- can simply be removed from the outer quantifier. Otherwise,
        -- it should be renamed in the inner quantifier.
        when (occurrences
          (reifyKind (KindProxy :: KindProxy a))
          (unkinded c) program wholeType == 2)
          $ tell [c]
        return $ TyQuantified
          (Forall (S.singleton c) S.empty S.empty type_)
          loc
    TyFunction a b e loc -> TyFunction
      <$> regeneralize' NonTopLevel a
      <*> regeneralize' NonTopLevel b
      <*> pure e
      <*> pure loc
    a :. b -> (:.)
      <$> regeneralize' NonTopLevel a
      <*> regeneralize' NonTopLevel b
    (:?) a -> (:?)
      <$> regeneralize' NonTopLevel a
    a :| b -> (:|)
      <$> regeneralize' NonTopLevel a
      <*> regeneralize' NonTopLevel b
    _ -> return type_

freeVars
  :: (Free (Type a))
  => Type a
  -> ([KindedId Stack], [KindedId Scalar], [KindedId EffRow])
freeVars type_
  = let (stacks, scalars, rows) = free type_
  in (nub stacks, nub scalars, nub rows)

class Free a where
  free :: a -> ([KindedId Stack], [KindedId Scalar], [KindedId EffRow])

instance Free (Type Stack) where
  free = \case
    a :. b -> free a <> free b
    TyConst name _ -> ([name], [], [])
    TyEmpty{} -> mempty
    TyVar name _ -> ([name], [], [])

instance Free (Type Scalar) where
  free = \case
    a :& b -> free a <> free b
    (:?) a -> free a
    a :| b -> free a <> free b
    TyFunction a b e _ -> free a <> free b <> free e
    TyConst name _ -> ([], [name], [])
    TyCtor{} -> mempty
    TyQuantified (Forall stacks scalars rows type_) _
      -> let (stacks', scalars', rows') = free type_
      in
        ( stacks' \\ S.toList stacks
        , scalars' \\ S.toList scalars
        , rows' \\ S.toList rows
        )
    TyVar name _ -> ([], [name], [])
    TyVector a _ -> free a

instance Free (Type EffRow) where
  free = \case
    _ :+ a -> free a
    TyConst name _ -> ([], [], [name])
    TyPure{} -> ([], [], [])
    TyVar name _ -> ([], [], [name])

instance Free TypeScheme where
  free (Forall stacks scalars rows type_) = let
    (stacks', scalars', rows') = free type_
    in
      ( stacks' \\ S.toList stacks
      , scalars' \\ S.toList scalars
      , rows' \\ S.toList rows
      )

occurs
  :: forall a
  . (Occurrences a, ReifyKind a)
  => Id TypeSpace -> Program -> Type a -> Bool
occurs = (> 0) ..: occurrences (reifyKind (KindProxy :: KindProxy a))

class Occurrences a where
  occurrences :: Kind -> Id TypeSpace -> Program -> Type a -> Int

instance Occurrences Stack where
  occurrences kind name program = \case
    a :. b -> recur a + recur b
    TyConst typeName@(KindedId name') _ -> case retrieve program typeName of
      Left{} -> if kind == Stack && name == name' then 1 else 0
      Right type' -> recur type'
    TyEmpty{} -> 0
    TyVar typeName@(KindedId name') _ -> case retrieve program typeName of
      Left{} -> if kind == Stack && name == name' then 1 else 0
      Right type' -> recur type'
    where
    recur :: (Occurrences a) => Type a -> Int
    recur = occurrences kind name program

instance Occurrences Scalar where
  occurrences kind name program = \case
    a :& b -> recur a + recur b
    (:?) a -> recur a
    a :| b -> recur a + recur b
    TyFunction a b _ _ -> recur a + recur b
    TyConst typeName@(KindedId name') _ -> case retrieve program typeName of
      Left{} -> if kind == Scalar && name == name' then 1 else 0
      Right type' -> recur type'
    TyCtor{} -> 0
    TyVar typeName@(KindedId name') _ -> case retrieve program typeName of
      Left{} -> if kind == Scalar && name == name' then 1 else 0
      Right type' -> recur type'
    TyQuantified (Forall _ s _ t) _
      -> if KindedId name `S.member` s then 0 else recur t
    TyVector a _ -> recur a
    where
    recur :: (Occurrences a) => Type a -> Int
    recur = occurrences kind name program

instance Occurrences EffRow where
  occurrences kind name program = \case
    a :+ b -> recur a + recur b
    TyConst typeName@(KindedId name') _ -> case retrieve program typeName of
      Left{} -> if name == name' then 1 else 0
      Right type_ -> recur type_
    TyPure{} -> 0
    TyVar typeName@(KindedId name') _ -> case retrieve program typeName of
      Left{} -> if name == name' then 1 else 0
      Right type_ -> recur type_
    where
    recur :: (Occurrences a) => Type a -> Int
    recur = occurrences kind name program

instance Occurrences Eff where
  occurrences _ _ _ _ = 0

class Simplify a where
  simplify :: Program -> Type a -> Type a

instance Simplify Stack where
  simplify program type_ = case type_ of
    TyVar name (Origin hint _loc)
      | Right type' <- retrieve program name
      -> simplify program type' `addHint` hint
    _ -> type_

instance Simplify Scalar where
  simplify program type_ = case type_ of
    TyVar name (Origin hint _loc)
      | Right type' <- retrieve program name
      -> simplify program type' `addHint` hint
    _ -> type_

instance Simplify EffRow where
  simplify program type_ = case type_ of
    TyVar name (Origin hint _loc)
      | Right type' <- retrieve program name
      -> simplify program type' `addHint` hint
    _ -> type_

instance Simplify Eff where
  simplify _ type_ = type_

class Substitute a where
  sub :: Program -> Type a -> Type a

instance Substitute Stack where
  sub program type_ = case type_ of
    a :. b -> sub program a :. sub program b
    TyConst{} -> type_  -- See Note [Constant Substitution].
    TyEmpty{} -> type_
    TyVar name (Origin hint _loc)
      | Right type' <- retrieve program name
      -> sub program type' `addHint` hint
      | otherwise
      -> type_

instance Substitute Scalar where
  sub program type_ = case type_ of
    TyFunction a b e origin -> TyFunction
      (sub program a)
      (sub program b)
      (sub program e)
      origin
    a :& b -> sub program a :& sub program b
    (:?) a -> (sub program a :?)
    a :| b -> sub program a :| sub program b
    TyConst{} -> type_  -- See Note [Constant Substitution].
    TyCtor{} -> type_
    TyQuantified (Forall r s e t) loc
      -> TyQuantified (Forall r s e (sub program t)) loc
    TyVar name (Origin hint _loc)
      | Right type' <- retrieve program name
      -> sub program type' `addHint` hint
      | otherwise
      -> type_
    TyVector a origin -> TyVector (sub program a) origin

instance Substitute EffRow where
  sub program type_ = case type_ of
    a :+ b -> a :+ sub program b
    TyConst{} -> type_  -- See Note [Constant Substitution].
    TyPure{} -> type_
    TyVar name (Origin hint _loc)
      | Right type' <- retrieve program name
      -> sub program type' `addHint` hint
      | otherwise
      -> type_

-- Note [Constant Substitution]:
--
-- Skolem constants do not unify with anything but
-- themselves, so they never appear as substitutions in the
-- typing environment. Therefore, it is unnecessary to
-- substitute on them.

-- | Skolemizes a type scheme by replacing all of the bound
-- variables with skolem constants. Returns the skolem
-- constants and the skolemized type.
skolemize
  :: TypeScheme
  -> K ([KindedId Stack], [KindedId Scalar], [KindedId EffRow], Type Scalar)
skolemize (Forall stackVars scalarVars rowVars type_) = do
  origin <- getsProgram inferenceOrigin
  let
    declares
      :: (Declare a)
      => Set (KindedId a) -> [KindedId a] -> Program -> Program
    declares vars consts program0
      = foldr (uncurry declare) program0
      $ zip (S.toList vars) (map (\name -> TyConst name origin) consts)
  scalarConsts <- replicateM (S.size scalarVars) freshScalarIdM
  stackConsts <- replicateM (S.size stackVars) freshStackIdM
  rowConsts <- replicateM (S.size rowVars) freshRowIdM
  program <- getsProgram
    $ declares scalarVars scalarConsts
    . declares stackVars stackConsts
    . declares rowVars rowConsts
  (stackConsts', scalarConsts', rowConsts', type')
    <- skolemizeType (sub program type_)
  return
    ( stackConsts ++ stackConsts'
    , scalarConsts ++ scalarConsts'
    , rowConsts ++ rowConsts'
    , type'
    )

skolemizeType
  :: Type a
  -> K ([KindedId Stack], [KindedId Scalar], [KindedId EffRow], Type a)
skolemizeType = \case
  TyFunction a b e origin -> do
    (stackConsts, scalarConsts, rowConsts, b') <- skolemizeType b
    return (stackConsts, scalarConsts, rowConsts, TyFunction a b' e origin)
  TyQuantified scheme _ -> skolemize scheme
  type_ -> return ([], [], [], type_)
