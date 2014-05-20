{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Kitten.Infer.Unify
  ( (===)
  , unifyM
  , unifyM_
  , unifyVar
  ) where

import Control.Applicative
import Control.Monad
import Data.Function
import Data.Maybe
import Data.Monoid
import Data.Text (Text)

import qualified Data.Text as T

import Kitten.Error
import Kitten.Infer.Locations
import Kitten.Infer.Monad
import Kitten.Infer.Scheme
import Kitten.Location
import Kitten.Type.Tidy
import Kitten.Types
import Kitten.Util.FailWriter
import Kitten.Util.Maybe
import Kitten.Util.Text (ToText(..))
import Kitten.Util.Tuple

-- | Simplifies and unifies two types.
unify
  :: (Unification a, Simplify a)
  => Type a
  -> Type a
  -> Program
  -> Either [ErrorGroup] Program
unify a b program = (unification `on` simplify program) a b program

class Unification a where
  unification
    :: Type a
    -> Type a
    -> Program
    -> Either [ErrorGroup] Program

instance Unification Stack where
  unification type1 type2 program = case (type1, type2) of
    _ | type1 == type2 -> Right program

    (a :. b, c :. d) -> unify b d program >>= unify a c

    (TyVar var (Origin hint _), type_) -> unifyVar var (type_ `addHint` hint) program
    (_, TyVar{}) -> commutative

    _ -> Left $ unificationError Nothing
      (originLocation $ inferenceOrigin program) type1 type2

    where commutative = unification type2 type1 program

instance Unification Scalar where
  unification type1 type2 program = case (type1, type2) of
    _ | type1 == type2 -> Right program
    (a :& b, c :& d) -> unify b d program >>= unify a c
    ((:?) a, (:?) b) -> unify a b program
    (a :| b, c :| d) -> unify b d program >>= unify a c
    (TyFunction a b c _, TyFunction d e f _)
      -> unify b e program >>= unify a d >>= unify c f
    (TyVector a _, TyVector b _) -> unify a b program
    (TyVar var (Origin hint _), type_) -> unifyVar var (type_ `addHint` hint) program
    (_, TyVar{}) -> commutative
    (TyQuantified scheme loc, _) -> let
      (type', program') = instantiate loc scheme program
      in unify type' type2 program'
    (_, TyQuantified{}) -> commutative

    _ -> Left $ unificationError Nothing
      (originLocation $ inferenceOrigin program) type1 type2

    where commutative = unification type2 type1 program

instance Unification EffRow where
  unification type1 type2 program = case both orderEffect (type1, type2) of
    _ | type1 == type2 -> Right program
    (l :+ r, s)
      | Just (rewritten, substitution, program') <- rowIso program l s
      -> if fromMaybe False $ occurs
        <$> (unkinded . fst <$> substitution)
        <*> pure program
        <*> pure (effectTail r)
        then Left $ unificationError Nothing
          (originLocation $ inferenceOrigin program) type1 type2
        else let
          program'' = maybe id (uncurry declare) substitution program'
          s' = effectTail rewritten
          in unify r s' program''
    (_, _ :+ _) -> commutative
    (TyVar var (Origin hint _), type_) -> unifyVar var (type_ `addHint` hint) program
    (_, TyVar{}) -> commutative
    _ -> Left $ unificationError Nothing
      (originLocation $ inferenceOrigin program) type1 type2
    where commutative = unification type2 type1 program

instance Unification Eff where
  unification type1 type2 program
    = if type1 == type2
      then Right program
      else Left $ unificationError Nothing
        (originLocation $ inferenceOrigin program) type1 type2

effectTail :: Type EffRow -> Type EffRow
effectTail (_ :+ a) = effectTail a
effectTail a@TyConst{} = a
effectTail a@TyVar{} = a
effectTail a@TyPure{} = a

rowIso
  :: Program
  -> Type Eff
  -> Type EffRow
  -> Maybe (Type EffRow, Maybe (KindedId EffRow, Type EffRow), Program)

-- head
rowIso p lin rin@(l :+ _) | l == lin
  = return (rin, Nothing, p)

-- swap
rowIso p l (l' :+ r) | l /= l' = do
  (r', substitution, p') <- rowIso p l r
  return (l :+ l' :+ r', substitution, p')

-- row-var
rowIso p l (TyVar a o) = let
  (b, p') = freshVar o p
  res = l :+ b
  in return (res, Just (a, res), p')

rowIso _ _ _ = Nothing

unificationError
  :: forall (a :: Kind). (ReifyKind a, TidyType a, ToText (Type a))
  => Maybe Text
  -> Location
  -> Type a
  -> Type a
  -> [ErrorGroup]
unificationError prefix location type1 type2 = runTidy $ do
  type1' <- tidyType type1
  type2' <- tidyType type2
  let
    primaryError = CompileError location Error $ T.unwords
      $ "cannot solve"
      : prefix `consMaybe` toText kind
      : "type constraint"
      : toText type1'
      : "="
      : toText type2'
      : []
    secondaryErrors = map errorDetail
      $ diagnosticLocations type1' ++ diagnosticLocations type2'
  return [ErrorGroup (primaryError : secondaryErrors)]
  where
  kind = reifyKind (KindProxy :: KindProxy a)
  errorDetail (loc, type_) = CompileError loc Note
    $ toText type_ <> " is from here"

-- | Unifies two types, returning the second type.
unifyM
  :: (Unification a, Simplify a)
  => Type a
  -> Type a
  -> K (Type a)
unifyM type1 type2 = do
  program <- getsProgram $ unify type1 type2
  case program of
    Right program' -> putProgram program' >> return type2
    Left errors -> liftFailWriter $ throwMany errors

unifyM_
  :: (Unification a, Simplify a)
  => Type a
  -> Type a
  -> K ()
unifyM_ = (void .) . unifyM

(===)
  :: (Unification a, Simplify a)
  => Type a
  -> Type a
  -> K ()
(===) = unifyM_

infix 3 ===

unifyVar
  :: forall a.
  ( Declare a
  , Occurrences a
  , ReifyKind a
  , Substitute a
  , TidyType a
  , ToText (Type a)
  )
  => KindedId a
  -> Type a
  -> Program
  -> Either [ErrorGroup] Program
unifyVar var1 type_ program = case type_ of
  TyVar var2 _ | var1 == var2 -> return program
  TyVar{} -> return $ declare var1 type_ program
  _ | occurs (unkinded var1) program type_
    -> let loc = originLocation $ inferenceOrigin program in Left $ unificationError
      (Just "infinite") loc
      (sub program (TyVar var1 (Origin HiNone loc) :: Type a))
      (sub program type_)
  _ -> return $ declare var1 type_ program
