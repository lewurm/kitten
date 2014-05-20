{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE RecursiveDo #-}

module Kitten.Infer
  ( infer
  , typeFragment
  , forAll
  ) where

import Control.Applicative hiding (some)
import Control.Monad
import Data.Monoid
import Data.Text (Text)
import Data.Vector (Vector)

import qualified Data.Foldable as F
import qualified Data.HashMap.Strict as H
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Traversable as T
import qualified Data.Vector as V

import Kitten.Error
import Kitten.Infer.Monad
import Kitten.Infer.Scheme
import Kitten.Infer.Type
import Kitten.Infer.Unify
import Kitten.Location
import Kitten.Types
import Kitten.Util.FailWriter
import Kitten.Util.Monad
import Kitten.Util.Text (toText)

import qualified Kitten.Util.Vector as V

typeFragment
  :: Fragment ResolvedTerm
  -> K (Fragment TypedTerm, Type Scalar)
typeFragment fragment = do
  rec
    -- Populate environment with definition types.
    --
    -- FIXME(strager):
    -- Use previously-inferred types (i.e. defTypeScheme def). We cannot
    -- right now because effects are not inferred properly (e.g. for the
    -- effects of the 'map' prelude function).
    _ <- T.mapM save (fragmentDefs fragment)

    typedDefs <- flip T.mapM (fragmentDefs fragment) $ \def
      -> withOrigin (defOrigin def) $ do
        (typedDefTerm, inferredScheme) <- generalize
          . infer finalProgram . unscheme $ defTerm def  -- See note [scheming defs].
        declaredScheme <- do
          decls <- getsProgram inferenceDecls
          case H.lookup (defName def) decls of
            Just decl -> return decl
            Nothing -> do
              origin <- getsProgram inferenceOrigin
              fmap mono . forAll $ \r s e -> TyFunction r s e origin
        saveDefWith (flip const) (defName def) inferredScheme
        instanceCheck inferredScheme declaredScheme $ let
          item = CompileError (defLocation def)
          in ErrorGroup
          [ item Error $ T.unwords
            [ "inferred type of"
            , defName def
            , "is not an instance of its declared type"
            ]
          , item Note $ T.unwords ["inferred", toText inferredScheme]
          , item Note $ T.unwords ["declared", toText declaredScheme]
          ]
        return def { defTerm = typedDefTerm <$ inferredScheme }

    topLevel <- getsProgram (originLocation . inferenceOrigin)
    (typedTerm, fragmentType) <- infer finalProgram $ fragmentTerm fragment

    -- Equate the bottom of the stack with stackTypes.
    do
      let TyFunction consumption _ _ _ = fragmentType
      bottom <- freshVarM
      enforce <- asksConfig configEnforceBottom
      when enforce $ bottom === TyEmpty (Origin HiNone topLevel)
      stackTypes <- asksConfig configStackTypes
      let stackType = F.foldl (:.) bottom stackTypes
      stackType === consumption

    let
      typedFragment = fragment
        { fragmentDefs = typedDefs
        , fragmentTerm = typedTerm
        }

    finalProgram <- getProgram

  return (typedFragment, sub finalProgram fragmentType)

  where
  defOrigin :: Def a -> Origin
  defOrigin def = Origin
    (HiType (AnDef (defName def)))
    (defLocation def)

  saveDecl :: Text -> TypeScheme -> K ()
  saveDecl name scheme = modifyProgram $ \program -> program
    { inferenceDecls = H.insert name scheme (inferenceDecls program) }

  saveDefWith
    :: (TypeScheme -> TypeScheme -> TypeScheme)
    -> Text
    -> TypeScheme
    -> K ()
  saveDefWith f name scheme = modifyProgram $ \program -> program
    { inferenceDefs = H.insertWith f name scheme (inferenceDefs program) }

  save :: Def a -> K ()
  save def = do
    scheme <- fromAnno (AnDef (defName def)) (defAnno def)
    saveDecl (defName def) scheme
    saveDefWith const (defName def) scheme

instanceCheck :: TypeScheme -> TypeScheme -> ErrorGroup -> K ()
instanceCheck inferredScheme declaredScheme errorGroup = do
  inferredType <- instantiateM inferredScheme
  (stackConsts, scalarConsts, rowConsts, declaredType) <- skolemize declaredScheme
  inferredType === declaredType
  let
    (escapedStacks, escapedScalars, escapedRows)
      = free inferredScheme <> free declaredScheme
    badStacks = filter (`elem` escapedStacks) stackConsts
    badScalars = filter (`elem` escapedScalars) scalarConsts
    badRows = filter (`elem` escapedRows) rowConsts
  unless (null badStacks && null badScalars && null badRows)
    $ liftFailWriter $ throwMany [errorGroup]

-- Note [scheming defs]:
--
-- Defs are always wrapped in 'Scheme's for convenience after type
-- inference, but they are always monomorphic beforehand.

class ForAll a b where
  forAll :: a -> K (Type b)

instance (ForAll a b, Fresh c) => ForAll (Type c -> a) b where
  forAll f = do
    var <- freshVarM
    forAll $ f var

instance ForAll (Type a) a where
  forAll = pure

-- | Infers the type of a term.
infer :: Program -> ResolvedTerm -> K (TypedTerm, Type Scalar)
infer finalProgram resolved = case resolved of

  TrCall hint name loc -> asTyped (TrCall hint name) loc
    . (instantiateM =<<) $ do
      decls <- getsProgram inferenceDecls
      case H.lookup name decls of
        Just decl -> return decl
        Nothing -> do
          mFound <- getsProgram (H.lookup name . inferenceDefs)
          case mFound of
            Just found -> return found
            Nothing -> liftFailWriter $ throwMany [errorGroup]
    where
    errorGroup = ErrorGroup
      [ CompileError loc Error $ T.concat
        ["missing signature for '", name, "'"] ]

  TrCompose hint terms loc -> withLocation loc $ do
    (typedTerms, types) <- V.mapAndUnzipM recur terms
    effect <- freshVarM
    r <- freshVarM
    origin <- getsProgram inferenceOrigin
    let
      composed = foldM
        (\x y -> do
          TyFunction a b c _ <- unquantify x
          TyFunction d e f _ <- unquantify y
          inferCompose a b c d e f)
        ((r --> r) effect origin)
        (V.toList types)

    -- We need the generalized type to check stack effects.
    (_, typeScheme) <- generalize $ (,) () <$> composed
    type_ <- composed

    -- Check stack effect hint.
    case hint of
      Stack0 -> do
        e <- freshVarM
        s <- freshStackIdM
        instanceCheck typeScheme
          (Forall (S.singleton s) S.empty S.empty
            $ (TyVar s origin --> TyVar s origin) e origin)
          $ ErrorGroup
          [ CompileError loc Error $ T.unwords
            [ toText typeScheme
            , "has a non-null stack effect"
            ]
          ]
      Stack1 -> do
        e <- freshVarM
        s <- freshStackIdM
        a <- freshScalarIdM
        -- Note that 'a' is not forall-bound. We want this effect hint
        -- to match function types that produce a single result of any
        -- type, and that operate on any input stack; but these two
        -- notions of "any" are quite different. In the former case, we
        -- care very much that the stack type is immaterial. In the
        -- latter, we don't care what the type is at all.
        instanceCheck typeScheme
          (Forall (S.singleton s) S.empty S.empty
            $ (TyVar s origin
              --> TyVar s origin :. TyVar a origin) e origin)
          $ ErrorGroup
          [ CompileError loc Error $ T.unwords
            [ toText typeScheme
            , "has a non-unary stack effect"
            ]
          ]
      StackAny -> noop

    return (TrCompose hint typedTerms (loc, sub finalProgram type_), type_)

  TrIntrinsic name loc -> asTyped (TrIntrinsic name) loc $ case name of

    InAddVector -> forAll $ \r a e
      -> (r :. TyVector a o :. TyVector a o
      --> r :. TyVector a o) e o

    InAddFloat -> binary (tyFloat o) o

    InAddInt -> binary (tyInt o) o

    InAndBool -> binary (tyBool o) o

    InAndInt -> binary (tyInt o) o

    InApply -> forAll $ \r s e
      -> TyFunction (r :. TyFunction r s e o) s e o

    InCharToInt -> forAll $ \r e
      -> (r :. tyChar o --> r :. tyInt o) e o

    InChoice -> forAll $ \r a b e -> TyFunction
      (r :. (a :| b) :. TyFunction (r :. a) r e o) r e o

    InChoiceElse -> forAll $ \r a b s e -> TyFunction
      (r :. (a :| b)
        :. TyFunction (r :. a) s e o
        :. TyFunction (r :. b) s e o)
      s e o

    InClose -> forAll $ \r e
      -> (r :. tyHandle o --> r) (tyIo o e) o

    InDivFloat -> binary (tyFloat o) o
    InDivInt -> binary (tyInt o) o

    InEqFloat -> relational (tyFloat o) o
    InEqInt -> relational (tyInt o) o

    InExit -> forAll $ \r s e
      -> (r :. tyInt o --> s) (tyExit o e) o

    InFirst -> forAll $ \r a b e
      -> (r :. a :& b --> r :. a) e o

    InFromLeft -> forAll $ \r a b e
      -> (r :. a :| b --> r :. a) e o

    InFromRight -> forAll $ \r a b e
      -> (r :. a :| b --> r :. b) e o

    InFromSome -> forAll $ \r a e
      -> (r :. (a :?) --> r :. a) e o

    InGeFloat -> relational (tyFloat o) o
    InGeInt -> relational (tyInt o) o

    InGet -> forAll $ \r a e
      -> (r :. TyVector a o :. tyInt o --> r :. (a :?)) e o

    InGetLine -> forAll $ \r e
      -> (r :. tyHandle o --> r :. string o) (tyIo o e) o

    InGtFloat -> relational (tyFloat o) o
    InGtInt -> relational (tyInt o) o

    InIf -> forAll $ \r e -> TyFunction
      (r :. tyBool o :. TyFunction r r e o) r e o

    InIfElse -> forAll $ \r s e -> TyFunction
      (r :. tyBool o
        :. TyFunction r s e o
        :. TyFunction r s e o)
      s e o

    InInit -> forAll $ \r a e
      -> (r :. TyVector a o --> r :. TyVector a o) e o

    InIntToChar -> forAll $ \r e
      -> (r :. tyInt o --> r :. (tyChar o :?)) e o

    InLeFloat -> relational (tyFloat o) o
    InLeInt -> relational (tyInt o) o

    InLeft -> forAll $ \r a b e
      -> (r :. a --> r :. a :| b) e o

    InLength -> forAll $ \r a e
      -> (r :. TyVector a o --> r :. tyInt o) e o

    InLtFloat -> relational (tyFloat o) o
    InLtInt -> relational (tyInt o) o

    InModFloat -> binary (tyFloat o) o
    InModInt -> binary (tyInt o) o

    InMulFloat -> binary (tyFloat o) o
    InMulInt -> binary (tyInt o) o

    InNeFloat -> relational (tyFloat o) o
    InNeInt -> relational (tyInt o) o

    InNegFloat -> unary (tyFloat o) o
    InNegInt -> unary (tyInt o) o

    InNone -> forAll $ \r a e
      -> (r --> r :. (a :?)) e o

    InNotBool -> unary (tyBool o) o
    InNotInt -> unary (tyInt o) o

    InOpenIn -> forAll $ \r e
      -> (r :. string o --> r :. tyHandle o) (tyIo o e) o

    InOpenOut -> forAll $ \r e
      -> (r :. string o --> r :. tyHandle o) (tyIo o e) o

    InOption -> forAll $ \r a e -> TyFunction
      (r :. (a :?) :. TyFunction (r :. a) r e o) r e o

    InOptionElse -> forAll $ \r a s e -> TyFunction
      (r :. (a :?)
        :. TyFunction (r :. a) s e o
        :. TyFunction r s e o)
      s e o

    InOrBool -> binary (tyBool o) o
    InOrInt -> binary (tyInt o) o

    InRest -> forAll $ \r a b e
      -> (r :. a :& b --> r :. b) e o

    InRight -> forAll $ \r a b e
      -> (r :. b --> r :. a :| b) e o

    InSet -> forAll $ \r a e
      -> (r :. TyVector a o :. tyInt o :. a
      --> r :. TyVector a o) e o

    InShowFloat -> forAll $ \r e
      -> (r :. tyFloat o --> r :. string o) e o

    InShowInt -> forAll $ \r e
      -> (r :. tyInt o --> r :. string o) e o

    InSome -> forAll $ \r a e
      -> (r :. a --> r :. (a :?)) e o

    InStderr -> forAll $ \r e
      -> (r --> r :. tyHandle o) e o
    InStdin -> forAll $ \r e
      -> (r --> r :. tyHandle o) e o
    InStdout -> forAll $ \r e
      -> (r --> r :. tyHandle o) e o

    InSubFloat -> binary (tyFloat o) o
    InSubInt -> binary (tyInt o) o

    InPair -> forAll $ \r a b e
      -> (r :. a :. b --> r :. a :& b) e o

    InPrint -> forAll $ \r e
      -> (r :. string o :. tyHandle o --> r) (tyIo o e) o

    InTail -> forAll $ \r a e
      -> (r :. TyVector a o --> r :. TyVector a o) e o

    InXorBool -> binary (tyBool o) o
    InXorInt -> binary (tyInt o) o

    where
    o :: Origin
    o = Origin (HiType (AnIntrinsic name)) loc

  TrLambda name term loc -> withOrigin (Origin (HiLocal name) loc) $ do
    a <- freshVarM
    (term', TyFunction b c e _) <- local a $ recur term
    origin <- getsProgram inferenceOrigin
    let type_ = TyFunction (b :. a) c e origin
    return (TrLambda name term' (loc, sub finalProgram type_), type_)

  TrMakePair x y loc -> withLocation loc $ do
    (x', a) <- secondM fromConstant =<< recur x
    (y', b) <- secondM fromConstant =<< recur y
    origin <- getsProgram inferenceOrigin
    type_ <- forAll $ \r e -> (r --> r :. a :& b) e origin
    return (TrMakePair x' y' (loc, sub finalProgram type_), type_)

  TrPush value loc -> withLocation loc $ do
    (value', a) <- inferValue finalProgram value
    origin <- getsProgram inferenceOrigin
    type_ <- forAll $ \r e -> (r --> r :. a) e origin
    return (TrPush value' (loc, sub finalProgram type_), type_)

  TrMakeVector values loc -> withLocation loc $ do
    (typedValues, types) <- V.mapAndUnzipM recur values
    elementType <- fromConstant =<< unifyEach types
    origin <- getsProgram inferenceOrigin
    type_ <- forAll $ \r e ->
      (r --> r :. TyVector elementType origin) e origin
    return
      ( TrMakeVector typedValues (loc, sub finalProgram type_)
      , type_
      )

  where
  recur = infer finalProgram

  asTyped
    :: ((Location, Type Scalar) -> a)
    -> Location
    -> K (Type Scalar)
    -> K (a, Type Scalar)
  asTyped constructor loc action = do
    type_ <- withLocation loc action
    return (constructor (loc, sub finalProgram type_), type_)

-- | Removes top-level quantifiers from a type.
unquantify :: Type a -> K (Type a)
unquantify (TyQuantified scheme _) = unquantify =<< instantiateM scheme
unquantify type_ = return type_

fromConstant :: Type Scalar -> K (Type Scalar)
fromConstant type_ = do
  a <- freshVarM
  r <- freshVarM
  e <- freshVarM
  origin <- getsProgram inferenceOrigin
  type_ === (r --> r :. a) e origin
  return a

binary :: Type Scalar -> Origin -> K (Type Scalar)
binary a origin = forAll
  $ \r e -> (r :. a :. a --> r :. a) e origin

relational :: Type Scalar -> Origin -> K (Type Scalar)
relational a origin = forAll
  $ \r e -> (r :. a :. a --> r :. tyBool origin) e origin

unary :: Type Scalar -> Origin -> K (Type Scalar)
unary a origin = forAll
  $ \r e -> (r :. a --> r :. a) e origin

string :: Origin -> Type Scalar
string origin = TyVector (tyChar origin) origin

local :: Type Scalar -> K a -> K a
local type_ action = do
  modifyProgram $ \program -> program { inferenceLocals = type_ : inferenceLocals program }
  result <- action
  modifyProgram $ \program -> program { inferenceLocals = tail $ inferenceLocals program }
  return result

withClosure :: Vector (Type Scalar) -> K a -> K a
withClosure types action = do
  original <- getsProgram inferenceClosure
  modifyProgram $ \program -> program { inferenceClosure = types }
  result <- action
  modifyProgram $ \program -> program { inferenceClosure = original }
  return result

getClosedName :: ClosedName -> K (Type Scalar)
getClosedName name = case name of
  ClosedName index -> getsProgram $ (!! index) . inferenceLocals
  ReclosedName index -> getsProgram $ (V.! index) . inferenceClosure

inferValue :: Program -> ResolvedValue -> K (TypedValue, Type Scalar)
inferValue finalProgram value = getsProgram inferenceOrigin >>= \origin -> case value of
  TrBool val loc -> ret loc (tyBool origin) (TrBool val)
  TrChar val loc -> ret loc (tyChar origin) (TrChar val)
  TrClosed index loc -> do
    type_ <- getsProgram ((V.! index) . inferenceClosure)
    ret loc type_ (TrClosed index)
  TrClosure names term loc -> do
    closedTypes <- V.mapM getClosedName names
    (term', type_) <- withClosure closedTypes (infer finalProgram term)
    ret loc type_ (TrClosure names term')
  TrFloat val loc -> ret loc (tyFloat origin) (TrFloat val)
  TrInt val loc -> ret loc (tyInt origin) (TrInt val)
  TrLocal index loc -> do
    type_ <- getsProgram ((!! index) . inferenceLocals)
    ret loc type_ (TrLocal index)
  TrQuotation{} -> error "quotation appeared during type inference"
  TrText val loc -> ret loc (TyVector (tyChar origin) origin) (TrText val)
  where
  ret loc type_ constructor = return (constructor (loc, type_), type_)

unifyEach :: Vector (Type Scalar) -> K (Type Scalar)
unifyEach xs = go 0
  where
  go i = if i >= V.length xs
    then freshVarM
    else if i == V.length xs - 1
      then return (xs V.! i)
      else do
        xs V.! i === xs V.! (i + 1)
        go (i + 1)

inferCompose
  :: Type Stack -> Type Stack -> Type EffRow
  -> Type Stack -> Type Stack -> Type EffRow
  -> K (Type Scalar)
inferCompose in1 out1 e1 in2 out2 e2 = do
  out1 === in2
  e1 === e2
  TyFunction in1 out2 e1 <$> getsProgram inferenceOrigin
