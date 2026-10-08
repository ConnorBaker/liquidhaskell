{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

{- | Primitive operations whose complete arrow depends on a type argument.
Ordinary application checks the returned arrow; this is not a rule for a
saturated call. In particular, an enum decoder retains its valid-tag domain
when aliased or passed as a function.
-}
module Language.Haskell.Liquid.GHC.PrimitiveContract (primitiveContract, dataTagPrefix, dataTagInterpretation) where

import qualified Data.HashMap.Strict as M
import GHC.Builtin.PrimOps (PrimOp (DataToTagLargeOp, DataToTagSmallOp, TagToEnumOp))
import GHC.Builtin.Types (liftedDataConTy)
import GHC.Builtin.Types.Prim (intPrimTy)
import GHC.Core.DataCon (dataConTagZ)
import GHC.Core.TyCon (isEnumerationTyCon, isValidDTT2TyCon)
import GHC.Types.Id (isPrimOpId_maybe)
import GHC.Types.Tickish (tickishIsCode)
import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.Bare.DataType (dataConMap)
import Language.Haskell.Liquid.Bare.Types (DataConMap)
import Language.Haskell.Liquid.Types.RType
import Language.Haskell.Liquid.Types.RTypeOp
import Language.Haskell.Liquid.Types.RefType
import Liquid.GHC.API

primitiveContract :: Maybe Int -> F.TCEmb TyCon -> [F.DataDecl] -> CoreExpr -> Maybe (Either String SpecType)
primitiveContract maxSmallTag embeddings declarations expression
  | Just (function, arguments) <- primitiveTypePrefix expression
  , Just TagToEnumOp <- isPrimOpId_maybe function =
      Just $ case arguments of
        [Type result] -> decoder function result
        _ -> Left "tagToEnum# requires a fully instantiated enumeration result type"
  | Just (function, operation, argument) <- dataTagPrefix expression =
      Just $ do
        (result, correspondence) <- dataTagInterpretation embeddings (dataConMap declarations) argument
        domain <- case (operation, maxSmallTag) of
          (DataToTagLargeOp, _) -> Right F.PTrue
          (_, Just capacity)
            | capacity >= 0 ->
                Right $
                  if capacity == 0
                    then F.PTrue
                    else F.PAtom F.Lt (result value) (F.expr (toInteger capacity))
          _ -> Left "dataToTagSmall# requires GHC's target pointer-tag capacity"
        arrow function domain $ \input ->
          F.PAnd [F.PAtom F.Eq value (result input), correspondence input value]
  | otherwise = Nothing
 where
  representation = toRTypeRep (ofType (exprType expression) :: SpecType)
  arrow function domain result = case ty_args representation of
    [argument] ->
      let parameter = F.intSymbol (F.symbol function) 1
       in Right $
            fromRTypeRep
              representation
                { ty_binds = [parameter]
                , ty_args = [refine domain argument]
                , ty_res = refine (result (F.EVar parameter)) (ty_res representation)
                }
    _ -> Left "primitive prefix must have its complete unary function type"
  decoder function result
    | Just (constructor, _) <- splitTyConApp_maybe result
    , isEnumerationTyCon constructor
    , let constructors = tyConDataCons constructor
    , not (null constructors)
    , FunTy{ft_arg, ft_res} <- exprType expression
    , ft_arg `eqType` intPrimTy
    , ft_res `eqType` result = do
        equation <- resultEquation constructor constructors result
        arrow
          function
          ( F.PAnd
              [ F.PAtom F.Le (F.expr (0 :: Integer)) value
              , F.PAtom F.Lt value (F.expr (toInteger (length constructors)))
              ]
          )
          equation
    | otherwise = Left "tagToEnum# requires a nonempty enumeration representation"
  resultEquation constructor constructors result
    | constructor == boolTyCon
    , typeSort embeddings result == F.boolSort =
        Right (\tag -> F.PIff value (F.PAtom F.Eq tag (F.expr (1 :: Integer))))
    | constructor == boolTyCon =
        Left "tagToEnum# @Bool requires the built-in Boolean logical sort"
    | F.FTC logicalTyCon : _ <- F.unFApp (typeSort embeddings result)
    , let matching = filter ((== logicalTyCon) . F.ddTyCon) declarations
    , Just represented <- traverse (\dc -> M.lookup (F.symbol dc, 0) (dataConMap matching)) constructors
    , all (all (null . F.dcFields) . F.ddCtors) matching
    , sum (map (length . F.ddCtors) matching) == length constructors =
        Right $ \tag ->
          F.PAnd
            [ F.PIff
                (F.PAtom F.Eq tag (F.expr (toInteger (dataConTagZ dc))))
                (F.PAtom F.Eq value (F.EVar logical))
            | (dc, logical) <- zip constructors represented
            ]
    | otherwise = Left "tagToEnum# requires its complete logical enumeration declaration"

-- Only the actual typed primitive prefix owns this interpretation. The
-- DataToTag class selector may carry an arbitrary method through withDict.
dataTagPrefix :: CoreExpr -> Maybe (Var, PrimOp, Type)
dataTagPrefix expression
  | Just (function, [Type levity, Type argument]) <- primitiveTypePrefix expression
  , Just operation <- isPrimOpId_maybe function
  , operation == DataToTagSmallOp || operation == DataToTagLargeOp
  , levity `eqType` liftedDataConTy
  , FunTy{ft_arg, ft_res} <- exprType expression
  , ft_arg `eqType` argument
  , ft_res `eqType` intPrimTy =
      Just (function, operation, argument)
dataTagPrefix _ = Nothing

-- GHC's constructor order is the runtime tag order; the existing logical
-- declaration supplies the matching constructor checkers. Never infer this
-- correspondence from a shared numeric carrier or reverse a source embedding.
-- The expression supplies the tag; its graph also records which source
-- constructor it observes. A declaration lookup alone does not establish
-- exhaustive constructor coverage in an uninterpreted logical carrier.
dataTagInterpretation :: F.TCEmb TyCon -> DataConMap -> Type -> Either String (F.Expr -> F.Expr, F.Expr -> F.Expr -> F.Expr)
dataTagInterpretation embeddings constructors argument
  | argument `eqType` boolTy
  , typeSort embeddings argument == F.boolSort
  , tyConDataCons boolTyCon == [falseDataCon, trueDataCon] =
      Right (\input -> F.EIte input (F.expr (1 :: Integer)) (F.expr (0 :: Integer)), \_ _ -> F.PTrue)
  | Just (constructor, arguments) <- splitTyConApp_maybe argument
  , isValidDTT2TyCon constructor
  , let sourceConstructors = tyConDataCons constructor
  , not (null sourceConstructors)
  , typeSort embeddings argument
      == F.fApp
        (F.FTC (F.symbolFTycon (F.dummyLoc (F.symbol constructor))))
        (typeSort embeddings <$> arguments)
  , Just represented <- traverse (\dc -> M.lookup (F.symbol dc, 0) constructors) sourceConstructors =
      let observations =
            [ (F.expr (toInteger (dataConTagZ dc)), F.EVar (F.testSymbol logical))
            | (dc, logical) <- zip sourceConstructors represented
            ]
       in Right
            ( \input -> foldr (\(tag, checker) rest -> F.EIte (F.EApp checker input) tag rest) (F.expr (0 :: Integer)) observations
            , \input result -> F.PAnd [F.PIff (F.PAtom F.Eq result tag) (F.EApp checker input) | (tag, checker) <- observations]
            )
  | otherwise = Left "dataToTag primitive requires its actual GHC datatype and matching logical constructor declaration"

value :: F.Expr
value = F.EVar F.vv_

refine :: F.Expr -> SpecType -> SpecType
refine predicate ty = strengthen ty (ofReft (F.Reft (F.vv_, predicate)))

primitiveTypePrefix :: CoreExpr -> Maybe (Var, [CoreExpr])
primitiveTypePrefix = go []
 where
  go arguments (Tick note expression)
    | not (tickishIsCode note) = go arguments expression
  go arguments (App expression argument@Type{}) = go (argument : arguments) expression
  go arguments (Var function) = Just (function, arguments)
  go _ _ = Nothing
