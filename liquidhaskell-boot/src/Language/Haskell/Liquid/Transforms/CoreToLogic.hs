{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE MagicHash              #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TemplateHaskellQuotes  #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE UndecidableInstances   #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Haskell.Liquid.Transforms.CoreToLogic
  ( coreToDef
  , coreToFun
  , coreToLogic
  , coreToLogicWithDefinitions
  , LogicM, castToLg
  , mkLit, mkI, mkS
  , runToLogic
  , runToLogicWithBoolBinds
  , logicType
  , inlineSpecType
  , measureSpecType
  , weakenResult
  , normalizeCoreExpr
  , preserveDemand
  , NewtypeCoercion(..)
  , newtypeCoercionDataCon
  ) where

import           Data.Bifunctor (first)
import           Data.ByteString                       (ByteString)
import           Prelude                               hiding (error)
import           Language.Haskell.Liquid.GHC.TypeRep   () -- needed for Eq 'Type'
import           Liquid.GHC.API       hiding (Expr, Located, get, panic)
import qualified Liquid.GHC.API       as Ghc
import qualified Liquid.GHC.API       as C
import qualified Data.List                             as L
import           Data.Maybe                            (listToMaybe)
import qualified Data.Text                             as T
import qualified Data.Char
import qualified Text.Printf as Printf
import           Data.Text.Encoding
import           Data.Text.Encoding.Error
import           Control.Monad (forM, unless, zipWithM)
import           Control.Monad.Except
import           Control.Monad.Identity
import qualified Control.Monad.Writer.Lazy as Writer
import qualified Language.Haskell.Liquid.Misc          as Misc
import           Language.Fixpoint.Types               hiding (panic, Error, R, simplify, isBool)
import qualified Language.Fixpoint.Types               as F
import qualified Language.Fixpoint.Types.Visitor       as Vis
import qualified Language.Haskell.Liquid.GHC.Misc      as GM
import Language.Haskell.Liquid.GHC.PrimitiveContract (dataTagPrefix, dataTagInterpretation)


import           Language.Haskell.Liquid.Bare.Types
import           Language.Haskell.Liquid.Bare.DataType
import           Language.Haskell.Liquid.Bare.Misc     (simpleSymbolVar)
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp
import           Language.Haskell.Liquid.Types.Types

import qualified Data.HashMap.Strict                   as M
import qualified Data.HashSet                          as S
import qualified Language.Haskell.Liquid.Measure       as Ms
import qualified GHC.Core                             as Core
import qualified GHC.Core.Coercion as Core
import qualified GHC.Core.Utils as Core
import qualified GHC.Core.Type as GhcType
import qualified GHC.Core.TyCo.Rep as GhcType
import GHC.Types.Var (isInvisibleFunArg)
import GHC.Builtin.Types (doubleDataCon)
import GHC.Types.Literal (LitNumType(LitNumBigNat))
import Control.Monad.Reader
import Language.Haskell.Liquid.UX.Config


logicType :: (IsReft r) => Bool -> Type -> RRType r
logicType _allowTC τ = fromRTypeRep $ t{ty_binds = bs, ty_info = is, ty_args = as, ty_refts = rs}
  where
    t            = toRTypeRep $ ofType τ
    (bs, is, as, rs) = Misc.unzip4 $ dropWhile (isErasable' . Misc.thd4) $ Misc.zip4 (ty_binds t) (ty_info t) (ty_args t) (ty_refts t)
    isErasable' = isEmbeddedClass

{- | [NOTE:inlineSpecType type]: the refinement depends on whether the result type is a Bool or not:
      CASE1: measure f@logic :: X -> Bool <=> f@haskell :: x:X -> {v:Bool | v <=> (f@logic x)}
     CASE2: measure f@logic :: X -> Y    <=> f@haskell :: x:X -> {v:Y    | v = (f@logic x)}
 -}
-- formerly: strengthenResult
inlineSpecType :: Bool -> Var -> SpecType
inlineSpecType _allowTC v = fromRTypeRep $ rep{ty_res = res `strengthen` r, ty_binds = xs}
  where
    r              = MkUReft (mkReft (mkEApp f (mkA <$> vxs))) mempty
    rep            = toRTypeRep t
    res            = ty_res rep
    xs = intSymbol (symbol ("x" :: String)) <$> [1 .. length $ ty_binds rep]
    vxs            = dropWhile (isErasable' . snd) $ zip xs (ty_args rep)
    isErasable' = isEmbeddedClass
    f              = dummyLoc (symbol v)
    t              = ofType (GM.expandVarType v) :: SpecType
    mkA            = EVar . fst
    mkReft :: Expr -> Reft
    mkReft         = if isBool res then propReft else exprReft

-- | Refine types of measures: keep going until you find the last data con!
--   this code is a hack! we refine the last data constructor,
--   it got complicated to support both
--   1. multi parameter measures     (see tests/pos/HasElem.hs)
--   2. measures returning functions (fromReader :: Reader r a -> (r -> a) )
--   TODO: SIMPLIFY by dropping support for multi parameter measures

-- formerly: strengthenResult'
measureSpecType :: Bool -> Var -> SpecType
measureSpecType _allowTC v = go mkT [] [(1 :: Int) ..] st
  where
    mkReft :: Expr -> Reft
    mkReft | boolRes   = propReft
           | otherwise = exprReft
    mkT xs          = MkUReft (mkReft $ mkEApp locSym (EVar <$> reverse xs)) mempty
    locSym          = dummyLoc (symbol v)
    st              = ofType (GM.expandVarType v) :: SpecType
    boolRes         =  isBool $ ty_res $ toRTypeRep st

    go f args i (RAllT a t r)    = RAllT a (go f args i t) r
    go f args i (RAllP p t)      = RAllP p $ go f args i t
    go f args i (RFun x ii t1 t2 r)
        | isEmbeddedClass t1 = RFun x ii t1 (go f args i t2) r
    go f args i t@(RFun _ ii t1 t2 r)
     | hasRApps t               = RFun x' ii t1 (go f (x':args) (tail i) t2) r
                                       where x' = intSymbol (symbol ("x" :: String)) (head i)
    go f args _ t                = t `strengthen` f args

    hasRApps (RFun _ _ t1 t2 _) = hasRApps t1 || hasRApps t2
    hasRApps RApp {}          = True
    hasRApps _                = False


-- | 'weakenResult foo t' drops the singleton constraint `v = foo x y`
--   that is added, e.g. for measures in /strengthenResult'.
--   This should only be used _when_ checking the body of 'foo'
--   where the output, is, by definition, equal to the singleton.
weakenResult :: Bool -> Var -> SpecType -> SpecType
weakenResult _allowTC v t = F.notracepp msg t'
  where
    msg = "weakenResult v =" ++ GM.showPpr v ++ " t = " ++ showpp t
    t'           = fromRTypeRep $ rep { ty_res = mapExprReft weaken (ty_res rep) }
    rep          = toRTypeRep t
    weaken x     = pAnd . filter ((Just vE /=) . isSingletonExpr x) . conjuncts
    vE           = mkEApp vF xs
    xs = EVar . fst <$> dropWhile (isEmbeddedClass . snd) xts
    xts          = zip (ty_binds rep) (ty_args rep)
    vF           = dummyLoc (symbol v)

type LogicM = ExceptT Error (Writer.WriterT LogicSupport (ReaderT LState Identity))

data LState = LState
  { lsSymMap  :: LogicMap
  , lsError   :: String -> Error
  , lsEmb     :: TCEmb TyCon
  , lsBools   :: [Var]
  , lsDCMap   :: DataConMap
  , lsConfig  :: Config
  , lsConstructorBoxes :: M.HashMap DataCon ConstructorBox
  , lsSourceFields :: [(CoreExpr, Expr)]
  }

throw :: String -> LogicM a
throw str = do
  fmkError  <- reader lsError
  throwError $ fmkError str

getState :: LogicM LState
getState = ask

runToLogic
  :: M.HashMap DataCon ConstructorBox -> TCEmb TyCon -> LogicMap -> DataConMap -> Config -> (String -> Error)
  -> LogicM t -> Either Error (t, LogicSupport)
runToLogic = runToLogicWithBoolBinds []

runToLogicWithBoolBinds
  :: [Var] -> M.HashMap DataCon ConstructorBox -> TCEmb TyCon -> LogicMap -> DataConMap -> Config -> (String -> Error)
  -> LogicM t -> Either Error (t, LogicSupport)
runToLogicWithBoolBinds xs boxes tce lmap dm cfg ferror m
  = fmap (, support) result
  where
    (result, support) = runReader (Writer.runWriterT (runExceptT m)) $ LState
      { lsSymMap = lmap
      , lsError  = ferror
      , lsEmb    = tce
      , lsBools  = xs
      , lsDCMap  = dm
      , lsConfig = cfg
      , lsConstructorBoxes = boxes
      , lsSourceFields = []
      }

coreAltToDef :: (IsReft r) => Located LHName -> Var -> [Var] -> Var -> Type -> [C.CoreAlt]
             -> LogicM [Def (Located (RRType r)) DataCon]
coreAltToDef locSym z zs y t alts
  | not (null litAlts) = measureFail locSym "Cannot lift definition with literal alternatives"
  | otherwise          = do
      d1s <- F.notracepp "coreAltDefs-1" <$> mapM (mkAlt locSym cc myArgs z) dataAlts
      d2s <- F.notracepp "coreAltDefs-2" <$>       mkDef locSym cc myArgs z  defAlts defExpr
      return (d1s ++ d2s)
  where
    myArgs   = reverse zs
    cc       = if eqType t boolTy then P else E
    defAlts  = GM.defaultDataCons (GM.expandVarType y) ((\(Alt c _ _) -> c) <$> alts)
    defExpr  = listToMaybe [ e |   (Alt C.DEFAULT _ e) <- alts ]
    dataAlts =             [ a | a@(Alt (C.DataAlt _) _ _) <- alts ]
    litAlts  =             [ a | a@(Alt (C.LitAlt _) _ _) <- alts ]

    -- mkAlt :: LocSymbol -> (Expr -> Body) -> [Var] -> Var -> (C.AltCon, [Var], C.CoreExpr)
    mkAlt x ctor _args dx (Alt (C.DataAlt d) xs e)
      = do
          initial <- coreToLg e
          fields <- sourceFields d (varType dx) (map Core.varToCoreExpr xs)
          let (_, names) = F.freshInNSL (map (F.tempSymbol (lhNameToResolvedSymbol (val x))) [0 .. toInteger (length fields) - 1])
                (F.syms initial `S.union` S.fromList (map F.symbol (dx:xs)))
              images = map F.EVar names
              annotations = [Just (F.atLoc x (ofType (exprType field))) | field <- fields]
              whole = F.mkEApp (GM.namedLocSymbol d) images
          su <- workerProjection xs fields images
          expression <- withSourceFields fields images e
          pure (Def x d (Just $ varRType dx) (zip names annotations)
            (ctor (F.subst su expression `subst1` (F.symbol dx, whole))))
    mkAlt _ _ _ _ alt
      = throw $ "Bad alternative" ++ GM.showPpr alt

    mkDef x ctor _args dx (Just dtss) (Just e) = do
      e0     <- coreToLg e
      let dxt = Just (varRType dx)
      -- The DEFAULT body may mention the scrutinee @dx@; for each data
      -- constructor @d@ covered by the default alternative, we re-express it as
      -- @d@ applied to the fresh field arguments, mirroring 'mkAlt'. Without
      -- this substitution the scrutinee would remain unbound.
      let mkOne (d, _, ts) =
            let args = defArgs x ts
                su   = (F.symbol dx, F.mkEApp (GM.namedLocSymbol d) (F.eVar . fst <$> args))
            in Def x d dxt args (ctor (e0 `subst1` su))
      return (mkOne <$> dtss)

    mkDef _ _ _ _ _ _ =
      return []

defArgs :: IsReft r => Located LHName -> [Type] -> [(Symbol, Maybe (Located (RRType r)))]
defArgs x     = zipWith (\i t -> (defArg i, defRTyp t)) [0..]
  where
    defArg    = tempSymbol (lhNameToResolvedSymbol $ val x)
    defRTyp   = Just . F.atLoc x . ofType

coreToDef ::
    (IsReft r) =>
    Located LHName ->
    Var ->
    C.CoreExpr ->
    LogicM [Def (Located (RRType r)) DataCon]
coreToDef locSym _ s = do
    allowTC <- reader $ typeclass . lsConfig
    go [] $ inlinePreds $ simplifyCoreExpr allowTC s
  where
    go args (C.Lam x e) = go (x : args) e
    go args (C.Tick _ e) = go args e
    go (z : zs) (C.Case scrutinee y t alts)
        | ownsScrutinee z scrutinee =
            owned (z : zs) $
                coreAltToDef
                    locSym
                    z
                    zs
                    y
                    t
                    [Alt con xs (sub y (C.Var z) rhs) | Alt con xs rhs <- alts]
        | otherwise =
            measureFail locSym "Case scrutinee is not the selected measure argument"
    go args (C.Let (C.NonRec x rhs) body)
        | isId x = go args (sub x rhs body)
    go (z : zs) e
        | Just t <- isMeasureArg z = owned (z : zs) $ coreAltToDef locSym z zs z t [Alt C.DEFAULT [] e]
    go _ _ = measureFail locSym "Does not have a case-of at the top-level"

    inlinePreds = inlineCoreExpr (eqType boolTy . GM.expandVarType)
    owned arguments = Writer.censor (filter (not . (`elem` arguments) . fst))

    -- A constructor equation describes this argument, not an unrelated
    -- value of the same type. Only source-preserving aliases may disappear.
    ownsScrutinee z (C.Var x) = z == x
    ownsScrutinee z (C.Tick _ expression) = ownsScrutinee z expression
    ownsScrutinee z (C.Cast expression co)
        | let (source, target) = coercionTypeEq co
        , eqType (sourceFamily source) (sourceFamily target) =
            ownsScrutinee z expression
    ownsScrutinee _ _ = False

    sourceFamily ty = maybe ty (uncurry Ghc.mkFamilyTyConApp) (Ghc.splitTyConApp_maybe ty)

measureFail       :: Located LHName -> String -> a
measureFail x msg = panic sp e
  where
    sp            = Just (GM.fSrcSpan x)
    e             = Printf.printf "Cannot create measure '%s': %s" (F.showpp x) msg


-- | 'isMeasureArg x' returns 'Just t' if 'x' is a valid argument for a measure.
isMeasureArg :: Var -> Maybe Type
isMeasureArg x
  | Just tc <- tcMb
  , Ghc.isAlgTyCon tc = F.notracepp "isMeasureArg" $ Just t
  | otherwise           = Nothing
  where
    t                   = GM.expandVarType x
    tcMb                = tyConAppTyCon_maybe t


varRType :: (IsReft r) => Var -> Located (RRType r)
varRType = GM.varLocInfo ofType

coreToFun :: LocSymbol -> Var -> C.CoreExpr ->  LogicM ([Var], Either Expr Expr)
coreToFun _ _v s = do
  allowTC <- reader $ typeclass . lsConfig
  go [] $ normalizeCoreExpr allowTC s
  where
    go acc (C.Lam x e)  | isTyVar x = go acc e
    go acc (C.Lam x e)  = do
        let isE = GM.isEmbeddedDictVar
        if isE x then go acc e else go (x : acc) e
    go acc (C.Tick _ e) = go acc e
    go acc e            = (reverse acc,) . Right <$> coreToLg e


instance Show C.CoreExpr where
  show = GM.showPpr

coreToLogic :: C.CoreExpr -> LogicM Expr
coreToLogic cb = do
    allowTC <- reader $ typeclass . lsConfig
    coreToLg $ normalizeCoreExpr allowTC cb

-- Interpret query-owned parameters and local implementations by their exact
-- denotations. Their complete Core remains the input to ordinary checking;
-- this environment changes only logical readback, not source assumptions.
coreToLogicWithDefinitions :: [(Id, Expr)] -> CoreExpr -> LogicM Expr
coreToLogicWithDefinitions definitions expression =
    local
        (\s -> s{lsSourceFields = [(C.Var identifier, meaning) | (identifier, meaning) <- definitions] ++ lsSourceFields s})
        (coreToLogic expression)


-- These local bindings name the actual typed source fields reconstructed by
-- GHC. Preserve whole fields before projecting the remaining worker leaves.
withSourceFields :: [CoreExpr] -> [Expr] -> CoreExpr -> LogicM Expr
withSourceFields fields images expression = do
    allowTC <- reader $ typeclass . lsConfig
    local
        (\s -> s{lsSourceFields = zip fields images ++ lsSourceFields s})
        (coreToLg (normalizeCoreExpr allowTC expression))

coreToLg :: C.CoreExpr -> LogicM Expr
coreToLg expression = do
    config <- reader lsConfig
    case GM.integerLiteral (targetIntBits config) expression of
        Just magnitude -> do
            embeddings <- reader lsEmb
            unless (typeSort embeddings (exprType expression) == F.intSort) $
                throw "A closed Integer literal requires the built-in integer logical sort"
            pure (F.expr magnitude)
        Nothing -> do
            meaning <- coreMeaning expression
            case meaning of
                Just image -> pure image
                Nothing -> coreToLg' expression

coreMeaning :: CoreExpr -> LogicM (Maybe Expr)
coreMeaning expression = do
    fields <- reader lsSourceFields
    pure (snd <$> L.find (\(field, _) -> Core.cheapEqExpr field expression && eqType (exprType field) (exprType expression)) fields)

coreToLg' :: C.CoreExpr -> LogicM Expr
coreToLg' expression
    | Just (function, _, argument) <- dataTagPrefix expression = do
        embeddings <- reader lsEmb
        constructors <- reader lsDCMap
        (result, _) <- either throw pure (dataTagInterpretation embeddings constructors argument)
        let parameter = F.intSymbol (F.symbol function) 1
        pure (F.ELam (parameter, typeSort embeddings argument) (result (F.EVar parameter)))
coreToLg' (C.Let (C.NonRec x (C.Coercion c)) e) =
    coreToLg (C.substExpr (C.extendCvSubst C.emptySubst x c) e)
coreToLg' (C.Let (C.NonRec identifier rhs) body) = do
    known <- coreMeaning (C.Var identifier)
    case known of
        Just _ -> coreToLg body
        Nothing -> do
            meaning <- coreToLg rhs
            -- Interpret aliases before their uses. Substituting a lambda only
            -- after interpreting applications loses their composition law.
            local
                (\s -> s{lsSourceFields = (C.Var identifier, meaning) : lsSourceFields s})
                (coreToLg body)
coreToLg' (C.Let C.Rec{} _) =
    throw "Cannot make Logical Substitution of Recursive Definitions"
coreToLg' (C.Tick _ e) = coreToLg e
coreToLg' (C.Var x)
    | x == falseDataConId = return PFalse
    | x == trueDataConId = return PTrue
    | ignoreVar x = do
        embeddings <- reader lsEmb
        case typeSort embeddings (varType x) of
            F.FFunc domain result
                | domain == result ->
                    let parameter = F.intSymbol (F.symbol x) 1
                     in pure (F.ELam (parameter, domain) (F.EVar parameter))
            _ -> throw "Primitive numeric box requires identical logical field/result sorts"
    | otherwise = do
        state <- getState
        definition <- declaredDefinition state (C.Var x)
        case definition of
            Just meaning -> pure meaning
            Nothing -> do
                Writer.tell [(x, rTypeSort (lsEmb state) (classRFInfoType True (ofType (varType x) :: SpecType)))]
                pure (eVarWithMap x (lsSymMap state))
coreToLg' e@(C.App _ _) = toPredApp e
coreToLg' (C.Case e b _ alts)
    | eqType (GM.expandVarType b) boolTy = checkBoolAlts alts >>= coreToIte b e
-- coreToLg (C.Lam x e)           = do p     <- coreToLg e
--                                     tce   <- lsEmb <$> getState
--                                     return $ ELam (symbol x, typeSort tce (GM.expandVarType x)) p
coreToLg' (C.Case e b _ alts) = do
    p <- coreToLg e
    casesToLg b p alts
coreToLg' (C.Lit l) = case mkLit l of
    Nothing -> throw $ "Bad Literal in measure definition" ++ GM.showPpr l
    Just i -> return i
coreToLg' (C.Cast e c) = coreToLg e >>= castToLg c
-- elaboration reuses coretologic
-- TODO: fix this
coreToLg' (C.Lam x e) = do
    meaning <- coreMeaning (C.Var x)
    p <- coreToLg e
    case meaning of
        Just _ -> pure p
        Nothing -> do
            tce <- lsEmb <$> getState
            return $ ELam (symbol x, typeSort tce (GM.expandVarType x)) p
coreToLg' e = throw ("Cannot transform to Logic:\t" ++ GM.showPpr e)

castToLg :: Coercion -> Expr -> LogicM Expr
castToLg co e = do
    embeddings <- reader lsEmb
    case newtypeCoercionDataCon co of
        Just (dc, _) | Just _ <- newtypeIdentitySort embeddings dc -> pure e
        Just (dc, WrapCoercion) ->
            pure (F.mkEApp (GM.namedLocSymbol dc) [e])
        Just (dc, UnwrapCoercion) -> do
            dm <- reader lsDCMap
            pure (EApp (EVar (makeDataConSelector (Just dm) dc 1)) e)
        Nothing -> do
            (s, t) <- coerceToLg co
            pure (ECoerc s t e)

coerceToLg :: Coercion -> LogicM (Sort, Sort)
coerceToLg = typeEqToLg . coercionTypeEq

data NewtypeCoercion = WrapCoercion | UnwrapCoercion
  deriving (Eq, Show)

-- | @newtypeCoercionDataCon co@ recognises the representational coercions that
--   GHC inserts to wrap and unwrap @newtype@ values.
--
-- Given a newtype declaration
--
-- > newtype NT = MkT (unwrap :: Rep)
--
-- an expression @Cast e co@, could stand for a wrap coercion @MkT e@, or an
-- unwrap coercion @unwrap e@, or something else. And this function must
-- distinguish between the three cases.
--
-- @Cast e (NT ~ Rep)@ is an unwrap coercion, and @Cast e (Rep ~ NT)@ is a
-- wrap coercion.
--
-- If this is a newtype coercion, it returns the newtype's 'DataCon' together
-- with a flag indicating the kind of coercion.
--
-- See note [Newtype checking] in "Language.Haskell.Liquid.Constraint.Generate".
newtypeCoercionDataCon :: Coercion -> Maybe (DataCon, NewtypeCoercion)
newtypeCoercionDataCon co
  | Ghc.Pair s t <- coercionKind co
  = case (asNewtypeRep t s, asNewtypeRep s t) of
      (Just dc, _) -> Just (dc, WrapCoercion)
      (_, Just dc) -> Just (dc, UnwrapCoercion)
      _            -> Nothing
  where
    -- @asNewtypeRep nt rep@ returns the newtype's 'DataCon' when @nt@ is a
    -- fully-applied non-recursive newtype whose instantiated representation
    -- type is @rep@.
    asNewtypeRep nt rep
      | Just (tc, args) <- splitTyConApp_maybe nt
      , isNewTyCon tc
      , args `lengthAtLeast` newTyConEtadArity tc
      , Just dc <- tyConSingleDataCon_maybe tc
      , newTyConInstRhs tc args `eqType` rep
      = Just dc
      | otherwise
      = Nothing


coercionTypeEq :: Coercion -> (Type, Type)
coercionTypeEq co
  | Ghc.Pair s t <- -- GM.tracePpr ("coercion-type-eq-1: " ++ GM.showPpr co) $
                       coercionKind co
  = (s, t)

typeEqToLg :: (Type, Type) -> LogicM (Sort, Sort)
typeEqToLg (s, t) = do
  tce   <- reader lsEmb
  let tx = typeSort tce . expandTypeSynonyms
  return $ F.notracepp "TYPE-EQ-TO-LOGIC" (tx s, tx t)

checkBoolAlts :: [C.CoreAlt] -> LogicM (C.CoreExpr, C.CoreExpr)
checkBoolAlts [Alt (C.DataAlt false) [] efalse, Alt (C.DataAlt true) [] etrue]
  | false == falseDataCon, true == trueDataCon
  = return (efalse, etrue)

checkBoolAlts [Alt (C.DataAlt true) [] etrue, Alt (C.DataAlt false) [] efalse]
  | false == falseDataCon, true == trueDataCon
  = return (efalse, etrue)
checkBoolAlts alts
  = throw ("checkBoolAlts failed on " ++ GM.showPpr alts)

-- @casesToLg v e alts@ transforms a case expression with scrutinee @e@ and
-- alternatives @alts@ into a logic expression. The variable @v@ is the binder
-- for the scrutinee in the case alternatives.
casesToLg :: Var -> Expr -> [C.CoreAlt] -> LogicM Expr
casesToLg v e alts = mapM (altToLg (varType v) e) normAlts >>= go
  where
    normAlts       = normalizeAlts alts
    go :: [(C.AltCon, Expr)] -> LogicM Expr
    go [(_,p)]     = return (p `subst1` su)
    go ((d,p):dps) = do c <- checkDataAlt d e
                        e' <- go dps
                        return (EIte c p e' `subst1` su)
    go []          = throw $ "Unexpected empty cases in casesToLg: " ++ show e
    su             = (symbol v, e)

checkDataAlt :: C.AltCon -> Expr -> LogicM Expr
checkDataAlt (C.DataAlt d) e = return $ EApp (EVar (makeDataConChecker d)) e
checkDataAlt C.DEFAULT     _ = return PTrue
checkDataAlt (C.LitAlt l)  e
  | Just le <- mkLit l       = return (EEq le e)
  | otherwise                = throw $ "Oops, not yet handled: checkDataAlt on Lit: " ++ GM.showPpr l

-- | 'altsDefault' reorders the CoreAlt to ensure that 'DEFAULT' is at the end.
normalizeAlts :: [C.CoreAlt] -> [C.CoreAlt]
normalizeAlts alts      = ctorAlts ++ defAlts
  where
    (defAlts, ctorAlts) = L.partition isDefault alts
    isDefault (Alt c _ _)   = c == C.DEFAULT

altToLg :: Type -> Expr -> C.CoreAlt -> LogicM (C.AltCon, Expr)
altToLg result de (Alt a@(C.DataAlt d) xs e) = do
    fields <- sourceFields d result (map Core.varToCoreExpr xs)
    images <- sourceProjections d de (length fields)
    su <- workerProjection xs fields images
    p <- withSourceFields fields images e
    return (a, subst su p)

altToLg _ _ (Alt a _ e)
  = (a, ) <$> coreToLg e

-- A case binds worker coordinates; logical projections select source fields.
-- Invert only GHC's checked boxer expression, covering every value coordinate.
sourceFields :: DataCon -> Type -> [CoreExpr] -> LogicM [CoreExpr]
sourceFields dc result actual = do
    boxes <- reader lsConstructorBoxes
    fields <-
        if eqType (varType (dataConWorkId dc)) (varType (dataConWrapId dc))
            then pure (drop (length (Ghc.dataConExTyCoVars dc)) actual)
            else
                maybe
                    (throw ("Missing GHC source reconstruction for " ++ GM.showPpr dc))
                    pure
                    (Ms.constructorSourceFields boxes dc result actual)
    pure (filter (not . GM.isEmbeddedDictType . exprType) fields)

sourceProjections :: DataCon -> Expr -> Int -> LogicM [Expr]
sourceProjections dc image count = do
    dm <- reader lsDCMap
    pure [if primDataCon dc then image else EApp (EVar (makeDataConSelector (Just dm) dc i)) image | i <- [1 .. count]]

workerProjection :: [Var] -> [CoreExpr] -> [Expr] -> LogicM F.Subst
workerProjection worker fields images = do
    unless (length fields == length images) (throw "GHC boxer source arity mismatch")
    pairs <- concat <$> zipWithM invert fields images
    let values = filter (\v -> isId v && not (GM.isEmbeddedDictVar v)) worker
        candidates v = [image | (w, image) <- pairs, w == v]
    assignments <- forM values $ \v -> case candidates v of
        image : rest | all (== image) rest -> pure (v, image)
        _ -> throw ("GHC boxer does not determine worker coordinate " ++ GM.showPpr v)
    unless (all (\(v, _) -> v `elem` values) pairs) (throw "GHC boxer contains a foreign value coordinate")
    pure (mkSubst (concat [[(symbol v, e), (GM.simplesymbol v, e)] | (v, e) <- assignments]))
  where
    invert (C.Var v) image = pure [(v, image)]
    invert (C.Cast e co) image = castToLg (Core.mkSymCo co) image >>= invert e
    invert (C.Tick _ e) image = invert e image
    invert expression image
        | (C.Var v, args) <- C.collectArgs expression
        , Just dc <- Ghc.isDataConId_maybe v = do
            let actual = drop (length (Ghc.dataConUnivTyVars dc)) args
            fields' <- case C.idDetails v of
                C.DataConWorkId _ -> sourceFields dc (exprType expression) actual
                _ ->
                    pure
                        ( filter
                            (not . GM.isEmbeddedDictType . exprType)
                            (drop (length (Ghc.dataConExTyCoVars dc)) actual)
                        )
            images' <- sourceProjections dc image (length fields')
            concat <$> zipWithM invert fields' images'
        | otherwise = throw ("Unsupported GHC boxer inversion: " ++ GM.showPpr expression)

primDataCon :: DataCon -> Bool
primDataCon = ignoreVar . dataConWorkId

coreToIte :: Var -> C.CoreExpr -> (C.CoreExpr, C.CoreExpr) -> LogicM Expr
coreToIte binder e (efalse, etrue)
  = do p  <- coreToLg e
       e1 <- coreToLg efalse
       e2 <- coreToLg etrue
       return $ EIte p e2 e1 `subst1` (symbol binder, p)

toPredApp :: C.CoreExpr -> LogicM Expr
toPredApp p = do
  allowTC <- reader (typeclass . lsConfig)
  go . first opSym . splitArgs allowTC $ p
  where
    opSym = tomaybesymbol
    go (Just f, [e])
      | f == symbol (show 'not)
      = PNot <$>  coreToLg e
    go (Just f, [e1, e2])
        | f == symbol (show '(||)) =
            preserveDemand . POr <$> mapM coreToLg [e1, e2]
        | f == symbol (show '(&&)) =
            preserveDemand . PAnd <$> mapM coreToLg [e1, e2]
        | f == symbol ("Language.Haskell.Liquid.Prelude.==>" :: String) =
            preserveDemand <$> (PImp <$> coreToLg e1 <*> coreToLg e2)
        | f == symbol ("Language.Haskell.Liquid.Prelude.<=>" :: String) =
            PIff <$> coreToLg e1 <*> coreToLg e2
        | f == symbol (show 'const) =
            coreToLg e1
    go (Just f, [es])
        | f == symbol (show 'or) =
            preserveDemand . POr . deList <$> coreToLg es
        | f == symbol (show 'and) =
            preserveDemand . PAnd . deList <$> coreToLg es
    go (_, _) =
        toLogicApp p

    deList :: Expr -> [Expr]
    deList (EApp (EApp (EVar cons) e) es)
      | cons == symbol (show '(:))
      = e:deList es
    deList (EVar nil)
        | nil == symbol (show '[]) =
            []
    deList e =
        [e]

-- The logical value is unchanged, but source short-circuit order is retained
-- for formation and PLE equation demand. Do not use pIte: it emits implications.
preserveDemand :: Expr -> Expr
preserveDemand = Vis.mapExprOnExpr go
  where
    go (PAnd es) = foldr (\e rest -> EIte e rest PFalse) PTrue es
    go (POr es)  = foldr (\e rest -> EIte e PTrue rest) PFalse es
    go (PImp p q) = EIte p q PTrue
    go e = e

toLogicApp :: C.CoreExpr -> LogicM Expr
toLogicApp expression
    | (C.Var constructor, _) <- C.collectArgs expression
    , ignoreVar constructor =
        ordinaryLogicApp expression
toLogicApp expression
    | (C.Var constructor, arguments) <- C.collectArgs expression
    , C.DataConWorkId dc <- C.idDetails constructor
    , Just (resultConstructor, _) <- splitTyConApp_maybe (exprType expression)
    , resultConstructor == Ghc.dataConTyCon dc = do
        let actual = drop (length (Ghc.dataConUnivTyVars dc)) arguments
        fields <- sourceFields dc (exprType expression) actual
        logicalFields <- mapM coreToLg fields
        pure (F.mkEApp (GM.namedLocSymbol dc) logicalFields)
toLogicApp expression
    | (C.Var constructor, arguments) <- C.collectArgs expression
    , C.DataConWrapId dc <- C.idDetails constructor
    , Just (resultConstructor, _) <- splitTyConApp_maybe (exprType expression)
    , let representation = Ghc.dataConTyCon dc
    , resultConstructor == maybe representation fst (Ghc.tyConFamInst_maybe representation) = do
        logicalFields <- mapM coreToLg (filter sourceArgument arguments)
        pure (F.mkEApp (GM.namedLocSymbol dc) logicalFields)
  where
    sourceArgument (C.Type _) = False
    sourceArgument (C.Coercion _) = False
    sourceArgument argument = not (GM.isEmbeddedDictType (exprType argument))
toLogicApp expression = ordinaryLogicApp expression

ordinaryLogicApp :: C.CoreExpr -> LogicM Expr
ordinaryLogicApp e = do
    state <- getState
    let (f, es) = splitArgs (typeclass (lsConfig state)) e
    known <- coreMeaning f
    definition <- case known of
        Just meaning -> Just . foldl applyMeaning meaning <$> mapM coreToLg es
        Nothing -> declaredDefinition state e
    case definition of
        Just meaning -> pure meaning
        Nothing -> do
            fe <- coreToLg f
            args <- mapM coreToLg es
            pure (foldl applyMeaning fe args)

-- An explicit define owns the interpretation of this exact source function,
-- not a law of its class. Its parameters name visible source arguments; actual
-- GHC constraint binders remain coordinates of the whole function, unused in
-- the declared body. Build that whole meaning before substituting any supplied
-- values, so partial applications and aliases obey capture-avoiding beta.
-- Type applications are consumed at their actual telescope positions, before
-- splitArgs erases them. Ordinary source checking still sees the complete Core.
declaredDefinition :: LState -> CoreExpr -> LogicM (Maybe Expr)
declaredDefinition state expression
    | (C.Var function, arguments) <- C.collectArgs expression
    , not (ignoreVar function)
    , Just (LMap _ parameters _) <- M.lookup (symbol function) (lmSymDefs definitions) = do
        let body = eAppWithMap definitions (symbol function) (map EVar parameters) (EVar (symbol function))
            namespace = F.syms body `S.union` S.fromList parameters
        (meaning, actuals) <- build body namespace (varType function) parameters arguments
        values <- mapM coreToLg actuals
        pure (Just (foldl applyMeaning meaning values))
    | otherwise = pure Nothing
  where
    definitions = lsSymMap state
    bad :: LogicM a
    bad = throw ("Cannot align declared logical alias with typed source application: " ++ GM.showPpr expression)

    build body namespace ty parameters arguments
        | GhcType.isForAllTy ty = case arguments of
            C.Type argument : rest ->
                build body namespace (GhcType.piResultTy ty argument) parameters rest
            C.Coercion argument : rest ->
                build body namespace (GhcType.piResultTy ty (GhcType.CoercionTy argument)) parameters rest
            _ -> bad
        | Just (visibility, _, domain, result) <- GhcType.splitFunTy_maybe ty
        , isInvisibleFunArg visibility = do
            let (namespace', binder) = F.freshInNS (symbol ("$defineEvidence" :: String)) namespace
            (actual, rest) <- argument arguments
            (body', actuals) <- build body namespace' result parameters rest
            if GM.isEmbeddedDictType domain
                then pure (body', actuals)
                else pure (ELam (binder, typeSort (lsEmb state) domain) body', maybe actuals (: actuals) actual)
        | null parameters = pure (body, arguments)
        | Just (_, _, domain, result) <- GhcType.splitFunTy_maybe ty
        , parameter : parameters' <- parameters = do
            (actual, rest) <- argument arguments
            (body', actuals) <- build body namespace result parameters' rest
            pure (ELam (parameter, typeSort (lsEmb state) domain) body', maybe actuals (: actuals) actual)
        | otherwise = bad

    argument [] = pure (Nothing, [])
    argument (C.Type{} : _) = bad
    argument (actual : rest) = pure (Just actual, rest)

applyMeaning :: Expr -> Expr -> Expr
-- Equal-sort coercions denote identity (also the existing PLE rule). Expose
-- the same function before beta; unequal coercions retain their interpretation.
applyMeaning (ECoerc source target function) argument
    | source == target = applyMeaning function argument
applyMeaning (ELam (parameter, _) body) argument =
    F.subst1 body (parameter, argument)
applyMeaning function argument = EApp function argument

eVarWithMap :: Id -> LogicMap -> Expr
eVarWithMap x lmap = do
    eAppWithMap lmap (symbol x) [] (EVar $ symbol x)

splitArgs :: Bool -> C.CoreExpr -> (C.CoreExpr, [C.CoreExpr])
splitArgs _allowTC exprt = (exprt', reverse args)
  where
    (exprt', args) = go exprt

    go expression | Just _ <- dataTagPrefix expression = (expression, [])
    go (C.App f (C.Type _)) = go f
    go (C.App f C.Coercion{}) = go f
    go (C.App f (C.Var v)) | GM.isEmbeddedDictVar v = go f
    go (C.App f e) = (f', e:es) where (f', es) = go f
    go f           = (f, [])

tomaybesymbol :: C.CoreExpr -> Maybe Symbol
tomaybesymbol (C.Var x) = Just $ symbol x
tomaybesymbol _         = Nothing


mkLit :: Literal -> Maybe Expr
mkLit (LitNumber LitNumBigNat _) = Nothing
mkLit (LitNumber _ n) = mkI n
-- mkLit (MachInt64  n)    = mkI n
-- mkLit (MachWord   n)    = mkI n
-- mkLit (MachWord64 n)    = mkI n
-- mkLit (LitInteger n _)  = mkI n
mkLit (LitFloat  n)    = mkR n
mkLit (LitDouble n)    = mkR n
mkLit (LitString    s) = Just (mkS s)
mkLit (LitChar   c)    = mkC c
mkLit LitNullAddr = mkI 0
mkLit _                 = Nothing -- ELit sym sort

mkI :: Integer -> Maybe Expr
mkI = Just . ECon . I

mkR :: Rational -> Maybe Expr
mkR                    = Just . ECon . F.R . fromRational

mkS :: ByteString -> Expr
mkS = ESym . SL  . decodeUtf8With lenientDecode

mkC :: Char -> Maybe Expr
mkC                    = Just . ECon . (`F.L` F.charSort)  . repr
  where
    repr               = T.pack . show . Data.Char.ord

ignoreVar :: Id -> Bool
ignoreVar i = case Ghc.isDataConId_maybe i of
    Just dc -> dc `elem` [Ghc.intDataCon, doubleDataCon, Ghc.integerISDataCon]
    Nothing -> False

-- | Tries to determine if a 'CoreAlt' maps to one of the 'Integer' type constructors.
isBangInteger :: [C.CoreAlt] -> Bool
isBangInteger [Alt (C.DataAlt s) _ _, Alt (C.DataAlt jp) _ _, Alt (C.DataAlt jn) _ _]
  =  s  == Ghc.integerISDataCon
  && jp == Ghc.integerIPDataCon
  && jn == Ghc.integerINDataCon
isBangInteger _ = False

isANF :: Id -> Bool
isANF      v = isPrefixOfSym (symbol ("lq_anf" :: String)) (simpleSymbolVar v)

isDead :: Id -> Bool
isDead     = isDeadOcc . occInfo . Ghc.idInfo

-- | 'normalizeCoreExpr allowTC e' simplifies the Core expression 'e' by:
--   1. inlining predicates (i.e. applications of measures that return Bool)
--   2. inlining ANF variables (i.e. variables that are introduced by the ANF transformation)
--   3. simplifying the expression by removing dead binders and applications of
--      type arguments and dictionaries.
--
-- Runtime dictionaries are retained independently of the optional class
-- elaboration mode; only primitive equality evidence is erased.
--
normalizeCoreExpr :: Bool -> CoreExpr -> CoreExpr
normalizeCoreExpr allowTC = inline_preds . inline_anf . simplifyCoreExpr allowTC
  where
    inline_preds = inlineCoreExpr (eqType boolTy . GM.expandVarType)
    inline_anf   = inlineCoreExpr isANF

-- | 'simplifyCoreExpr allowTC e' removes dead binders while retaining typed
-- application spines. Constructor reconstruction needs the actual type and
-- evidence arguments; 'splitArgs' erases them at logical interpretation.
--
-- The optional class elaboration mode does not change runtime meaning.
-- Only primitive equality evidence has no logical value coordinate.
--
-- This function is used in 'normalizeCoreExpr' to simplify the Core expression
-- before inlining predicates and ANF variables.
--
-- The 'simplifyCoreExpr' function recursively traverses the Core expression and
-- applies the following simplifications:
--   1. It retains applications of type arguments (i.e. 'C.App e1 (C.Type _)').
--   2. It retains applications of evidence variables for typed reconstruction.
--   3. It removes applications of lambda expressions where the binder is dead
--      (i.e. 'C.App (C.Lam x e) _' where 'x' is dead).
--   4. It removes lambda expressions where the binder is a type variable
--      (i.e. 'C.Lam x e' where 'x' is a type variable).
--   5. It removes lambda expressions where the binder is considered erasable
--      (i.e. 'C.Lam x e' where 'x' is erasable).
--   6. It removes non-recursive let bindings where the binder is considered
--      erasable (i.e. 'C.Let (C.NonRec x eb) e' where 'x' is erasable).
--   7. It removes recursive let bindings where all binders are considered
--      erasable (i.e. 'C.Let (C.Rec xes) e' where all 'x' in 'xes' are
--      erasable).
--   8. It simplifies case expressions that match on a boolean by checking if
--      the alternatives correspond to 'True' and 'False' and then substituting
--      the scrutinee with the appropriate alternative.
--   9. It simplifies case expressions by removing alternatives that correspond
--      to pattern match errors (i.e. 'isPatErrorAlt').
--   10. It recursively simplifies applications, casts, ticks, coercions, and
--       type expressions.
--
simplifyCoreExpr :: Bool -> CoreExpr -> CoreExpr
simplifyCoreExpr _allowTC = go
  where
    isDictOrErasable = GM.isEmbeddedDictVar

    go :: CoreExpr -> CoreExpr
    go e@(C.Var _)
      = e
    go e@(C.Lit _)
      = e
    go (C.App e1 arg@(C.Type _)) =
        C.App (go e1) arg
    go (C.App (C.Lam x e) _)
      | isDead x
      = go e
    go (C.App e1 e2)
      = C.App (go e1) (go e2)
    go (C.Lam x e)
      | isTyVar x
      = go e
    go (C.Lam x e)
      | isDictOrErasable x
      = go e
    go (C.Lam x e)
      = C.Lam x (go e)
    go (C.Let (C.NonRec x eb) e)
      | isDictOrErasable x
      = go e
      | otherwise
      = C.Let (C.NonRec x (go eb)) (go e)
    go (C.Let (C.Rec xes) e)
      | all (isDictOrErasable . fst) xes
      = go e
      | otherwise
      = C.Let (C.Rec (map (fmap go) xes)) (go e)
    go (C.Case e x _t alts@[Alt _ _ ee,_,_])
      | isBangInteger alts
      = sub x (go e) (go ee)
    go (C.Case e x t alts)
      = C.Case (go e) x t $
         filter
           (not . isPatErrorAlt)
           [ Alt c xs (go ealt) | Alt c xs ealt <- alts ]
    go (C.Cast e c)
      = C.Cast (go e) c
    go (C.Tick _ e)
      = go e
    go (C.Coercion c)
      = C.Coercion c
    go (C.Type t)
      = C.Type t

-- | Substitute variable bindings in a CoreExpr using GHC's capture-avoiding
-- substExpr.
--
-- TODO: This implementation is a bit wastful since it collects the free
-- variables of both expressions every time, we could pass a superset of the
-- free variables instead. But the overhead is not observable in our tests.
sub :: CoreBndr -> CoreExpr -> CoreExpr -> CoreExpr
sub x e0 e = Ghc.substExpr su e
  where
    fvs     = Ghc.exprFreeVars e `Ghc.unionVarSet` Ghc.exprFreeVars e0
    inScope = Ghc.mkInScopeSet fvs
    su   = Ghc.extendIdSubst (Ghc.mkEmptySubst inScope) x e0

inlineCoreExpr :: (Id -> Bool) -> CoreExpr -> CoreExpr
inlineCoreExpr p (C.Let (C.NonRec x ex) e)
  | p x = sub x (inlineCoreExpr p ex) (inlineCoreExpr p e)
  | otherwise = C.Let (C.NonRec x (inlineCoreExpr p ex)) (inlineCoreExpr p e)
inlineCoreExpr p (C.Let (C.Rec xes) e) = C.Let (C.Rec (map (fmap (inlineCoreExpr p)) xes)) (inlineCoreExpr p e)
inlineCoreExpr p (C.App e1 e2)       = C.App (inlineCoreExpr p e1) (inlineCoreExpr p e2)
inlineCoreExpr p (C.Lam x e)         = C.Lam x (inlineCoreExpr p e)
inlineCoreExpr p (C.Case e x t alts) =
  C.Case (inlineCoreExpr p e) x t
    [ Alt c xs (inlineCoreExpr p ealt) | Alt c xs ealt <- alts ]
inlineCoreExpr p (C.Cast e c)        = C.Cast (inlineCoreExpr p e) c
inlineCoreExpr p (C.Tick t e)        = C.Tick t (inlineCoreExpr p e)
inlineCoreExpr _ (C.Var x)           = C.Var x
inlineCoreExpr _ (C.Lit l)           = C.Lit l
inlineCoreExpr _ (C.Coercion c)      = C.Coercion c
inlineCoreExpr _ (C.Type t)          = C.Type t
