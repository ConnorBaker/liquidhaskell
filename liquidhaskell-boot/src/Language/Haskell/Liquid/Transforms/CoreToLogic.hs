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
  , firstOrderOnly
  , mkLit, mkI, mkS
  , runToLogic
  , runToLogicWithBoolBinds
  , logicType
  , inlineSpecType
  , measureSpecType
  , weakenResult
  , normalizeCoreExpr
  , workerApp
  ) where

import           Data.Bifunctor (first)
import           Data.ByteString                       (ByteString)
import           Prelude                               hiding (error)
import           Language.Haskell.Liquid.GHC.TypeRep   () -- needed for Eq 'Type'
import           Liquid.GHC.API       hiding (Expr, Located, get, panic)
import qualified Liquid.GHC.API       as Ghc
import qualified Liquid.GHC.API       as C
import qualified Data.List                             as L
import           Data.Maybe                            (listToMaybe, fromMaybe)
import qualified Data.Text                             as T
import qualified Data.Char
import qualified Text.Printf as Printf
import           Data.Text.Encoding
import           Data.Text.Encoding.Error
import           Control.Monad.Except
import           Control.Monad.Identity
import qualified Language.Haskell.Liquid.Misc          as Misc
import           Language.Fixpoint.Types               hiding (panic, Error, R, simplify, isBool)
import qualified Language.Fixpoint.Types               as F
import qualified Language.Haskell.Liquid.GHC.Misc      as GM


import           Language.Haskell.Liquid.Bare.Types
import           Language.Haskell.Liquid.Bare.DataType
import           Language.Haskell.Liquid.Types.RepMap
import           Language.Haskell.Liquid.Bare.Misc     (simpleSymbolVar)
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp
import           Language.Haskell.Liquid.Types.Types

import qualified Data.HashMap.Strict                   as M
import qualified Data.HashSet                          as HS
import Control.Monad.Reader
import Language.Fixpoint.Types.Visitor (mapExprOnExpr, lamSize)
import Language.Haskell.Liquid.UX.Config

import Data.Ratio
import GHC.Base ((+#), (-#), (*#))

logicType :: (IsReft r) => Bool -> Type -> RRType r
logicType allowTC τ      = fromRTypeRep $ t { ty_binds = bs, ty_info = is, ty_args = as, ty_refts = rs}
  where
    t            = toRTypeRep $ ofType τ
    (bs, is, as, rs) = Misc.unzip4 $ dropWhile (isErasable' . Misc.thd4) $ Misc.zip4 (ty_binds t) (ty_info t) (ty_args t) (ty_refts t)
    isErasable'  = if allowTC then isEmbeddedClass else isClassType

{- | [NOTE:inlineSpecType type]: the refinement depends on whether the result type is a Bool or not:
      CASE1: measure f@logic :: X -> Bool <=> f@haskell :: x:X -> {v:Bool | v <=> (f@logic x)}
     CASE2: measure f@logic :: X -> Y    <=> f@haskell :: x:X -> {v:Y    | v = (f@logic x)}
 -}
-- formerly: strengthenResult
inlineSpecType :: Bool -> Var -> SpecType
inlineSpecType  allowTC v = fromRTypeRep $ rep {ty_res = res `strengthen` r , ty_binds = xs}
  where
    r              = MkUReft (mkReft (mkEApp f (mkA <$> vxs))) mempty
    rep            = toRTypeRep t
    res            = ty_res rep
    xs             = intSymbol (symbol ("x" :: String)) <$> [1..length $ ty_binds rep]
    vxs            = dropWhile (isErasable' . snd) $ zip xs (ty_args rep)
    isErasable'    = if allowTC then isEmbeddedClass else isClassType
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
measureSpecType allowTC v = go mkT [] [(1::Int)..] st
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
     | (if allowTC then isEmbeddedClass else isClassType) t1           = RFun x ii t1 (go f args i t2) r
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
weakenResult allowTC v t = F.notracepp msg t'
  where
    msg          = "weakenResult v =" ++ GM.showPpr v ++ " t = " ++ showpp t
    t'           = fromRTypeRep $ rep { ty_res = mapExprReft weaken (ty_res rep) }
    rep          = toRTypeRep t
    weaken x     = pAnd . filter ((Just vE /=) . isSingletonExpr x) . conjuncts
    vE           = mkEApp vF xs
    xs           = EVar . fst <$> dropWhile ((if allowTC then isEmbeddedClass else isClassType) . snd) xts
    xts          = zip (ty_binds rep) (ty_args rep)
    vF           = dummyLoc (symbol v)

type LogicM = ExceptT Error (ReaderT LState Identity)

data LState = LState
  { lsSymMap  :: LogicMap
  , lsError   :: String -> Error
  , lsEmb     :: TCEmb TyCon
  , lsBools   :: [Var]
  , lsDCMap   :: Maybe DataConMap
    -- ^ 'Nothing' at the inline leaf, which is lifted before the module's
    -- datatypes are declared (see 'firstOrderOnly' and @Bare.Measure@).
  , lsConfig  :: Config
  }

-- | The datatype map, empty where the leaf carries none.
dcMap :: LState -> DataConMap
dcMap = fromMaybe mempty . lsDCMap

throw :: String -> LogicM a
throw str = do
  fmkError  <- reader lsError
  throwError $ fmkError str

getState :: LogicM LState
getState = ask

runToLogic
  :: TCEmb TyCon -> LogicMap -> Maybe DataConMap -> Config -> (String -> Error)
  -> LogicM t -> Either Error t
runToLogic = runToLogicWithBoolBinds []

runToLogicWithBoolBinds
  :: [Var] -> TCEmb TyCon -> LogicMap -> Maybe DataConMap -> Config -> (String -> Error)
  -> LogicM t -> Either Error t
runToLogicWithBoolBinds xs tce lmap dm cfg ferror m
  = runReader (runExceptT m) $ LState
      { lsSymMap = lmap
      , lsError  = ferror
      , lsEmb    = tce
      , lsBools  = xs
      , lsDCMap  = dm
      , lsConfig = cfg
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
          allowTC <- reader (typeclass . lsConfig)
          dm      <- reader dcMap
          embs    <- reader lsEmb
          let xs' = filter (not . if allowTC then GM.isEmbeddedDictVar else GM.isEvVar) xs
          body    <- coreToLg e >>= firstOrderOnly
          -- The alternative's binders @xs'@ are the constructor's REPRESENTATION
          -- arguments, but a measure equation is written against its SOURCE
          -- fields -- which is what the logic knows @d@ to take. The two agree
          -- unless GHC has UNPACKed a strict field, so re-express the body over
          -- source-field binders whenever it has. See 'unpackedFieldSubst'.
          case dataConRepMap embs d of
            Right rm | Just (srcArgs, rewrite) <- unpackedFieldSubst dm rm xs' x ->
              -- ...unless the composition reaches through a field that has no
              -- selector, exactly as 'altToLg' refuses for the nested-case
              -- twin, or the equation KEEPS a source binder that 'toWorkerDef'
              -- will later have to rebuild through a constructor the logic does
              -- not know. Without either refusal the equation is lifted around
              -- an undeclared symbol and the failure surfaces as
              -- @Unbound symbol@ at the DATA DECLARATION, naming neither the
              -- measure nor the field. The second case is the one the eta law
              -- makes reachable: @a2R (A2 r) = r@ over @A2 !(IORef Int)@ has
              -- the Core body @IORef (STRef mv)@, whose rewrite collapses to
              -- the source binder @r@ and so names no selector at all.
              let out = rewrite body
              in case namesDroppedSelector (undeclaredSelectorsOf (knownDataCon dm) (makeDataConSelector (Just dm)) rm) out
                        `orElseMb` keepsUnrebuildable (knownDataCon dm) rm srcArgs out of
                Just (d', i) -> throw (noSelectorMsg d' i)
                Nothing      ->
                  return
                    . Def x d (Just $ varRType dx) srcArgs
                    . ctor
                    $ out `subst1` (F.symbol dx, F.mkEApp (GM.namedLocSymbol d) (F.eVar . fst <$> srcArgs))
            _ ->
              return
                . Def x {- (toArgs id args) -} d (Just $ varRType dx) (toArgs Just xs')
                . ctor
                $ body `subst1` (F.symbol dx, F.mkEApp (GM.namedLocSymbol d) (F.eVar <$> xs'))
    mkAlt _ _ _ _ alt
      = throw $ "Bad alternative" ++ GM.showPpr alt

    mkDef x ctor _args dx (Just dtss) (Just e) = do
      e0     <- coreToLg e >>= firstOrderOnly
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

toArgs :: IsReft r => (Located (RRType r) -> b) -> [Var] -> [(Symbol, b)]
toArgs f args = [(symbol x, f $ varRType x) | x <- args]

defArgs :: IsReft r => Located LHName -> [Type] -> [(Symbol, Maybe (Located (RRType r)))]
defArgs x     = zipWith (\i t -> (defArg i, defRTyp t)) [0..]
  where
    defArg    = tempSymbol (lhNameToResolvedSymbol $ val x)
    defRTyp   = Just . F.atLoc x . ofType

coreToDef :: IsReft r => Located LHName -> Var -> C.CoreExpr
          -> LogicM [Def (Located (RRType r)) DataCon]
coreToDef locSym _ s              = do
    allowTC <- reader $ typeclass . lsConfig
    go [] $ inlinePreds $ simplifyCoreExpr allowTC s
  where
    go args   (C.Lam  x e)        = go (x:args) e
    go args   (C.Tick _ e)        = go args e
    go (z:zs) (C.Case _ y t alts) = coreAltToDef locSym z zs y t alts
    go (z:zs) e
      | Just t <- isMeasureArg z  = coreAltToDef locSym z zs z t [Alt C.DEFAULT [] e]
    go _ _                        = measureFail locSym "Does not have a case-of at the top-level"

    inlinePreds   = inlineCoreExpr (eqType boolTy . GM.expandVarType)

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
      allowTC <- reader $ typeclass . lsConfig
      let isE = if allowTC then GM.isEmbeddedDictVar else isErasable
      if isE x then go acc e else go (x:acc) e
    go acc (C.Tick _ e) = go acc e
    go acc e            = (reverse acc,) . Right <$> (coreToLg e >>= firstOrderOnly)


instance Show C.CoreExpr where
  show = GM.showPpr

coreToLogic :: C.CoreExpr -> LogicM Expr
coreToLogic cb = do
  allowTC <- reader $ typeclass . lsConfig
  coreToLg $ normalizeCoreExpr allowTC cb


-- | Make a lifted DEFINITION first-order where eta-reduction can, and refuse
-- it where eta cannot, unless higher-order logic is on.
--
-- 'coreToLg' lifts a 'C.Lam' to an 'ELam' unconditionally, but liquid-fixpoint
-- can only send a lambda to the SMT solver when its @allowHO@ flag is set,
-- which 'higherOrderFlag' controls: @Defunctionalize.txExpr@ renames lambda
-- binders to @lam_arg##i@ (and declares those) only under that flag, while
-- @Serialize.smt2Lam@ always renders the binder through @smtLamArg@. Without the
-- flag the binder reaches z3 as @x##0@ beside a body that says @x@, neither of
-- them declared, and the whole query dies with
-- @crash: SMTLIB2 respSat = Error "... unknown constant x##0"@ -- no
-- location, no binder, and no mention that a flag exists.
--
-- GHC manufactures such a lambda from source that has none: a data constructor
-- passed as a VALUE desugars to @\\ds -> $WW ds@ (@\\ds -> W ds@ for a lazy
-- field), at -O0 as much as at -O2, so @mkW n = apply W n@ under @reflect@
-- lifts to @apply (\\ds -> W ds) n@ once 'toLogicApp' has put the wrapper
-- @$WW@ back onto the logic constructor @W@. That lambda is exactly
-- @\\x -> f x@ with @x@ not free in @f@, and 'etaReduce' turns it into @f@,
-- so the definition becomes @apply W n@ -- a function SYMBOL in argument
-- position, which liquid-fixpoint represents without @allowHO@ through its
-- @apply##@ encoding, the same way it represents @apply inc n@ for a
-- reflected @inc@.
--
-- Whatever lambda eta cannot remove -- @\\x -> x + 1@, or any body that is not
-- an application to the bound variable -- is refused here, through 'LogicM''s
-- 'throw', so the error is an 'ErrHMeas' located at the reflect/inline/measure
-- pragma, naming the function and the flag.
--
-- ONE lambda is withheld from eta: under 'adtFlag' (@--adt@, or @--reflection@
-- which implies it), a lambda whose eta result has a DATA CONSTRUCTOR at its
-- head. With that flag 'Constraint.ToFixpoint.makeDecls' declares the module's
-- datatypes to z3 through @declare-datatypes@, and a constructor used as a
-- VALUE -- the bare @W@ of @apply W n@, or the partial @MkPair x@ of
-- @State (MkPair x)@ -- is then read by z3 at the function-as-array sort
-- @(Array Int W)@, which neither @apply## (Int Int)@ nor a constructor field
-- declared @Int@ accepts:
--
-- > unknown constant apply##1 (Int (Array Int W)) declared: (declare-fun apply##1 (Int Int) Int)
-- > unknown constant MkPair (Int) (Pair Int Int) declared: (declare-fun MkPair (Int Int) (Pair Int Int))
--
-- Without the flag every symbol is an @Int@-sorted @declare-fun@ and the same
-- eta result is well sorted; a function that is not a constructor (@plus a@)
-- is well sorted either way. The lambda itself serializes under @allowHO@ as an
-- @Int@-sorted @smt_lambda##@, so for that one shape the lambda is KEPT when
-- 'higherOrderFlag' is on and REFUSED when it is off, where both encodings
-- crash. The head test is membership in the 'Bare.DataConMap' ('lsDCMap'),
-- keyed on @(constructor symbol, 0)@ for every constructor the logic has a
-- datatype for -- the same map 'knownDataCon' reads and the same set of
-- datatypes @makeDecls@ declares, so at the reflect and measure leaves, which
-- carry that map, the guard fires on exactly the symbols z3 will see as
-- constructors. The inline leaf carries NO map ('lsDCMap' is 'Nothing'): it
-- is lifted at stage 0 of @Bare.makeGhcSpec0@, before 'Bare.makeTycEnv0'
-- builds the map, and the map depends on the inlines themselves through the
-- alias expansion of the data declarations, so threading it there would make
-- a data refinement that names such an inline force its own body. There the
-- guard has no oracle and withholds eta from EVERY lambda under 'adtFlag',
-- erring toward the refusal: an inlined constructor-as-value is kept and
-- serialized under @--reflection@ and refused under @--adt@ alone, and so is
-- an inlined @\\x -> plus a x@ under @--adt@ alone, which the reflect leaf
-- would have proved. Under @--adt@ from -O1 up GHC eta-reduces the Core lambda
-- itself and 'workerApp' is off, so @mkW@ lifts to @apply $WW n@ and is
-- merely unprovable; that is not this function's to fix.
--
-- Both steps sit on what becomes a logic DEFINITION -- a reflected body
-- ('Bare.Axiom.makeAssumeType'), an inlined body and a bound ('coreToFun'), a
-- measure alternative ('coreAltToDef') -- and deliberately NOT inside
-- 'coreToLg' itself. Its other callers want the lambdas: the typeclass
-- elaborator ('Bare.Elaborate.elaborateSpecType') lifts a lambda per binder
-- on purpose, peels them off again with @grabLams@, and PANICS if the count it
-- gets back differs from the count it wrapped, which an eta step under it
-- would cause for any refinement of the form @p x@; and
-- 'Constraint.Generate.lamExpr' is only reached under 'higherOrderFlag'.
firstOrderOnly :: Expr -> LogicM Expr
firstOrderOnly e0 = do
  cfg  <- reader lsConfig
  dmMb <- reader lsDCMap
  let ctorHead f = case (dmMb, F.splitEAppThroughECst f) of
                     (Nothing, _)           -> True
                     (Just dm, (EVar c, _)) -> M.member (c, 0) dm
                     (Just _,  _)           -> False
      e = etaReduce (if adtFlag cfg then ctorHead else const False) e0
  if higherOrderFlag cfg || lamSize e == 0
    then return e
    else throw $ unwords
      [ "the body contains a lambda, which requires the --higherorder flag"
      , "(implied by --reflection); without it liquid-fixpoint cannot represent"
      , "the term:", F.showpp e ]

-- | Rewrite every @\\x -> f x@ whose @x@ does not occur in @f@ to @f@,
-- innermost lambda first, so @\\a -> \\b -> f a b@ becomes @f@ -- except where
-- the predicate says the result @f@ must not stand alone (see
-- 'firstOrderOnly').
--
-- This is sound in the logic because its functions are TOTAL and
-- EXTENSIONAL: a function-sorted term denotes a mathematical function, two of
-- them are equal exactly when they agree at every argument, and
-- @(\\x -> f x) a@ and @f a@ are the same term for every @a@ -- there is no
-- bottom, no partial application that fails, and no observable difference
-- between a lambda and the function it wraps. liquid-fixpoint's encoding
-- keeps that reading: a function value is an uninterpreted symbol and its
-- application is @apply##@ over it, so @f@ in argument position means what
-- @\\x -> f x@ would have meant had the lambda been representable.
--
-- The guard, @x@ not among @syms f@, is what makes it a REDUCTION rather than
-- a rewrite: in @\\x -> plus x x@ the function part mentions the binder, the
-- two terms differ, and the lambda is left alone. 'F.syms' collects every
-- symbol in @f@, bound or free, so the test is conservative -- it withholds
-- the reduction from a term that shadows @x@ inside @f@ as well.
--
-- 'mapExprOnExpr' is post-order and descends into lambda bodies, so the inner
-- lambda of @\\a -> \\b -> f a b@ is reduced first, to @\\a -> f a@, and the
-- outer one then reduces to @f@.
etaReduce :: (Expr -> Bool) -> Expr -> Expr
etaReduce withheld = mapExprOnExpr step
  where
    step (ELam (x, _) (EApp f (EVar y)))
      | x == y, not (x `HS.member` F.syms f), not (withheld f) = f
    step e = e

coreToLg :: C.CoreExpr -> LogicM Expr
coreToLg (C.Let (C.NonRec x (C.Coercion c)) e)
  = coreToLg (C.substExpr (C.extendCvSubst C.emptySubst x c) e)
coreToLg (C.Let b e)
  = subst1 <$> coreToLg e <*> makesub b
coreToLg (C.Tick _ e)          = coreToLg e
coreToLg (C.App (C.Var v) e)
  | ignoreVar v                = coreToLg e
coreToLg (C.Var x)
  | x == falseDataConId        = return PFalse
  | x == trueDataConId         = return PTrue
  | otherwise                  = eVarWithMap x . lsSymMap <$> getState
coreToLg e@(C.App _ _)         = toPredApp e
coreToLg (C.Case e b _ alts)
  | eqType (GM.expandVarType b) boolTy  = checkBoolAlts alts >>= coreToIte e
-- coreToLg (C.Lam x e)           = do p     <- coreToLg e
--                                     tce   <- lsEmb <$> getState
--                                     return $ ELam (symbol x, typeSort tce (GM.expandVarType x)) p
coreToLg (C.Case e b _ alts)   = do p <- coreToLg e
                                    casesToLg b p alts
coreToLg (C.Lit l)             = case mkLit l of
                                          Nothing -> throw $ "Bad Literal in measure definition" ++ GM.showPpr l
                                          Just i  -> return i
coreToLg (C.Cast e c)
  | Just (dc, ntCo) <- newtypeCoercionDataCon c
  = do e'   <- coreToLg e
       case ntCo of
         -- @e |> (Rep ~ NT)@ is the newtype constructor applied to @e@.
         WrapCoercion ->
           return $ F.mkEApp (GM.namedLocSymbol dc) [e']
         -- @e |> (NT ~ Rep)@ is the newtype field selector applied to @e@.
         UnwrapCoercion -> do
           dm <- reader dcMap
           return $ EApp (EVar (makeDataConSelector (Just dm) dc 1)) e'
coreToLg (C.Cast e c)          = do (s, t) <- coerceToLg c
                                    e'     <- coreToLg e
                                    return (ECoerc s t e')
-- elaboration reuses coretologic
-- TODO: fix this
coreToLg (C.Lam x e) = do p     <- coreToLg e
                          tce   <- lsEmb <$> getState
                          return $ ELam (symbol x, typeSort tce (GM.expandVarType x)) p
coreToLg e                     = throw ("Cannot transform to Logic:\t" ++ GM.showPpr e)




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
casesToLg v e alts = mapM (altToLg e) normAlts >>= go
  where
    normAlts       = normalizeAlts alts
    go :: [(C.AltCon, Expr)] -> LogicM Expr
    go [(_,p)]     = return (p `subst1` su)
    go ((d,p):dps) = do c <- checkDataAlt d e
                        e' <- go dps
                        return (EIte c p e' `subst1` su)
    go []          = panic (Just (getSrcSpan v)) $ "Unexpected empty cases in casesToLg: " ++ show e
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

altToLg :: Expr -> C.CoreAlt -> LogicM (C.AltCon, Expr)
altToLg de (Alt a@(C.DataAlt d) xs e) = do
    p  <- coreToLg e
    dm <- reader dcMap
    embs <- reader lsEmb
    allowTC <- reader (typeclass . lsConfig)
    let xs' = filter (not . if allowTC then GM.isEmbeddedDictVar else GM.isEvVar) xs
        sel = makeDataConSelector (Just dm)
        bind v pr = [(symbol v, pr), (GM.simplesymbol v, pr)]
    case dataConRepMap embs d of
      -- The alternative binds the constructor's REPRESENTATION arguments,
      -- while 'makeDataConSelector' names its SOURCE fields; the two lists
      -- agree only when GHC unpacked nothing. Where it did, reach each
      -- representation binder by the composition of selectors that gets to
      -- it -- 'projectField' over the constructor's 'RepMap', exactly as
      -- 'unpackedFieldSubst' does for the top-level case of a lifted
      -- equation, of which this is the nested-case twin.
      Right rm | rmChanged rm
               , let projs = concat [ projectField sel fr (EApp (EVar (sel d j)) de)
                                    | (j, fr) <- zip [1 ..] (rmFields rm) ]
               , length projs == length xs' ->
        -- ...unless a field this projects through has NO selector, because
        -- unpacking moved its sort. 'makeDataConSelector' still returns a
        -- name for it, but 'makeMeasureSelectors' never declared it, so the
        -- equation would be lifted around an @Unbound symbol@ reported at the
        -- DATA DECLARATION rather than here. Refusing names the measure and
        -- the field instead. 'undeclaredSelectorsOf' walks the whole descent,
        -- not only this constructor, and 'namesDroppedSelector' refuses only
        -- when the equation this actually emits names one of them.
        let out = etaCollapse (ctorLeafProjs sel rm : concatMap (fieldCtorProjs sel) (rmFields rm))
                    (subst (mkSubst (concat (zipWith bind xs' projs))) p)
        in case namesDroppedSelector (undeclaredSelectorsOf (knownDataCon dm) sel rm) out of
             Just (d', i) -> throw (noSelectorMsg d' i)
             Nothing      -> return (a, out)
      _ -> do
        let su = mkSubst $ concat [ dataConProj dm de d x i | (x, i) <- zip xs' [1..]]
        return (a, subst su p)

altToLg _ (Alt a _ e)
  = (a, ) <$> coreToLg e

-- | @unpackedFieldSubst dm d xs x@ bridges the gap between a data
-- constructor's REPRESENTATION arguments -- what a Core @case@ alternative
-- binds -- and its SOURCE fields, which is what the refinement logic declares
-- @d@ to take.
--
-- The two coincide unless GHC decided to UNPACK a strict field: from @-O1@ up,
-- @-funbox-small-strict-fields@ replaces a strict field whose type is a
-- single-constructor type by that constructor's own arguments. A record
-- selector for such a field is then compiled as
--
-- > pw = \p -> case p of P s -> W s
--
-- where @s@ is the UNPACKED component, of type @Set Int@, and @W s@ rebuilds
-- the source field. Lifting that body with @s@ bound at the source field's type
-- @W@ produces the ill-sorted @W (s :: W)@ -- reported as @Bad Measure
-- Specification@ on the measure and @Illegal type specification@ on the
-- constructor's wrapper, neither naming the real cause.
--
-- So: bind the equation at the source fields and substitute each
-- representation binder by the composition of selectors that reaches it. For
-- the example above @s@ becomes @wSet a1@, and the body becomes @W (wSet a1)@,
-- which 'etaCollapse' -- not the solver, which is not told that @W@ is a
-- datatype -- reduces back to @a1@.
--
-- Returns 'Nothing' -- leaving the pre-existing behaviour untouched -- unless
-- the constructor's 'RepMap' says something changed ('rmChanged') and the
-- expansion accounts for every binder. 'rmChanged' is the ONE "did anything
-- change" decision; a second one here, "is some projection more than a
-- variable", was measured wrong on a strict field of a NULLARY type, which
-- unpacks to NO worker argument: every surviving projection is a variable,
-- the equation was left Core-shaped, and the module failed at its measure
-- with @Requires 2 fields but given 1@. See
-- @tests/datacon/pos/NullaryUnpack.hs@.
unpackedFieldSubst
  :: IsReft r
  => DataConMap -> RepMap -> [Var] -> Located LHName
  -> Maybe ([(Symbol, Maybe (Located (RRType r)))], Expr -> Expr)
unpackedFieldSubst dm rm xs x
  | rmChanged rm, length projs == length xs
  = Just (srcArgs, etaCollapse ctorProjs . F.subst (F.mkSubst (concat (zipWith bind xs projs))))
  | otherwise
  = Nothing
  where
    sel         = makeDataConSelector (Just dm)
    srcArgs     = defArgs x (frSource <$> rmFields rm)
    projs       = concat (zipWith (projectField sel) (rmFields rm) (F.eVar . fst <$> srcArgs))
    ctorProjs   = ctorLeafProjs sel rm : concatMap (fieldCtorProjs sel) (rmFields rm)
    bind v p    = [(symbol v, p), (GM.simplesymbol v, p)]


-- | The first dropped selector an EMITTED expression actually names, if any.
--
-- Deciding the refusal on the expression rather than on the constructor is the
-- whole point, and getting that wrong is loud: a guard that refuses whenever
-- the CONSTRUCTOR has a resorted field rejects every equation that simply does
-- not project through it, which is most of them. Measured 2026-09-06, that
-- spelling turned ELEVEN passing modules in @tests/datacon@ red -- the five
-- @Dep@ ones project field 1 while field 2 is the @Set@ that resorts -- while
-- passing every arm written for the defect it was meant to fix.
--
-- The check runs after 'etaCollapse', so a selector the reconstruction cancels
-- is correctly not a reason to refuse.
namesDroppedSelector :: [(Symbol, (DataCon, Int))] -> Expr -> Maybe (DataCon, Int)
namesDroppedSelector tbl e
  | null tbl  = Nothing
  -- @tbl@ is in descent order and 'F.syms' is an unordered set, so the scan
  -- goes this way round: which field gets NAMED in the message would otherwise
  -- depend on a hash.
  | otherwise = listToMaybe [ field | (sel, field) <- tbl, sel `HS.member` named ]
  where
    named = F.syms e

-- | The first source-field binder the equation keeps whose field the logic
-- cannot rebuild from the worker's arguments ('fieldRebuildable'), if any.
-- 'toWorkerDef' would have to substitute that rebuild for the binder.
keepsUnrebuildable :: (DataCon -> Bool) -> RepMap -> [(Symbol, a)] -> Expr -> Maybe (DataCon, Int)
keepsUnrebuildable known rm srcArgs e
  = listToMaybe [ (rmDataCon rm, i)
                | (i, fr, (b, _)) <- zip3 [1 ..] (rmFields rm) srcArgs
                , not (fieldRebuildable known fr)
                , b `HS.member` named ]
  where
    named = F.syms e

orElseMb :: Maybe a -> Maybe a -> Maybe a
orElseMb (Just a) _ = Just a
orElseMb Nothing  b = b

-- | The refusal both projection sites report, so the two cannot drift apart.
noSelectorMsg :: DataCon -> Int -> String
noSelectorMsg d i
  =  "field " ++ show i ++ " of " ++ GM.showPpr d
  ++ " has no selector in the logic: unpacking changes its sort"


-- | @C (proj_1 e) .. (proj_m e) ==> e@: the eta law of a single-constructor
-- datatype, with @proj_k@ the projection of @e@ to the logic constructor's
-- @k@-th LEAF -- 'fieldCtorProjs' -- since the logic's @C@ takes its unpacked
-- fields' components flat.
--
-- Lifting a record selector for an UNPACKed field yields exactly that redex,
-- because GHC's Core rebuilds the field from its components and
-- 'unpackedFieldSubst' then re-expresses each component as a projection. Left
-- standing it is well sorted but opaque -- the solver has no equations for a
-- selector applied to a value it did not see constructed -- so collapse it
-- here, where the two halves are known to be inverse by construction. The
-- candidates for @e@ are the first argument and everything under it, since
-- @proj_1 e@ is a chain of selectors applied to @e@.
etaCollapse :: [(Symbol, Expr -> [Expr])] -> Expr -> Expr
etaCollapse dcs
  | null dcs  = id
  | otherwise = mapExprOnExpr step
  where
    step e0 = case splitEApp e0 of
      (EVar c, args@(a1 : _))
        | Just projs <- L.lookup c dcs
        , Just e <- L.find (\e -> projs e == args) (under a1)
        -> e
      _ -> e0
    under e = e : case splitEApp e of
      (_, [e']) -> under e'
      _         -> []

dataConProj :: DataConMap -> Expr -> DataCon -> Var -> Int -> [(Symbol, Expr)]
dataConProj dm de d x i = [(symbol x, t), (GM.simplesymbol x, t)]
  where
    t | primDataCon  d  = de
      | otherwise       = EApp (EVar $ makeDataConSelector (Just dm) d i) de

primDataCon :: DataCon -> Bool
primDataCon d = d == intDataCon

coreToIte :: C.CoreExpr -> (C.CoreExpr, C.CoreExpr) -> LogicM Expr
coreToIte e (efalse, etrue)
  = do p  <- coreToLg e
       e1 <- coreToLg efalse
       e2 <- coreToLg etrue
       return $ EIte p e2 e1

toPredApp :: C.CoreExpr -> LogicM Expr
toPredApp p = do
  allowTC <- reader (typeclass . lsConfig)
  go . first opSym . splitArgs allowTC $ p
  where
    opSym = tomaybesymbol
    go (Just f, [e1, e2])
      | Just rel <- M.lookup f brels
      = PAtom rel <$> coreToLg e1 <*> coreToLg e2
    go (Just f, [e])
      | f == symbol (show 'not)
      = PNot <$>  coreToLg e
    go (Just f, [e1, e2])
      | f == symbol (show '(||))
      = POr <$> mapM coreToLg [e1, e2]
      | f == symbol (show '(&&))
      = PAnd <$> mapM coreToLg [e1, e2]
      | f == symbol ("Language.Haskell.Liquid.Prelude.==>" :: String)
      = PImp <$> coreToLg e1 <*> coreToLg e2
      | GM.dropModuleUnique f == symbol ("==>" :: String)
      = PImp <$> coreToLg e1 <*> coreToLg e2
      | f == symbol ("Language.Haskell.Liquid.Prelude.<=>" :: String)
      = PIff <$> coreToLg e1 <*> coreToLg e2
      | GM.dropModuleUnique f == symbol ("<=>" :: String)
      = PIff <$> coreToLg e1 <*> coreToLg e2
      | f == symbol (show 'const)
      = coreToLg e1
    go (Just f, [es])
      | f == symbol (show 'or)
      = POr  . deList <$> coreToLg es
      | f == symbol (show 'and)
      = PAnd . deList <$> coreToLg es
    go (_, _)
      = toLogicApp p

    deList :: Expr -> [Expr]
    deList (EApp (EApp (EVar cons) e) es)
      | cons == symbol (show '(:))
      = e:deList es
    deList (EVar nil)
      | nil == symbol (show '[])
      = []
    deList e
      = [e]

toLogicApp :: C.CoreExpr -> LogicM Expr
toLogicApp e = do
  allowTC <- reader (typeclass . lsConfig)
  let (f, es) = splitArgs allowTC e
  case f of
    C.Var v -> do args <- mapM coreToLg es
                  embs <- reader lsEmb
                  dm   <- reader dcMap
                  cfg  <- reader lsConfig
                  case workerApp cfg embs dm v args of
                    Just w  -> return w
                    Nothing -> do
                      lmap <- lsSymMap <$> getState
                      def  <- (`mkEApp` args) <$> tosymbol f
                      (\x -> makeApp def lmap x args) <$> tosymbol' f
    _       -> do fe   <- coreToLg f
                  args <- mapM coreToLg es
                  return $ foldl EApp fe args

-- | A saturated application of a data constructor's WRAPPER, re-expressed over
-- its WORKER.
--
-- The logic has exactly ONE symbol per data constructor -- @'F.Symbolic'
-- 'DataCon'@ is @'F.symbol' . 'Ghc.dataConWorkId'@ -- and every fact the solver
-- is given about a constructor is stated over it: the @match@ equations lifted
-- from its selectors, and the result refinement of its spec type. Haskell has
-- TWO argument lists, though. Below @-O1@ they coincide and GHC builds no
-- wrapper at all, so lifting @'C.Var'@ by @'symbol'@ happens to name the
-- worker. From @-O1@ up, @-funbox-small-strict-fields@ makes them differ, GHC
-- compiles a construction as a call to the wrapper, and lifting that by
-- @'symbol'@ names @$WT@ -- a SECOND, unrelated uninterpreted constant, at the
-- SOURCE field sorts:
--
-- > constant M.$WDep : func(0, [M.Prio; M.Notes;            M.Dep])
-- > constant M.Dep   : func(0, [M.Prio; (Set_Set M.Text);   M.Dep])
--
-- Nothing relates the two, so a reflected body that CONSTRUCTS is disconnected
-- from every fact in scope about what it constructed. It is well sorted, so
-- there is no error -- the obligation is merely undischargeable, far from the
-- constructor, and only above @-O0@.
--
-- This is the construction direction of the seam 'unpackedFieldSubst' handles
-- for projection, and it reuses the same expansion: each source argument
-- becomes the representation arguments it unpacks to, so @$WDep p n@ lifts to
-- @Dep p (notesSet n)@. Where nothing unpacks the expansion is the identity and
-- this is a pure rename, which is exactly the @-O0@ shape.
--
-- ALL OF THAT IS CONDITIONAL ON @'adtFlag'@ BEING OFF, and the condition is
-- not a preference. @'Constraint.ToFixpoint'@ declares the datatype to the SMT
-- solver exactly when @'adtFlag'@ is on (its @makeDecls@), and it declares it
-- from the SOURCE fields -- so under @--reflection@ or @--adt@ the logic's
-- constructor symbol is bound at the SOURCE sorts and there is no seam to
-- close. Rewriting there produces the ill-sorted @Dep p (notesSet n)@ against
-- a @Dep : func([Prio; Notes; Dep])@, which liquid-fixpoint reports as
-- @Cannot unify Notes with (Array_t Text bool)@ from @evalCandsLoop@ at
-- @dummyLoc@, naming no binder. Measured on
-- @tests/datacon/pos/UnpackedFieldWorkerReflect.hs@.
--
-- Returns 'Nothing' -- leaving the pre-existing behaviour untouched -- unless
-- the application is saturated and the constructor's 'RepMap' aligns its
-- source fields with the worker's arguments, which is the count AND the sort
-- check at once: the 'RepMap' reads each leaf's type off the worker, so a
-- field whose one worker argument is at another sort ('frResorted') is
-- visible here rather than inferred from a count. Counting alone is measurably
-- not enough -- @data T = T !(IORef Int) !Int@ has ONE argument per field
-- either way while the worker's first argument is a @MutVar#@, and emitting
-- @T r n@ there is ill-sorted and takes down the whole module with
-- @Cannot unify MutVar# with IORef@; @tests/datacon/pos/UnpackedFieldSorts.hs@
-- is the arm that caught it. Such a field is projected through its newtype's
-- selector instead, when the logic has one (see 'fieldProjectable').
workerApp :: Config -> TCEmb TyCon -> DataConMap -> Var -> [Expr] -> Maybe Expr
workerApp cfg embs dm v args
  | not (adtFlag cfg)
  , Ghc.DataConWrapId d <- Ghc.idDetails v
  , Right rm <- dataConRepMap embs d
  , length args == length (rmFields rm)
  , all (fieldProjectable (knownDataCon dm)) (rmFields rm)
  = Just (F.mkEApp (GM.namedLocSymbol d)
                   (concat (zipWith (projectField (makeDataConSelector (Just dm))) (rmFields rm) args)))
  | otherwise
  = Nothing
    -- The projection composes the selectors of every constructor a field is
    -- unpacked through, and those exist only for constructors the logic knows
    -- ('Bare.knownDataCon'): @!(IORef Int)@ becomes a @MutVar#@ through
    -- @IORef@ and @STRef@, neither of which has a datatype in the logic. There
    -- the rewrite declines and the construction stays on the wrapper --
    -- disconnected but well sorted, the pre-existing behaviour.

makeApp :: Expr -> LogicMap -> Located Symbol-> [Expr] -> Expr
makeApp _ _ f [e]
  | val f == symbol (show 'negate)
  = ENeg e
  | val f == symbol (show 'fromInteger)
  , ECon c <- e
  = ECon c
  | (modName, sym) <- GM.splitModuleName (val f)
  , symbol ("Ghci" :: String) `isPrefixOfSym` modName
  , sym == "len"
  = EApp (EVar sym) e

makeApp _ _ f [e1, e2]
  | Just op <- M.lookup (val f) bops
  = EBin op e1 e2
  -- Hack for typeclass support. (overriden == without Eq constraint defined at Ghci)
  | (modName, sym) <- GM.splitModuleName (val f)
  , symbol ("Ghci" :: String) `isPrefixOfSym` modName
  , Just op <- M.lookup (mappendSym (symbol ("GHC.Internal.Num." :: String)) sym) bops
  = EBin op e1 e2

makeApp def lmap f es =
    eAppWithMap lmap (val f) es def
  -- where msg = "makeApp f = " ++ show f ++ " es = " ++ show es ++ " def = " ++ show def

eVarWithMap :: Id -> LogicMap -> Expr
eVarWithMap x lmap = do
    eAppWithMap lmap (symbol x) [] (EVar $ symbol x)

brels :: M.HashMap Symbol Brel
brels = M.fromList [ (symbol (show '(==)), Eq)
                   , (symbol (show '(/=)), Ne)
                   , (symbol (show '(>=)), Ge)
                   , (symbol (show '(>)) , Gt)
                   , (symbol (show '(<=)), Le)
                   , (symbol (show '(<)) , Lt)
                   ]

-- bops is a map between GHC function names/symbols and binary operators
-- from the logic. We want GHC functions like +, -, etc. to map to the
-- corresponding operators. There are actually multiple sources for +, -,
-- they can come from GHC.Prim, GHC.Internal.Num, GHC.Internal.Real or
-- be an instance of Num for Int.
bops :: M.HashMap Symbol Bop
bops = M.fromList [ (symbol (show '(+)), Plus)
                  , (numIntSymbol "+", Plus)
                  , (symbol (show '(+#)), Plus)
                  , (symbol (show '(-)), Minus)
                  , (numIntSymbol "-", Minus)
                  , (symbol (show '(-#)), Minus)
                  , (symbol (show '(*)), Times)
                  , (numIntSymbol "*", Times)
                  , (symbol (show '(*#)), Times)
                  , (symbol (show '(/)), Div)
                  , (symbol (show '(%)), Mod)
                  ]
  where
    numIntSymbol :: String -> Symbol
    numIntSymbol = symbol . (++) "GHC.Internal.Num.$fNumInt_$c"

splitArgs :: Bool -> C.Expr t -> (C.Expr t, [C.Arg t])
splitArgs allowTC exprt = (exprt', reverse args)
 where
    (exprt', args) = go exprt

    go (C.App (C.Var i) e) | ignoreVar i       = go e
    go (C.App f (C.Var v)) | if allowTC then GM.isEmbeddedDictVar v else isErasable v   = go f
    go (C.App f e) = (f', e:es) where (f', es) = go f
    go f           = (f, [])

tomaybesymbol :: C.CoreExpr -> Maybe Symbol
tomaybesymbol (C.Var x) = Just $ symbol x
tomaybesymbol _         = Nothing

tosymbol :: C.CoreExpr -> LogicM (Located Symbol)
tosymbol e
 = case tomaybesymbol e of
    Just x -> return $ dummyLoc x
    _      -> throw ("Bad Measure Definition:\n" ++ GM.showPpr e ++ "\t cannot be applied")

tosymbol' :: C.CoreExpr -> LogicM (Located Symbol)
tosymbol' (C.Var x) = return $ dummyLoc $ symbol x
tosymbol' e        = throw ("Bad Measure Definition:\n" ++ GM.showPpr e ++ "\t cannot be applied")

makesub :: C.CoreBind -> LogicM (Symbol, Expr)
makesub (C.NonRec x e) = (symbol x,) <$> coreToLg e
makesub _              = throw "Cannot make Logical Substitution of Recursive Definitions"

mkLit :: Literal -> Maybe Expr
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
ignoreVar i = simpleSymbolVar i `elem` ["I#", "D#"]

-- | Tries to determine if a 'CoreAlt' maps to one of the 'Integer' type constructors.
isBangInteger :: [C.CoreAlt] -> Bool
isBangInteger [Alt (C.DataAlt s) _ _, Alt (C.DataAlt jp) _ _, Alt (C.DataAlt jn) _ _]
  =  s  == Ghc.integerISDataCon
  && jp == Ghc.integerIPDataCon
  && jn == Ghc.integerINDataCon
isBangInteger _ = False

isErasable :: Id -> Bool
isErasable v = F.notracepp msg $ isGhcSplId v && not (isDCId v)
  where
    msg      = "isErasable: " ++ GM.showPpr (v, Ghc.idDetails v)

isGhcSplId :: Id -> Bool
isGhcSplId v = isPrefixOfSym (symbol ("$" :: String)) (simpleSymbolVar v)

isDCId :: Id -> Bool
isDCId v = case Ghc.idDetails v of
  DataConWorkId _ -> True
  DataConWrapId _ -> True
  _               -> False

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
-- The 'allowTC' flag controls whether type class dictionaries are considered erasable
-- and will be removed from the expression.
--
normalizeCoreExpr :: Bool -> CoreExpr -> CoreExpr
normalizeCoreExpr allowTC = inline_preds . inline_anf . simplifyCoreExpr allowTC
  where
    inline_preds = inlineCoreExpr (eqType boolTy . GM.expandVarType)
    inline_anf   = inlineCoreExpr isANF

-- | 'simplifyCoreExpr allowTC e' simplifies the Core expression 'e' by removing
-- applications of type arguments and dictionaries, and by removing dead
-- binders.
--
-- The 'allowTC' flag controls whether type class dictionaries are considered
-- erasable.
--
-- If 'allowTC' is 'True', then type class dictionaries are considered erasable
-- and will be removed from the expression. If 'allowTC' is 'False', then type
-- class dictionaries are not considered erasable and will not be removed.
--
-- This function is used in 'normalizeCoreExpr' to simplify the Core expression
-- before inlining predicates and ANF variables.
--
-- The 'simplifyCoreExpr' function recursively traverses the Core expression and
-- applies the following simplifications:
--   1. It removes applications of type arguments (i.e. 'C.App e1 (C.Type _)').
--   2. It removes applications of variables that are considered erasable
--      (i.e. 'C.App e1 (C.Var v)' where 'v' is erasable).
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
simplifyCoreExpr allowTC = go
  where
    isDictOrErasable = if allowTC then GM.isEmbeddedDictVar else isErasable

    go :: CoreExpr -> CoreExpr
    go e@(C.Var _)
      = e
    go e@(C.Lit _)
      = e
    go (C.App e1 (C.Type _))
      = go e1
    go (C.App e1 (C.Var v))
      | isDictOrErasable v
      = go e1
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
