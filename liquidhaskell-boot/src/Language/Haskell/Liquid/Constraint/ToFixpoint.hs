{-# LANGUAGE FlexibleContexts          #-}

{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Language.Haskell.Liquid.Constraint.ToFixpoint
  ( cgInfoFInfo
  , fixConfig
  , sourceNativeEnv
  , refinementEQs
  , canRewrite
  ) where

import           Prelude hiding (error)
import qualified Liquid.GHC.API as Ghc
import           Liquid.GHC.API (Var, Id, TyCon)
import qualified Language.Fixpoint.Types.Config as FC
import qualified Language.Fixpoint.Types        as F
import           Language.Fixpoint.Solver.Rewrite (unify)
import           Language.Haskell.Liquid.Constraint.Types
import qualified Language.Haskell.Liquid.Types.RefType as RT
import           Control.Monad (guard)
import qualified Data.Maybe as Mb

-- AT: Move to own module?
-- imports for AxiomEnv
import           Language.Haskell.Liquid.UX.Config
import           Language.Haskell.Liquid.UX.DiffCheck (coreDefs, proofDependents, Def(..))
import qualified Language.Haskell.Liquid.GHC.Misc  as GM -- (simplesymbol)
import qualified Data.HashMap.Strict               as M
import qualified Data.HashSet                      as S
-- import           Language.Fixpoint.Misc

import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp
import           Language.Haskell.Liquid.Types.Specs
import           Language.Haskell.Liquid.Types.Types hiding     ( binds )

-- The compiler reuses typed predicates; presentation follows instantiation.
-- Source formation knows the selected representation only when the solver is
-- configured. Reuse the query's resolved datatype catalog and configuration;
-- absent configuration is not an empty, supposedly complete native catalog.
sourceNativeEnv :: Config -> [F.DataDecl] -> Maybe F.SymEnv
sourceNativeEnv cfg declarations = do
    _ <- smtsolver cfg
    pure $ F.symEnv (fixConfig "" cfg) mempty mempty nativeDeclarations mempty []
  where
    nativeDeclarations = if adtFlag cfg then declarations else []

fixConfig :: FilePath -> Config -> FC.Config
fixConfig tgt cfg = FC.defConfig
  { FC.solver         = Mb.fromJust (smtsolver cfg)
  , FC.sortedSolution = True
  , FC.linear         = linear            cfg
  , FC.eliminate      = eliminate         cfg
  , FC.save           = saveQuery         cfg
  , FC.saveBfqOnError = saveBfqOnError    cfg
  , FC.srcFile        = tgt
  , FC.cores          = cores             cfg
  , FC.minPartSize    = minPartSize       cfg
  , FC.maxPartSize    = maxPartSize       cfg
  , FC.elimStats      = elimStats         cfg
  , FC.elimBound      = elimBound         cfg
  , FC.allowHO        = higherOrderFlag   cfg
  , FC.allowHOqs      = higherorderqs     cfg
  , FC.smtTimeout     = smtTimeout        cfg
  , FC.noStringTheory = not (stringTheory cfg)
  , FC.noslice        = noslice           cfg
  , FC.rewriteAxioms  = allowPLE   cfg
  , FC.pleUndecGuards = pleWithUndecidedGuards cfg
  , FC.etabeta        = etabeta    cfg
  , FC.localRewrites  = dependantCase cfg
  , FC.etaElim        = extensionality cfg
  , FC.extensionality = extensionality    cfg
  , FC.interpreter    = interpreter    cfg
  , FC.rwTermination  = rwTerminationCheck cfg
  , FC.fuel           = fuel      cfg
  , FC.noEnvReduction = not (environmentReduction cfg)
  , FC.inlineANFBinds = inlineANFBindings cfg
  }

cgInfoFInfo :: [(Var, LocSpecType)] -> TargetInfo -> CGInfo -> IO (F.FInfo Cinfo)
cgInfoFInfo rewrites info cgi = return (targetFInfo rewrites info cgi)

targetFInfo :: [(Var, LocSpecType)] -> TargetInfo -> CGInfo -> F.FInfo Cinfo
targetFInfo rewrites info cgi = mappend (mempty { F.ae = ax, F.lrws = localRewrites cgi }) fi
  where
    fi               = F.fi cs ws bs ls consts ks qs bi aHO aHOqs es mempty adts
    cs               = fixCs    cgi
    ws               = fixWfs   cgi
    bs               = binds    cgi
    ls               = fEnv     cgi
    consts           = cgConsts cgi
    ks               = kuts     cgi
    cfg              = getConfig info
    makeDecls        = adtFlag cfg
    adts             = if makeDecls then cgADTs   cgi else mempty
    -- The source driver supplies the complete candidate set after scraping
    -- these constraints; no alternate signature view contributes qualifiers.
    qs               = []
    bi               = (\x -> Ci x Nothing Nothing) <$> bindSpans cgi
    aHO              = allowHO cgi
    -- Logical higher-order binders do not enable automatic qualifier enumeration.
    aHOqs            = higherorderqs cfg
    es               = [] -- makeAxioms info
    ax               = makeAxiomEnvironment rewrites info (dataConTys cgi) (F.cm fi)
    -- msg              = show . map F.symbol . M.keys . tyConInfo

makeAxiomEnvironment :: [(Var, LocSpecType)] -> TargetInfo -> [(Var, SpecType)] -> M.HashMap F.SubcId (F.SubC Cinfo) -> F.AxiomEnv
makeAxiomEnvironment rewrites info xts fcs =
    F.AEnv
        eqs
        (concatMap makeSimplify xts)
        (doExpand sp cfg <$> fcs)
        (makeRewrites rewrites info <$> fcs)
        (Just mempty)
  where
    eqs = axioms ++ newtypeIdentities
    cfg = getConfig info
    sp = giSpec info
    axioms = gsMyAxioms refl ++ gsImpAxioms refl
    refl = gsRefl sp
    -- The same generic identity law is used by the Core cast interpreter.
    -- Register it here too so source constructor names have that meaning.
    newtypeIdentities =
        [ F.mkEquation (F.symbol dc) [(field, sort)] (F.EVar field) sort
        | dc <- M.keys (gsConstructorBoxes (gsName sp))
        , Just sort <- [RT.newtypeIdentitySort (gsTcEmbeds (gsName sp)) dc]
        ]
    field = F.symbol ("lq_newtype_field" :: String)

makeRewrites :: [(Var, LocSpecType)] -> TargetInfo -> F.SubC Cinfo -> [F.AutoRewrite]
makeRewrites sigs info sub = concatMap (makeRewriteOne tce) $ filter ((`S.member` rws) . fst) sigs
  where
    tce = gsTcEmbeds (gsName spec)
    spec = giSpec info
    parentFunction :: Maybe Var
    parentFunction =
        case subVar sub of
            Just v -> Just v
            Nothing ->
                Mb.listToMaybe $ do
                    D s e v <- coreDefs $ giCbs $ giSrc info
                    let (Ghc.RealSrcSpan cc _) = ci_loc $ F.sinfo sub
                    guard $ s <= Ghc.srcSpanStartLine cc && e >= Ghc.srcSpanEndLine cc
                    return v

    rws = case parentFunction of
        Nothing -> globalRws
        Just owner
            | S.null (rewrites owner) -> S.empty
            | otherwise -> rewrites owner `S.difference` forbiddenRWs owner

    forbiddenRWs owner = proofDependents (giCbs (giSrc info)) rewrites [owner]

    rewrites owner
        | owner `S.member` globalRws = S.empty
        | otherwise =
            S.union globalRws $
                S.fromList $
                    M.lookupDefault [] owner (gsRewritesWith (gsRefl spec))

    globalRws = S.map val $ gsRewrites $ gsRefl spec


canRewrite :: S.HashSet F.Symbol -> F.Expr -> F.Expr -> Bool
canRewrite freeVars' from to = noFreeSyms && doesNotDiverge
  where
    fromSyms           = S.intersection freeVars' (F.syms from)
    toSyms             = S.intersection freeVars' (F.syms to)
    noFreeSyms         = S.null $ S.difference toSyms fromSyms
    doesNotDiverge     = Mb.isNothing (unify (S.toList freeVars') from to)
                      || Mb.isJust (unify (S.toList freeVars') to from)

refinementEQs :: LocSpecType -> [(F.Expr, F.Expr)]
refinementEQs t =
  case stripRTypeBase tres of
    Just r ->
      [ (lhs, rhs) | (F.EEq lhs rhs) <- F.splitPAnd $ F.reftPred (toReft r) ]
    Nothing ->
      []
  where
    tres = ty_res tRep
    tRep = toRTypeRep $ val t

makeRewriteOne :: F.TCEmb TyCon -> (Var, LocSpecType) -> [F.AutoRewrite]
makeRewriteOne tce (_, t)
  = [rw | (lhs, rhs) <- refinementEQs t , rw <- rewrites lhs rhs ]
  where

    rewrites :: F.Expr -> F.Expr -> [F.AutoRewrite]
    rewrites lhs rhs =
         (guard (canRewrite freeVars' lhs rhs) >> [F.AutoRewrite xs lhs rhs])
      ++ (guard (canRewrite freeVars' rhs lhs) >> [F.AutoRewrite xs rhs lhs])

    freeVars' = S.fromList (ty_binds tRep)

    xs = do
      (sym, arg) <- zip (ty_binds tRep) (ty_args tRep)
      let e = maybe F.PTrue (F.reftPred . toReft) (stripRTypeBase arg)
      return $ F.RR (RT.rTypeSort tce arg) (F.Reft (sym, e))

    tRep = toRTypeRep $ val t

_isClassOrDict :: Id -> Bool
_isClassOrDict x = F.tracepp ("isClassOrDict: " ++ F.showpp x) (hasClassArg x || GM.isDictionary x || Mb.isJust (Ghc.isClassOpId_maybe x))

hasClassArg :: Id -> Bool
hasClassArg x = F.tracepp msg (GM.isDataConId x && any Ghc.isClassPred (t:ts'))
  where
    msg       = "hasClassArg: " ++ showpp (x, t:ts')
    (ts, t)   = Ghc.splitFunTys . snd . Ghc.splitForAllTyCoVars . Ghc.varType $ x
    ts'       = map Ghc.irrelevantMult ts


doExpand :: TargetSpec -> Config -> F.SubC Cinfo -> Bool
doExpand sp cfg sub = allowGlobalPLE cfg
                   || (allowLocalPLE cfg && maybe False (isPLEVar sp) (subVar sub))

-- [TODO:missing-sorts] data-constructors often have unelaboratable 'define' so either
-- 1. Make `elaborate` robust so it doesn't crash and returns maybe or
-- 2. Make the `ctor` well-sorted or
-- 3. Don't create `define` for the ctor.
-- Unfortunately 3 breaks a bunch of tests...

-- Note [GADT workers and coercion binders]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- For GADT constructors, GHC generates a *worker* and a *wrapper* DataCon.
-- The worker's type includes coercion arguments for each equality constraint
-- (e.g. @Succ n ~ n+1@ for a length-indexed vector).  However, the fixpoint
-- SMT encoding drops those coercion arguments: a pattern match
-- @case xs of { (:>) x xr -> ... }@ produces a constraint
-- @xs = $:>(x, xr)@ with only the value arguments.
--
-- The spec type for the worker therefore has @nCoerce@ extra binders at the
-- front (one per equality constraint) that do NOT appear in the SMT
-- application.  We build the application expression using only the remaining
-- *value* binders (@valBs@), so that the resulting rewrite has the right
-- arity to fire on the worker applications that appear in constraints.
--
-- | Generate measure rewrites at the carrier owned by this constructor Id.
-- Wrapper equations use the canonical source constructor; worker equations
-- use its distinct physical symbol when GHC changes the representation.
--
-- The measures are generated from the refinement in the result type of @t@,
-- which is expected to be of the form
--
-- > x0:t0 -> ... -> xn:tn -> { v: T | e }
--
-- where @e@ is a conjunction whose conjuncts have one of the following forms:
--
-- > f (dc x1 ... xn) = body
-- > f (dc x1 ... xn) <=> body
-- > f (dc x1 ... xn)
-- > not (f (dc x1 ... xn))
--
makeSimplify :: (Var, SpecType) -> [F.Rewrite]
makeSimplify (var, t)
  | not (GM.isDataConId var)
  = []
  | otherwise
  = go $ specTypeToResultRef eVal t
  where
    trep = toRTypeRep t
    -- Source equations and physical worker equations retain their own carriers.
    dcSym = case Ghc.idDetails var of
      Ghc.DataConWrapId dc -> F.symbol dc
      _                    -> F.symbol var
    -- Value-only binders: for GADT workers, drop the leading coercion binders
    -- that are present in the spec type but absent in the SMT encoding.
    -- See note [GADT workers and coercion binders].
    valBs = case Ghc.idDetails var of
      Ghc.DataConWorkId dc ->
        let nCoerce = length $ filter (Ghc.isSimplePredTy . Ghc.irrelevantMult)
                              $ Ghc.dataConRepArgTys dc
        -- Class dictionary constructors can take superclass dictionaries as
        -- arguments. Keep their binders so the dictionary arguments are retained.
        in if Ghc.isClassTyCon (Ghc.dataConTyCon dc)
            then ty_binds trep
            else drop nCoerce (ty_binds trep)
      _                    -> ty_binds trep
    eVal  = F.eApps (F.EVar dcSym) (F.EVar <$> valBs)

    go (F.PAnd es) = concatMap go es

    go (F.PAtom eq (F.EApp (F.EVar f) expr) bd)
      | eq `elem` [F.Eq, F.Ueq]
      , (F.EVar dc, xs) <- F.splitEApp expr
      , dc == dcSym
      , all isEVar xs
      = [F.SMeasure f dc (fromEVar <$> xs) bd]

    go (F.PIff (F.EApp (F.EVar f) expr) bd)
      | (F.EVar dc, xs) <- F.splitEApp expr
      , dc == dcSym
      , all isEVar xs
      = [F.SMeasure f dc (fromEVar <$> xs) bd]

    go (F.EApp (F.EVar f) expr)
      | (F.EVar dc, xs) <- F.splitEApp expr
      , dc == dcSym
      , all isEVar xs
      = [F.SMeasure f dc (fromEVar <$> xs) F.PTrue]

    go (F.PNot (F.EApp (F.EVar f) expr))
      | (F.EVar dc, xs) <- F.splitEApp expr
      , dc == dcSym
      , all isEVar xs
      = [F.SMeasure f dc (fromEVar <$> xs) F.PFalse]

    go _ = []

    isEVar (F.EVar _) = True
    isEVar _ = False

    fromEVar (F.EVar x) = x
    fromEVar _ = impossible Nothing "makeSimplify.fromEVar"

specTypeToResultRef :: F.Expr -> SpecType -> F.Expr
specTypeToResultRef e t
  = mkExpr $ toReft $ Mb.fromMaybe mempty (stripRTypeBase $ ty_res trep)
  where
    mkExpr (F.Reft (v, ev)) = F.subst1 ev (v, e)
    trep                   = toRTypeRep t
