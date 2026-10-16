{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TupleSections #-}

module Language.Haskell.Liquid.Transforms.ShareEvidence
  ( shareGeneratedEvidence
  )
where

import           Liquid.GHC.API
import           GHC.Core.Map.Expr              (eqCoreExpr)
import           GHC.Core.Predicate             (isDictTy)
import           GHC.Types.Id                   (mkSysLocal)
import           GHC.Types.Unique.Supply        (mkSplitUniqSupply, uniqsFromSupply)
import           GHC.Types.Var.Env              (VarEnv, emptyVarEnv, extendVarEnv, lookupVarEnv)
import           GHC.Types.Var.Set              (disjointVarSet, mkVarSet)
import           Control.Monad.State.Strict     (State, evalState, gets, modify', state)
import           Data.List                      (find)
import           Data.Maybe                     (isJust)
import qualified Data.Map.Strict               as Map
import           Data.Word                      (Word64)

-- | Share the evidence that generated bindings construct.
--
-- The desugarer builds a generated binding's dictionaries where they are
-- used: every method of a derived (or deriving-via) instance reconstructs the
-- same instance dictionaries, which GHC's optimiser would otherwise share. A
-- dictionary application that mentions no locally bound term or type
-- variable denotes the same dictionary wherever it occurs. Each becomes a
-- top-level binding, inner dictionaries first, and one that constructs the
-- same evidence as an earlier one is replaced by it. The program's meaning
-- is unchanged; each distinct construction is checked once rather than once
-- per use. The new binders are themselves generated.
--
-- An instance's dictionary function is not rewritten: it owns its whole
-- defining construction, and its class methods are found from the fields of
-- that construction ('instanceDictionaryOwners'). Hoisting it, or evidence
-- nested in it, would leave the instance an alias of a shared binding.
-- Likewise a top-level evidence binding is already shared evidence, and its
-- uses find their instance through its definition (e.g. @$dIsString =
-- $fIsStringList \@Char $d~@); it is not replaced by an alias either.
shareGeneratedEvidence :: (Var -> Bool) -> CoreProgram -> IO CoreProgram
shareGeneratedEvidence generated program = do
    supply <- mkSplitUniqSupply 'S'
    pure $ evalState (concat <$> mapM bind program) (Sharing Map.empty [] (uniqsFromSupply supply))
  where
    bind (NonRec x rhs)
      | generated x, not (isDFunId x), not (isDictId x) = do
          rhs' <- expr emptyVarSet emptyVarEnv emptyVarEnv rhs
          hoisted <- state (\s -> (reverse (shHoisted s), s{shHoisted = []}))
          pure (hoisted ++ [NonRec x rhs'])
    bind b = pure [b]

data Sharing = Sharing
    { shShared :: Map.Map (Maybe Word64) [(CoreExpr, Var)]
    -- ^ Hoisted constructions, indexed by their head.
    , shHoisted :: [CoreBind]
    -- ^ Bindings hoisted from the current generated binding, newest first.
    , shUniques :: [Unique]
    }

-- | Rewrite under the locally bound variables, replacing let-bound evidence
-- that was shared.
--
-- A dictionary built by its class constructor stays where it is built:
-- checking reads such evidence through its constructor (the DataToTag
-- evidence of a derived comparison interprets its dataToTag#), which a
-- shared top-level binding no longer exposes. A closed one bound by a let
-- stays bound there, and evidence built from it is still shared: the shared
-- copy names a shared copy of the construction instead.
expr :: VarSet -> VarEnv CoreExpr -> VarEnv CoreExpr -> CoreExpr -> State Sharing CoreExpr
expr locals constructions env = go
  where
    go e = case e of
        Var v -> pure (maybe e id (lookupVarEnv env v))
        App{} -> do
            let (f, args) = collectArgs e
            e' <- mkApps <$> go f <*> mapM go args
            if isDictTy (exprType e') && closed e' && not (constructed e')
                then Var <$> (share Nothing =<< sharedCopy constructions e')
                else pure e'
        Lam b body -> Lam b <$> expr (extendVarSet locals b) constructions env body
        Let (NonRec d rhs) body
            | isDictId d -> do
                rhs' <- go rhs
                if
                    | not (closed rhs') ->
                        Let (NonRec d rhs') <$> expr (extendVarSet locals d) constructions env body
                    | constructed rhs' -> do
                        body' <- expr locals (extendVarEnv constructions d rhs') env body
                        pure $ if d `elemVarSet` exprFreeVars body' then Let (NonRec d rhs') body' else body'
                    | otherwise -> do
                        shared <- share (Just d) =<< sharedCopy constructions rhs'
                        expr locals constructions (extendVarEnv env d (Var shared)) body
        Let (NonRec b rhs) body -> Let . NonRec b <$> go rhs <*> expr (extendVarSet locals b) constructions env body
        Let (Rec bs) body -> do
            let locals' = extendVarSetList locals (map fst bs)
            Let . Rec <$> mapM (\(b, rhs) -> (b,) <$> expr locals' constructions env rhs) bs <*> expr locals' constructions env body
        Case scrutinee b t alts ->
            Case <$> go scrutinee <*> pure b <*> pure t <*> mapM (alt b) alts
        Cast inner co -> (`Cast` co) <$> go inner
        Tick t inner -> Tick t <$> go inner
        _ -> pure e
    alt b (Alt c bs rhs) = Alt c bs <$> expr (extendVarSetList locals (b : bs)) constructions env rhs
    -- Let-bound constructions are not local: a shared copy replaces them.
    closed e = disjointVarSet locals (exprFreeVars e)

-- | Whether a dictionary is built by its class constructor.
constructed :: CoreExpr -> Bool
constructed e = case collectArgs e of
    (Var f, _) -> isJust (isDataConId_maybe f)
    _ -> False

-- | A closed expression's top-level copy: each let-bound constructor-built
-- dictionary it names is replaced by that construction's shared binder.
sharedCopy :: VarEnv CoreExpr -> CoreExpr -> State Sharing CoreExpr
sharedCopy constructions e = do
    replacements <-
        sequence
            [ (d,) <$> (share Nothing =<< sharedCopy constructions construction)
            | d <- exprFreeVarsList e
            , Just construction <- [lookupVarEnv constructions d]
            ]
    pure $
        if null replacements
            then e
            else
                substExpr
                    (extendIdSubstList (mkEmptySubst (mkInScopeSet (exprFreeVars e `unionVarSet` mkVarSet (map snd replacements)))) [(d, Var v) | (d, v) <- replacements])
                    e

-- | The top-level binder of a closed dictionary construction: an earlier one
-- that constructs the same evidence, else the given or a fresh binder.
share :: Maybe Var -> CoreExpr -> State Sharing Var
share binder e = do
    candidates <- gets (Map.findWithDefault [] key . shShared)
    case find (eqCoreExpr e . fst) candidates of
        Just (_, existing) -> pure existing
        Nothing -> do
            v <- maybe fresh pure binder
            modify' $ \s ->
                s
                    { shShared = Map.insertWith (++) key [(e, v)] (shShared s)
                    , shHoisted = NonRec v e : shHoisted s
                    }
            pure v
  where
    key = case collectArgs e of
        (Var f, _) -> Just (getKey (getUnique f))
        _ -> Nothing
    fresh = state $ \s -> case shUniques s of
        u : us -> (mkSysLocal (fsLit "$dshared") u ManyTy (exprType e), s{shUniques = us})
        [] -> error "shareGeneratedEvidence: exhausted uniques"
