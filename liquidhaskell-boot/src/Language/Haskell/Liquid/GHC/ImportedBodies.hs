{-# LANGUAGE ScopedTypeVariables #-}

{- | Selected imported definitions enter the ordinary source checker.  An
unfolding is a body to check, not evidence for its authored signature.
-}
module Language.Haskell.Liquid.GHC.ImportedBodies (hydrateImportedBodies, hydrateAuthoredImportedBodies) where

import Data.Generics (everything, extQ, mkQ)
import qualified Data.Graph as Graph
import qualified Data.HashSet as HashSet
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import GHC.Tc.Utils.Env (tcLookupId)
import qualified Language.Fixpoint.Types as F
import qualified Language.Haskell.Liquid.Bare.Resolve as Resolve
import qualified Language.Haskell.Liquid.GHC.Misc as LH
import Language.Haskell.Liquid.LHNameResolution (mkLookupGRE)
import Language.Haskell.Liquid.Types.Names
import Language.Haskell.Liquid.Types.Specs
import qualified Language.Haskell.Liquid.UX.Config as Config
import Liquid.GHC.API

-- The first slice supports only owners absent from dependency metadata.
-- This conservative scan can reject harmless uses as well as authority:
-- pruning callable rows alone would leave imported equations/logic metadata.
-- An explicit assumption and an ordinary selected claim cannot share an owner.
hydrateAuthoredImportedBodies ::
    Config.Config ->
    Module ->
    GlobalRdrEnv ->
    BareSpecParsed ->
    [LiftedSpec] ->
    CoreProgram ->
    TcM (Either (SrcSpan, String) (BareSpecParsed, CoreProgram))
hydrateAuthoredImportedBodies cfg current reader request dependencies existing =
    case traverse select (sigs request) of
        Left diagnostic -> pure (Left diagnostic)
        Right signatures -> do
            let resolvedRequest = request{sigs = signatures}
                declarations =
                    [ (name, owner)
                    | (owner, _) <- signatures
                    , Just name <- [getLHGHCName (F.val owner)]
                    , nameModule_maybe name /= Just current
                    , isExternalName name
                    ]
                refusal root owner reason =
                    Left
                        ( maybe (getSrcSpan root) LH.fSrcSpan (lookup (getName root) declarations)
                        , "Imported body admission for " ++ LH.showPpr root ++ ": " ++ LH.showPpr owner ++ " " ++ reason
                        )
            selected <- mapM (tcLookupId . fst) declarations
            pure $ case selected of
                root : _ | not strictMode -> refusal root root "requires complete strict source checking (totality, termination, and refinement domains)"
                _ -> case List.find ((`Set.member` assumed) . getName) selected of
                    Just owner -> refusal owner owner "also has an authored assumption"
                    Nothing -> case hydrateImportedBodies selected justified existing of
                        Left (root, missing) -> refusal root missing "has neither an actual unfolding nor a retained dependency contract"
                        Right core ->
                            let original = Set.fromList (map getName (bindersOfBinds existing))
                                owned = [owner | owner <- bindersOfBinds core, getName owner `Set.notMember` original]
                                incoming owner = any (mentions owner) dependencies
                             in case selected of
                                    [] -> Right (resolvedRequest, core)
                                    root : _ -> case [(owner, reason) | owner <- owned, (annotation, reason) <- forbidden, blocks owner annotation] of
                                        (owner, reason) : _ -> refusal root owner reason
                                        [] -> case List.find incoming owned of
                                            Just owner -> refusal root owner "occurs in dependency metadata; re-admission is not supported"
                                            Nothing -> Right (resolvedRequest, core)
  where
    strictMode =
        Config.totalityCheck cfg
            && Config.terminationCheck cfg
            && Config.checkRefinements cfg
            && null (Config.checks cfg)
            && not (Config.compileSpec cfg)
            && not (Config.diffcheck cfg)
    -- Only owner lookup occurs here. Local/ANF-only names and all refinement
    -- syntax retain the ordinary final resolution path. GHC supplies the
    -- original defining identity, including qualified import aliases.
    select pair@(owner, ty) = case F.val owner of
        LHNUnresolved (LHVarName _) symbol
            | not (LH.isQualifiedSym symbol)
            , Just _ <- Resolve.lookupLetBoundVar (Resolve.makeLocalVars [] existing) (F.atLoc owner symbol) ->
                Right pair
        LHNUnresolved (LHVarName _) symbol -> case lookupOwner symbol of
            [] -> Right pair
            [entry]
                | isLocalGRE entry -> Right pair
                | otherwise -> Right (LHNResolved (LHRGHC (greName entry)) symbol <$ owner, ty)
            entries -> Left (LH.fSrcSpan owner, "Ambiguous imported body owner: " ++ LH.showPpr entries)
        _ -> Right pair
    lookupOwner = lookupGRE reader . mkLookupGRE (LHVarName LHAnyModuleNameF)
    assumed =
        Set.fromList
            [ name
            | (owner, _) <- asmSigs request
            , name <-
                maybe [] pure (getLHGHCName (F.val owner))
                    ++ map greName (lookupOwner (getLHNameSymbol (F.val owner)))
            ]
    forbidden =
        [(owner, "also has an authored assumption") | (owner, _) <- asmSigs request]
            ++ [(owner, "has an authored assumed-reflection alias") | (left, right) <- asmReflectSigs request, owner <- [left, right]]
            ++ [(owner, "is authored ignored") | owner <- HashSet.toList (ignores request)]
            ++ [(owner, "has an authored termination waiver") | owner <- HashSet.toList (lazy request)]
            ++ [(owner, "has an authored expected-failure annotation") | owner <- HashSet.toList (fails request)]
            ++ [(owner, "has an authored deferred-use annotation") | owner <- HashSet.toList (lvars request)]
    blocks owner annotated =
        Just (getName owner) == getLHGHCName (F.val annotated)
            || getName owner `elem` map greName (lookupOwner symbol)
            || symbol == F.symbol owner
      where
        symbol = getLHNameSymbol (F.val annotated)
    justified =
        [ name
        | dependency <- dependencies
        , (owner, _) <- HashSet.toList (liftedSigs dependency) ++ HashSet.toList (liftedAsmSigs dependency)
        , Just name <- [getLHGHCName (F.val owner)]
        ]
    mentions owner =
        everything
            (||)
            ( mkQ False (\(name :: LHName) -> Just (getName owner) `elem` [getLHGHCName name, maybeReflectedLHName name])
                `extQ` (\(symbol :: F.Symbol) -> symbol == F.symbol owner)
            )

{- | The boundary is the existing dependency-callable catalog, not erased GHC
types.  Only explicit roots start discovery; ordinary client Core does not.
Its liftedAsmSigs entries remain explicit external trust, not checked evidence
or premise elimination. A closure that relies on them retains those premises.
Every reachable Id either has a catalog contract or supplies
its actual body.  Missing bodies fail closed, naming root and dependency.
Original Ids (including private helper identities) are retained throughout.
Constructor workers/wrappers have no exemption: this slice refuses them
unless their particular callable identity has a retained contract or body.
-}
hydrateImportedBodies ::
    [Id] -> [Name] -> CoreProgram -> Either (Id, Id) CoreProgram
hydrateImportedBodies selected justified existing = do
    bodies <- discover Set.empty Map.empty [(root, root) | root <- ordered selected]
    pure (map binding (Graph.stronglyConnComp (map vertex (orderedBodies bodies))) ++ existing)
  where
    local = Set.fromList (map getName (bindersOfBinds existing))
    roots = Set.fromList (map getName selected)
    boundary = Set.fromList justified
    ordered = List.sortOn (nameStableString . getName)
    orderedBodies = List.sortOn (nameStableString . getName . fst) . Map.elems
    dependencies = ordered . exprSomeFreeVarsList isId
    discover _ bodies [] = Right bodies
    discover seen bodies ((root, owner) : pending)
        | name `Set.member` seen = discover seen bodies pending
        | name `Set.member` local = continue bodies pending
        | name `Set.member` boundary && not (name `Set.member` roots) = continue bodies pending
        | otherwise = case realUnfoldingInfo (idInfo owner) of
            CoreUnfolding body _ _ _ _ ->
                continue
                    (Map.insert name (owner, body) bodies)
                    ([(root, dependency) | dependency <- dependencies body] ++ pending)
            _ -> Left (root, owner)
      where
        name = getName owner
        continue = discover (Set.insert name seen)
    vertex pair@(owner, body) =
        (pair, getName owner, map getName (dependencies body))
    binding (Graph.AcyclicSCC (owner, body)) = NonRec owner body
    binding (Graph.CyclicSCC bodies) = Rec (orderedBodies (Map.fromList [(getName owner, pair) | pair@(owner, _) <- bodies]))
