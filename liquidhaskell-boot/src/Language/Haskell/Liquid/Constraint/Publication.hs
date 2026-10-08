module Language.Haskell.Liquid.Constraint.Publication (
    PublicationCheck,
    publicationCandidates,
    publicationAdmissible,
) where

import Data.Data (Data)
import Data.Generics (everythingBut, extQ, mkQ)
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import qualified Data.Maybe as Mb
import qualified Data.Set as Set
import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.Types.Names (LHName (..), LHResolvedName (..), LogicName (..), getLHGHCName, lhNameToResolvedSymbol, maybeReflectedLHName)
import Language.Haskell.Liquid.Types.Specs
import Language.Haskell.Liquid.Types.Types (LogicMap (..))
import Liquid.GHC.API (Var, getName)

-- Raw solver/CG failures before expected-failure presentation. The source
-- checker establishes callable premises independently of failed goals; this
-- evidence additionally decides whether the original library may be exported.
type PublicationCheck = F.FixResult (Maybe Var)

-- Use the original target, never a stage's restricted view.
-- A reflected/logic-map owner is not an isolated checking-only probe even
-- when one particular query omits its equation.
publicationCandidates :: TargetInfo -> S.HashSet Var
publicationCandidates info = S.filter eligible (S.map F.val (gsFail (gsTerm spec)))
  where
    spec = giSpec info
    refl = gsRefl spec
    logic = gsLogicMap refl
    reserved =
        S.unions
            [ S.fromList (F.symbol <$> (gsReflects refl ++ gsOpaqueRefls (gsData spec)))
            , S.fromList [F.symbol v | (actual, assumed) <- gsAsmReflects (gsSig spec), v <- [actual, assumed]]
            , symbols (M.toList (lmSymDefs logic))
            , S.fromList [F.symbol v | v <- M.keys (lmVarSyms logic)]
            , S.fromList (Mb.catMaybes (M.elems (lmVarSyms logic)))
            ]
    eligible v = not (isExportedVar (giSrc info) v) && not (F.symbol v `S.member` reserved)

-- Called only after complete source checking reports Safe: every mandatory
-- formation/source judgment passed, and failed authored goals were never
-- reusable premises. ErrFailUsed also excludes failed dictionary field owners.
-- Check the ORIGINAL target and dependency library, before name serialization;
-- never filter exports to make a failed public contract appear admissible.
publicationAdmissible :: S.HashSet Var -> [LiftedSpec] -> PublicationCheck -> Bool
publicationAdmissible _ _ (F.Safe _) = True
publicationAdmissible candidates specs (F.Unsafe _ owners) =
    case sequence owners of
        Nothing -> False
        Just failed ->
            not (null failed)
                && all (`S.member` candidates) failed
                && absentFrom failed specs
  where
    -- Disjointness distributes over support union. Check the same complete
    -- specification directly instead of constructing its universe of names.
    absentFrom failed = everythingBut (&&) (mkQ (True, False) raw `extQ` resolved)
      where
        failedSymbols = S.fromList (F.symbol <$> failed)
        failedNames = Set.fromList (getName <$> failed)
        raw symbol = (not (symbol `S.member` failedSymbols), True)
        -- Continue below LHName: parser spelling and embedded symbols remain
        -- observations in addition to canonical and reflected ownership.
        resolved name = (known name && absent name, False)
        absent name =
            not (lhNameToResolvedSymbol name `S.member` failedSymbols)
                && all (not . (`Set.member` failedNames)) (Mb.catMaybes [getLHGHCName name, maybeReflectedLHName name])
        known (LHNResolved (LHRGHC _) _) = True
        known (LHNResolved (LHRLocal _) _) = True
        known (LHNResolved (LHRLogic (LogicName _ _ _)) _) = True
        known (LHNResolved (LHRLogic (GeneratedLogicName _)) _) = True
        known _ = False
publicationAdmissible _ _ (F.Crash _ _) = False

symbols :: (Data a) => a -> S.HashSet F.Symbol
symbols = everythingBut S.union (mkQ (S.empty, False) (\s -> (S.singleton s, True) :: (S.HashSet F.Symbol, Bool)))
