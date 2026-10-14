module NativeRefinementFixtures (
    falseDomain,
    trueDomain,
    badHelperBody,
    distinctPredicates,
    alphaEquivalentPredicates,
    aggregatePrimitive,
    alphaCallbackPredicate,
    distinctCallbackPredicates,
    alphaProjectedCallbackPredicate,
    distinctProjectedCallbackPredicates,
    sameSpelledTermPredicate,
    falseMembershipGuard,
    inadmissibleMembershipGuard,
    falseClassMembershipGuard,
    inadmissibleClassMembershipGuard,
    privateFalseDomain,
    privateTrueDomain,
    privateIdentityDomain,
    transitivePrivateFalseDomain,
    pendingDictionaryDomain,
    consistentSharedMethods,
    reversedConsistentSharedMethods,
    conflictingSharedMethods,
    reversedConflictingSharedMethods,
) where

-- These are source fixtures, not receipts. Run them with total-Haskell,
-- check-derived, and check-refinements; no helper is assumed or axiomatized.
-- The class/instance syntax follows tests/pos/InterleavedMethodEvidence.hs;
-- opaque-reflect follows tests/basic/pos/OpaqueRefl05.hs.
falseDomain :: String
falseDomain = nativeDomain "NativeFalseDomain" "alwaysFalse" "not b" "False"

trueDomain :: String
trueDomain = nativeDomain "NativeTrueDomain" "alwaysTrue" "b" "True"

badHelperBody :: String
badHelperBody = nativeDomain "NativeBadHelperBody" "alwaysFalse" "not b" "True"

-- These helpers have no LH signature and are deliberately private. Their
-- callable contracts must come from independent body checking, not export
-- inference or a consumer's empty instance domain.
-- Opaque registration supplies only the source name and Haskell scheme.
privateFalseDomain, privateTrueDomain, privateIdentityDomain, transitivePrivateFalseDomain :: String
privateFalseDomain = privateDomain "NativePrivateFalse" ["helper _ = False"]
privateTrueDomain = privateDomain "NativePrivateTrue" ["helper _ = True"]
privateIdentityDomain = privateDomain "NativePrivateIdentity" ["helper flag = flag"]
transitivePrivateFalseDomain =
    privateDomain "NativeTransitivePrivateFalse" ["helper flag = second flag", "second :: Bool -> Bool", "second _ = False", "{-# NOINLINE second #-}"]

privateDomain :: String -> [String] -> String
privateDomain name helpers =
    unlines $
        [ "{-# LANGUAGE NoImplicitPrelude #-}"
        , "module " ++ name ++ " (NativeDomain(..)) where"
        , "import GHC.Types (Bool(..), Int)"
        , "helper :: Bool -> Bool"
        ]
            ++ helpers
            ++ [ "{-# NOINLINE helper #-} {-@ opaque-reflect helper @-}"
               , "{-@ class NativeDomain a where"
               , "      selected :: flag:Bool -> {v:a | helper flag} -> Bool @-}"
               , "class NativeDomain a where"
               , "  selected :: Bool -> a -> Bool"
               , "{-@ instance NativeDomain Int where"
               , "      selected :: Bool -> {v:Int | false} -> Bool @-}"
               , "instance NativeDomain Int where"
               , "  selected _ _ = False"
               ]

-- Body inference must not manufacture authority for a still-pending local
-- instance dictionary used by the prerequisite helper.
pendingDictionaryDomain :: String
pendingDictionaryDomain =
    unlines
        [ "{-# LANGUAGE NoImplicitPrelude #-}"
        , "module NativePendingDictionary (NativeDomain(..)) where"
        , "import GHC.Types (Bool(..), Int)"
        , "class Provider a where provider :: a -> Bool"
        , "instance Provider Int where provider _ = False"
        , "helper :: Int -> Bool"
        , "helper value = provider value"
        , "{-# NOINLINE helper #-} {-@ opaque-reflect helper @-}"
        , "{-@ class NativeDomain a where"
        , "      selected :: a -> {v:Int | helper v} -> Bool @-}"
        , "class NativeDomain a where"
        , "  selected :: a -> Int -> Bool"
        , "{-@ instance NativeDomain Int where"
        , "      selected :: Int -> {v:Int | false} -> Bool @-}"
        , "instance NativeDomain Int where"
        , "  selected _ _ = False"
        ]

-- Both dictionaries retain the same actual source implementation Id. Every
-- private claim must be checked, while each consumer keeps its own selector's
-- instantiated contract. Catalog order cannot select which claim is required.
-- `shared` stays private: an exported binder without a specification has the
-- trivial contract, which could not establish either instance claim. A
-- conflicting claim fails at the instance body that must establish it.
consistentSharedMethods, reversedConsistentSharedMethods, conflictingSharedMethods, reversedConflictingSharedMethods :: String
consistentSharedMethods = sharedMethods "NativeSharedMethods" False False
reversedConsistentSharedMethods = sharedMethods "NativeSharedMethodsReversed" False True
conflictingSharedMethods = sharedMethods "NativeConflictingSharedMethods" True False
reversedConflictingSharedMethods = sharedMethods "NativeConflictingSharedMethodsReversed" True True

sharedMethods :: String -> Bool -> Bool -> String
sharedMethods name conflicting reversed =
    unlines $
        [ "{-# LANGUAGE NoImplicitPrelude, AllowAmbiguousTypes, TypeApplications #-}"
        , "module " ++ name ++ " (Marker (..), consumeInt, consumeBool) where"
        , "import GHC.Types (Bool, Int)"
        , "class Marker a where selected :: Int"
        , "shared :: Int"
        , "shared = 0"
        , "{-# NOINLINE shared #-}"
        , "{-@ class Marker a where"
        , "      selected :: {v:Int | true} @-}"
        ]
            ++ concat (if reversed then reverse instances else instances)
            ++ [ "{-@ consumeInt :: {v:Int | v == 0} @-}"
               , "consumeInt = selected @Int"
               , "{-@ consumeBool :: {v:Int | v == 0} @-}"
               , "consumeBool = selected @Bool"
               ]
  where
    instances =
        [
            [ "{-@ instance Marker Int where"
            , "      selected :: {v:Int | " ++ (if conflicting then "v > 0" else "v == 0") ++ "} @-}"
            , "instance Marker Int where selected = shared"
            ]
        ,
            [ "{-@ instance Marker Bool where"
            , "      selected :: {v:Int | v == 0} @-}"
            , "instance Marker Bool where selected = shared"
            ]
        ]

-- Native contravariance must prove the class domain implies the instance
-- domain. The false helper makes this implication valid; the true helper
-- refutes it. NOINLINE keeps the opaque source call visible at both -O0/-O2.
nativeDomain :: String -> String -> String -> String -> String
nativeDomain moduleName helper resultPredicate resultConstructor =
    unlines
        [ "{-# LANGUAGE NoImplicitPrelude #-}"
        , "module " ++ moduleName ++ " where"
        , "import GHC.Types (Bool(..), Int)"
        , "import GHC.Classes (not)"
        , "{-@ opaque-reflect " ++ helper ++ " @-}"
        , "{-@ " ++ helper ++ " :: a -> {b:Bool | " ++ resultPredicate ++ "} @-}"
        , helper ++ " :: a -> Bool"
        , helper ++ " _ = " ++ resultConstructor
        , "{-# NOINLINE " ++ helper ++ " #-}"
        , "{-@ class NativeDomain a where"
        , "      selected :: {v:a | " ++ helper ++ " v} -> Bool @-}"
        , "class NativeDomain a where"
        , "  selected :: a -> Bool"
        , "{-@ instance NativeDomain Int where"
        , "      selected :: {v:Int | false} -> Bool @-}"
        , "instance NativeDomain Int where"
        , "  selected _ = False"
        ]

-- Neither rigid predicate entails the other. This must be rejected even
-- though the instance's ordinary identity body satisfies its own signature.
distinctPredicates :: String
distinctPredicates =
    predicateDomain
        "DistinctNativePredicates"
        "forall <p :: a -> Bool, q :: a -> Bool>. a<p> -> a<q>"
        "forall <r :: Int -> Bool, s :: Int -> Bool>. Int<r> -> Int<r>"

-- The abstract predicate and the source term intentionally share a label.
-- Only the abstract owner changes from p to q; papp1 consumes the term token.
sameSpelledTermPredicate :: String
sameSpelledTermPredicate =
    unlines
        [ "{-# LANGUAGE NoImplicitPrelude #-}"
        , "module NativeSameSpelledTermPredicate where"
        , "import GHC.Types (Int)"
        , "import Data.Kind (Type)"
        , "data PredicateToken (a :: Type) = PredicateToken"
        , "{-@ embed PredicateToken as Pred @-}"
        , "{-@ class TokenDomain a where"
        , "      selected :: forall <p :: a -> Bool>. p:PredicateToken a -> value:{a<p> | papp1 p value} -> {r:a<p> | papp1 p r} @-}"
        , "class TokenDomain a where"
        , "  selected :: PredicateToken a -> a -> a"
        , "{-@ instance TokenDomain Int where"
        , "      selected :: forall <q :: Int -> Bool>. p:PredicateToken Int -> value:{Int<q> | papp1 p value} -> {r:Int<q> | papp1 p r} @-}"
        , "instance TokenDomain Int where"
        , "  selected _ value = value"
        ]

-- The method-local predicate names differ, but both contracts mean identity
-- at an arbitrary predicate. Alpha-renaming must not change admission.
alphaEquivalentPredicates :: String
alphaEquivalentPredicates =
    predicateDomain
        "AlphaNativePredicates"
        "forall <p :: a -> Bool>. a<p> -> a<p>"
        "forall <q :: Int -> Bool>. Int<q> -> Int<q>"

predicateDomain :: String -> String -> String -> String
predicateDomain moduleName classSignature instanceSignature =
    unlines
        [ "{-# LANGUAGE NoImplicitPrelude #-}"
        , "module " ++ moduleName ++ " where"
        , "import GHC.Types (Int)"
        , "{-@ class PredicateDomain a where"
        , "      selected :: " ++ classSignature ++ " @-}"
        , "class PredicateDomain a where"
        , "  selected :: a -> a"
        , "{-@ instance PredicateDomain Int where"
        , "      selected :: " ++ instanceSignature ++ " @-}"
        , "instance PredicateDomain Int where"
        , "  selected value = value"
        ]

-- Both empty operands and their union retain Set a throughout native query
-- elaboration. The permissive instance must satisfy this tautological result
-- without interpreting aggregate equality as numeric equality.
aggregatePrimitive :: String
aggregatePrimitive =
    unlines
        [ "{-# LANGUAGE NoImplicitPrelude #-}"
        , "module NativeAggregatePrimitive where"
        , "import GHC.Types (Int)"
        , "import Data.Set (Set)"
        , "{-@ class K a where"
        , "      f :: v:a -> s:Set a -> {r:a | Set_sub (Set_cup (Set_empty 0) (Set_empty 0)) s} @-}"
        , "class K a where"
        , "  f :: a -> Set a -> a"
        , "{-@ instance K Int where"
        , "      f :: Int -> Set Int -> Int @-}"
        , "instance K Int where"
        , "  f value _ = value"
        ]

-- The callback's checked result makes the concrete guard true. Its argument
-- domain nevertheless contains the method-local abstract predicate and must
-- be transported when the subtype judgment opens that predicate rigidly.
alphaCallbackPredicate :: String
alphaCallbackPredicate =
    callbackPredicateDomain
        "NativeCallbackAlpha"
        "forall <p :: a -> Bool>. callback:(a<p> -> {b:Bool | b}) -> value:{a<p> | callback value} -> a<p>"
        "forall <q :: Int -> Bool>. callback:(Int<q> -> {b:Bool | b}) -> value:{Int<q> | callback value} -> Int<q>"

-- An empty logical membership does not demand its guarded source call. In
-- contrast, a nonempty membership cannot license that same empty-domain call.
falseMembershipGuard :: String
falseMembershipGuard = membershipGuard "NativeFalseMembership" "false"

inadmissibleMembershipGuard :: String
inadmissibleMembershipGuard = membershipGuard "NativeInadmissibleMembership" "true"

-- The declaration must be meaningful without an instance implementation.
falseClassMembershipGuard, inadmissibleClassMembershipGuard :: String
falseClassMembershipGuard = unlines $ membershipDeclaration "NativeClassFalseMembership" "false"
inadmissibleClassMembershipGuard = unlines $ membershipDeclaration "NativeClassFormationOnly" "true"

membershipGuard :: String -> String -> String
membershipGuard name membership =
    unlines $
        membershipDeclaration name membership
            ++ [ "{-@ instance Membership Int where"
               , "      selected :: callback:({v:Int | false} -> Bool) -> {v:Int | false} -> Bool @-}"
               , "instance Membership Int where"
               , "  selected _ _ = False"
               ]

membershipDeclaration :: String -> String -> [String]
membershipDeclaration name membership =
    [ "{-# LANGUAGE NoImplicitPrelude #-}"
    , "{-@ LIQUID \"--higherorder\" @-}"
    , "module " ++ name ++ " where"
    , "import GHC.Types (Bool(..), Int)"
    , "{-@ class Membership a where"
    , "      selected :: callback:({v:a | false} -> Bool) -> value:{a | " ++ membership ++ " && callback value} -> Bool @-}"
    , "class Membership a where"
    , "  selected :: (a -> Bool) -> a -> Bool"
    ]

-- A true native guard cannot discharge the independent p => q result goal.
-- The same identity implementation satisfies the instance's own contract.
distinctCallbackPredicates :: String
distinctCallbackPredicates =
    callbackPredicateDomain
        "NativeCallbackDistinct"
        "forall <p :: a -> Bool, q :: a -> Bool>. callback:(a<p> -> {b:Bool | b}) -> value:{a<p> | callback value} -> a<q>"
        "forall <r :: Int -> Bool, s :: Int -> Bool>. callback:(Int<r> -> {b:Bool | b}) -> value:{Int<r> | callback value} -> Int<r>"

callbackPredicateDomain :: String -> String -> String -> String
callbackPredicateDomain moduleName classSignature instanceSignature =
    callbackDomain moduleName [] "(a -> Bool)" classSignature instanceSignature

-- Unlike a direct callback argument, this logical selector creates a native
-- query projector. Its retained callable domain must follow the same rigid
-- predicate owner as the datatype and the value argument.
alphaProjectedCallbackPredicate :: String
alphaProjectedCallbackPredicate =
    callbackDomain
        "NativeProjectedCallbackAlpha"
        callbackProjection
        "Callback a"
        "forall <p :: a -> Bool>. callback:Callback<p> a -> value:{a<p> | project callback value} -> a<p>"
        "forall <q :: Int -> Bool>. callback:Callback<q> Int -> value:{Int<q> | project callback value} -> Int<q>"

distinctProjectedCallbackPredicates :: String
distinctProjectedCallbackPredicates =
    callbackDomain
        "NativeProjectedCallbackDistinct"
        callbackProjection
        "Callback a"
        "forall <p :: a -> Bool, q :: a -> Bool>. callback:Callback<p> a -> value:{a<p> | project callback value} -> a<q>"
        "forall <r :: Int -> Bool, s :: Int -> Bool>. callback:Callback<r> Int -> value:{Int<r> | project callback value} -> Int<r>"

callbackProjection :: [String]
callbackProjection =
    [ "data Callback a = Callback (a -> Bool)"
    , "{-@ data Callback a <p :: a -> Bool> = Callback {stored :: a<p> -> {b:Bool | b}} @-}"
    , "{-@ measure project :: forall <p :: a -> Bool>. Callback<p> a -> (a<p> -> {b:Bool | b})"
    , "      project (Callback function) = function @-}"
    ]

callbackDomain :: String -> [String] -> String -> String -> String -> String
callbackDomain moduleName declarations callbackType classSignature instanceSignature =
    unlines
        ( [ "{-# LANGUAGE NoImplicitPrelude #-}"
          , "{-@ LIQUID \"--higherorder\" @-}"
          , "module " ++ moduleName ++ " where"
          , "import GHC.Types (Bool, Int)"
          ]
            ++ declarations
            ++ [ "{-@ class CallbackDomain a where"
               , "      selected :: " ++ classSignature ++ " @-}"
               , "class CallbackDomain a where"
               , "  selected :: " ++ callbackType ++ " -> a -> a"
               , "{-@ instance CallbackDomain Int where"
               , "      selected :: " ++ instanceSignature ++ " @-}"
               , "instance CallbackDomain Int where"
               , "  selected _ value = value"
               ]
        )
