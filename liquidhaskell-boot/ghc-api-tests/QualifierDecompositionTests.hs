{-# LANGUAGE OverloadedStrings #-}

module QualifierDecompositionTests (tests) where

import ConstraintGenerationTests (emptyTarget)
import Control.Exception (evaluate)
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as FC
import Language.Haskell.Liquid.Constraint.Qualifier (giQuals)
import Language.Haskell.Liquid.GHC.Misc (getSourcePos)
import Language.Haskell.Liquid.Types.Names
import Language.Haskell.Liquid.Types.RType
import Language.Haskell.Liquid.Types.RTypeOp (rTypeReft, toRSort)
import Language.Haskell.Liquid.Types.RefType (ofType, strengthen, uPVar, uTop)
import Language.Haskell.Liquid.Types.Specs
import Language.Haskell.Liquid.Types.Types (RTAlias (..))
import qualified Language.Haskell.Liquid.UX.CmdLine as CmdLine
import qualified Language.Haskell.Liquid.UX.Config as LH
import qualified Liquid.GHC.API as G
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests =
    testGroup
        "qualifier syntax and query interpretation"
        [ testCase "node scope, duplicate order, and complete source positions" $ do
            let arrow =
                    RFun
                        "x"
                        defRFInfo
                        (refined (F.PNot (F.EVar value)))
                        (refined (F.PNot (F.EVar "x")))
                        mempty
                body = F.PNot (F.EVar value)
                info = aliasTarget [at first arrow, at second (refined body), at first arrow]
                expected =
                    [ auto [(value, F.boolSort)] (F.PNot (F.EVar value)) first
                    , auto [(value, F.boolSort), ("x", F.boolSort)] (F.PNot (F.EVar "x")) first
                    ]
                middle = auto [(value, F.boolSort)] body second
                firstNode = auto [(value, F.boolSort)] body first
            observe (giQuals info mempty) @?= expected ++ [middle] ++ expected
            -- Alias validation uses the final query environment too: an incompatible
            -- global binding refuses the otherwise lexical Bool parameter.
            observe (giQuals info (F.fromListSEnv [("x", F.FInt)]))
                @?= [firstNode, middle, firstNode]
        , testCase "query globals are not qualifier parameters; lexical locals still are" $ do
            let concrete = signatures [refined (F.PNot (F.EVar "global"))]
                prepared = giQuals concrete
                env = F.fromListSEnv [("global", F.boolSort)]
            observe (prepared mempty) @?= []
            observe (prepared env) @?= [auto [(value, F.boolSort)] (F.PNot (F.EVar "global")) ownerPosition]
        , testCase "concrete judgments check sorts; abstract argument equalities retain old policy" $ do
            let p = PV "predicate" (toRSort boolean) [(toRSort boolean, "formal", F.EVar "global")]
                abstract = RAllP p (strengthen boolean (MkUReft mempty (Pr [uPVar p])))
                env = F.fromListSEnv [("global", F.FInt)]
                body = F.PAtom F.Eq (F.EVar "vv") (F.EVar "global")
            observe (giQuals (signatures [refined (F.PNot (F.EVar "global"))]) env) @?= []
            observe (giQuals (signatures [abstract]) env)
                @?= [auto [("vv", F.boolSort)] body ownerPosition]
        , testCase "fixed and enriched stage syntax inventories are independently derived" $ do
            let body = F.PNot (F.EVar value)
                fixed = giQuals (signatures [refined body])
                stage = giQuals (signatures [refined body, refined body])
                expected = auto [(value, F.boolSort)] body ownerPosition
            observe (fixed mempty) @?= [expected]
            observe (stage mempty) @?= [expected, expected]
            observe (fixed mempty) @?= [expected]
        , testCase "maximum parameter filtering runs after lexical interpretation" $ do
            let arrow = RFun "x" defRFInfo boolean (refined (F.PNot (F.EVar "x"))) mempty
                info = signatures [arrow]
                spec = giSpec info
                limited = info{giSpec = spec{gsConfig = config{LH.maxParams = 0}}}
            observe (giQuals info mempty)
                @?= [auto [(value, F.boolSort), ("x", F.boolSort)] (F.PNot (F.EVar "x")) ownerPosition]
            observe (giQuals limited mempty) @?= []
        , testCase "unselected syntax, native metadata, and globals remain unused" $ do
            let base = emptyTarget config{LH.eliminate = FC.All}
                spec = giSpec base
                info =
                    base
                        { giSpec =
                            spec
                                { gsSig = (gsSig spec){gsTySigs = [error "unused signature"]}
                                , gsName = (gsName spec){gsADTs = [error "unused native declaration"]}
                                }
                        }
            evaluate (giQuals (error "unused target")) >> pure ()
            observe (giQuals info (error "unused global environment")) @?= []
        ]

config :: LH.Config
config = CmdLine.defConfig{LH.smtsolver = Nothing, LH.eliminate = FC.None, LH.maxParams = 4}

boolean :: SpecType
boolean = ofType G.boolTy

value :: F.Symbol
value = case rTypeReft boolean of F.Reft (v, _) -> v

refined :: F.Expr -> SpecType
refined p = strengthen boolean (uTop (F.Reft (value, p)))

owner :: G.Var
owner = G.dataConWorkId G.falseDataCon

ownerPosition :: F.SourcePos
ownerPosition = getSourcePos owner

first, second :: F.SourcePos
first = F.toSourcePos ("QualifierDecomposition.hs", F.mkPos 3, F.mkPos 7)
second = F.toSourcePos ("ImportedAlias.hs", F.mkPos 9, F.mkPos 2)

at :: F.SourcePos -> SpecType -> F.Located (RTAlias RTyVar SpecType)
at pos body = F.Loc pos pos (RTA (F.dummyLoc (LHNUnresolved LHLogicName "Alias")) [] [] body)

signatures :: [SpecType] -> TargetInfo
signatures bodies =
    let base = emptyTarget config
        spec = giSpec base
        names = gsName spec
     in base
            { giSpec =
                spec
                    { gsName = names{gsTcEmbeds = F.tceInsert G.boolTyCon F.boolSort F.NoArgs mempty}
                    , gsSig = (gsSig spec){gsTySigs = [(owner, F.dummyLoc body) | body <- bodies]}
                    }
            }

aliasTarget :: [F.Located (RTAlias RTyVar SpecType)] -> TargetInfo
aliasTarget bodies =
    let base = signatures []
        spec = giSpec base
     in base
            { giSpec =
                spec
                    { gsConfig = config{LH.higherorder = True, LH.eliminate = FC.Some}
                    , gsQual = (gsQual spec){gsRTAliases = bodies}
                    }
            }

-- Compare every public observation, including positions (Qualifier Eq omits them).
observe = map (\q -> (F.qName q, [(F.qpSym p, F.qpSort p, F.qpPat p) | p <- F.qParams q], F.qBody q, F.sourcePosElts (F.qPos q)))
auto params body pos = ("Auto", [(x, sort, F.PatNone) | (x, sort) <- params], body, F.sourcePosElts pos)
