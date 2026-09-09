-- | ONE authority for the correspondence between a data constructor's SOURCE
-- fields and its WORKER's arguments.
--
-- Haskell gives a data constructor two argument lists. The SOURCE fields are
-- what the user wrote, what a @{-@ data @-}@ block refines, what a measure
-- equation is stated over and what 'Ghc.dataConOrigArgTys' returns. The
-- WORKER's arguments are what a Core @case@ alternative binds, what the
-- constructor's spec type has to be bound at (the "specified type does not
-- refine Haskell type" check compares against the worker) and what
-- 'Ghc.dataConRepArgTys' returns. Below @-O1@ the two coincide. From @-O1@ up,
-- @-funbox-small-strict-fields@ and @{-# UNPACK #-}@ make them differ: a
-- strict field whose type is a single-constructor product is replaced by that
-- constructor's own arguments, transitively, and through newtypes.
--
-- Until this module existed the correspondence was recomputed at roughly nine
-- sites, with two different newtype rules ('deepSplitProductType' saw through
-- them, 'unpackInto' refused them) and four different class-argument rules,
-- and the site the others called "the single authority" -- @resortedFields@ --
-- answered @replicate n False@ whenever it did not recognise a shape, which
-- KEEPS a selector it cannot declare. This module makes the decisions once:
--
--   * NEWTYPES. An @HsUnpack (Just co)@ bang means GHC unpacked THROUGH one or
--     more newtypes, @co :: field-ty ~ product-ty@. They are recorded in
--     'frVia', outermost first, because they are real logic constructors --
--     @newtype Pos = Pos Int@ has @Pos : func([int; Pos])@ and the measure
--     equation @posVal (Pos n) = n@ is stated over it -- so a rebuild of the
--     field from its components is @Pos v@, not the @I# v@ that normalising
--     through the newtype and asking the product's constructor produced.
--
--   * EMBEDDED TYPES stop the descent. @Int@ as @int@, @Set a@ as @Set_Set a@:
--     there is no datatype in the logic, hence no constructor to rebuild with
--     and no selector to project through, so the component stands for the
--     field at the embedded sort.
--
--   * CLASS AND EQUALITY EVIDENCE. The worker leads with one argument per
--     entry of 'Ghc.dataConTheta'; that count is 'rmDictArity' and nothing
--     here re-derives it from a predicate on types.
--
--   * THE SOURCE IS THE TRUTH FOR STRUCTURE. The descent into an unpacked
--     field follows the product constructor's SOURCE fields
--     ('Ghc.dataConInstOrigArgTys') and their own bangs, never its
--     representation: @data C = C !W@ over @data W = W (Set Int)@ has the
--     representation @[Set Int]@, and asking for that would erase the @W@
--     layer, so that a projection through @C@ would name @C@'s own selector at
--     the leaf instead of @W@'s selector under it. Measured: the refusal for a
--     projection through a selector that does not exist stopped firing, and
--     the equation went out cancelled to the identity.
--
--   * SELECTORS. A field's selector is a logic function at the field's SOURCE
--     type whose one equation is @sel_i (D ys) = rebuild_i@, the field rebuilt
--     from the worker arguments it stands on. That equation is well sorted
--     exactly when the rebuild is expressible, so the selector is DROPPED only
--     for a field whose sort moved AND whose rebuild names a constructor the
--     logic does not have ('fieldSelectorDropped'): @!(IORef Int)@ becomes a
--     @MutVar#@ and neither @IORef@ nor @STRef@ has a datatype in the logic,
--     while @!W@ over a module-local @W@ keeps @sel (D y) = W y@. Which
--     constructors the logic has is a predicate passed in -- membership in the
--     'Bare.DataConMap' -- because this module sits below the place that is
--     decided. Before this module, EVERY field whose sort moved lost its
--     selector, and a @{-@ data @-}@ record with such a field was rejected at
--     its own selector's signature with @Unbound symbol@.
--
--   * THE WORKER IS THE TRUTH FOR SORTS. The descent decides STRUCTURE -- which
--     field expands into which constructor and how many leaves -- and the leaf
--     types are then read off the worker's own argument list, in order. If the
--     count disagrees the answer is a 'Left', never a default: a shape this
--     module does not model is reported at the constructor rather than
--     silently disarming a guard downstream.
--
-- The sort function is a parameter rather than an import so that this module
-- sits below 'Language.Haskell.Liquid.Types.RefType', whose 'expandProductType'
-- is a consumer; 'RefType.dataConRepMap' is the one-liner everyone else calls.
module Language.Haskell.Liquid.Types.RepMap
  ( RepMap (..)
  , FieldRep (..)
  , Shape (..)
  , RepMapError (..)
  , repMap
  , repMapErrorDoc
  , dictArity
    -- * Reading a 'FieldRep'
  , fieldLeaves
  , fieldLeafCount
  , fieldChanged
  , fieldProduct
    -- * The two directions of the seam
  , rebuildField
  , projectField
  , fieldCtorProjs
  , ctorLeafProjs
  , splitLeaves
    -- * What the logic can name
  , fieldRebuildable
  , fieldProjectable
  , fieldSelectorDropped
  , undeclaredSelectorsOf
  ) where

import           Prelude hiding (error)

import qualified Data.List as L
import           Text.PrettyPrint.HughesPJ (Doc, text, (<+>), quotes)

import qualified Language.Fixpoint.Types as F
import           Liquid.GHC.API as Ghc hiding (Expr, text, (<+>), quotes)
import qualified Language.Haskell.Liquid.GHC.Misc as GM
import           Language.Haskell.Liquid.GHC.TypeRep () -- Eq Type instance
import           Language.Haskell.Liquid.Types.Types () -- Symbolic DataCon: the ONE logic symbol per constructor, its worker's

-- | One data constructor's source-to-worker correspondence.
data RepMap = RepMap
  { rmDataCon   :: DataCon
  , rmDictArity :: Int
    -- ^ How many arguments the worker takes BEFORE the value arguments: one per
    -- entry of 'Ghc.dataConTheta' (equality evidence first, then class
    -- dictionaries).
  , rmFields    :: [FieldRep]
    -- ^ One per source field, in source order.
  , rmChanged   :: Bool
    -- ^ Did unpacking change ANY field's representation? 'False' is exactly
    -- the @-O0@ shape, where every site's rewrite is the identity.
  }

-- | How one source field is represented in the worker.
data FieldRep = FieldRep
  { frSource   :: Type
    -- ^ The field's type as written.
  , frVia      :: [DataCon]
    -- ^ Newtype constructors GHC unpacked THROUGH to reach 'frShape',
    -- outermost first. Empty unless the bang was @HsUnpack (Just co)@.
  , frShape    :: Shape
  , frResorted :: Bool
    -- ^ Does this field stand on exactly ONE worker argument whose SORT differs
    -- from the field's own? Then its binder in the constructor's spec is at the
    -- worker's sort, a refinement written on it has to be rebuilt over the
    -- component ('rebuildField'), and its selector survives only if that
    -- rebuild is expressible ('fieldSelectorDropped'). A field standing on
    -- several arguments is never resorted: its reconstruction @C b_j b_k@ is
    -- at the field's own type.
  }

data Shape
  = Atom Type
    -- ^ One worker argument stands for the field; the type is the WORKER's.
    -- Equal to 'frSource' when GHC did nothing; @Int#@ for a @!Int@; the
    -- embedded component when the descent stopped at an embedded type; an
    -- unboxed sum when GHC unpacked a sum type.
  | Product DataCon [FieldRep]
    -- ^ GHC unpacked the field into this constructor's fields, each of which is
    -- itself represented as described.

data RepMapError
  = BangCountMismatch DataCon Int Int
    -- ^ 'Ghc.dataConImplBangs' and 'Ghc.dataConOrigArgTys' disagree in length.
  | LeafCountMismatch DataCon Int Int Int
    -- ^ The descent's leaves do not account for the worker's value arguments:
    -- @(source fields, leaves, worker value arguments)@.
  | NewtypeChainTooDeep DataCon Type

repMapErrorDoc :: RepMapError -> Doc
repMapErrorDoc (BangCountMismatch d nSrc nBang)
  = text "cannot align the fields of" <+> quotes (text (GM.showPpr d))
    <+> text "with their strictness annotations:" <+> text (show nSrc)
    <+> text "fields but" <+> text (show nBang) <+> text "bangs"
repMapErrorDoc (LeafCountMismatch d nSrc nLeaf nRep)
  = text "cannot align the fields of" <+> quotes (text (GM.showPpr d))
    <+> text "with its worker's arguments:" <+> text (show nSrc)
    <+> text "source fields expand to" <+> text (show nLeaf)
    <+> text "arguments, but the worker takes" <+> text (show nRep)
repMapErrorDoc (NewtypeChainTooDeep d t)
  = text "cannot unwrap the newtypes of field type" <+> quotes (text (GM.showPpr t))
    <+> text "of" <+> quotes (text (GM.showPpr d))

-- | Compute the correspondence for one constructor. @sortOf@ is the logic sort
-- of a type -- 'RefType.typeSort' applied to the embeddings -- and decides
-- 'frResorted'.
repMap :: F.TCEmb TyCon -> (Type -> F.Sort) -> DataCon -> Either RepMapError RepMap
repMap embs sortOf dc
  | length bangs /= length srcTys
  = Left (BangCountMismatch dc (length srcTys) (length bangs))
  | otherwise
  = do shapes <- mapM (uncurry (descend embs dc)) (zip srcTys bangs)
       let nLeaf = sum (map leafCount0 shapes)
       if nLeaf /= length valTys
         then Left (LeafCountMismatch dc (length srcTys) nLeaf (length valTys))
         else let (fields, rest) = fillAll shapes valTys
              in if not (null rest)
                   then Left (LeafCountMismatch dc (length srcTys) nLeaf (length valTys))
                   else Right RepMap
                          { rmDataCon   = dc
                          , rmDictArity = nDict
                          , rmFields    = fields
                          , rmChanged   = any fieldChanged fields
                          }
  where
    srcTys = irrelevantMult <$> dataConOrigArgTys dc
    bangs  = dataConImplBangs dc
    nDict  = dictArity dc
    valTys = drop nDict (irrelevantMult <$> dataConRepArgTys dc)

    -- Hand each leaf, in worker order, the worker's type for it.
    fillAll [] ys = ([], ys)
    fillAll (s : ss) ys =
      let (f, ys')   = fill s ys
          (fs, ys'') = fillAll ss ys'
      in (f : fs, ys'')

    fill (Field0 src via sh) ys = case sh of
      Atom0 -> case ys of
        (y : ys') -> (mk src via (Atom y) (Just y), ys')
        []        -> (mk src via (Atom src) Nothing, [])  -- unreachable: counts were checked
      Product0 d parts ->
        let (fs, ys') = fillAll parts ys
            leaves    = concatMap fieldLeaves fs
        in (mk src via (Product d fs) (case leaves of [l] -> Just l; _ -> Nothing), ys')

    mk src via sh single = FieldRep
      { frSource   = src
      , frVia      = via
      , frShape    = sh
      , frResorted = case single of
          Just rep -> sortOf src /= sortOf rep
          Nothing  -> False
      }

-- | How many arguments the worker takes BEFORE its value arguments: one per
-- entry of 'dataConTheta', equality evidence first, then class
-- dictionaries. The one place that count is decided; 'rmDictArity' is it.
dictArity :: DataCon -> Int
dictArity = length . dataConTheta

-- | Structure only: what does GHC's bang say this field expands to?
data Field0 = Field0 Type [DataCon] Shape0
data Shape0 = Atom0 | Product0 DataCon [Field0]

leafCount0 :: Field0 -> Int
leafCount0 (Field0 _ _ Atom0)             = 1
leafCount0 (Field0 _ _ (Product0 _ parts)) = sum (map leafCount0 parts)

descend :: F.TCEmb TyCon -> DataCon -> Type -> HsImplBang -> Either RepMapError Field0
descend embs dc t b = case b of
  HsUnpack mco -> do
    (via, t') <- case mco of
      Just co | Pair _ rhs <- coercionKind co -> unwrapNewtypes dc t rhs
      _                                       -> Right ([], t)
    case productOf embs t' of
      Just (d, argTys) -> do
        parts <- mapM (uncurry (descend embs dc)) (zip argTys (dataConImplBangs d))
        Right (Field0 t via (Product0 d parts))
      Nothing -> Right (Field0 t via Atom0)
  _ -> Right (Field0 t [] Atom0)

-- | The single-constructor, non-embedded, non-newtype product a type is, with
-- that constructor's SOURCE argument types instantiated at the type's
-- arguments. Source, not representation: 'Ghc.dataConInstArgTys' would answer
-- with the constructor's own unpacked fields already flattened, and the
-- descent below is what decides that.
-- Anything else -- an embedded type, a sum GHC unboxed to an unboxed sum, a
-- type variable -- is a leaf.
productOf :: F.TCEmb TyCon -> Type -> Maybe (DataCon, [Type])
productOf embs t0
  | Just (tc, args) <- splitTyConApp_maybe (expandTypeSynonyms t0)
  , not (isNewTyCon tc)
  , not (F.tceMember tc embs)
  , Just d <- tyConSingleDataCon_maybe tc
  , null (dataConExTyCoVars d)
  , length (dataConImplBangs d) == length (dataConOrigArgTys d)
  = Just (d, irrelevantMult <$> dataConInstOrigArgTys d args)
  | otherwise
  = Nothing

-- | Peel newtype constructors off @t@ until the type GHC's coercion lands on.
unwrapNewtypes :: DataCon -> Type -> Type -> Either RepMapError ([DataCon], Type)
unwrapNewtypes dc t0 rhs = go (64 :: Int) t0
  where
    go 0 _ = Left (NewtypeChainTooDeep dc t0)
    go n t
      | eqType (expandTypeSynonyms t) (expandTypeSynonyms rhs) = Right ([], t)
      | Just (tc, args) <- splitTyConApp_maybe (expandTypeSynonyms t)
      , isNewTyCon tc
      , Just d <- tyConSingleDataCon_maybe tc
      = do (ds, t') <- go (n - 1) (newTyConInstRhs tc args)
           Right (d : ds, t')
      | otherwise
      -- GHC's coercion knows better than the loop: trust its right-hand side.
      = Right ([], rhs)

--------------------------------------------------------------------------------
-- Reading a FieldRep
--------------------------------------------------------------------------------

-- | The worker's argument types this field stands on, in worker order.
fieldLeaves :: FieldRep -> [Type]
fieldLeaves fr = case frShape fr of
  Atom t          -> [t]
  Product _ parts -> concatMap fieldLeaves parts

fieldLeafCount :: FieldRep -> Int
fieldLeafCount = length . fieldLeaves

-- | Did GHC change this field's representation at all? A lazy or merely strict
-- field of an unchanged type is the only 'False'.
fieldChanged :: FieldRep -> Bool
fieldChanged fr = case (frVia fr, frShape fr) of
  ([], Atom t) -> not (eqType (frSource fr) t)
  _            -> True

-- | The constructor GHC unpacked this field into, if any.
fieldProduct :: FieldRep -> Maybe (DataCon, [FieldRep])
fieldProduct fr = case frShape fr of
  Product d parts -> Just (d, parts)
  Atom _          -> Nothing

--------------------------------------------------------------------------------
-- The two directions
--------------------------------------------------------------------------------

-- | RECONSTRUCTION. Given the expressions denoting this field's worker
-- arguments, in worker order, the expression denoting the field.
--
-- The application to a 'Product' is FLAT: the constructor is applied to every
-- leaf, with no intermediate constructor between it and them, however deep
-- those leaves were found. That is what the logic's constructor takes:
-- 'RefType.expandProductType' rewrites EVERY constructor's spec, this one's
-- included, so if GHC unpacked one of ITS fields then the logic's symbol
-- already takes that field's components. The newtypes in 'frVia' are the
-- exception and the reason it is recorded: a newtype has no worker, its logic
-- symbol takes its one source field, so it wraps the reconstruction rather
-- than being flattened into it.
rebuildField :: FieldRep -> [F.Expr] -> F.Expr
rebuildField fr leaves = foldr wrap body (frVia fr)
  where
    wrap d e = F.mkEApp (GM.namedLocSymbol d) [e]
    body = case (frShape fr, leaves) of
      (Atom _, [l])        -> l
      (Product d _, _)     -> F.mkEApp (GM.namedLocSymbol d) leaves
      (Atom _, _)          -> F.PFalse -- unreachable when @leaves@ came from 'splitLeaves'

-- | PROJECTION, the inverse. Given a way to name constructor @d@'s @i@-th
-- selector and the expression denoting the field, the expressions denoting
-- its worker arguments, in worker order. Newtypes in 'frVia' are projected
-- through by their one selector.
projectField :: (DataCon -> Int -> F.Symbol) -> FieldRep -> F.Expr -> [F.Expr]
projectField sel fr e0 = case frShape fr of
  Atom _          -> [inner]
  Product d parts -> concat [ projectField sel part (F.EApp (F.EVar (sel d i)) inner)
                            | (i, part) <- zip [1 ..] parts ]
  where
    inner = L.foldl' (\e d -> F.EApp (F.EVar (sel d 1)) e) e0 (frVia fr)

-- | Every constructor the field's expansion passes through, each with the
-- function that PROJECTS a value of it down to its worker arguments -- what
-- the eta law @C (proj_1 e) .. (proj_m e) ==> e@ needs. The logic's @C@ is
-- applied FLAT to its leaves, so @proj_k@ is the whole selector composition
-- from @e@ to leaf @k@, not @C@'s own selector alone: for @Pair !W !Int@ over
-- @W (Set Int)@ the redex is @Pair (W.sel1 (Pair.sel1 e)) (Pair.sel2 e)@, and
-- that is @e@ -- @W (W.sel1 w) = w@ and @Pair (Pair.sel1 e) (Pair.sel2 e) = e@
-- together -- which the solver cannot see without PLE, since @W.sel1@ is a
-- function it has no equations for.
fieldCtorProjs :: (DataCon -> Int -> F.Symbol) -> FieldRep -> [(F.Symbol, F.Expr -> [F.Expr])]
fieldCtorProjs sel fr
  =  [ (F.val (GM.namedLocSymbol v), \e -> [F.EApp (F.EVar (sel v 1)) e]) | v <- frVia fr ]
  ++ case frShape fr of
       Atom _          -> []
       Product d parts -> leafProjs sel d parts : concatMap (fieldCtorProjs sel) parts

-- | The constructor itself, projected to its leaves: the entry 'fieldCtorProjs'
-- gives for a nested product, for the constructor at the top.
ctorLeafProjs :: (DataCon -> Int -> F.Symbol) -> RepMap -> (F.Symbol, F.Expr -> [F.Expr])
ctorLeafProjs sel rm = leafProjs sel (rmDataCon rm) (rmFields rm)

leafProjs :: (DataCon -> Int -> F.Symbol) -> DataCon -> [FieldRep] -> (F.Symbol, F.Expr -> [F.Expr])
leafProjs sel d frs =
  ( F.val (GM.namedLocSymbol d)
  , \e -> concat [ projectField sel fr (F.EApp (F.EVar (sel d i)) e) | (i, fr) <- zip [1 ..] frs ] )

-- | Cut a worker-ordered list into one group per field, or 'Nothing' if the
-- list is not exactly the fields' leaves.
splitLeaves :: [FieldRep] -> [a] -> Maybe [[a]]
splitLeaves []         []  = Just []
splitLeaves []         _   = Nothing
splitLeaves (fr : frs) xs
  | length xs >= n = (here :) <$> splitLeaves frs there
  | otherwise      = Nothing
  where
    n             = fieldLeafCount fr
    (here, there) = splitAt n xs

-- | Every selector a projection through this constructor can NAME and the
-- logic never DECLARED -- each resorted field of the constructor and of every
-- constructor its fields expand into, transitively -- with the field it
-- belongs to, in descent order.
-- | Can the logic REBUILD this field from its worker arguments -- is every
-- constructor 'rebuildField' applies one the logic knows?
fieldRebuildable :: (DataCon -> Bool) -> FieldRep -> Bool
fieldRebuildable known fr = all known (frVia fr) && case frShape fr of
  Product d _ -> known d
  Atom _      -> True

-- | Can the logic PROJECT this field's worker arguments out of the field -- is
-- every selector 'projectField' composes one the logic declares? Deeper than
-- 'fieldRebuildable', because a rebuild applies the outermost constructor to
-- the leaves FLAT while a projection walks every level.
fieldProjectable :: (DataCon -> Bool) -> FieldRep -> Bool
fieldProjectable known fr = all known (frVia fr) && case frShape fr of
  Product d parts -> known d && all (fieldProjectable known) parts
  Atom _          -> True

-- | Does this field lose its selector? Only when its sort moved AND the
-- selector's equation @sel (D ys) = rebuild@ cannot be stated. See the module
-- header, SELECTORS.
fieldSelectorDropped :: (DataCon -> Bool) -> FieldRep -> Bool
fieldSelectorDropped known fr = frResorted fr && not (fieldRebuildable known fr)

-- | Every selector a projection along this constructor's descent can NAME that
-- the logic does NOT declare, in descent order: the constructor's own dropped
-- selectors, the selector of every unknown newtype passed through, every
-- selector of an unknown product, and the same for each product's fields --
-- the descent of a nested product IS that constructor's own 'RepMap', so its
-- fields' verdicts here agree with the ones its own declaration got. A
-- consumer refuses to emit an equation that names one of these, since the
-- failure would otherwise surface as @Unbound symbol@ at the data declaration,
-- naming neither the measure nor the field.
undeclaredSelectorsOf :: (DataCon -> Bool) -> (DataCon -> Int -> F.Symbol) -> RepMap
                      -> [(F.Symbol, (DataCon, Int))]
undeclaredSelectorsOf known sel rm = walk (rmDataCon rm) (rmFields rm)
  where
    walk d frs = concat
      [ [ (sel d i, (d, i)) | fieldSelectorDropped known fr ] ++ deeper fr
      | (i, fr) <- zip [1 ..] frs ]
    deeper fr
      =  [ (sel v 1, (v, 1)) | v <- frVia fr, not (known v) ]
      ++ case frShape fr of
           Product d parts -> [ (sel d j, (d, j)) | not (known d), j <- [1 .. length parts] ]
                              ++ walk d parts
           Atom _          -> []
