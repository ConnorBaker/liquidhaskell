{-# OPTIONS_GHC -O1 #-}

-- | The control 'UnpackedFieldExpandedSorts' names: a constructor with an
-- EXPANDING field and no RESORTED one.
--
-- 'Bare.resortedFields' answers, per source field, whether unpacking moved
-- that field's sort -- and it has to answer that while the source and worker
-- argument lists no longer correspond one-to-one, because an
-- @{-\# UNPACK \#-}@ed multi-field product contributes several worker
-- arguments. The regrouping that rebuilds the correspondence must NOT report a
-- field as resorted merely because it expanded: a field standing on several
-- worker arguments still has a selector, since the result refinement rebuilds
-- it as @sel_i VV == C b_j b_k@, at the field's own type.
--
-- Without this module a fix that simply refused every expanding constructor
-- would make 'UnpackedFieldExpandedSorts' green and look correct. Both fields
-- here keep their selectors and 'widthOf' reaches through the expanded one.
--
-- @{-\# UNPACK \#-}@ is load-bearing for the same reason it is there:
-- @-funbox-small-strict-fields@ unpacks only single-WORD strict fields, so a
-- bare @!Extent@ is left alone, the arities never disagree, and the regrouping
-- path is never reached.
--
-- 'mkT' is what raises an obligation. A measure on its own reports
-- @SAFE (0 constraints checked)@, which is nothing proved.
module UnpackedFieldExpandedOnly where

data Extent = Extent !Int !Int

data T = T !Int {-# UNPACK #-} !Extent

{-@ measure widthOf @-}
widthOf :: T -> Int
widthOf (T _ (Extent w _)) = w

{-@ mkT :: n:Int -> w:Int -> h:Int -> {v:T | widthOf v == w} @-}
mkT :: Int -> Int -> Int -> T
mkT n w h = T n (Extent w h)
