{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
module TotalityErrorNoTotality (value) where
-- Preserve Prelude.error's historical contract even with no-totality.
value :: Int
value = error "reachable pure bottom"
