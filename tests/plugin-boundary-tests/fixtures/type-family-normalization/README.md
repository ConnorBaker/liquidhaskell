# Family-root refinement preservation

The family witnesses explicitly interpret `Carrier` as the logical `int` sort.
They test preservation of the authored root obligation during carrier
normalization: `I# 1#` satisfies `v > 0`, while `I# 0#` does not. The direct
`Int` witness checks the same counterclaim without a family application.

These witnesses do not establish automatic closed-type-family interpretation.
Although GHC reduces `Carrier Int` to `Int`, Liquid's default logical sort for
the application remains nominal. Interpreting that reduction requires the
appropriate family environment and its coercion evidence; preserving a root
refinement alone does not supply either.
