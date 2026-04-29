# Cycle 560 Results

## Worked on
§384 standalone (2-leaf, 2-singleton-leaf) four-children mixed Butcher
group `IsG1Equiv` slice on the concrete tree
`tQuadMixedTwoTwo = BTree.node [BTree.leaf, BTree.leaf,
BTree.node [BTree.leaf], BTree.node [BTree.leaf]]`. Successor of the
cycle 559 quad-mixed slice (3 leaves + 1 singleton-leaf).

## Approach
Followed the cycle 559 template in
`OpenMath/ButcherGroup/Section384SlicesQuadMixed.lean`:

- New helpers in `Section384SlicesQuadMixed.lean`:
  - `tQuadMixedTwoTwo : BTree`.
  - `quadMixedTwoTwoLeafChoiceCount : Fin 3 → ℕ`
    (binomial keep counts 2/1/0 for the two pure leaves).
  - `quadMixedTwoTwoLeafChoiceCoef : Fin 3 → ℝ → ℝ → ℝ`
    (binomial expansion of `(X + R)^2`: `R^2`, `2*X*R`, `X^2`).
  - `quadMixedTwoTwoLeafChoiceCount_sum`
    (cut + keep = 2).
  - `quad_mixed_two_two_leaf_stage_polynomial_expand`
    (`(X + R)^2 = ∑ k : Fin 3, …`).
  - `quadMixedTwoTwoSingletonChoiceCoef`,
    `quadMixedTwoTwoSingletonStageChoiceCoef` reusing cycle 559's
    per-singleton-leaf shape.
  - `quadMixedTwoTwoChoiceTree (k : Fin 3) (h₁ h₂ : Fin 3) : BTree`.
  - `quad_mixed_two_two_singleton_stage_expand`
    (`(Y + (X*R + C))^2 = ∑ h₁, ∑ h₂, …`) via squaring cycle 559's
    `quad_mixed_singleton_stage_expand` and `Finset.sum_mul_sum`.
  - `quad_mixed_two_two_stage_polynomial_expand`
    (full `(X+R)^2 * (Y + X*R + C)^2 = ∑ k h₁ h₂, …`).
  - `ButcherProduct.convAt_node_quadMixedTwoTwo_at_i_eq` per-stage
    closed form, factored through cycle 559's
    `convAt_node_mixed_leaf_singleton_leaf_at_i_eq` with `a=2, b=2`.
  - `ButcherProduct.bWeighted_convAt_node_quadMixedTwoTwo_eq` swaps
    sums, collapses each `(k, h₁, h₂)` cell via
    `bSeries_node_replicate_leaf_append_replicate_singleton_leaf` and
    a unified `fin_cases k <;> fin_cases h₁ <;> fin_cases h₂` finisher.
  - `ButcherProduct.bConv_node_quadMixedTwoTwo_eq`,
    `ButcherProduct.bSeries_node_quadMixedTwoTwo_eq` corollaries.

- Lifts in `OpenMath/ButcherGroup.lean`:
  - `QuotEquiv.bSeriesHom_product_node_quadMixedTwoTwo` quotient lift
    via `Quotient.inductionOn₂` + `simpa`.
  - `IsG1Equiv.product_congr_node_quadMixedTwoTwo` headline slice for
    any `p` with `tQuadMixedTwoTwo.order ≤ p` (i.e. `7 ≤ p`).
    Reused the existing
    `order_node_replicate_leaf_append_replicate_singleton_leaf` helper
    to discharge the per-cell second-tableau order bound, identically
    to cycle 559.

## Result
SUCCESS — all nine planned deliverables compile sorry-free.
`lake build` is green (8078 jobs).
No Aristotle submissions: per the strategy, slice cycles since 504
have been HTTP 429 / `IN_PROGRESS` on every submission attempt; manual
closure was the expected path and turned out to be straightforward by
mirroring cycle 559.

## Dead ends
None on the final pass. One mid-cycle fix: the polynomial-expand step
initially used `Finset.sum_mul_sum`, but the right factor was a nested
double sum, so the outer rewrite unified to `Finset.sum_mul` followed
by per-`k` `Finset.mul_sum` — clean and avoids touching the inner
`(h₁, h₂)` shape.

## Discovery
The strategy's "Fin 3 × Fin 3" cut-count axis is most naturally
realised as three independent `Fin 3` axes
`(k, h₁, h₂) : Fin 3 × Fin 3 × Fin 3`: one for the leaf cut count and
one Fin 3 per singleton-leaf child. Squaring cycle 559's per-stage
expansion (leaving the `(Y + X*R + C)` factor unfolded) and then
multiplying out gives the clean grouped expansion in 27 cases. The
finisher `fin_cases k <;> fin_cases h₁ <;> fin_cases h₂ <;> simp [...]`
followed by `first | (Finset.mul_sum + ring) | (Finset.sum_congr +
ring)` discharges all 27 cells uniformly.

## Suggested next approach
Natural next slice: `BTree.node [BTree.leaf, BTree.node [BTree.leaf],
BTree.node [BTree.leaf], BTree.node [BTree.leaf]]` — one pure leaf and
three singleton-leaf children — order 8. Use the same template:
`(X + row)^1 * (Y + X*R + C)^3` per stage, indexed by
`(k, h₁, h₂, h₃) : Fin 2 × Fin 3 × Fin 3 × Fin 3`. The leaf side is
trivial (`(X + R) = ∑ k : Fin 2`), the singleton side cubes cycle 559's
`quad_mixed_singleton_stage_expand` via two applications of the
sum-of-products identity. After this, the `(0-leaf, 4-singleton-leaf)`
all-singleton-leaf parametric slice (cycle 547) already covers the
last quad-shape; the only remaining quad shape is then mixed with
double-leaves, which still needs honest convolution closure work.
