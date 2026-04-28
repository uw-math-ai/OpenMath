# Cycle 537 Results

## Worked on
Butcher §384 `t₂`-slot `IsRKEquivalent` invariance in
`OpenMath/ButcherGroup/Section384.lean`.

## Approach
Added the sorry-first scaffold for:

- `ButcherProduct.convAt_isRKEquivalent_t2`
- `ButcherProduct.bWeighted_convAt_isRKEquivalent_t2`
- `ButcherProduct.bConv_isRKEquivalent_t2`
- `ButcherProduct.bSeries_product_isRKEquivalent_t2`

The live product API is `ButcherProduct t₁ t₂`, not field notation
`t₁.product t₂`, so the fourth statement was adjusted minimally.

Submitted five Aristotle scaffold files under
`.prover-state/aristotle_scaffolds/cycle_537/`:

- `convAt_isRKEquivalent_t2.lean`
- `bWeighted_convAt_isRKEquivalent_t2.lean`
- `bConv_isRKEquivalent_t2.lean`
- `bSeries_product_isRKEquivalent_t2.lean`
- `convAt_perm_t2_aux.lean`

All five submissions returned HTTP 429 immediately. After the required
30-minute wait, a single project-list check showed only older queued jobs and
no cycle-537 artifacts to incorporate.

## Result
SUCCESS.

Closed all four target theorems with zero new `sorry`s. The manual fallback
added a private core lemma `convAt_perm_t2_aux`, proved by `BTree.rec` with
the same nested motive split used in cycles 524 / 534 / 536. The node case
reindexes the inner `Fin t` sum through the `IsRKEquivalent` permutation
using `Equiv.sum_comp`, after rewriting the `A` entries and recursive
`convAt` calls pointwise.

The downstream consequences are direct:

- `bWeighted_convAt_isRKEquivalent_t2` uses `Equiv.sum_comp` plus the
  `b`-transport field from `IsRKEquivalent`.
- `bConv_isRKEquivalent_t2` unfolds `bConv` and rewrites the weighted sum.
- `bSeries_product_isRKEquivalent_t2` rewrites both sides with
  `bSeries_eq_bConv` and applies `bConv_isRKEquivalent_t2`.

Verification:

- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup/Section384.lean`
  passed cleanly.
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build` completed
  successfully.
- `rg -n "\\bsorry\\b" OpenMath` found no live proof sorries, only old prose
  comments in unrelated files.

Line count: `OpenMath/ButcherGroup/Section384.lean` went from 1660 to 1776
lines (+116), still under the 3000-line cap.

## Dead ends
Aristotle did not accept any cycle-537 jobs because the service returned HTTP
429 for every batch member. No generated proof was available to use.

## Discovery
The live `IsRKEquivalent t₂ t₂'` witness has the orientation
`t₂'.A i j = t₂.A (σ i) (σ j)` and `t₂'.b i = t₂.b (σ i)`. This makes the
stronger internal lemma most convenient in the form
`convAt t₂' coef τ i = convAt t₂ coef τ (σ i)`. The public existential
theorem then chooses `σ.symm i` as the transported stage.

## Suggested next approach
Proceed to `IsG1Equiv.product_congr`. The two prerequisites now exist:
the `t₁`-slot coefficient congruence from cycle 536
(`ButcherProduct.convAt_congr_coef`) and this cycle's `t₂`-slot
`IsRKEquivalent` permutation invariance chain through product `bSeries`.
