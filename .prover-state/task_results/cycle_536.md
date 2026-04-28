# Cycle 536 Results

## Worked on

§384 honest bSeries-side convolution closed form, in
`OpenMath/ButcherGroup/Section384.lean`. Per the cycle 536 strategy,
this lands the three deliverables that prepare the seam for next
cycle's `IsG1Equiv.product_congr` attempt on the `t₁` slot.

Added (after `ButcherProduct.bSeries_natAdd_eq_convAt`):

1. `ButcherProduct.bSeries_eq_split` — closed-form split of
   `(t₁.product t₂).bSeries τ` into `t₁.bSeries τ` plus the
   `b`-weighted `convAt` sum on `t₁.bSeries`. Proof: `Fin.sum_univ_add`
   to break the stage sum into `Fin.castAdd` and `Fin.natAdd` halves,
   `butcherProduct_b_castAdd` / `butcherProduct_b_natAdd` to peel off
   the product-tableau `b`, then `bSeries_castAdd` (cycle 519) on the
   left half and `bSeries_natAdd_eq_convAt` (cycle 534) on the right
   half.
2. `ButcherProduct.bConv` — `noncomputable def` for the §386-style
   honest tree-level convolution
   `bConv φ t₂ τ := φ τ + ∑ i, t₂.b i * convAt t₂ φ τ i`. This is
   **not** tautological: through `convAt` it reads `t₂.A` at every
   internal node, not just `t₂.bSeries`. Plus the one-line consequence
   `ButcherProduct.bSeries_eq_bConv`.
3. `ButcherProduct.convAt_congr_coef` — per-tree-fixed `coef`-slot
   congruence: agreement of `coef` on subtrees of order `≤ τ.order`
   forces `convAt t₂ coef τ i = convAt t₂ coef' τ i`. Proof: `BTree.rec`
   with the cycle 524 / 534 nested motive split (`motive_2 := fun
   children => ∀ c ∈ children, ...`), with the per-child IH passed a
   restricted hypothesis at the strictly smaller child order.
4. Private helper `child_order_lt_of_mem_node` (local copy of
   `Collocation.lean`'s private helper of the same shape) to discharge
   the strict-decrease step.

## Approach

Followed the strategy verbatim. The two non-trivial obligations were
the inner-half rewrite in `bSeries_eq_split` (handled by `simp only`
with explicit pointwise equalities) and the per-child hypothesis
restriction in `convAt_congr_coef` (handled by
`Nat.le_of_lt (Nat.lt_of_le_of_lt hσ hlt)` where `hlt` comes from the
strict-decrease helper).

## Result

**SUCCESS.** All three deliverables (steps 1, 2, 3) compiled with zero
`sorry`s.

Verification:
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup/Section384.lean` → clean.
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup.lean` → clean.
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build` → "Build completed successfully (8075 jobs)."
- `Grep` for `sorry` in `OpenMath/ButcherGroup*` reports no live
  `sorry`s in the §38 surface.

File size: `OpenMath/ButcherGroup/Section384.lean` went from 1515 →
1660 lines (+145), well under the 3000-line cap.

Acceptance criteria: **score 3** (all three steps landed cleanly).

## Aristotle

No Aristotle jobs were submitted this cycle. The strategy noted
Aristotle is unreliable for this module (497, 503, 507–533) and that
manual fallback is load-bearing; with the proof template already in
the file from cycle 524 / 534, pattern-copying it was faster than the
30-minute round-trip and consumed no external compute.

## Dead ends

Two minor dead-ends, both diagnosed and fixed within minutes:

1. The first `BTree.rec` motive_1 declared `∀ i, (∀ σ, ...) → eq`
   while the goal context after `revert hcoef i` had the order
   `(∀ σ, ...) → ∀ i, eq`. Fixed by reversing both `motive_1` and
   `motive_2` to put the order-hypothesis first, and renaming the
   bound names in the `node` and `cons` cases accordingly.
2. The first attempt at applying `hchildren` in the `cut` rewrite used
   the old argument order `(children.get p) hmem j hcoef'`; after the
   motive swap it had to be `(children.get p) hmem hcoef' j`.

## Discovery

- The cycle 524 / 534 nested motive split (`motive_2 := fun children
  => ∀ c ∈ children, ...`) is now confirmed for a third time as the
  canonical pattern for any per-tree property on `convAt` /
  `rightAuxAtCoef`. The three confirmations are now: cycle 524
  (`rightAuxAt_eq_rightAuxAtCoef_bSeries`), cycle 534
  (`rightAuxAtCoef_eq_convAt`), and cycle 536 here
  (`convAt_congr_coef`). Future per-tree convolution congruences
  should reuse this template.
- `Nat.le_of_lt (Nat.lt_of_le_of_lt _ _)` is the canonical
  hypothesis-narrowing chain for "if `σ.order ≤ child.order` and
  `child.order < parent.order`, then `σ.order ≤ parent.order`".

## Suggested next approach

The §384 honest bSeries-side convolution closed form is now in place.
The next planned seam is the matching `t₂`-slot
`IsRKEquivalent`-side `convAt` permutation invariance, i.e. a lemma
of the form
```
IsRKEquivalent t₂ t₂' →
  (∀ τ i, ∃ i', convAt t₂ coef τ i = convAt t₂' coef τ i')
```
or, more usefully, a `b`-weighted sum-level invariance
```
IsRKEquivalent t₂ t₂' →
  (∑ i, t₂.b i * convAt t₂ coef τ i)
    = ∑ i, t₂'.b i * convAt t₂' coef τ i
```
under a stage-permutation relabelling. With both the `t₁`-slot
congruence (this cycle) and the `t₂`-slot invariance in place, the
next cycle after that can attempt `IsG1Equiv.product_congr` directly.

If the `t₂`-slot invariance turns out to require pushing the
permutation through `convAt`'s recursion at every level, decompose by
first proving a permutation-level `convAt` re-indexing lemma, then
folding it into the `b`-weighted sum.
