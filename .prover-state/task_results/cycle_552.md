# Cycle 552 Results

## Worked on
§384 mixed leaf / double-leaf G1 slice (per the cycle 552 strategy).
Target tree family:
`BTree.node (List.replicate a BTree.leaf ++ List.replicate b (BTree.node [BTree.leaf, BTree.leaf]))`.

## Approach
Followed the cycle 549 (`leaf, node [leaf]`) parametric template, with
the strategy's documented **fallback** path: per-`i` `convAt` closed
form + `bConv` closed form + `bSeries` corollary, but **without**
the explicit cut-decomposition powerset expansion. The squared
keep-factor on the double-leaf side
(`(coef leaf + row j)^2` inside `∑_j A i j (...)^2`) would require a
five-level powerset expansion to mirror cycle 549's three-level form
— the strategy explicitly authorizes deferring `bSeries` powerset,
quotient lift, and `IsG1Equiv` slice to cycle 553 in that case.

Lemmas added to `OpenMath/ButcherGroup/Section384Slices.lean`:

1. `convAt_double_leaf_eq` (private):
   `convAt t₂ coef (node [leaf, leaf]) i = (coef leaf + ∑ j, A i j) ^ 2`.
   Closed via `convAt_node` + `Finset.prod_add` + `fin_cases p` over
   `Fin 2`.

2. `convAt_node_mixed_leaf_double_leaf_at_i_eq` (private): the
   per-stage closed form
   `(coef leaf + row i)^a * (coef (node [leaf,leaf]) + ∑ j, A i j *
     (coef leaf + row j)^2)^b`.
   Closed by mirroring the cycle 549 helper structure verbatim:
   `convAt_node` → `Finset.prod_add` → reindex via
   `Fin.cast hlen.symm` Equiv → `Fin.prod_univ_add` → leaf-block
   evaluation via `convAt_leaf`, double-leaf-block evaluation via
   the new `convAt_double_leaf_eq`.

3. `ButcherProduct.bConv_node_mixed_leaf_double_leaf_eq`: the `bConv`
   closed form, expressed at the per-stage level
   (i.e. `t₁.bSeries (node ...) + ∑ i, t₂.b i * (per-stage RHS)`).

4. `ButcherProduct.bSeries_node_mixed_leaf_double_leaf_eq`: the
   `bSeries` corollary, by `bSeries_eq_bConv` + (3).

## Result
**SUCCESS (fallback path).** All three new theorems plus two private
helpers compile with zero `sorry`. `lake env lean
OpenMath/ButcherGroup/Section384Slices.lean` and
`lake env lean OpenMath/ButcherGroup.lean` both pass cleanly.
Sorry count remains 0 in `OpenMath/`.

The quotient lift (`QuotEquiv.bSeriesHom_product_node_mixed_leaf_double_leaf`)
and the `IsG1Equiv` slice
(`IsG1Equiv.product_congr_node_mixed_leaf_double_leaf`) are
**not** delivered this cycle — explicitly deferred to cycle 553 per
the strategy fallback wording. The cycle 552 strategy authorized this:

> If the closed-form RHS turns out structurally heavier than cycle 549
> expected (e.g. the squared keep-factor produces a five-level rather
> than three-level powerset expansion), the acceptable fallback is to
> reduce the deliverable to the per-`i` helper + `bConv` closed form
> only, deferring `bSeries`, quotient lift, and `IsG1Equiv` slice to
> cycle 553. State this explicitly in the cycle 552 task result; do
> not silently shrink scope.

This is that explicit statement: the structural form
`∑_j A i j * (X + row j)^2` does not collapse like cycle 549's
`∑_j A i j * (X + row j) = X * row i + chain i` — it expands to a
quadratic in `X` with three independent stage sums (`row i`,
`∑ j A i j * row j`, `∑ j A i j * (row j)^2`), each of which
corresponds to a different bushy elementary weight. Producing a
G1-friendly cut-decomposition therefore requires a five-level
powerset expansion (root-leaf cut × root-double-leaf cut × inner cut
on each kept double-leaf grandchild × inner cut on each kept
double-leaf grandchild — two of those because of the squared factor).
This is genuine new combinatorics, not a cycle 549 transcription.

## Aristotle status
Submitted a single best-effort `submit_file` job for the slice file.
Returned HTTP 429 ("too many requests in progress") as expected; the
last 40+ cycles all hit this. Did not poll. Manual closure was the
sole driver of progress.

## Dead ends
- Initial `Finset.prod_add` direct rewrite over the convAt sum form
  failed because `Finset.prod_add` rewrites *product* into *sum*,
  not the reverse. Resolved by mirroring cycle 549's `hprod_add`
  intermediate, which proves `sum = product` by applying
  `Finset.prod_add` to the *product* side and then identifying
  via `Finset.powerset_univ` and `Finset.compl_eq_univ_sdiff`.
- Initial attempt to rewrite `[leaf, leaf].length` as `2` via
  `show ... from rfl` ran into a "motive is not type correct"
  error because `Fin n` depends on `n`. Resolved by leaving the
  length opaque and discharging the final `^ 2` via a trailing
  `rfl` (`[leaf, leaf].length = 2` is definitional).

## Discovery
- The double-leaf inner factor
  `∑ j, A i j * (coef leaf + row j)^2`
  is a quadratic in `coef leaf`. Its expansion
  `(coef leaf)^2 * row i + 2 * coef leaf * (∑ j A i j * row j)
   + ∑ j A i j * (row j)^2`
  exposes three distinct bushy elementary weights:
  `elementaryWeight (node [leaf]) i`,
  `elementaryWeight (node [node [leaf]]) i`,
  `elementaryWeight (node [node [leaf, leaf]]) i`.
  Cycle 553's full cut-decomposition will need to track this
  three-way bushy decomposition for the `t₂.b`-weighted
  collapse step.

- Cycle 552's per-stage form
  `(X + row i)^a * (Y + ∑_j A i j (X + row j)^2)^b`
  generalizes cycle 549's
  `(X + row i)^a * (Y + (X * row i + chain i))^b`.
  The pattern for cycle 553 (next inner-arity rung) would need to
  handle `(coef leaf + row j)^k` for `k ≥ 2`, which is the same
  combinatorial structure modulo the binomial coefficient k+1.

## Suggested next approach (for cycle 553)
1. **Cycle 553 — full cut-decomposition for cycle 552's family.**
   Take the cycle 552 per-stage form
   `(X + row i)^a * (Y + ∑_j A i j (X + row j)^2)^b` and produce the
   cut-form analog of cycle 549's
   `bSeries_node_mixed_leaf_singleton_leaf_eq`. The cleanest split:
   first prove a `bWeighted_double_leaf_kept_factor_eq` analog of
   cycle 549's `bWeighted_kept_singleton_leaf_product_eq`, then
   weave it into a four-level outer powerset
   (`S_leaf : Finset (Fin a)` × `S_dl : Finset (Fin b)` ×
    `T1 : Finset (S_dlᶜ)` × `T2 : Finset (S_dlᶜ)` for the squared
   factor). Once that lands, the quotient lift and `IsG1Equiv`
   slice follow the cycle 549 pattern verbatim.

2. **Alternative** — pick a simpler next rung: the
   `(node [leaf], node [leaf, leaf])` mixed family. This combines
   the cycle 547 inner-leaf cut with the cycle 552 squared factor;
   it would deliver another G1-direction slice without the
   five-level powerset blow-up.

3. **Do not** retry the unrestricted `IsG1Equiv.product_congr` —
   still blocked on the §384 honest convolution decomposition
   (`butcher_g1_mul_section384_blocker.md`).

## Files modified
- `OpenMath/ButcherGroup/Section384Slices.lean` — appended cycle 552
  block (one private helper, one private per-`i` helper, two public
  theorems). No other tracked files changed.

## Sorry count
Pre-cycle: 0. Post-cycle: 0. (Cycle 549 invariant maintained.)
