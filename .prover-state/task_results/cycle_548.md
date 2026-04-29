# Cycle 548 Results

## Worked on
§384 mixed leaf / singleton-leaf root-children parametric closed form. Four
deliverables targeted: `bConv_node_mixed_leaf_singleton_leaf_eq` (headline),
`bSeries_node_mixed_leaf_singleton_leaf_eq` (corollary),
`QuotEquiv.bSeriesHom_product_node_mixed_leaf_singleton_leaf` (lift), and
`product_congr_node_mixed_leaf_singleton_leaf` (G1 slice with bound
`1 + a + 2 * b ≤ p`).

## Approach
Sorry-first scaffold + Aristotle-first batch. After 429 throttling on
Aristotle, manual closure of the structural pieces.

Built a private helper `convAt_node_mixed_leaf_singleton_leaf_at_i_eq` that
produces the per-i closed form
```
convAt t₂ coef (node (replicate a leaf ++ replicate b (node [leaf]))) i
  = (coef leaf + ∑ j, A i j) ^ a *
    (coef (node [leaf]) + (coef leaf * ∑ j, A i j + ∑ j, A i j * ∑ k, A j k))^b
```
via `convAt_node` → `Finset.prod_add` (univ powerset → product) →
length-cast `Equiv` and `Fintype.prod_equiv` → `Fin.prod_univ_add` to split
into the leaf-prefix and singleton-leaf-suffix factors → per-position
evaluation using `List.get_eq_getElem`, `List.getElem_append_left/right`,
`List.get_replicate`, `convAt_leaf`, and `convAt_singleton_leaf_eq`.

Wired the QuotEquiv lift (`bSeriesHom_product_node_mixed_leaf_singleton_leaf`)
via `Quotient.inductionOn₂` + `simpa` from
`bSeries_node_mixed_leaf_singleton_leaf_eq`.

The bSeries corollary chains via `bSeries_eq_bConv` and the headline.

For the G1 slice, mirrored cycle 547's pattern:
- `hleaf` from `BTree.order_leaf = 1`,
- `hnode` from `order_node_replicate_leaf_append_replicate_singleton_leaf = 1 + a + 2b`,
- `hsl_pow` by `S_sl.card = 0` case-split (when nonempty, `b ≥ 1` ⇒ `p ≥ 2`),
- `hmixed` for the kept-side r-summand bounded by
  `1 + (a - |S_leaf| + |T|) + 2 * (|S_slᶜ| - |T|) ≤ 1 + a + 2b ≤ p`.

## Result
SUCCESS (partial):
- ✅ `convAt_node_mixed_leaf_singleton_leaf_at_i_eq` helper (Section384.lean) — full proof.
- ❌ `ButcherProduct.bConv_node_mixed_leaf_singleton_leaf_eq` — `sorry` (live, headline).
- ✅ `ButcherProduct.bSeries_node_mixed_leaf_singleton_leaf_eq` (corollary) — chains
  via `bSeries_eq_bConv` and the headline (compiles modulo headline `sorry`).
- ✅ `QuotEquiv.bSeriesHom_product_node_mixed_leaf_singleton_leaf` (lift)
  — full proof via `Quotient.inductionOn₂` (compiles modulo headline `sorry`).
- ✅ `IsG1Equiv.product_congr_node_mixed_leaf_singleton_leaf` (G1 slice
  deliverable) — full proof, ~85 lines.

`OpenMath/ButcherGroup.lean` compiles cleanly. `OpenMath/ButcherGroup/Section384.lean`
compiles with one `sorry` warning at the headline.

## Dead ends
- `Finset.prod_equiv` directly without `.symm` was hitting metavariable
  inference. Switched to `Fintype.prod_equiv` which takes `f, g` explicitly.
- `(Finset.prod_const _).symm.trans ?_` couldn't pin down the constant.
  Replaced with explicit `calc` using `Finset.prod_congr` then `prod_const`.
- `List.get_append_left`/`get_append_right` don't exist in current Mathlib.
  Use `List.get_eq_getElem` + `List.getElem_append_left`/`getElem_append_right`.
- `rw [convAt_singleton_leaf_eq]` failed under a `∑ x` binder — `simp only`
  goes under binders.
- Aristotle returned HTTP 429 ("too many requests in progress") on every
  retry. Per CLAUDE.md, did not poll.

## Discovery
- For the headline, the natural strategy is to mirror cycle 547's
  `bWeighted_convAt_node_replicate_singleton_leaf_eq_length` but generalize
  to a heterogeneous children list `replicate a leaf ++ replicate b (node [leaf])`,
  then reindex `Fin (a+b)` powerset → `Fin a × Fin b` powersets via
  `Finset.subset_disjUnion` (or a manual product Equiv on Finsets).
- The per-i helper `convAt_node_mixed_leaf_singleton_leaf_at_i_eq` already
  gives the closed form at each i. An alternative approach (potentially
  simpler than reindexing the kept-children powerset directly) is:
  expand each per-i factor `(coef leaf + row)^a * (coef sl + coef leaf * row + chain)^b`
  by `Finset.prod_add` reverse to materialize the triple `S_leaf, S_sl, T`
  powersets, then collapse the kept-side `row^k * chain^m` via
  `bSeries_node_replicate_leaf_append_replicate_singleton_leaf` after
  swapping `∑ i` inside.

## Suggested next approach
- Cycle 549 should land the headline `bConv_node_mixed_leaf_singleton_leaf_eq`.
  Two viable routes:
  1. **Reindex route** (mirrors cycle 547): write
     `bWeighted_convAt_node_mixed_leaf_singleton_leaf_eq_length` then
     `bWeighted_convAt_node_mixed_leaf_singleton_leaf_eq` reindexing
     `Finset (Fin (a+b))` ≃ `Finset (Fin a) × Finset (Fin b)` via
     `Finset.subset_disjUnion` or a custom Equiv.
  2. **Per-i route** (uses cycle 548 helper): start from
     `bConv = ∑ i b_i * convAt`, rewrite via the helper, expand each
     factor by `Finset.prod_add` reverse to get a triple-powerset sum
     inside `∑ i`, swap `∑ i` inside, then collapse the kept-side product
     of row/chain using `bSeries_node_replicate_leaf_append_replicate_singleton_leaf`.
- Estimated 150-300 lines of Lean either way. Aristotle should be tried
  first when its queue clears.
- Once headline lands, the bSeries corollary, QuotEquiv lift, and G1 slice
  (already proved) all compile without further changes.

## Status of plan.md alignment
The cycle 548 G1 slice deliverable is fully landed. The remaining gap is
the headline `bConv` proof, blocking the bSeries corollary and the
QuotEquiv lift. All four target theorems exist with their canonical
statements; only one carries a live `sorry`.
