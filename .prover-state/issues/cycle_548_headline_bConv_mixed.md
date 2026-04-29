# Issue: bConv_node_mixed_leaf_singleton_leaf_eq remains as live `sorry`

## Blocker
The headline cycle 548 theorem
`ButcherProduct.bConv_node_mixed_leaf_singleton_leaf_eq` in
`OpenMath/ButcherGroup/Section384.lean` (line ~3143) carries a live `sorry`.
The bSeries corollary, QuotEquiv lift, and G1 slice all compile because
they only invoke this lemma's signature, but the underlying convolution
identity is unproved.

## Context
Statement:
```
ButcherProduct.bConv (t₁.bSeries) t₂
    (BTree.node (List.replicate a BTree.leaf ++
                 List.replicate b (BTree.node [BTree.leaf])))
  = t₁.bSeries (BTree.node (...))
    + ∑ S_leaf ⊆ Fin a, ∑ S_sl ⊆ Fin b,
        (t₁.bSeries leaf)^|S_leaf| *
          (t₁.bSeries (node [leaf]))^|S_sl| *
          (∑ T ⊆ S_slᶜ,
             (t₁.bSeries leaf)^|T| *
             t₂.bSeries (node (
               replicate (a - |S_leaf| + |T|) leaf ++
               replicate (|S_slᶜ| - |T|) (node [leaf])))) := by
  sorry
```

Reference proofs (slices already landed):
- `ButcherProduct.bConv_node_replicate_leaf_eq` (cycle 542, b=0 slice)
- `ButcherProduct.bConv_node_replicate_singleton_leaf_eq` (cycle 547, a=0 slice)

The cycle 547 proof uses `ButcherProduct.bWeighted_convAt_node_kept_eq`
plus a length-cast `Equiv.finsetCongr` and per-S kept-side collapsing via
`bWeighted_kept_singleton_leaf_product_eq` and
`bSeries_node_replicate_leaf_append_replicate_singleton_leaf`.

Helper available (cycle 548): `convAt_node_mixed_leaf_singleton_leaf_at_i_eq`
gives the per-i closed form for the convAt factor.

## What was tried
- Aristotle submission for the headline: HTTP 429 throttled (queue full).
- Manual closure deferred to keep the cycle's G1 slice landable.

## Possible solutions
**Route A (reindex, mirror cycle 547):**
1. Write `bWeighted_convAt_node_mixed_leaf_singleton_leaf_eq_length`:
   apply `bWeighted_convAt_node_kept_eq` directly to the mixed children
   list. The resulting sum is over `S ⊆ Fin (a + b).length`.
2. Reindex `Finset (Fin (a+b))` ≃ `Finset (Fin a) × Finset (Fin b)` via
   `Finset.subset_disjUnion`-style decomposition or a custom Equiv on
   Finsets through the length-cast Equiv `Fin (a+b) ≃ Fin a ⊕ Fin b`.
3. Per-S, evaluate `∏ p ∈ S, coef (children.get p)` to
   `(coef leaf)^|S_leaf| * (coef (node [leaf]))^|S_sl|` by splitting S
   along the `Fin a / Fin b` decomposition.
4. The kept-side `∑ i, b_i * ∏ p ∈ Sᶜ, ...` requires per-position match:
   leaf positions contribute `row i`, singleton-leaf positions contribute
   `convAt(node [leaf]) j`. After splitting, this is
   `∑ i, b_i * (row i)^(a - |S_leaf|) * (convAt(node[leaf]))^(b - |S_sl|)`,
   then expand the singleton-leaf factor via `convAt_singleton_leaf_eq`
   and the inner `∑ T ⊆ S_slᶜ` powerset via `Finset.prod_add` (reverse)
   on `(coef leaf + row)^(b - |S_sl|)` (a generalization of cycle 547's
   `bWeighted_kept_singleton_leaf_product_eq`).
5. Collapse the kept-side
   `∑ i, b_i * (row i)^k * (chain i)^m` via
   `bSeries_node_replicate_leaf_append_replicate_singleton_leaf`.

**Route B (use the cycle 548 per-i helper):**
1. Start from `bConv = ∑ i, b_i * convAt`; rewrite via
   `convAt_node_mixed_leaf_singleton_leaf_at_i_eq` to get
   `∑ i, b_i * (coef leaf + row i)^a *
        (coef (node [leaf]) + coef leaf * row i + chain i)^b`.
2. Apply `Finset.prod_add` reverse three times to materialize the
   triple-powerset sum inside `∑ i`.
3. Use `Finset.sum_comm` to push `∑ i` inside the powerset sums, then
   collapse the kept-side `row^k * chain^m` factor into `t₂.bSeries`
   via `bSeries_node_replicate_leaf_append_replicate_singleton_leaf`.
4. Extract the "S_leaf = ∅, S_sl = ∅, T = ∅" term separately for the
   `t₁.bSeries (node mixed)` headline term, or check whether the all-
   zero-cut term in the powerset sum already reproduces the bSeries node
   mixed (the typical pattern is to leave it inside the sum since `^0`
   evaluates to `1`).

Route B may be more tractable because cycle 548 already has the per-i
helper proved; Route A would need extra `bWeighted_kept_*` lemmas
(generalized from cycle 547).

Estimated 150-300 lines either way. Try Aristotle first once the queue
clears.

## Why this matters
Cycle 548's deliverable, the G1 slice
`product_congr_node_mixed_leaf_singleton_leaf`, is fully proved but the
mathematical content of the headline `bConv` identity remains unverified.
Plan downstream cycles depend on the headline closed form.
