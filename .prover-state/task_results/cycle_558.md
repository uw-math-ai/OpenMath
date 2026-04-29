# Cycle 558 Results

## Worked on

§384 G₁ slice for the all-triple-leaf parametric family
`BTree.node (List.replicate n (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))`.
Mirrors cycle 547's all-singleton-leaf parametric structure but with a
`Fin 4` per-kept-child cut/keep choice over the three internal leaves of
each kept triple-leaf root child.

## Approach

1. **File hygiene**. Created `OpenMath/ButcherGroup/Section384SlicesTripleLeaf.lean`
   to host the cycle-557 standalone triple-leaf declarations together with the
   new cycle-558 parametric family. Removed `private` from
   `convAt_node_mixed_leaf_singleton_leaf_at_i_eq` in
   `Section384SlicesMixed.lean` so the cross-module triple-leaf depends on it
   work. This split keeps `Section384SlicesMixed.lean` under the 3000-line
   informal cap.

2. **New definitions** in `Section384SlicesTripleLeaf.lean`:
   - `tripleLeafChoiceFiber {n} (χ : Fin n → Fin 4) (k : Fin 4) : ℕ`:
     count of kept root children with cut-count `k`.
   - `tripleLeafChoiceTree {n} (χ : Fin n → Fin 4) : BTree`: aggregate
     second-tableau tree formed by the 4 fibers, with positions
     `node [leaf, leaf, leaf]`, `node [leaf, leaf]`, `node [leaf]`, `leaf`.
   - `tripleLeafChoiceProductCoef {n} (X : ℝ) (χ : Fin n → Fin 4) : ℝ`:
     product of per-kept-child scalar coefficients
     `tripleLeafChoiceCoef (χ p) X 1` over `p : Fin n`.

3. **New theorems**:
   - `ButcherProduct.bConv_node_replicate_triple_leaf_eq` (sorry — Aristotle
     submission `61b2eb7c-0cca-4df3-9dd0-6f8338b39754`).
   - `ButcherProduct.bSeries_node_replicate_triple_leaf_eq` (proved by
     `bSeries_eq_bConv` then `bConv_...`).
   - `bSeriesHom_product_node_replicate_triple_leaf` (umbrella, in
     `OpenMath/ButcherGroup.lean`, depends on `bSeries_...`).
   - `product_congr_node_replicate_triple_leaf` (cycle 558 G₁ slice with
     order bound `1 + 4 * n ≤ p`, in `OpenMath/ButcherGroup.lean`).

4. **Order helpers** in `OpenMath/ButcherGroup.lean`:
   - `order_node_replicate_triple_leaf n : (...).order = 1 + 4 * n`.
   - `foldr_order_append`, `foldr_order_replicate_{leaf, singleton_leaf,
     double_leaf, triple_leaf}` (modular factorisation of the
     order-of-foldr formula across appended replicate segments).
   - `order_node_replicate_triple_double_singleton_leaf f0 f1 f2 f3 : (...).order
     = 1 + 4*f0 + 3*f1 + 2*f2 + f3` (4-segment aggregate order).
   - `tripleLeafChoiceFiber_sum`: `f0 + f1 + f2 + f3 = n`.
   - `order_tripleLeafChoiceTree`: pointwise formula.
   - `order_tripleLeafChoiceTree_le`: bound by `1 + 4 * n ≤ p`.

5. **Aristotle batch (size 1)**. Submitted the project root with the directive
   to fill `bConv_node_replicate_triple_leaf_eq`. Provided pointers to the
   parallel singleton-leaf template and the new helpers.

## Result

- **G₁ slice landed (depends on inner sorry)**. The cycle-558 deliverable
  `product_congr_node_replicate_triple_leaf` is fully proved modulo
  `bConv_node_replicate_triple_leaf_eq`. Order accounting and powerset/χ
  congruence machinery are in place.
- **Inner bConv sorry remains**. The mathematical decomposition is fully
  specified: per-kept factor at stage `i` equals
  `∑_k tripleLeafChoiceCoef k X 1 * el-wt(node [τ_k]) i` where
  `τ_0 = node [leaf, leaf, leaf]`, `τ_1 = node [leaf, leaf]`,
  `τ_2 = node [leaf]`, `τ_3 = leaf`. The proof should follow the cycle-547
  singleton-leaf template with an auxiliary
  `bWeighted_convAt_node_replicate_triple_leaf_eq` lemma.
- **Aristotle in queue**. As of last check, project status was QUEUED.
  Strategy says skip retry on HTTP 429.
- Build verified: `lake build OpenMath.ButcherGroup` is green (one expected
  sorry warning).

## Dead ends

- Initial attempt at `order_node_replicate_triple_double_singleton_leaf`
  used a quadruple-nested induction with `simp + omega`; failed because
  `simp` left non-numeric `List.foldr` heads in the goals. Refactored to
  use `BTree.order_node`, modular `foldr_order_append`, and the four
  per-shape `foldr_order_replicate_*` helpers — clean.

## Discovery

- The 4-segment order helper benefits from a generic `foldr_order_append`
  splitter rather than direct nested induction. This pattern should
  generalise to any future N-shape mixed root family.
- `BTree.leaf` and `BTree.node []` both have `el-wt = 1`, so τ_3 (the
  all-leaves-cut kept-child contribution) can be either; we picked
  `BTree.leaf` to match the cycle 547 / 553 convention.

## Suggested next approach

- **Land the inner bConv proof.** Adapt the cycle-547 helper chain
  (`bWeighted_convAt_node_replicate_singleton_leaf_eq_length` →
  `bWeighted_convAt_node_replicate_singleton_leaf_eq` → `bConv_..._eq`)
  to triple-leaf. Key auxiliary: a `Fin n → Fin 4` analogue of
  `bWeighted_kept_singleton_leaf_product_eq` that expands the kept-side
  product `(c_0 f_0(i) + c_1 f_1(i) + c_2 f_2(i) + c_3 f_3(i))^|Sᶜ|` via
  `Finset.prod_univ_sum` / multinomial.
- **Mixed slices.** Once the all-triple-leaf parametric family is closed,
  follow up with mixed `replicate a leaf ++ replicate b (node [leaf]) ++
  replicate c (node [leaf, leaf]) ++ replicate d (node [leaf, leaf, leaf])`
  closures. The current §384 G₁ machinery is now ready for a fully mixed
  Butcher-degree-4 parametric closure.
