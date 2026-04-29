# Cycle 568 Results

## Worked on

Closing the cycle 567 all-leaves bridge for `bSeriesConv` in
`OpenMath/ButcherGroup/Section386Conv.lean`. The cycle 567 singleton-leaf
consistency check is now extended to the parametric family
`BTree.node (List.replicate n BTree.leaf)` for arbitrary `n`.

Two helpers landed plus the headline theorem:

1. `cutSum_filterMap_eq_map` — the cut sum's filterMap shape collapses to a
   plain `List.map` because the kept option is always `some`.
2. `innerCutForest_leaf_cons` — concrete cons unfolding of
   `BTree.innerCutForest` on a leaf prefix.
3. `sum_finset_fin_succ_card_eq` — Pascal-style cardinality split of a
   `Finset (Fin (n+1))` sum into `Finset (Fin n)` kept-head and cut-head pieces.
4. `innerCutForest_replicate_leaf_sum` — the list enumeration of inner cuts of
   `BTree.node (List.replicate n BTree.leaf)` reindexes to the `Finset (Fin n)`
   powerset sum from cycle 542.
5. `bSeriesConv_node_replicate_leaf_consistency` — headline parametric
   consistency identity for `bSeriesConv`.

## Approach

Sorry-first scaffolds for the four sub-lemmas were written under
`.prover-state/aristotle_scaffolds/cycle_568/`. Aristotle submission hit 429
rate limits and was not retried (per project rules), so all closures are
manual.

For `innerCutForest_replicate_leaf_sum`:

- Convert the LHS filterMap to `List.map` via `cutSum_filterMap_eq_map`.
- Induct on `n` generalizing `β`. Base case is direct after unfolding
  `BTree.innerCutForest` on the empty list.
- In the successor case, use `innerCutForest_leaf_cons` to split the forest
  into kept-head and cut-head parts. The kept branch is re-expressed via
  `β_kept := xs ↦ β(node (leaf :: xs))` and re-folded back to the original
  filterMap shape so the inductive hypothesis applies. The cut branch factors
  out a uniform `α leaf` factor by direct induction on the forest list, and
  IH is then applied with `β` itself.
- The right-hand `Finset (Fin (n+1))` sum is split via
  `sum_finset_fin_succ_card_eq` into a `S.card` piece and a `S.card + 1`
  piece, which match the kept and cut branches respectively.

For `sum_finset_fin_succ_card_eq`:

- Convert each `Finset (Fin m)`-sum to a `range (m+1)` sum weighted by
  binomial coefficients via `Finset.sum_powerset_apply_card`.
- Reindex the LHS by peeling off `k = 0` with `sum_range_succ'` and matching
  the kept-head piece by peeling off `k = n` with `sum_range_succ`.
- Apply Pascal's identity (`Nat.choose_succ_succ'`) inside the residual sum
  and close with `Finset.sum_add_distrib` plus `abel`.

For the headline `bSeriesConv_node_replicate_leaf_consistency`:

- Rewrite the RHS via `ButcherProduct.bSeries_node_replicate_leaf_eq`.
- Unfold `bSeriesConv`, expand the outer `BTree.innerCut` via `innerCut_node`,
  drop the leading prune-the-root cut by `simp` filtering `Option.map_none`,
  and apply `innerCutForest_replicate_leaf_sum` to identify the remaining
  list-sum with the powerset closed form. Finish with `add_comm` plus `rfl`
  (the `Finset.univ` and `(Finset.univ).powerset` views of the index set are
  defeq for sums).

## Result

SUCCESS. Both the targeted file `OpenMath/ButcherGroup/Section386Conv.lean`
and the umbrella `OpenMath/ButcherGroup.lean` build clean (no errors, no
remaining `sorry` in the new code).

## Dead ends

- Initial `List.filterMap_eq_map_of_isSome` attempt for the cut-branch
  rewrite: this lemma name does not exist in this Mathlib snapshot (the
  scaffolding had a `sorry`). Switched to first converting the whole
  filterMap to a `List.map` via `List.filterMap_eq_map_iff_forall_eq_some`,
  then doing pointwise simplification.
- `ring` for the Pascal split closing step: failed because the underlying
  monoid has no multiplication. Replaced with `abel` (additive commutative
  monoid only).
- `Finset.sum_range_succ'` produces `1 + x` form; needed `add_comm` after
  `Nat.choose_succ_succ', add_smul` to align with `(x + 1)` shape.
- `(default : Finset (Fin 0))` did not reduce via `simp` alone; rewrote to
  `∅` explicitly so `α^0 = 1` simplifies cleanly.

## Discovery

- The natural framing for cut sums on leaf-only forests is `List.map` rather
  than `List.filterMap`: every cut keeps the trunk `some`, so the option
  layer is just bookkeeping. Future cycles working on more general tree
  shapes (mixed leaf/internal children, bigger forest types) should expect
  to need the dual lemma where some cuts genuinely return `none`.
- A Pascal-style split lemma over `Finset (Fin (n+1)).card` is broadly
  reusable: it should generalize to any sum-by-cardinality identity. If
  another cycle needs the same shape on `Finset.powerset` directly, this
  lemma can be lifted into a public infrastructure helper.

## Suggested next approach

The headline `bSeriesConv_node_replicate_leaf_consistency` is now the all-
leaves analogue of cycle 567's singleton-leaf check. The strategy should
plan the next bridge step (e.g., the dual all-empty-node family, or a
mixed-leaf parametric family) using the same template:

1. Land a list-level reindexing helper for the new family.
2. Apply it with `ButcherProduct.bSeries_*_eq` from `Section384Slices.lean`.
3. Sanity-check via the existing `bSeriesConv_node_singleton_leaf_consistency`
   shape.

`sum_finset_fin_succ_card_eq` and `cutSum_filterMap_eq_map` are reusable for
those follow-ups and may want promotion out of the `private` namespace if
called from elsewhere.
