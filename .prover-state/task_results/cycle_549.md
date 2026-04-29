# Cycle 549 Results

## Worked on
§384 mixed leaf / singleton-leaf root-children chain:

- `ButcherProduct.convAt_node_mixed_leaf_singleton_leaf_at_i_eq`
- `ButcherProduct.bConv_node_mixed_leaf_singleton_leaf_eq`
- `ButcherProduct.bSeries_node_mixed_leaf_singleton_leaf_eq`
- `QuotEquiv.bSeriesHom_product_node_mixed_leaf_singleton_leaf`
- `IsG1Equiv.product_congr_node_mixed_leaf_singleton_leaf`

The mixed family is
`BTree.node (List.replicate a BTree.leaf ++ List.replicate b (BTree.node [BTree.leaf]))`
with order `1 + a + 2 * b`.

## Approach
Re-landed the clean cycle 548 per-stage helper, then closed the headline
manually through a per-stage polynomial expansion rather than a direct
cut-set reindexing.

Aristotle-first batch was attempted with five scaffold files under
`.prover-state/aristotle_scaffolds/cycle_549/`:

1. `bConv_node_mixed.lean`
2. `bSeries_node_mixed.lean`
3. `quot_product_node_mixed.lean`
4. `cut_set_bijection.lean`
5. `sum_filter_reindex.lean`

All five submissions returned HTTP 429 (`too many requests in progress`), so
there were no Aristotle project IDs to poll or incorporate. Per strategy, I
did not retry and proceeded manually.

Manual proof structure:

- Recovered the cycle 548 per-`i` `convAt` helper.
- Added private finite-product algebra helpers:
  `prod_const_add_eq_powerset`, `pow_add_eq_powerset`,
  `mixed_stage_polynomial_expand`, and `weighted_mixed_stage_sum_expand`.
- Proved `bWeighted_convAt_node_mixed_leaf_singleton_leaf_eq` by expanding
  `(coef leaf + row)^a * (coef singleton + coef leaf * row + chain)^b`,
  commuting the stage sum inward, and collapsing the remaining
  `row^m * chain^n` weighted sum via the existing
  `bSeries_node_replicate_leaf_append_replicate_singleton_leaf`.
- Closed `bConv`, `bSeries`, quotient lift, and the `G1` slice from that
  weighted theorem.

## Result
SUCCESS.

Landed 586 tracked Lean lines total:

- `OpenMath/ButcherGroup/Section384.lean`: +458 lines, now 3408 lines.
- `OpenMath/ButcherGroup.lean`: +128 lines, now 1730 lines.

No live `sorry` or `admit` remains in either touched Lean file.

Verification succeeded:

```bash
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup/Section384.lean
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup.lean
```

## Dead ends
Aristotle remained unavailable with HTTP 429 for all five submissions, matching
the recent-cycle throttling pattern.

The direct root cut-set bijection route was not needed. The per-stage
polynomial route avoided constructing an explicit
`Finset (Fin (a + b)) ≃ Finset (Fin a) × Finset (Fin b)` reindexing theorem.

## Discovery
The mixed headline can be closed cleanly by treating the per-`i` helper as a
polynomial identity:

```lean
(X + R)^a * (Y + (X * R + C))^b
```

The first powerset chooses root leaf cuts, the second chooses root
singleton-leaf cuts, and the inner powerset chooses internal leaf cuts among
kept singleton-leaf children. After the three expansions, the remaining
weighted stage sum is exactly the existing mixed-node `bSeries` helper.

## Suggested next approach
Continue the §384 parametric ladder from this closed mixed slice. The next
planner can either extend the same polynomial-expansion method to nearby
two-level root families or return to the unblocked §387 power arithmetic
items if no immediate §384 family is scheduled.
