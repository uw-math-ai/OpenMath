# Cycle 544 Results

## Worked on

§38 / §384 — third tracked `G1.mul`-direction well-definedness
deliverable. Followed the cycle 544 strategy directly: land the dual
all-empty-node parametric closed form mirroring cycle 542's all-leaves
family.

- Helper landed: `ButcherProduct.convAt_node_nil`
  (`@[simp]`) in `OpenMath/ButcherGroup/Section384.lean`.
- Headline landed: `ButcherProduct.bConv_node_replicate_node_nil_eq`
  in the same file.
- Corollary landed: `ButcherProduct.bSeries_node_replicate_node_nil_eq`.
- Auxiliary tracked lemma:
  `ButcherProduct.bWeighted_convAt_node_all_node_nil_eq` (parallel of
  cycle 538's `bWeighted_convAt_node_all_leaves_eq`).
- Two private helpers: `rightAuxAtCoef_node_nil`,
  `elementaryWeight_node_replicate_node_nil`.
- Quotient lift: `QuotEquiv.bSeriesHom_product_node_replicate_node_nil`
  in `OpenMath/ButcherGroup.lean`.
- G1 slice: `IsG1Equiv.product_congr_node_replicate_node_nil` in same.
- Private order helper: `order_node_replicate_node_nil`.

## Approach

### Helper: `convAt_node_nil`

Naive `simp` after `convAt_node` left a residual goal involving
`default : Finset (Fin 0)` (Fintype `default`). Closed by rewriting
`Finset.univ : Finset (Finset (Fin ([] : List BTree).length))` to
`{∅}` via definitional equality, then `simp`.

### Auxiliary: `bWeighted_convAt_node_all_node_nil_eq`

Cycle 538's all-leaves lemma uses the leaf-specific
`bWeighted_rightAuxAtCoef_node_trunk_kept_leaf_eq`. There is no
existing all-`node []` analogue at the rightAuxAtCoef level, so
instead I went via the more general
`bWeighted_rightAuxAtCoef_node_trunk_recursion`, then collapsed each
`(∑ j, A i j * rightAuxAtCoef t₂ coef (children.get p) j)` to
`∑ j, A i j` using the new private `rightAuxAtCoef_node_nil`. This
bridges the cycle 538 and cycle 542 ladders to the dual `node []`
shape without needing a tracked
`bWeighted_rightAuxAtCoef_node_trunk_kept_node_nil_eq` analogue.

### Headline: `bConv_node_replicate_node_nil_eq`

Direct mirror of cycle 542's `bConv_node_replicate_leaf_eq`: invoke
the new auxiliary `bWeighted_convAt_node_all_node_nil_eq`, then
transport the powerset sum across `Fin (replicate n (node [])).length
≃ Fin n` via `Equiv.finsetCongr` + `Finset.sum_equiv`. Same
construction as cycle 542 (manual `Equiv` + `Fin.cast`), since the
mathlib snapshot has no top-level `Fin.castIso`.

### bSeries corollary, quotient lift, G1 slice

All three are line-for-line mirrors of the cycle 542 chain. The
quotient lift is `Quotient.inductionOn₂ + simpa`. The G1 slice
mirrors `product_congr_node_replicate_leaf` — the head term closes
via `hq` and `order_node_replicate_node_nil`, and the powerset-sum
term closes pointwise via `hq` at `(BTree.node []).order = 1` and
`hr` at `(n - S.card) + 1 ≤ p`.

The order helper `order_node_replicate_node_nil` is a three-line
induction, exactly mirroring `order_node_replicate_leaf` from
cycle 542; the only delta is using `(BTree.node []).order = 1`
(closed by `simp`) instead of `BTree.order_leaf`.

## Result

SUCCESS — all deliverables landed with no live `sorry`.

Verification:
- `lake env lean OpenMath/ButcherGroup/Section384.lean` — clean.
- `lake env lean OpenMath/ButcherGroup.lean` — clean.
- `lake build OpenMath.ButcherGroup` — clean
  (`Build completed successfully (8031 jobs)`).
- `rg -n 'sorry' OpenMath/ButcherGroup OpenMath/ButcherGroup.lean`
  — empty output.

## Dead ends

- Initial `simp` after `convAt_node` did not collapse the empty
  powerset because the residual `Finset.univ : Finset (Finset (Fin 0))`
  was elaborated through the `Fintype` `default` chain rather than
  reducing to `{∅}`. Fixed by an explicit `rfl`-rewrite to `{∅}`.

## Discovery

- The `bWeighted_rightAuxAtCoef_node_trunk_recursion` general lemma
  is sufficient to derive both the all-leaves and all-`node []`
  closed forms without dedicated trunk-kept analogues — the kept-side
  factor collapses identically once `rightAuxAtCoef _ _ _ j = 1`
  holds at the relevant subtree. Future "all-trivial-children"
  family lemmas should be derivable from the same template.
- `(BTree.node []).order = 1` closes by `simp` (not `BTree.order_leaf`,
  which is for a different constructor). Worth noting for any future
  G1 slice on empty-node families.

## Aristotle outcome

Did not submit any jobs this cycle. Each deliverable is a
short-to-medium mirror of an existing cycle 542 proof, so an
Aristotle batch would have been wasted compute given the long-running
HTTP 429 / queue-saturation pattern reported in cycles 509, 511–515,
517, 519, 521, 523, 524, 529, 539. The cycle 544 strategy explicitly
allowed this fall-back ("close manually using the cycle 542 proof
template").

## Suggested next approach

Per the strategy's stretch deliverable: the natural next §384
milestone is the **mixed leaf-and-node-nil family**
`ButcherProduct.bSeries_node_mixed_trivial_eq` covering arbitrary
arrangements of `BTree.leaf` and `BTree.node []` children. The
generalization should lift `bWeighted_convAt_node_all_leaves_eq` and
the new `bWeighted_convAt_node_all_node_nil_eq` to a single
"all-trivial-children" lemma (predicate: `convAt _ _ c j = 1` for
every child `c` and stage `j`). Both `BTree.leaf` and `BTree.node []`
satisfy this; the resulting closed form would cover an infinite
family at every order ≥ 1.

If the lift requires a new `IsConvAtUnit` predicate, sketch in
`.prover-state/scratch/cycle_545_stretch.lean` first per the strategy.
