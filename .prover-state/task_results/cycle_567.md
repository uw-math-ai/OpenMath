# Cycle 567 Results

## Worked on

Butcher §386 coefficient-only admissible-cut convolution for b-series.

## Approach

Defined a structural cut enumeration in
`OpenMath/ButcherGroup/Section386Conv.lean`:

- `BTree.innerCut τ α : List (Option BTree × ℝ)` enumerates root-kept
  trunks and root-pruned cuts.
- `BTree.innerCutForest children α` is the list-level cartesian product
  of one cut choice per child.
- `bSeriesConv α β τ` filters root-kept cuts and sums
  `weight * β trunk`.

The recursion is direct mutual recursion over `BTree` and `List BTree`,
not a separate generic cartesian-product helper.

## Result

SUCCESS for the structural cycle-567 baseline.

Landed sorry-free:

- `innerCut_leaf`
- `innerCut_node_nil`
- `innerCut_node`
- `innerCut_node_singleton_leaf`
- `bSeriesConv_leaf`
- `bSeriesConv_node_nil`
- `bSeriesConv_node_singleton_leaf`
- `bSeriesConv_singleton_leaf_consistency`

The cycle 540 consistency check closes against
`ButcherProduct.bSeries_singleton_leaf_eq` after rewriting
`t₂.bSeries (BTree.node [])` by `bSeries_node_nil`.

Added `import OpenMath.ButcherGroup.Section386Conv` to the umbrella
`OpenMath/ButcherGroup.lean`.

## Aristotle

Submitted the planned batch early after the sorry-first scaffold compiled:

- `1f7eb94c-f55d-487d-95f5-ded82c084717`
  (`bSeriesConv_node_singleton_leaf`) — still `QUEUED` after the single
  30-minute wait.
- `7ccc1e06-6360-40a0-8929-bcc9967c54a2`
  (`bSeriesConv_singleton_leaf_consistency`) — still `QUEUED`.
- `e44cd870-c4fa-4bb0-8c68-e2772ae447d8`
  (`bSeriesConv_node_replicate_leaf_consistency`) — still `QUEUED`.
- `bd8dcc16-d32f-4897-8f30-4b0f49c1396b`
  (headline scaffold under `.prover-state/aristotle_scaffolds/cycle_567/`)
  — still `QUEUED`.
- Fifth requested node-unfolding submission returned HTTP 429
  ("too many requests in progress"); per instructions, no retry was made.

No Aristotle proof was transplanted.

## Dead ends

The parametric all-leaves consistency check did not land. After rewriting
by `ButcherProduct.bSeries_node_replicate_leaf_eq`, the remaining goal is
a pure reindexing lemma equating the `innerCutForest` list enumeration of
`n` independent leaf choices with the existing `Finset (Fin n)` powerset
sum. Direct induction and `grind` did not close this bridge.

Recorded the obstruction in
`.prover-state/issues/cycle_567_bseriesConv_all_leaves_bridge.md`.

## Discovery

The landed definition has the right singleton behavior without any
tableau-dependent shortcut:

```lean
bSeriesConv α β (BTree.node [BTree.leaf])
  = β (BTree.node [BTree.leaf]) + α BTree.leaf * β (BTree.node [])
```

This exactly matches cycle 540's product closed form after the outer
`t₁.bSeries` summand is added.

For cycle 568, the headline target still looks structurally tractable, but
it needs a reusable list-to-cut-index bridge. The all-leaves bridge is the
smallest useful version of that infrastructure.

## Suggested next approach

Before attempting the unrestricted headline equality, prove the
`innerCutForest (List.replicate n BTree.leaf)` powerset reindexing lemma.
The likely invariant should include a prefix count `m`, so the successor
case splits into a kept-head branch and a cut-head branch cleanly.
