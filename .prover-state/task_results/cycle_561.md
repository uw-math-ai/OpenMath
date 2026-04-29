# Cycle 561 Results

## Worked on
§384 standalone four-child mixed `IsG1Equiv` slice for the
`(1-leaf, 3-singleton-leaf)` tree:

```lean
tQuadMixedOneThree =
  BTree.node
    [BTree.leaf, BTree.node [BTree.leaf], BTree.node [BTree.leaf],
      BTree.node [BTree.leaf]]
```

## Approach
Audited the ready Aristotle bundle
`ecfa6dfd-63ba-4d00-a057-68f70e660efc` first. It only targeted the already
landed cycle 559 `tQuadMixed` lemmas and included stub modules plus remaining
`sorry`s, so it was not transplanted.

Mirrored the cycle 560 `(2-leaf, 2-singleton-leaf)` implementation:

- Added `tQuadMixedOneThree`.
- Added the `Fin 2` pure-leaf choice count/coefficient helpers and the
  single-leaf polynomial expansion.
- Reused the cycle 559 singleton-leaf choice helpers for the three singleton
  children.
- Added `quadMixedOneThreeChoiceTree`.
- Proved the singleton cube expansion and full per-stage polynomial expansion.
- Proved the per-stage `convAt` closed form through
  `convAt_node_mixed_leaf_singleton_leaf_at_i_eq` with `a = 1`, `b = 3`.
- Proved the `b`-weighted collapse by swapping sums and closing all
  `Fin 2 × Fin 3 × Fin 3 × Fin 3` cells with case splits, `simp`,
  `Finset.mul_sum`, and `ring`.
- Added `bConv` and `bSeries` corollaries.
- Lifted the closed form to `QuotEquiv.bSeriesHom_product_node_quadMixedOneThree`.
- Added `IsG1Equiv.product_congr_node_quadMixedOneThree`, using
  `order_node_replicate_leaf_append_replicate_singleton_leaf` for the
  second-tableau cell order bounds.

## Result
SUCCESS. The cycle 561 one-three mixed slice is landed sorry-free.

Modified tracked files:

- `OpenMath/ButcherGroup/Section384SlicesQuadMixed.lean`
- `OpenMath/ButcherGroup.lean`

Verification:

- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup/Section384SlicesQuadMixed.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build`
- `rg -n '^\s*sorry\b|by\s+sorry\b|admit\b' OpenMath --glob '*.lean' || true`

The full build completed successfully. The tracked-code proof scan found no
live `sorry`/`admit` terms.

## Aristotle status
Submitted one small cycle 561 scaffold:

- Project: `14b9915a-6951-4a55-a2e5-fad8b1a74007`
- File:
  `.prover-state/aristotle_scaffolds/cycle_561/QuadMixedOneThreeCore.lean`
- Sorries: singleton cube expansion, full stage expansion, per-stage `convAt`,
  and weighted collapse.

After the required single 30-minute wait, `refresh_status` still reported
`QUEUED`. No result was available to incorporate, and no retry was made.

## Dead ends
The first umbrella proof attempt left the `Fin 2` leaf-choice index symbolic in
the per-cell order bound. `omega` could not infer the kept pure-leaf count from
the unmatched `quadMixedOneThreeLeafChoiceCount k`. Splitting on `k` alongside
the three singleton-choice indices made the bound concrete and closed all cells.

## Discovery
The cycle 560 weighted-collapse finisher scales directly to the one-three
shape once the coefficient nesting is kept consistent:

```lean
leafCoef * (choice h₁ * (choice h₂ * choice h₃)) * bSeries choiceTree
```

This associativity shape lets the `fin_cases ... <;> simp [...]` block reduce
each cell to a single finite-sum algebra goal, closed by either distributing a
constant through the sum or by direct `sum_congr` plus `ring`.

## Suggested next approach
Continue the standalone four-child mixed family with the remaining adjacent
leaf/singleton shapes if the planner wants more §384 `IsG1Equiv` coverage.
The same template should apply, with the per-cell order proof case-splitting
every finite choice index before calling `omega`.
