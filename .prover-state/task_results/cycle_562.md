# Cycle 562 Results

## Worked on
Cycle 562 strategy headline: pivot from single-shape four-child §384 slices
(cycles 557, 559, 560, 561) to the **all-double-leaf parametric family**
`BTree.node (List.replicate n (BTree.node [BTree.leaf, BTree.leaf]))`.
Landed the four target theorems:

- `ButcherProduct.bSeries_node_replicate_double_leaf_eq` and
  `ButcherProduct.bConv_node_replicate_double_leaf_eq` in
  `OpenMath/ButcherGroup/Section384SlicesMixed.lean`.
- `QuotEquiv.bSeriesHom_product_node_replicate_double_leaf` and
  `IsG1Equiv.product_congr_node_replicate_double_leaf` in
  `OpenMath/ButcherGroup.lean`.

## Approach
The all-double-leaf family is the `a = 0` slice of the cycle 552/553
mixed leaf+double-leaf machinery already in
`Section384SlicesMixed.lean`. Rather than rebuild the per-stage `convAt`
expansion from scratch, the new `bSeries_node_replicate_double_leaf_eq`
derives the closed form by specializing
`ButcherProduct.bSeries_node_mixed_leaf_double_leaf_cut_eq t₁ t₂ 0 n`,
collapsing the outer `S_leaf ∈ (Finset.univ : Finset (Fin 0)).powerset`
sum (a singleton `{∅}`) and simplifying `S_leaf.card = 0`,
`(t₁.bSeries leaf)^0 = 1`, `0 - 0 = 0`. The `bConv` form follows directly
via `bSeries_eq_bConv`.

The quotient lift uses the standard `Quotient.inductionOn₂` pattern with
`simpa [bSeriesHom, bSeries, product, ButcherTableau.bSeries]`,
mirroring `bSeriesHom_product_node_replicate_singleton_leaf` (cycle 547)
and `bSeriesHom_product_node_mixed_leaf_double_leaf` (cycle 553).

The `IsG1Equiv` slice uses the `order_node_replicate_double_leaf` order
identity (`1 + 3 * n`) plus the existing
`order_doubleLeafChoiceTree_le` machinery to discharge the per-tree
agreement hypotheses for `q.bSeriesHom` and `r.bSeriesHom`. The kept
double-leaf factor `q.bSeriesHom (node [leaf, leaf])` only matters when
`S.card > 0`, in which case `n > 0` and the order bound `1 + 3 * n ≤ p`
gives `3 ≤ p`.

## Result
SUCCESS — all four targets compile sorry-free.

`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build` completes
all 8078 jobs without errors. `rg '^\s*sorry\b|by\s+sorry\b|admit\b'`
returns no matches under `OpenMath`.

## Dead ends
None this cycle: the `a = 0` specialization route worked on the first
try after the file-rebuild step refreshed the `.olean` cache so
`ButcherGroup.lean` could see the new lemma.

The first `lake env lean` attempt on `ButcherGroup.lean` failed with
`Unknown constant ButcherTableau.ButcherProduct.bSeries_node_replicate_double_leaf_eq`
because the importing module's `.olean` was stale; `lake build
OpenMath.ButcherGroup.Section384SlicesMixed` cleared this immediately.

## Discovery
The cycle 552/553 mixed leaf+double-leaf machinery already subsumes the
all-double-leaf family at `a = 0`. The same observation applies symmetrically
to the singleton-leaf-only family at `a = 0` of the mixed
leaf+singleton-leaf machinery (cycle 549), but cycle 547 was landed first
as a from-scratch derivation; the `a = 0` shortcut is purely cosmetic
in that direction since both proofs already exist.

For future parametric extensions, **first check whether the target is a
boundary slice of an already-landed mixed family** before re-deriving
from scratch — the powerset+choice cleanup is one `simp` away.

## Suggested next approach
Cycle 563: retry the parametric **all-triple-leaf** family
`BTree.node (List.replicate n (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))`.
Cycle 558 was REVERTED (left a sorry) but the cycle 562 pattern now
confirms the parametric route works. The all-triple-leaf family does
**not** have a directly subsuming mixed family (the cycle 558 attempt
needed a fresh `tripleLeafChoiceCount` over `Fin 4`), so the proof does
need a from-scratch per-stage `convAt` closed form. The single-tree
`bConv_node_triple_leaf_eq` from cycle 561 (and the
`tripleLeafChoiceCount` / `triple_leaf_stage_polynomial_expand` helpers
already at the bottom of `Section384SlicesMixed.lean` lines 2555–2695)
are the starting infrastructure.

If cycle 563 also lands cleanly, cycle 564 should pivot to the
**mixed leaf + triple-leaf** parametric family
`replicate a leaf ++ replicate b (node [leaf, leaf, leaf])` to match the
cycle 552/553 / cycle 562 pattern.
