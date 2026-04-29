# Cycle 563 Results

## Worked on
Parametric all-triple-leaf Section 384 slice for
`BTree.node (List.replicate n (BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))`.

## Approach
Added the all-triple-leaf closed form in
`OpenMath/ButcherGroup/Section384SlicesMixed.lean` by building a direct
per-stage `convAt` expansion. The kept triple-leaf child is grouped by a
`Fin 4` cut-count choice, with residual second-tableau trees grouped as leaf,
singleton-leaf, double-leaf, and triple-leaf children.

Submitted five Aristotle scaffold jobs under
`.prover-state/aristotle_scaffolds/cycle_563/`:

- `2be1ae95-3250-4c1c-b0d2-fa6a7d866ff5` (`PerStage.lean`)
- `e3c31c62-8843-4d0e-bf96-34b5f9c812c7` (`BConvTriple.lean`)
- `c3dd87bd-edcb-4411-bb49-1a10acdd43d1` (`BSeriesTriple.lean`)
- `7609a42a-7684-4222-8dde-e40f61e6042b` (`QuotLiftTriple.lean`)
- `8c6ba006-df5d-4524-b269-7bf78bfda4f6` (`G1Triple.lean`)

After the required 30-minute sleep, all five jobs were still `QUEUED`, so no
Aristotle proof output was available to incorporate.

## Result
SUCCESS. Proved all four requested deliverables sorry-free:

- `ButcherProduct.bConv_node_replicate_triple_leaf_eq`
- `ButcherProduct.bSeries_node_replicate_triple_leaf_eq`
- `QuotEquiv.bSeriesHom_product_node_replicate_triple_leaf`
- `IsG1Equiv.product_congr_node_replicate_triple_leaf`

Verification completed:

- `lake env lean OpenMath/ButcherGroup/Section384SlicesMixed.lean`
- `lake env lean OpenMath/ButcherGroup.lean`
- `lake build`
- `lean_verify` on the four public deliverables, all with only standard
  `propext`, `Classical.choice`, and `Quot.sound` axioms and no warnings.

## Dead ends
Aristotle did not start any submitted job within the mandated wait window, so
the cycle was closed manually.

## Discovery
The all-triple-leaf family needs a genuine four-way residual tree helper rather
than a specialization of the mixed leaf/double-leaf family. The useful canonical
residual tree groups a choice function by cut count:
leaf for three internal cuts, singleton-leaf for two cuts, double-leaf for one
cut, and triple-leaf for no internal cuts.

## Suggested next approach
The natural next slice is the mixed leaf + triple-leaf parametric family
`BTree.node (List.replicate a BTree.leaf ++ List.replicate b
(BTree.node [BTree.leaf, BTree.leaf, BTree.leaf]))`, reusing the new
`tripleLeafChoiceFunctionCoef` and `tripleLeafChoiceTree` infrastructure.
