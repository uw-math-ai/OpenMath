# Cycle 553 Results

## Worked on
Mixed leaf / double-leaf §384 product slice:
`BTree.node (List.replicate a BTree.leaf ++
List.replicate b (BTree.node [BTree.leaf, BTree.leaf]))`.

## Approach
Followed Step 2, not the Step 2-prime fallback.  I added the kept double-leaf
summand collapse, then expanded each kept double-leaf factor through a
`Fin 3` choice: both internal leaves cut, one internal leaf cut, or both
kept.  The resulting cut form is expressed only through `t1.bSeries`,
`t2.bSeries`, and the public choice helpers
`doubleLeafChoiceCoef` / `doubleLeafChoiceTree`.

Aristotle scaffolds were written under
`.prover-state/aristotle_scaffolds/cycle_553/`.  The first submission
returned HTTP 429 ("too many requests in progress"), matching the recent
cycle failure mode, so I did not retry or poll and closed the proofs
manually.

## Result
SUCCESS.

Landed:
- `bWeighted_kept_double_leaf_summand_eq`
- `ButcherProduct.bSeries_node_mixed_leaf_double_leaf_cut_eq`
- `QuotEquiv.bSeriesHom_product_node_mixed_leaf_double_leaf`
- `IsG1Equiv.product_congr_node_mixed_leaf_double_leaf`

Both modified Lean files compile with `lake env lean`, and there are no
live `sorry`s in `OpenMath/`.

## Dead ends
The first choice coefficient used count-power arithmetic.  It made the
`Fin 3` product expansion unnecessarily brittle, so I changed
`doubleLeafChoiceCoef` to the direct product over choices.  This kept the
cut form equivalent while making the G1 proof rewrite pointwise from the
leaf equality.

## Discovery
For this family the actual order arithmetic is
`1 + a + 3 * b`, since `BTree.node [BTree.leaf, BTree.leaf]` has order
3.  The generated choice tree has order bounded by the headline tree via
`c0 + c1 + c2 = n` and `c0 + 2*c1 + 3*c2 <= 3*n`.

## Suggested next approach
Continue with the next mixed §384 slice suggested in cycle 552: the
`(node [leaf], node [leaf, leaf])` mixed family.  Reuse the `Fin 3`
choice-tree pattern from this cycle for the double-leaf kept factors.
