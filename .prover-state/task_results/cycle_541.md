# Cycle 541 Results

## Worked on

Section 38 / 384 small-order product congruence infrastructure:

- Step 1 landed: `BTree.order_le_two_iff`.
- Step 2 landed: `ButcherTableau.bSeries_node_nil` and
  `ButcherTableau.bSeries_node_node_nil` (plus the supporting
  `ButcherTableau.bSeries_leaf` helper).
- Step 3 landed: `ButcherProduct.bSeries_node_nil_eq`,
  `ButcherProduct.bSeries_node_node_nil_eq`,
  `QuotEquiv.bSeriesHom_product_node_nil`, and
  `QuotEquiv.bSeriesHom_product_node_node_nil`.
- Step 4 landed: `IsG1Equiv.product_congr_le_two`.

## Approach

Started sorry-first by adding the theorem skeletons to the three sanctioned
Lean files and checking that the intended names and signatures compiled.
Then closed each proof manually, following the planner's explicit Aristotle
exception for this cycle.

For `BTree.order_le_two_iff`, added two local list helpers: one forcing an
order-sum-zero child list to be empty, and one forcing an order-sum-at-most-one
child list to be either empty or a singleton child of order one. The theorem
then case-splits a tree into `leaf` or `node children`, uses
`BTree.order_node_sum`, and reduces the singleton child of order one to
`leaf` or `node []`.

For the bSeries lemmas, used direct unfold/simp proofs at the representative
level, then reused the cycle 540 singleton-leaf closed form to get the
`node [node []]` product formula. The quotient lifts are
`Quotient.inductionOn2 + simpa`.

For `IsG1Equiv.product_congr_le_two`, used `BTree.order_le_two_iff` to split
the target tree into the four order-at-most-two cases. Each case rewrites the
product coefficient through the appropriate closed form, applies `hq` and
`hr` to the exposed subtrees, and closes by rewriting.

## Result

SUCCESS. All four planned steps landed with no live `sorry`s.

Verification run:

- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/RootedTree.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup/Section384.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.ButcherGroup`
- `rg -n "sorry" OpenMath/ButcherGroup.lean OpenMath/ButcherGroup/Section384.lean OpenMath/RootedTree.lean`

The build completed successfully. Lake replayed existing warnings from
`OpenMath/OrderConditions.lean`; the touched files checked cleanly.

## Dead ends

No proof dead ends. The only workflow wrinkle was that `lake env lean
OpenMath/ButcherGroup.lean` initially could not see newly added imported
constants until `OpenMath.RootedTree` and `OpenMath.ButcherGroup.Section384`
were rebuilt as Lake modules.

## Discovery

This is the first concrete `G1.mul`-direction well-definedness deliverable in
tracked code: `IsG1Equiv.product_congr_le_two` proves that product respects
`G1` equivalence through order two. The proof is small only because the order
two tree space is now explicitly enumerated and the extra `node []` /
`node [node []]` product coefficients collapse to the same bSeries-only
surface as the cycle 540 `node [leaf]` closed form.

Aristotle outcome: no jobs were submitted. The cycle 541 strategy explicitly
overrode the standing Aristotle-first workflow because this seam has returned
HTTP 429 / QUEUED for many recent cycles and the planned proof steps were
shorter than a 30-minute wait.

## Suggested next approach

Do not extend the finite enumeration to order three. The unrestricted
`IsG1Equiv.product_congr` still needs the full Section 384 `(trunk, cuts)`
convolution closure for arbitrary trees. The next useful work should package
that recursive bSeries-only convolution rather than adding larger
small-order case splits.
