# Cycle 521 Results

## Worked on

Butcher §384 right-block powerset decomposition in
`OpenMath/ButcherGroup.lean`, immediately after the cycle 520
`ButcherProduct.elementaryWeight_natAdd` block.

Added:
- `ButcherProduct.rightAuxAt_node_eq_powerset_sum`
- `ButcherProduct.bSeries_natAdd_node_eq_powerset_sum`

## Approach

1. Followed the cycle 521 strategy and matched the existing cycle 518/519
   powerset style around `foldr_mul_add_eq_powerset_sum` and
   `ButcherProduct.elementaryWeight_natAdd_node_eq_powerset_sum_bSeries`.
2. Added both requested theorem statements with `sorry` first and verified
   `OpenMath/ButcherGroup.lean` compiled with only the expected two
   `sorry` warnings.
3. Created the single requested Aristotle scaffold at
   `.prover-state/aristotle_scaffolds/cycle_521/rightauxat_powerset.lean`
   for the first lemma and submitted it once.
4. Aristotle returned HTTP 429 immediately ("too many requests in
   progress"). Per strategy, I did not retry and did not sleep.
5. Proved `rightAuxAt_node_eq_powerset_sum` manually by rewriting with
   `ButcherProduct.rightAuxAt_node`, applying the private
   `foldr_mul_add_eq_powerset_sum`, converting the powerset-restricted
   sum to a full `Finset` sum, and reindexing by complement so `S`
   denotes the kept children.
6. Proved `bSeries_natAdd_node_eq_powerset_sum` by rewriting each
   `rightAuxAt` stage with the new node lemma, distributing
   multiplication over the finite powerset sum, commuting the `Fin t`
   and kept-set sums, and factoring the cut product outside the
   `t₂.b`-weighted stage sum.

## Result

SUCCESS — both concrete deliverables landed with zero tracked `sorry`s.

Verification:
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup.lean`
  succeeded.
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.ButcherGroup`
  succeeded; it replayed `OpenMath.OrderConditions` with only pre-existing
  linter/info output.
- `grep -c sorry OpenMath/ButcherGroup.lean` returned `0`.

The §384 subsection of `plan.md` now records the two cycle 521 lemma names.

## Dead ends

No proof dead ends for the required deliverables. The optional stretch
lemma `ButcherProduct.rightAuxAt_castSubtree_kept` was not added because
there is no existing `castSubtree` naming pattern or precise local API
shape in the file; adding a weak rewrite lemma would have been less useful
than preserving a clean interface around the two planned powerset results.

## Discovery

The `rightAuxAt` node recursion is now in exactly the same kept-child
orientation as cycle 519's
`ButcherProduct.elementaryWeight_natAdd_node_eq_powerset_sum_bSeries`:
cut factors live over `Sᶜ`, while kept recursive factors live over `S`.

The weighted corollary confirms that the next convolution layer can work
set-by-set: for each kept set `S`, the cut-side product is independent of
the second-method stage and can be carried outside the
`∑ i : Fin t, t₂.b i * ...` coefficient sum.

## Suggested next approach

Define the honest `(trunk, cuts)` closed form for the right-block
contribution and prove it by structural recursion on `BTree`, using
`ButcherProduct.bSeries_natAdd_node_eq_powerset_sum` as the node step.
That should be the next prerequisite before returning to
`IsG1Equiv.product_congr`, `G1.mul`, or the group multiplication layer.
