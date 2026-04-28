# Cycle 523 Results

## Worked on

Butcher §384 closed right-block auxiliary infrastructure in
`OpenMath/ButcherGroup.lean`, immediately after the cycle 522 two-level
powerset expansion.

Added:
- `ButcherProduct.rightAuxAtCoef`
- `ButcherProduct.rightAuxAtCoef_leaf`
- `ButcherProduct.rightAuxAtCoef_node`
- `ButcherProduct.rightAuxAt_leaf_eq_coef`
- `ButcherProduct.rightAuxAt_node_eq_coef_one_level`

## Approach

1. Added the closed-form auxiliary `rightAuxAtCoef` as an honest structural
   recursion depending only on `t₂` and an arbitrary cut coefficient
   `coef : BTree → ℝ`.
2. Checked the sorry-first surface with two temporary sorries
   (`rightAuxAtCoef_node` and the optional one-level restatement). Lean
   accepted the recursive call through `children.get p` using the same
   `sizeOf` decrease argument as the existing `rightAuxAt` recursion.
3. Submitted the file once to Aristotle with instructions to fill the two
   remaining sorries. The service returned HTTP 429 immediately, so no retry
   was attempted per the cycle strategy.
4. Closed `rightAuxAtCoef_node` by unfolding `rightAuxAtCoef`.
5. Closed `rightAuxAt_leaf_eq_coef` by simp, and closed
   `rightAuxAt_node_eq_coef_one_level` by reusing
   `ButcherProduct.rightAuxAt_node_eq_powerset_sum` with simp converting the
   powerset-indexed sum.

## Result

SUCCESS — the planned A-C deliverables landed, and optional deliverable D
also landed, with no remaining `sorry`s in `OpenMath/ButcherGroup.lean`.

Verification:
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup.lean`
  succeeded.
- `grep -c sorry OpenMath/ButcherGroup.lean` returned `0`.
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.ButcherGroup`
  succeeded.

`plan.md` records the new declarations under §384 in the chapter ledger and
in the `## Current Target` body. §38 remains active.

## Dead ends

Aristotle was unavailable for this cycle due to an immediate HTTP 429:
"You have too many requests in progress." The manual proofs were direct, so
no additional proof-search dead ends were encountered.

## Discovery

The proposed `match`-style definition is accepted by Lean's termination
checker. For the recursive call at `children.get p`, the proof obligation is
closed by `List.get_mem`, `List.sizeOf_lt_of_mem`, and the strict size
increase from `children` to `BTree.node children`.

The existing `rightAuxAt_node_eq_powerset_sum` is strong enough to prove the
new one-level coefficient restatement by `simpa`; no extra reindexing lemma
is needed.

## Suggested next approach

Prove the full structural equivalence

```lean
ButcherProduct.rightAuxAt t₁ t₂ τ i =
  ButcherProduct.rightAuxAtCoef t₂ (t₁.bSeries) τ i
```

by induction on `τ`. The node step should rewrite both sides with
`rightAuxAt_node_eq_coef_one_level` and `rightAuxAtCoef_node`, then propagate
the induction hypothesis through the kept-child product and inner `Fin t`
sum.
