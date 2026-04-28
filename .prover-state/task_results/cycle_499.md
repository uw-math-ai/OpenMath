# Cycle 499 Results

## Worked on
Butcher §383 quotient-facing Butcher-series coefficient and the §382
composition blocker issue:

- `OpenMath/ButcherGroup.lean`
- `.prover-state/issues/butcher_section382_composition.md`
- `plan.md`

## Approach
Extracted the b-weighted elementary-weight sum invariance from the existing
`satisfiesTreeCondition_iff` proof as
`IsRKEquivalent.bSeries_eq`, then refactored
`satisfiesTreeCondition_iff` to reuse that helper. Added
`QuotEquiv.bSeries` by the same `Quotient.lift` pattern used for
`weightsSum` and `cSum`, plus the `_mk` computation lemma and
`satisfiesTreeCondition_iff_bSeries`.

Opened the requested issue file for the §382 raw-tableau composition
associativity blocker and rotated the §383 notes in `plan.md`.

Aristotle job results: none submitted. The cycle strategy explicitly said
not to submit Aristotle work for this small surface, and there were no
pending results from cycle 498.

## Result
SUCCESS. New declarations landed sorry-free:

- `ButcherTableau.IsRKEquivalent.bSeries_eq`
- `ButcherTableau.QuotEquiv.bSeries`
- `ButcherTableau.QuotEquiv.bSeries_mk`
- `ButcherTableau.QuotEquiv.satisfiesTreeCondition_iff_bSeries`

Verification:

- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.ButcherGroup`
- `rg -n "sorry" OpenMath/ButcherGroup.lean` found no matches.

## Dead ends
The first Lean check exposed a syntax/indentation problem in a copied
`Equiv.sum_comp` application. Parenthesizing the application fixed it, and
the existing recursive elementary-weight proof replayed cleanly.

No new attempt was made to define §382 composition, per the strategy.

## Discovery
The b-weighted elementary-weight sum is exactly the invariant value needed
for quotient-facing §383 packaging. The per-stage elementary-weight vector
still should not be lifted to `QuotEquiv`: it is only invariant up to the
witnessing permutation, while the b-weighted sum is genuinely invariant.

The §382 composition blocker is now documented in
`.prover-state/issues/butcher_section382_composition.md`, including the
cycle-495 nested weight-list mismatch and two plausible routes forward.

## Suggested next approach
Use `QuotEquiv.bSeries` as the representative-independent `BTree -> ℝ`
surface for §383. The homomorphism statement should wait until §382
composition is resolved, either by proving associativity modulo relabeling
on the summed stage type or by routing composition through the `G1`
B-series convolution algebra.
