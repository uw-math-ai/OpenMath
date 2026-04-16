# Issue: Spectral bound proof still exceeds heartbeat budget

## Blocker
`OpenMath/SpectralBound.lean` compiles, but two Aristotle-generated proofs still
require elevated heartbeat caps:
- `pow_apply_eq_sum_of_genEigenspace` needs `800000`
- `uniformly_bounded_iterates_of_spectral_bound` needs `1600000`

Lowering both to `200000` produces deterministic timeouts.

## Context
Observed failures when recompiling with `set_option maxHeartbeats 200000`:
- `OpenMath/SpectralBound.lean:93:4`: timeout in `simp` during the induction
  step of `pow_apply_eq_sum_of_genEigenspace`
- `OpenMath/SpectralBound.lean:221:94`: timeout at `whnf` while elaborating the
  large `h_bound_basis` proof
- `OpenMath/SpectralBound.lean:258:49`: timeout in tactic execution while
  selecting bounds from `h_bound_basis`

The file otherwise typechecks and `DahlquistEquivalence.lean` successfully uses
the imported theorem.

## What was tried
Copied in the Aristotle proof, verified it compiles as imported by
`DahlquistEquivalence.lean`, then reduced the two heartbeat caps to `200000` and
reran `lake env lean OpenMath/SpectralBound.lean`.

## Possible solutions
Extract the induction-step algebra in
`pow_apply_eq_sum_of_genEigenspace` into explicit helper lemmas for:
- applying `T` to the finite sum
- reindexing the shifted sum
- the Pascal recombination identity

Extract the large proof inside
`uniformly_bounded_iterates_of_spectral_bound` into smaller lemmas for:
- bounding iterates on one generalized-eigenspace component
- combining finitely many component bounds for one basis vector
- turning basis-vector bounds into a global operator bound without the current
  heavy `choose` block
