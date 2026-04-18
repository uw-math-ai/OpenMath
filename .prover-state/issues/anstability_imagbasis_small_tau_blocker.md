# Issue: AN-stability imaginary-basis small-τ expansion blocker

## Blocker
The remaining sorry in `OpenMath/ANStability.lean` is
`norm_stabilityFn_imagBasis_gt_one`. The natural proof needs three pieces:

1. a finite-sum identity
   `vᵀ M v = 2 * Σᵢⱼ bᵢ vᵢ aᵢⱼ vⱼ - (Σᵢ bᵢ vᵢ)^2`
2. a continuity argument showing
   `det (I - A * diag(iτv)) ≠ 0` for sufficiently small positive `τ`
3. a small-`τ` expansion of `R(iτ diag(v))`

I attempted to formalize (1) and (2) as helper lemmas inside `ANStability.lean`,
but the finite-sum algebra became brittle under `ring_nf` / `Finset.sum_*`
rewrites, and I reverted the partial proof rather than leave the main file broken.

## Context
- Remaining sorry: `OpenMath/ANStability.lean:204`
- Current mathematical target:
  `|R(iτ diag(v))|² = 1 - τ² (vᵀ M v) + O(τ³)`
- Failed Lean pattern:
  nested `Finset.sum_congr` plus `ring_nf` changed monomial order enough that
  later rewrites with `hleft` / `hright` / `hsq` stopped matching
- Continuity sublemma looked feasible, but the algebra helper was not robust enough
  to keep in the file without more time

## What was tried
- Added local helper lemmas for the quadratic-form identity and determinant
  nonvanishing
- Tried to prove the quadratic-form identity by:
  - unfolding `algStabMatrix`
  - splitting the sum into three terms
  - swapping indices with `Finset.sum_comm`
  - factoring the rank-1 term as a square
  - normalizing with `ring`, `ring_nf`, `abel_nf`, and `nlinarith`
- Tried a continuity proof for the determinant using
  `Metric.continuousAt_iff` and continuity of `Matrix.diagonal` / `Matrix.det`

## Possible solutions
- Prove the algebraic helper in a standalone file first, where its normal form can
  be controlled more aggressively before porting it back into `ANStability.lean`
- Use a more explicit `calc` proof with separately named intermediate sums instead
  of relying on `rw` to match post-`ring_nf` expressions
- For the main theorem, try to avoid a full `O(τ³)` infrastructure by proving an
  exact algebraic identity for the first two Neumann terms and then bounding the
  remainder entrywise
- Harvest the new Aristotle jobs created in cycle 111:
  - `1be8d0a1-92d5-42c4-b1ae-6d766b88a48b` (`OpenMath/ANStability.lean`)
  - `b0bfbf1f-2b35-41d3-a4bc-ac5057557660` (`cycle_111_algStabMatrix_quadForm.lean`)
  - `1dfac67a-d980-41a0-8873-a395285eb451` (`cycle_111_imagBasis_det.lean`)
  - `ebff41fc-ac07-411c-a5ed-caef513bb041` (`cycle_111_norm_imagBasis.lean`)
