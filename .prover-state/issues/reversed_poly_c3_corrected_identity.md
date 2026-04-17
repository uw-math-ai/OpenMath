# Issue: Corrected C3 reversed identity still unproved

## Blocker
The old lemma target
`3σ̃''(1) + ρ̃'''(1) + 3ρ̃''(1) = 0`
is false for the project’s `orderCondVal` definition. The corrected target
`6σ̃''(1) + 2ρ̃'''(1) + 3ρ̃''(1) - ρ̃'(1) = 0`
appears to be the right identity, but its proof is still missing.

## Context
- File: `OpenMath/MultistepMethods.lean`
- Lemma: `reversed_poly_C3_condition`
- The corrected statement is already in the file.
- `hQ₁pp` now uses this corrected form and compiles if the lemma is assumed.
- A concrete check against `bdf3` shows the old target is nonzero, so the original planner statement must not be reused.

## What was tried
- Mirroring the `reversed_poly_C2_condition` proof directly.
- Combining the derivative-expanded sums with pointwise identities like
  `2*x*(x-1)*(x-2) + 3*x*(x-1) - x = 2*x^3 - 3*x^2`.
- Reindexing by `Fin.revPerm` and expanding `rev(k) = s - k`.
- Normalizing the resulting expressions with `ring`, `ring_nf`, and `linear_combination`.

## Possible solutions
- Introduce abbreviations for the moment sums
  `S₀ = ∑ α`, `S₁ = ∑ k α`, `S₂ = ∑ k² α`, `S₃ = ∑ k³ α`,
  `T₀ = ∑ β`, `T₁ = ∑ k β`, `T₂ = ∑ k² β`
  immediately after reindexing, then reduce the corrected identity to
  `-2 * V₃ + (6s - 3) * V₂ + ...` with `C₀` and `C₁`.
- Avoid rewriting large nested sums in place; prove named helper equalities for each reindexed moment first, then finish by `linear_combination`.
