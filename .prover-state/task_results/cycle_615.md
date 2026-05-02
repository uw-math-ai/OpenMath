# Cycle 615 Results

## Worked on
Butcher §520 stability matrix for general linear methods:
`OpenMath/GeneralLinearMethod.lean`, plus the §502 RK and §503 LMM
specialisations in `OpenMath/RKAsGLM.lean` and `OpenMath/LMMAsGLM.lean`.

## Approach
Added complex lifts `Aℂ`, `Uℂ`, `Bℂ`, `Vℂ` for GLM blocks and defined
`stabilityMatrix z = Vℂ + z • (Bℂ * (I - z • Aℂ)⁻¹ * Uℂ)` using total
`Matrix.inv`.

Followed sorry-first locally:
1. Inserted the GLM, RK, and LMM theorem shells with sorries.
2. Verified the sorry-first files elaborated.
3. Tried Aristotle submissions for the directory, the GLM file, and a
   prompt-level proof request. All three connector calls timed out before
   returning a project id, so there was no Aristotle result to refresh.
4. Closed the proofs manually with Lean LSP.

## Result
SUCCESS.

* `GeneralLinearMethod.stabilityMatrix_apply` is sorry-free. The proof
  expands matrix multiplication and swaps the two finite sums with
  `Finset.sum_comm`.
* `GeneralLinearMethod.stabilityMatrix_zero` is sorry-free by simplification.
* `ButcherTableau.stabilityFunction` and
  `ButcherTableau.toGLM_stabilityMatrix` are sorry-free. The RK proof uses
  a small `Aℂ` extensionality rewrite so the inverse-matrix factor matches
  the scalar stability-function definition.
* `LMM.toGLM_stabilityMatrix_apply` is sorry-free. Since the LMM embedding
  is one-stage, the double sum collapses to the single `(0,0)` resolvent
  factor.
* `plan.md` now marks §520 closed and moves the backlog to §521.

## Dead ends
* `simp [stabilityMatrix, Matrix.mul_apply]` for the GLM entry theorem left
  the two finite sums in the opposite order. Adding `rw [Finset.sum_comm]`
  after the expansion closed it.
* The RK stability-function matrix literal needed a local `let Aℂ :
  Matrix ...`; direct function-literal subtraction did not provide enough
  type information for `HSub`.
* The first RK proof attempt simplified the scalar equality to a disjunction
  involving `z = 0`. Rewriting `t.toGLM.Aℂ` to the literal complex RK
  `A` matrix before simplification avoided that branch.
* Aristotle submission attempts timed out at 120 seconds for directory,
  file, and prompt submissions, before any project id was returned.

## Discovery
* `lake env lean OpenMath/RKAsGLM.lean` reads the imported `.olean`, so after
  changing `GeneralLinearMethod.lean` the downstream checks needed
  `lake build OpenMath.GeneralLinearMethod` first.
* The generic §520 entry theorem is strong enough to make one-stage
  specialisations almost automatic: `rw [stabilityMatrix_apply]; simp`.

## Suggested next approach
Start §521 by defining a stability-order predicate for `M(z)` near zero,
probably as a matrix-valued Taylor/Pade-like matching condition against
`Complex.exp z • 1`. Keep determinant/rational-function bridges to the
existing A-stability files for a later cycle.
