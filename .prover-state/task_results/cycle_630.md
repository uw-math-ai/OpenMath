# Cycle 630 Results

## Worked on

§521 LMM A-stability — first concrete LMM-side transport through the
§503 GLM embedding: `backwardEuler_toGLM_isAStable` in
`OpenMath/LMMAsGLM.lean`. This is the LMM analogue of cycle 627's
`rkImplicitEuler_toGLM_isAStable` and cycle 629's
`rkImplicitMidpoint_toGLM_isAStable`.

## Approach

Direct proof at `s = 1`, **without** routing through any
`LMM.toGLM_isAStable_iff` bridge (per strategy: the iff bridge needs a
general-`s` charpoly factorisation that is not yet available, and a
sorry-first iff bridge was the cause of the cycle 628 revert).

Three steps:

1. **Stability matrix shape.** Compute
   `backwardEuler.toGLM.stabilityMatrix z = !![1/(1-z), 0; z/(1-z), 0]`
   entry-by-entry via `LMM.toGLM_stabilityMatrix_apply`, with
   `Aℂ = !![1]`, `(1 - z • Aℂ)⁻¹ 0 0 = 1/(1-z)` (using
   `Matrix.inv_def` + `Matrix.adjugate_fin_one`), and a
   `fin_cases k <;> fin_cases l` split unfolding `LMM.toGLM`,
   `backwardEuler`, and `Vℂ`/`Bℂ`/`Uℂ`. Each branch closes by
   `rfl` or `field_simp; ring`.
2. **Charpoly factorisation.**
   `charpoly(!![a, 0; c, 0]) = X * (X - C a)` via `Matrix.charpoly`
   + `Matrix.charmatrix` + `Matrix.det_fin_two` + `simp; ring`.
3. **Eigenvalue bound.** `IsRoot` gives `μ = 0` or
   `μ = (1 - z)⁻¹`. The first is trivial; the second uses
   `‖1 - z‖ ≥ 1` for `z.re ≤ 0` (replicated from the LMM-side
   `backwardEuler_aStable` proof) plus `inv_le_one_iff₀`.

## Result

SUCCESS. `backwardEuler_toGLM_isAStable : backwardEuler.toGLM.IsAStable`
lands in `OpenMath/LMMAsGLM.lean` (sorry-free). Full `lake build`
passes; `lake env lean OpenMath/LMMAsGLM.lean` is clean. The repo's
sorry count remains at zero in tracked `OpenMath/*.lean`.

## Dead ends

- **Initial mismatch in the eigenvalue branch.** The cycle 628
  reverted skeleton had
  `have hμeq : μ = (1 - z)⁻¹ := by have : μ = 1 / (1 - z) := sub_eq_zero.mp hμ1; rw [this]; rw [one_div]`
  but the `simp at hμ` after `Polynomial.IsRoot` already rewrites
  `1 / (1 - z)` to `(1 - z)⁻¹`. Direct
  `have hμeq : μ = (1 - z)⁻¹ := sub_eq_zero.mp hμ1` works.
- No other dead ends: the cycle 628 skeleton compiled essentially
  verbatim once the post-`simp` form of the eigenvalue equation was
  matched.

## Discovery

- The `rkImplicitEuler_toGLM_isAStable` recipe (cycle 627) routes
  through `ButcherTableau.toGLM_isAStable_iff` because the RK side
  has the iff bridge already proved. The LMM side does **not** have
  the analogous iff yet (cycle 628 attempted it sorry-first and was
  reverted), so concrete LMM A-stability transports must currently
  be proved by direct charpoly computation, exactly as done here.
- The 2×2 charpoly factorisation
  `charpoly(!![a, 0; c, 0]) = X * (X - C a)` is independent of the
  off-diagonal `c`, which matches the structural prediction
  `charpoly(M(z)) = X^s · π(·, z)` at `s = 1` (here
  `π(X, z) = X - 1/(1-z)`).
- `Matrix.adjugate_fin_one` plus `Matrix.inv_def` cleanly handles
  the scalar resolvent `(1 - z • !![1])⁻¹ 0 0 = 1/(1-z)`. No
  Cramer's rule machinery needed.

## Suggested next approach

1. **`trapezoidalRule_toGLM_isAStable` (cycle 631 candidate)**.
   Same `s = 1` recipe with `A = [[1/2]]`, amplification factor
   `(2 + z)/(2 - z)`. The 2×2 stability matrix should reduce to
   `!![ (2+z)/(2-z), 0; (something)/(2-z), 0 ]` and the
   eigenvalues are `0` and `(2+z)/(2-z)`. The norm bound uses the
   existing `trapezoidalRule_aStable` `‖2+z‖ ≤ ‖2-z‖` argument at
   `OpenMath/MultistepMethods.lean` lines 377–.
2. The `LMM.toGLM_isAStable_iff` headline still requires a
   structural lemma `charpoly(M(z)) = X^s · π(·, z)` (up to scaling)
   for general `s`. The cycle 630 result confirms the `s = 1` shape
   and so the conjectural factorisation is consistent at the base
   case. A possible route: factor through the matrix determinant
   lemma + the LMM companion-matrix recurrence already used in the
   §512 stability lift.
3. Pivot back to §38 `cut_assoc` only when a structural Hopf-algebra
   plan is available (still gated by
   `.prover-state/issues/section386aug_strong_induction_obstruction.md`).

## Cycle hygiene notes

- `lake build` passes (8087 jobs, only pre-existing simp-style
  warnings on `ButcherGroup/Section386Aug/DepthThree.lean`, unrelated
  to this cycle).
- `OpenMath/LMMAsGLM.lean` grew from 1329 to ~1393 lines — well
  under the 6000-line cap.
- `plan.md` Active Frontier and §52 Backlog Queue item #7 updated
  to reflect the new milestone state.
