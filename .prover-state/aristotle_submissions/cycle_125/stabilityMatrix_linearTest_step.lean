/-
Cycle 125 Aristotle Job A: close the body of `thm:520B`
(`GeneralLinearMethod.stabilityMatrix_linearTest_step`).

This is Butcher Theorem 520B (p. 397): for the linear test equation
`y' = q·y`, one step of a GLM transforms `y^[n−1] → y^[n] = M(z) y^[n−1]`
with `z = h·q`, where `M(z) = V + z·B·(I − z·A)⁻¹·U` is the stability
matrix.

Recommended proof outline:
1. From `hY_stage : Y = z • A *ᵥ Y + U *ᵥ yPrev`, rearrange to get
   `(1 - z • A) *ᵥ Y = U *ᵥ yPrev`.
2. Use `h_inv : IsUnit (1 - z • A)` to conclude
   `Y = (1 - z • A)⁻¹ *ᵥ U *ᵥ yPrev`.
3. Substitute into `z • B *ᵥ Y + V *ᵥ yPrev` and combine via
   `Matrix.add_mulVec`, `Matrix.smul_mulVec`, `Matrix.mulVec_mulVec`.
4. Match the result against `M.stabilityMatrix z *ᵥ yPrev`, where
   `M.stabilityMatrix z = V + z • B * (1 - z • A)⁻¹ * U`.

Key Mathlib lemmas:
- `Matrix.sub_mulVec`, `Matrix.one_mulVec`, `Matrix.smul_mulVec`,
  `Matrix.add_mulVec`, `Matrix.mulVec_mulVec`
- `Matrix.nonsing_inv_mul`, `Matrix.mul_nonsing_inv` (or analog for IsUnit)
- `Matrix.isUnit_iff_isUnit_det`
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic

open Matrix

set_option maxHeartbeats 400000

/-- A self-contained statement of Butcher Theorem 520B. The four matrix
blocks are inlined as parameters to avoid pulling in the
`GeneralLinearMethod` structure. The conclusion mirrors the textbook:
under `(I − zA)` invertibility and the stage equation, the output
formula collapses to `M(z) · yPrev` where `M(z) = V + zB(I − zA)⁻¹U`. -/
theorem stabilityMatrix_linearTest_step
    {s r : ℕ}
    (Acplx : Matrix (Fin s) (Fin s) ℂ)
    (Ucplx : Matrix (Fin s) (Fin r) ℂ)
    (Bcplx : Matrix (Fin r) (Fin s) ℂ)
    (Vcplx : Matrix (Fin r) (Fin r) ℂ)
    (z : ℂ)
    (h_inv : IsUnit (1 - z • Acplx))
    (yPrev : Fin r → ℂ) (Y : Fin s → ℂ)
    (hY_stage : Y = z • Acplx *ᵥ Y + Ucplx *ᵥ yPrev) :
    z • Bcplx *ᵥ Y + Vcplx *ᵥ yPrev
      = (Vcplx + z • Bcplx * (1 - z • Acplx)⁻¹ * Ucplx) *ᵥ yPrev := by
  sorry
