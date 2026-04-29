import OpenMath.Chapter3.Section312
import Mathlib.Data.Matrix.Mul

/-!
# Butcher §370 — Symplectic Runge–Kutta methods (Definition 370A)

This file formalises Definition 370A from Butcher's *Numerical Methods for
Ordinary Differential Equations* (3rd ed., page 297).

## Textbook statement (Definition 370A, quoted verbatim from `def_370A.json`)

> A Runge–Kutta method `(A, b, c)` is *symplectic* if
> \[
>   M = \operatorname{diag}(b) A + A \operatorname{diag}(b) - b b^{\top}
> \]
> is the zero matrix.

The defining identity in entry-wise form (equation (370a)) is
`m_{ij} = b_i a_{ij} + b_j a_{ji} − b_i b_j`.

## Faithfulness notes

* `symplecticityMatrix R` is the matrix `M` above, defined directly as
  `Matrix.diagonal R.b * R.A + R.A * Matrix.diagonal R.b -
   Matrix.vecMulVec R.b R.b`.
  `Matrix.vecMulVec b b` is precisely the outer product `b bᵀ`
  (`(Matrix.vecMulVec b b) i j = b i * b j`).
* `IsSymplectic R` is the predicate `symplecticityMatrix R = 0`.
  This is the literal textbook statement, with no reformulation.
* The §370 prose mentions the §381 reducibility framework (`def:381A`–
  `def:381F`, `thm:381G/H`), but those references are paragraph context
  about the surrounding discussion — Butcher's Definition 370A itself is
  self-contained on `RKTableau` and does not depend on them.

## Concrete witness — the implicit midpoint method

The implicit midpoint method (`s = 1`, `A = [[1/2]]`, `b = [1]`,
`c = [1/2]`) is the canonical 1-stage symplectic Runge–Kutta method.
For it `M` is the 1×1 matrix with entry
`1·(1/2) + (1/2)·1 − 1·1 = 0`, so `IsSymplectic` holds.
-/

namespace OpenMath.Chapter3.Section370

open OpenMath.Chapter3.Section310
open OpenMath.Chapter3.Section312

/-- Butcher §370 — the *symplecticity matrix* of a Runge–Kutta method
`(A, b, c)`:
\[
  M = \operatorname{diag}(b) A + A \operatorname{diag}(b) - b b^{\top}.
\]
Its entry-wise form is `m_{ij} = b_i a_{ij} + b_j a_{ji} − b_i b_j`
(equation (370a) in the textbook). -/
def symplecticityMatrix {s : ℕ} (R : RKTableau s) :
    Matrix (Fin s) (Fin s) ℝ :=
  Matrix.diagonal R.b * R.A + R.A * Matrix.diagonal R.b -
    Matrix.vecMulVec R.b R.b

/-- Butcher §370 Definition 370A — a Runge–Kutta method `(A, b, c)` is
*symplectic* iff its symplecticity matrix vanishes. -/
def IsSymplectic {s : ℕ} (R : RKTableau s) : Prop :=
  symplecticityMatrix R = 0

/-! ## Concrete witness — implicit midpoint -/

/-- The implicit midpoint method as a 1-stage Runge–Kutta tableau:
`A = [[1/2]]`, `b = [1]`, `c = [1/2]`. -/
noncomputable def implicitMidpoint : RKTableau 1 where
  A := Matrix.of (fun _ _ => (1/2 : ℝ))
  b := fun _ => 1
  c := fun _ => 1/2

/-- The implicit midpoint method is symplectic: its symplecticity matrix
vanishes (the single entry is `1·(1/2) + (1/2)·1 − 1·1 = 0`). -/
theorem implicitMidpoint_isSymplectic : IsSymplectic implicitMidpoint := by
  unfold IsSymplectic symplecticityMatrix implicitMidpoint
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.diagonal, Matrix.vecMulVec, Matrix.mul_apply]
  ring

end OpenMath.Chapter3.Section370
