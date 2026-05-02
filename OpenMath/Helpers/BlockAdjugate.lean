import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Block

/-!
# Block-triangular adjugate identity

Auxiliary helpers supporting the LMM-as-GLM stability charpoly bridge in
`OpenMath/LMMAsGLM/StabilityCharpoly.lean`. Provides:

* `Matrix.vecMul_adjugate_apply` — the row-vector form of Cramer's rule:
  `(vecMul x A.adjugate) j = (A.updateRow j x).det`.
* `Matrix.adjugate_fromBlocks_zero₂₁` — the adjugate of an
  upper-block-triangular matrix `fromBlocks A B 0 D` in terms of the
  adjugates of `A` and `D` (sorry-first scaffold; the off-diagonal
  correction proof is deferred to a follow-up cycle).
-/

namespace Matrix

variable {m n α : Type*}

/-- Cramer's rule, row-vector form: pairing a row vector `x` against the
adjugate of `A` from the left gives the determinant of `A` with row `j`
replaced by `x`. -/
theorem vecMul_adjugate_apply [DecidableEq n] [Fintype n] [CommRing α]
    (A : Matrix n n α) (x : n → α) (j : n) :
    Matrix.vecMul x A.adjugate j = (A.updateRow j x).det := by
  classical
  have h1 :
      Matrix.vecMul x A.adjugate = A.transpose.cramer x := by
    rw [← Matrix.mulVec_transpose, Matrix.adjugate_transpose,
      ← Matrix.cramer_eq_adjugate_mulVec]
  rw [h1, Matrix.cramer_transpose_apply]

/-- Adjugate of an upper-block-triangular matrix (zero in the bottom-left
block): the adjugate is itself upper-block-triangular, with diagonal
blocks scaled by the determinant of the opposite block and an explicit
off-diagonal correction.

**TODO (cycle 664+).** Sorry-first scaffold; proof to be supplied in a
follow-up cycle. The shape above can be verified by direct computation
of `(fromBlocks A B 0 D) * X` and `X * (fromBlocks A B 0 D)`, both of
which collapse to `det • 1` via `Matrix.mul_adjugate` and
`Matrix.adjugate_mul`; the remaining step is unique-ness of the adjugate
relation, which is delicate over a general commutative ring. -/
theorem adjugate_fromBlocks_zero₂₁
    [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n] [CommRing α]
    (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α) :
    (Matrix.fromBlocks A B 0 D).adjugate =
      Matrix.fromBlocks
        (D.det • A.adjugate)
        (-(A.adjugate * B * D.adjugate))
        0
        (A.det • D.adjugate) := by
  sorry

end Matrix
