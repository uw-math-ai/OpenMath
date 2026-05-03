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
  adjugates of `A` and `D`.
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

private theorem adjugate_eq_right_inverse_of_mul_eq_one
    {ι α : Type*} [DecidableEq ι] [Fintype ι] [CommRing α]
    {A B : Matrix ι ι α} (hmul : A * B = 1) (hdet : A.det = 1) :
    A.adjugate = B := by
  calc
    A.adjugate = A.adjugate * 1 := by rw [Matrix.mul_one]
    _ = A.adjugate * (A * B) := by rw [hmul]
    _ = (A.adjugate * A) * B := by rw [Matrix.mul_assoc]
    _ = (A.det • (1 : Matrix ι ι α)) * B := by rw [Matrix.adjugate_mul]
    _ = B := by rw [hdet, one_smul, Matrix.one_mul]

private theorem fromBlocks_updateRow_inl [DecidableEq m] [DecidableEq n]
    (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α) (D : Matrix n n α)
    (j : m) (x : m ⊕ n → α) :
    (Matrix.fromBlocks A B C D).updateRow (Sum.inl j) x =
      Matrix.fromBlocks
        (A.updateRow j (fun k => x (Sum.inl k)))
        (B.updateRow j (fun k => x (Sum.inr k)))
        C D := by
  ext i k
  rcases i with i | i <;> rcases k with k | k
  · by_cases hi : i = j <;> simp [Matrix.updateRow, hi]
  · by_cases hi : i = j <;> simp [Matrix.updateRow, hi]
  · simp [Matrix.updateRow]
  · simp [Matrix.updateRow]

private theorem fromBlocks_updateRow_inr [DecidableEq m] [DecidableEq n]
    (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α) (D : Matrix n n α)
    (j : n) (x : m ⊕ n → α) :
    (Matrix.fromBlocks A B C D).updateRow (Sum.inr j) x =
      Matrix.fromBlocks
        A B
        (C.updateRow j (fun k => x (Sum.inl k)))
        (D.updateRow j (fun k => x (Sum.inr k))) := by
  ext i k
  rcases i with i | i <;> rcases k with k | k
  · simp [Matrix.updateRow]
  · simp [Matrix.updateRow]
  · by_cases hi : i = j <;> simp [Matrix.updateRow, hi]
  · by_cases hi : i = j <;> simp [Matrix.updateRow, hi]

private theorem single_inl_inl [DecidableEq m] [DecidableEq n] [Zero α] [One α] (i : m) :
    (fun k : m => ((Pi.single (Sum.inl i : m ⊕ n) (1 : α) : m ⊕ n → α) (Sum.inl k))) =
      Pi.single i 1 := by
  funext k
  by_cases h : i = k
  · subst k
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · have hs : (Sum.inl i : m ⊕ n) ≠ Sum.inl k := by
      intro hsum
      exact h (Sum.inl.inj hsum)
    rw [Pi.single_eq_of_ne hs.symm, Pi.single_eq_of_ne (Ne.symm h)]

private theorem single_inl_inr [DecidableEq m] [DecidableEq n] [Zero α] [One α] (i : m) :
    (fun k : n => ((Pi.single (Sum.inl i : m ⊕ n) (1 : α) : m ⊕ n → α) (Sum.inr k))) =
      0 := by
  funext k
  simp

private theorem single_inr_inl [DecidableEq m] [DecidableEq n] [Zero α] [One α] (i : n) :
    (fun k : m => ((Pi.single (Sum.inr i : m ⊕ n) (1 : α) : m ⊕ n → α) (Sum.inl k))) =
      0 := by
  funext k
  simp

private theorem single_inr_inr [DecidableEq m] [DecidableEq n] [Zero α] [One α] (i : n) :
    (fun k : n => ((Pi.single (Sum.inr i : m ⊕ n) (1 : α) : m ⊕ n → α) (Sum.inr k))) =
      Pi.single i 1 := by
  funext k
  by_cases h : i = k
  · subst k
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · have hs : (Sum.inr i : m ⊕ n) ≠ Sum.inr k := by
      intro hsum
      exact h (Sum.inr.inj hsum)
    rw [Pi.single_eq_of_ne hs.symm, Pi.single_eq_of_ne (Ne.symm h)]

private theorem adjugate_fromBlocks_diagonal_one₂₂
    [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n] [CommRing α]
    (A : Matrix m m α) :
    (Matrix.fromBlocks A 0 0 (1 : Matrix n n α)).adjugate =
      Matrix.fromBlocks A.adjugate 0 0 (A.det • (1 : Matrix n n α)) := by
  classical
  ext i j; rcases i with i | i <;> rcases j with j | j
  · rw [Matrix.adjugate_apply, fromBlocks_updateRow_inl, single_inl_inl,
      single_inl_inr, Matrix.updateRow_zero_zero, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_one, mul_one]
    rw [Matrix.fromBlocks_apply₁₁, Matrix.adjugate_apply]
  · rw [Matrix.adjugate_apply]
    apply Matrix.det_eq_zero_of_column_eq_zero (Sum.inr j)
    intro k
    rcases k with k | k
    · simp [Matrix.updateRow]
    · by_cases hk : k = j <;> simp [Matrix.updateRow, hk]
  · rw [Matrix.adjugate_apply]
    apply Matrix.det_zero_of_row_eq (show (Sum.inl j : m ⊕ n) ≠ Sum.inr i by simp)
    ext k
    rcases k with k | k
    · simp [Matrix.updateRow]
    · simp [Matrix.updateRow, Matrix.one_apply, Pi.single_apply, eq_comm]
  · rw [Matrix.adjugate_apply, fromBlocks_updateRow_inr, single_inr_inl,
      single_inr_inr, Matrix.updateRow_zero_zero, Matrix.det_fromBlocks_zero₂₁,
      Matrix.fromBlocks_apply₂₂]
    rw [← Matrix.adjugate_apply (1 : Matrix n n α) i j, Matrix.adjugate_one]
    simp [smul_eq_mul]

private theorem adjugate_fromBlocks_one_zero₂₁
    [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n] [CommRing α]
    (D : Matrix n n α) :
    (Matrix.fromBlocks (1 : Matrix m m α) 0 0 D).adjugate =
      Matrix.fromBlocks (D.det • (1 : Matrix m m α)) 0 0 D.adjugate := by
  classical
  ext i j; rcases i with i | i <;> rcases j with j | j
  · rw [Matrix.adjugate_apply, fromBlocks_updateRow_inl, single_inl_inl,
      single_inl_inr, Matrix.updateRow_zero_zero, Matrix.det_fromBlocks_zero₂₁]
    rw [Matrix.fromBlocks_apply₁₁]
    rw [← Matrix.adjugate_apply (1 : Matrix m m α) i j, Matrix.adjugate_one]
    simp [smul_eq_mul, mul_comm]
  · rw [Matrix.adjugate_apply]
    apply Matrix.det_zero_of_row_eq (show (Sum.inl i : m ⊕ n) ≠ Sum.inr j by simp)
    ext k
    rcases k with k | k
    · simp [Matrix.updateRow, Matrix.one_apply, Pi.single_apply, eq_comm]
    · simp [Matrix.updateRow]
  · rw [Matrix.adjugate_apply]
    apply Matrix.det_eq_zero_of_column_eq_zero (Sum.inl j)
    intro k
    rcases k with k | k
    · by_cases hk : k = j <;> simp [Matrix.updateRow, hk]
    · simp [Matrix.updateRow]
  · rw [Matrix.adjugate_apply, fromBlocks_updateRow_inr, single_inr_inl,
      single_inr_inr, Matrix.updateRow_zero_zero, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_one, one_mul]
    rw [Matrix.fromBlocks_apply₂₂, Matrix.adjugate_apply]

private theorem adjugate_fromBlocks_unipotent
    [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n] [CommRing α]
    (B : Matrix m n α) :
    (Matrix.fromBlocks (1 : Matrix m m α) B 0 (1 : Matrix n n α)).adjugate =
      Matrix.fromBlocks (1 : Matrix m m α) (-B) 0 (1 : Matrix n n α) := by
  classical
  apply adjugate_eq_right_inverse_of_mul_eq_one
  · rw [Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]
  · rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, one_mul]

private theorem adjugate_fromBlocks_zero₂₁_one
    [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n] [CommRing α]
    (A : Matrix m m α) (B : Matrix m n α) :
    (Matrix.fromBlocks A B 0 (1 : Matrix n n α)).adjugate =
      Matrix.fromBlocks A.adjugate (-(A.adjugate * B)) 0
        (A.det • (1 : Matrix n n α)) := by
  classical
  have hfactor :
      Matrix.fromBlocks A B 0 (1 : Matrix n n α) =
        Matrix.fromBlocks (1 : Matrix m m α) B 0 (1 : Matrix n n α) *
          Matrix.fromBlocks A 0 0 (1 : Matrix n n α) := by
    rw [Matrix.fromBlocks_multiply]
    simp
  rw [hfactor, Matrix.adjugate_mul_distrib,
    adjugate_fromBlocks_diagonal_one₂₂, adjugate_fromBlocks_unipotent,
    Matrix.fromBlocks_multiply]
  simp [Matrix.mul_neg]

/-- Row-vector of a `fromBlocks` matrix, evaluated at a `Sum.inr` index:
the result splits as the row-vector against the top-right and bottom-right
blocks. -/
theorem vecMul_fromBlocks_apply_inr
    [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring α]
    (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) (x : m ⊕ n → α) (j : n) :
    Matrix.vecMul x (Matrix.fromBlocks A B C D) (Sum.inr j) =
      Matrix.vecMul (x ∘ Sum.inl) B j +
        Matrix.vecMul (x ∘ Sum.inr) D j := by
  simp only [Matrix.vecMul, dotProduct, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₂, Fintype.sum_sum_type, Function.comp_apply]

/-- Row-vector of a `fromBlocks` matrix, evaluated at a `Sum.inl` index:
the result splits as the row-vector against the top-left and bottom-left
blocks. -/
theorem vecMul_fromBlocks_apply_inl
    [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring α]
    (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) (x : m ⊕ n → α) (j : m) :
    Matrix.vecMul x (Matrix.fromBlocks A B C D) (Sum.inl j) =
      Matrix.vecMul (x ∘ Sum.inl) A j +
        Matrix.vecMul (x ∘ Sum.inr) C j := by
  simp only [Matrix.vecMul, dotProduct, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₂₁, Fintype.sum_sum_type, Function.comp_apply]

/-- Adjugate of an upper-block-triangular matrix (zero in the bottom-left
block): the adjugate is itself upper-block-triangular, with diagonal
blocks scaled by the determinant of the opposite block and an explicit
off-diagonal correction.
-/
theorem adjugate_fromBlocks_zero₂₁
    [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n] [CommRing α]
    (A : Matrix m m α) (B : Matrix m n α) (D : Matrix n n α) :
    (Matrix.fromBlocks A B 0 D).adjugate =
      Matrix.fromBlocks
        (D.det • A.adjugate)
        (-(A.adjugate * B * D.adjugate))
        0
        (A.det • D.adjugate) := by
  classical
  have hfactor :
      Matrix.fromBlocks A B 0 D =
        Matrix.fromBlocks (1 : Matrix m m α) 0 0 D *
          Matrix.fromBlocks A B 0 (1 : Matrix n n α) := by
    rw [Matrix.fromBlocks_multiply]
    simp
  rw [hfactor, Matrix.adjugate_mul_distrib,
    adjugate_fromBlocks_zero₂₁_one, adjugate_fromBlocks_one_zero₂₁,
    Matrix.fromBlocks_multiply]
  simp [Matrix.mul_assoc, Matrix.mul_smul]

end Matrix
