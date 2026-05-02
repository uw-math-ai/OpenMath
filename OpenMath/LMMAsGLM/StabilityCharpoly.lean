import OpenMath.LMMAsGLM
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Butcher §521 — Step C helpers for the LMM-as-GLM stability charpoly

This module collects sparse-projection lemmas for the rank-one row and column
of the LMM-as-GLM stability decomposition, supporting the Step C adjugate
contraction toward `LMM.toGLM_stabilityMatrix_charpoly_explicit`.

Reference: J. C. Butcher, *Numerical Methods for Ordinary Differential
Equations*, 2nd ed., §521.
-/

open Finset Real

namespace LMM

variable {s : ℕ}

/-- §521 — Past-`y` projection of the rank-one row. -/
@[simp] theorem toGLM_rankOneRow_castAdd (m : LMM s) (q : Fin s) :
    toGLM_rankOneRow m (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s q))
      = ((-m.α (Fin.castSucc q) : ℝ) : ℂ) := by
  simp [toGLM_rankOneRow]

/-- §521 — Past-`h*f` projection of the rank-one row. -/
@[simp] theorem toGLM_rankOneRow_natAdd (m : LMM s) (q : Fin s) :
    toGLM_rankOneRow m (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s q))
      = ((m.β (Fin.castSucc q) : ℝ) : ℂ) := by
  unfold toGLM_rankOneRow
  rw [toGLM_Uℂ_natAdd]

/-- §521 — Past-`y` projection of the rank-one column. The `B` block is
non-zero only on the last past-`y` row, where it carries `m.β (Fin.last s)`. -/
@[simp] theorem toGLM_rankOneColumn_castAdd (m : LMM s) (z : ℂ) (q : Fin s) :
    toGLM_rankOneColumn m z (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s q))
      = if (q : ℕ) + 1 = s then z * ((m.β (Fin.last s) : ℝ) : ℂ) else 0 := by
  unfold toGLM_rankOneColumn
  by_cases hq : (q : ℕ) + 1 = s
  · rw [if_pos hq]
    have hB : m.toGLM.Bℂ
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s q)) 0 =
        ((m.β (Fin.last s) : ℝ) : ℂ) := by
      show ((m.toGLM.B (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s q)) 0
            : ℝ) : ℂ) = _
      rw [toGLM_B_castAdd_last_apply m q hq]
    rw [hB]
  · rw [if_neg hq]
    have hB : m.toGLM.Bℂ
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s q)) 0 = 0 := by
      show ((m.toGLM.B (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s q)) 0
            : ℝ) : ℂ) = _
      rw [toGLM_B_castAdd_shift_apply m q hq]; norm_cast
    rw [hB, mul_zero]

/-- §521 — Past-`h*f` projection of the rank-one column. The `B` block is
non-zero only on the last past-`h*f` row, where it carries `1`. -/
@[simp] theorem toGLM_rankOneColumn_natAdd (m : LMM s) (z : ℂ) (q : Fin s) :
    toGLM_rankOneColumn m z (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s q))
      = if (q : ℕ) + 1 = s then z else 0 := by
  unfold toGLM_rankOneColumn
  by_cases hq : (q : ℕ) + 1 = s
  · rw [if_pos hq]
    have hB : m.toGLM.Bℂ
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s q)) 0 = 1 := by
      show ((m.toGLM.B (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s q)) 0
            : ℝ) : ℂ) = _
      rw [toGLM_B_natAdd_last_apply m q hq]; norm_cast
    rw [hB, mul_one]
  · rw [if_neg hq]
    have hB : m.toGLM.Bℂ
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s q)) 0 = 0 := by
      show ((m.toGLM.B (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s q)) 0
            : ℝ) : ℂ) = _
      rw [toGLM_B_natAdd_shift_apply m q hq]; norm_cast
    rw [hB, mul_zero]

/-- §521 Step C — Reduce the rank-one adjugate contraction in
`LMM.toGLM_stabilityMatrix_charpoly_rankOne` to an explicit two-block sum
over the past-`y` and past-`h*f` halves. The resolvent prefactor
`Polynomial.C (1 / (1 - z β_s))` is pulled out of the dot product, and the
sparse rank-one column is collapsed by the Subtask 1 simp lemmas to a
selector indexed by `q : Fin s` with `(q : ℕ) + 1 = s`.

Each term of the resulting sum is a product of one entry of
`Matrix.vecMul (Polynomial.C ∘ toGLM_rankOneRow m)
   (toGLM_V_active_lift m).charmatrix.adjugate` against an at-most-one-term
column-projection coefficient. -/
theorem toGLM_stabilityMatrix_charpoly_rankOne_contraction
    (m : LMM s) (z : ℂ) :
    dotProduct (fun j => Polynomial.C ((toGLM_rankOneRow m) j))
        (((toGLM_V_active_lift m).charmatrix).adjugate.mulVec
          (fun i => Polynomial.C
            (((1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) •
              toGLM_rankOneColumn m z) i)))
      = Polynomial.C (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
        ((∑ q : Fin s,
          (Matrix.vecMul (fun j => Polynomial.C ((toGLM_rankOneRow m) j))
              ((toGLM_V_active_lift m).charmatrix).adjugate)
            (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s q)) *
            (if (q : ℕ) + 1 = s then
              Polynomial.C (z * ((m.β (Fin.last s) : ℝ) : ℂ)) else 0))
        +
        (∑ q : Fin s,
          (Matrix.vecMul (fun j => Polynomial.C ((toGLM_rankOneRow m) j))
              ((toGLM_V_active_lift m).charmatrix).adjugate)
            (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s q)) *
            (if (q : ℕ) + 1 = s then Polynomial.C z else 0))) := by
  have hcol :
      (fun i => Polynomial.C
        (((1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) •
          toGLM_rankOneColumn m z) i))
        = (Polynomial.C (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)))) •
            (fun i => Polynomial.C ((toGLM_rankOneColumn m z) i)) := by
    funext i; simp [Pi.smul_apply, Polynomial.C_mul]
  rw [hcol, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
    Matrix.dotProduct_mulVec]
  congr 1
  rw [dotProduct, ← (finCongr (Nat.two_mul s).symm).sum_comp,
    Fin.sum_univ_add]
  show
      (∑ i : Fin s,
          Matrix.vecMul (fun j => Polynomial.C ((toGLM_rankOneRow m) j))
              ((toGLM_V_active_lift m).charmatrix).adjugate
              (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s i)) *
            Polynomial.C ((toGLM_rankOneColumn m z)
              (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s i))))
        +
        (∑ i : Fin s,
          Matrix.vecMul (fun j => Polynomial.C ((toGLM_rankOneRow m) j))
              ((toGLM_V_active_lift m).charmatrix).adjugate
              (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s i)) *
            Polynomial.C ((toGLM_rankOneColumn m z)
              (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s i))))
        = _
  congr 1
  · apply Finset.sum_congr rfl
    intro q _
    rw [toGLM_rankOneColumn_castAdd]
    by_cases hq : (q : ℕ) + 1 = s
    · rw [if_pos hq, if_pos hq]
    · rw [if_neg hq, if_neg hq]; simp
  · apply Finset.sum_congr rfl
    intro q _
    rw [toGLM_rankOneColumn_natAdd]
    by_cases hq : (q : ℕ) + 1 = s
    · rw [if_pos hq, if_pos hq]
    · rw [if_neg hq, if_neg hq]; simp

end LMM
