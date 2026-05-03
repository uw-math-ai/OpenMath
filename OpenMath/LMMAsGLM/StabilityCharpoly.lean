import OpenMath.LMMAsGLM
import OpenMath.Helpers.BlockAdjugate
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

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

/-- §521 — Past-`y` adjugate row entry at the unique selected index
`q + 1 = s` (i.e. `q = ⟨s - 1, _⟩`). -/
noncomputable def toGLM_stabilityCharpolyRowY (m : LMM s) : Polynomial ℂ :=
  if h : s = 0 then 0 else
    Matrix.vecMul (fun j => Polynomial.C ((toGLM_rankOneRow m) j))
        ((toGLM_V_active_lift m).charmatrix).adjugate
      (Fin.cast (Nat.two_mul s).symm
        (Fin.castAdd s ⟨s - 1, by omega⟩))

/-- §521 — Past-`h*f` adjugate row entry at the unique selected index. -/
noncomputable def toGLM_stabilityCharpolyRowF (m : LMM s) : Polynomial ℂ :=
  if h : s = 0 then 0 else
    Matrix.vecMul (fun j => Polynomial.C ((toGLM_rankOneRow m) j))
        ((toGLM_V_active_lift m).charmatrix).adjugate
      (Fin.cast (Nat.two_mul s).symm
        (Fin.natAdd s ⟨s - 1, by omega⟩))

private theorem fin_q_succ_eq_s_iff (hs : 0 < s) (q : Fin s) :
    (q : ℕ) + 1 = s ↔ q = ⟨s - 1, by omega⟩ := by
  constructor
  · intro h
    apply Fin.ext
    change (q : ℕ) = s - 1
    omega
  · intro h
    rw [h]
    simpa using Nat.sub_add_cancel hs

/-- §521 Step C.2 — Collapse the past-`y` selector sum to the unique
selected adjugate-row entry. -/
theorem sum_castAdd_selector_collapse (m : LMM s) (z : ℂ) (hs : 0 < s) :
    (∑ q : Fin s,
      Matrix.vecMul (fun j => Polynomial.C ((toGLM_rankOneRow m) j))
          ((toGLM_V_active_lift m).charmatrix).adjugate
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s q)) *
      (if (q : ℕ) + 1 = s then
         Polynomial.C (z * ((m.β (Fin.last s) : ℝ) : ℂ)) else 0))
      = toGLM_stabilityCharpolyRowY m *
          Polynomial.C (z * ((m.β (Fin.last s) : ℝ) : ℂ)) := by
  classical
  let qlast : Fin s := ⟨s - 1, by omega⟩
  have hlast : (qlast : ℕ) + 1 = s := by
    dsimp [qlast]
    omega
  rw [Finset.sum_eq_single qlast]
  · rw [if_pos hlast]
    unfold toGLM_stabilityCharpolyRowY
    rw [dif_neg (by omega : ¬ s = 0)]
  · intro q _ hne
    have hnot : (q : ℕ) + 1 ≠ s := by
      intro hq
      exact hne ((fin_q_succ_eq_s_iff hs q).mp hq)
    rw [if_neg hnot, mul_zero]
  · simp

/-- §521 Step C.2 — Collapse the past-`h*f` selector sum to the unique
selected adjugate-row entry. -/
theorem sum_natAdd_selector_collapse (m : LMM s) (z : ℂ) (hs : 0 < s) :
    (∑ q : Fin s,
      Matrix.vecMul (fun j => Polynomial.C ((toGLM_rankOneRow m) j))
          ((toGLM_V_active_lift m).charmatrix).adjugate
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s q)) *
      (if (q : ℕ) + 1 = s then Polynomial.C z else 0))
      = toGLM_stabilityCharpolyRowF m * Polynomial.C z := by
  classical
  let qlast : Fin s := ⟨s - 1, by omega⟩
  have hlast : (qlast : ℕ) + 1 = s := by
    dsimp [qlast]
    omega
  rw [Finset.sum_eq_single qlast]
  · rw [if_pos hlast]
    unfold toGLM_stabilityCharpolyRowF
    rw [dif_neg (by omega : ¬ s = 0)]
  · intro q _ hne
    have hnot : (q : ℕ) + 1 ≠ s := by
      intro hq
      exact hne ((fin_q_succ_eq_s_iff hs q).mp hq)
    rw [if_neg hnot, mul_zero]
  · simp

/-- §521 Step C.2 — Rewrite the rank-one contraction using the two named
surviving scalar adjugate-row entries. -/
theorem toGLM_stabilityMatrix_charpoly_rankOne_contraction_explicit
    (m : LMM s) (z : ℂ) (hs : 0 < s) :
    dotProduct (fun j => Polynomial.C ((toGLM_rankOneRow m) j))
        (((toGLM_V_active_lift m).charmatrix).adjugate.mulVec
          (fun i => Polynomial.C
            (((1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) •
              toGLM_rankOneColumn m z) i)))
      = Polynomial.C (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
          ( toGLM_stabilityCharpolyRowY m *
              Polynomial.C (z * ((m.β (Fin.last s) : ℝ) : ℂ))
          + toGLM_stabilityCharpolyRowF m * Polynomial.C z ) := by
  rw [toGLM_stabilityMatrix_charpoly_rankOne_contraction,
    sum_castAdd_selector_collapse m z hs,
    sum_natAdd_selector_collapse m z hs]

/-! ### Step C.3 — explicit form of the two scalar adjugate-row entries -/

private theorem reindex_updateRow_eq {α m' n' : Type*} [DecidableEq m']
    [DecidableEq n'] (e : m' ≃ n') (M : Matrix m' m' α) (j : n')
    (x : n' → α) :
    (Matrix.reindex e e M).updateRow j x =
      Matrix.reindex e e (M.updateRow (e.symm j) (x ∘ e)) := by
  ext i k
  by_cases hi : i = j
  · subst hi
    simp [Matrix.reindex, Matrix.updateRow]
  · have hi' : e.symm i ≠ e.symm j := fun h => hi (e.symm.injective h)
    rw [Matrix.updateRow_ne hi]
    simp [Matrix.reindex, Matrix.updateRow_ne hi']

private theorem fromBlocks_zero₂₁_updateRow_castAdd
    {α m' n' : Type*} [DecidableEq m'] [DecidableEq n'] [Zero α]
    (A : Matrix m' m' α) (B : Matrix m' n' α) (D : Matrix n' n' α)
    (j' : m') (y : m' ⊕ n' → α) :
    (Matrix.fromBlocks A B 0 D).updateRow (Sum.inl j') y =
      Matrix.fromBlocks
        (A.updateRow j' (fun k => y (Sum.inl k)))
        (B.updateRow j' (fun k => y (Sum.inr k)))
        0 D := by
  ext i k
  rcases i with i | i
  · -- Top half, may match the updated row
    by_cases hi : i = j'
    · subst hi
      rcases k with k | k <;> simp [Matrix.updateRow, Matrix.fromBlocks]
    · have hne : (Sum.inl i : m' ⊕ n') ≠ Sum.inl j' := by
        intro h
        exact hi (Sum.inl.inj h)
      rw [Matrix.updateRow_ne hne]
      rcases k with k | k <;>
        simp [Matrix.fromBlocks, Matrix.updateRow_ne hi]
  · -- Bottom half, definitely not the updated row
    have hne : (Sum.inr i : m' ⊕ n') ≠ Sum.inl j' := Sum.inr_ne_inl
    rw [Matrix.updateRow_ne hne]
    rcases k with k | k <;> simp [Matrix.fromBlocks]

/-- §521 Step C.3 — Past-`y` adjugate-row entry as the determinant of a
single rank-one updated past-`y` block, scaled by the past-`h*f`
characteristic polynomial.

The clean intermediate form makes downstream simplification (using the
known closed forms `toGLM_stabilityMatrixPY_charpoly` and
`toGLM_stabilityMatrixPHF_charpoly`) routine. -/
theorem toGLM_stabilityCharpolyRowY_eq_explicit
    (m : LMM s) (hs : 0 < s) :
    toGLM_stabilityCharpolyRowY m =
      ((toGLM_stabilityMatrixPY m 0).charmatrix.updateRow
          ⟨s - 1, by omega⟩
          (fun k => Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ))).det *
        (toGLM_stabilityMatrixPHF m 0).charpoly := by
  classical
  unfold toGLM_stabilityCharpolyRowY
  rw [dif_neg (by omega : ¬ s = 0)]
  rw [Matrix.vecMul_adjugate_apply]
  show (m.toGLM.Vℂ.charmatrix.updateRow
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s ⟨s - 1, by omega⟩))
        (fun j => Polynomial.C ((toGLM_rankOneRow m) j))).det = _
  rw [toGLM_V_active_lift_eq_fromBlocks_zero, Matrix.charmatrix_reindex,
    reindex_updateRow_eq, Matrix.det_reindex_self]
  rw [toGLM_stabilityBlockEquiv_symm_castAdd, Matrix.charmatrix_fromBlocks]
  simp only [Matrix.map_zero _ Polynomial.C_0, neg_zero]
  rw [fromBlocks_zero₂₁_updateRow_castAdd, Matrix.det_fromBlocks_zero₂₁]
  -- Reduce: rankOneRow at e (Sum.inl k) = -α (Fin.castSucc k)
  have hrow : (fun k =>
        ((fun j => Polynomial.C ((toGLM_rankOneRow m) j))
          ∘ (toGLM_stabilityBlockEquiv s)) (Sum.inl k))
      = (fun k => Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ)) := by
    funext k
    have he : toGLM_stabilityBlockEquiv s (Sum.inl k) =
        Fin.cast (Nat.two_mul s).symm (Fin.castAdd s k) := by
      simp [toGLM_stabilityBlockEquiv]
    show Polynomial.C ((toGLM_rankOneRow m)
          (toGLM_stabilityBlockEquiv s (Sum.inl k))) = _
    rw [he, toGLM_rankOneRow_castAdd]
  rw [hrow]
  rfl

/-- §521 Step C.3 — Past-`h*f` adjugate-row entry placeholder.

The reusable block-adjugate identity needed for the real scalar expansion is
available as `Matrix.adjugate_fromBlocks_zero₂₁`; the remaining work is to
push it through the `toGLM_stabilityBlockEquiv` reindexing and simplify the
off-diagonal correction term against the rank-one row. -/
theorem toGLM_stabilityCharpolyRowF_eq_explicit
    (m : LMM s) :
    ∃ R : Polynomial ℂ,
      toGLM_stabilityCharpolyRowF m = R :=
  ⟨_, rfl⟩

/-- §521 Step C.3 (headline) — Explicit form of the LMM-as-GLM stability
matrix characteristic polynomial as the active block charpoly minus the
contracted rank-one correction in the named scalar adjugate entries.
-/
theorem toGLM_stabilityMatrix_charpoly_explicit
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (m.toGLM.stabilityMatrix z).charpoly =
      (toGLM_stabilityMatrixPY m 0).charpoly *
          (toGLM_stabilityMatrixPHF m 0).charpoly -
        Polynomial.C (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
          ( toGLM_stabilityCharpolyRowY m *
              Polynomial.C (z * ((m.β (Fin.last s) : ℝ) : ℂ))
          + toGLM_stabilityCharpolyRowF m * Polynomial.C z ) := by
  rw [toGLM_stabilityMatrix_charpoly_rankOne m hz]
  rw [toGLM_stabilityMatrix_charpoly_rankOne_contraction_explicit m z hs]
  rw [show (toGLM_V_active_lift m).charpoly = m.toGLM.Vℂ.charpoly from rfl,
    toGLM_V_active_charpoly]

end LMM
