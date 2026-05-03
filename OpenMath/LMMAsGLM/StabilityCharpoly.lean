import OpenMath.LMMAsGLM
import OpenMath.LMMAsGLM.Stability
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

/-- §521 Step C.3 — Past-`h*f` adjugate-row entry as a sum of two block
contributions: a top-half rank-one updated past-`y` correction (the
off-diagonal block of the upper-triangular adjugate) and a bottom-half
`PY.charmatrix.det`-scaled past-`h*f` adjugate row.

This is the `RowF` analogue of `toGLM_stabilityCharpolyRowY_eq_explicit`,
obtained by routing through `Matrix.adjugate_fromBlocks_zero₂₁` rather
than `Matrix.det_fromBlocks_zero₂₁` (the row-update at `Sum.inr` does not
preserve the bottom-left zero block, so the determinant shortcut does
not apply here). -/
theorem toGLM_stabilityCharpolyRowF_eq_explicit
    (m : LMM s) (hs : 0 < s) :
    toGLM_stabilityCharpolyRowF m =
      Matrix.vecMul
          (fun k => Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ))
          (-(toGLM_stabilityMatrixPY m 0).charmatrix.adjugate *
            (-(toGLM_stabilityMatrixPYHF m 0).map Polynomial.C) *
            (toGLM_stabilityMatrixPHF m 0).charmatrix.adjugate)
          ⟨s - 1, by omega⟩
      +
      Matrix.vecMul
          (fun k => Polynomial.C ((m.β (Fin.castSucc k) : ℝ) : ℂ))
          ((toGLM_stabilityMatrixPY m 0).charmatrix.det •
            (toGLM_stabilityMatrixPHF m 0).charmatrix.adjugate)
          ⟨s - 1, by omega⟩ := by
  classical
  unfold toGLM_stabilityCharpolyRowF
  rw [dif_neg (by omega : ¬ s = 0)]
  show Matrix.vecMul (fun j => Polynomial.C ((toGLM_rankOneRow m) j))
        (m.toGLM.Vℂ.charmatrix).adjugate
      (Fin.cast (Nat.two_mul s).symm
        (Fin.natAdd s ⟨s - 1, by omega⟩)) = _
  rw [toGLM_V_active_lift_eq_fromBlocks_zero, Matrix.charmatrix_reindex,
    Matrix.adjugate_reindex, Matrix.reindex_apply,
    Matrix.submatrix_vecMul_equiv]
  simp only [Equiv.symm_symm, Function.comp_apply,
    toGLM_stabilityBlockEquiv_symm_natAdd]
  rw [Matrix.charmatrix_fromBlocks]
  simp only [Matrix.map_zero _ Polynomial.C_0, neg_zero]
  rw [Matrix.adjugate_fromBlocks_zero₂₁]
  rw [Matrix.vecMul_fromBlocks_apply_inr]
  -- Rewrite the row-vector restrictions using the rank-one row simp lemmas.
  have hrow_inl :
      ((fun j => Polynomial.C ((toGLM_rankOneRow m) j)) ∘
          (toGLM_stabilityBlockEquiv s)) ∘ Sum.inl
        = fun k => Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ) := by
    funext k
    have he : toGLM_stabilityBlockEquiv s (Sum.inl k) =
        Fin.cast (Nat.two_mul s).symm (Fin.castAdd s k) := by
      simp [toGLM_stabilityBlockEquiv]
    show Polynomial.C ((toGLM_rankOneRow m)
          (toGLM_stabilityBlockEquiv s (Sum.inl k))) = _
    rw [he, toGLM_rankOneRow_castAdd]
  have hrow_inr :
      ((fun j => Polynomial.C ((toGLM_rankOneRow m) j)) ∘
          (toGLM_stabilityBlockEquiv s)) ∘ Sum.inr
        = fun k => Polynomial.C ((m.β (Fin.castSucc k) : ℝ) : ℂ) := by
    funext k
    have he : toGLM_stabilityBlockEquiv s (Sum.inr k) =
        Fin.cast (Nat.two_mul s).symm (Fin.natAdd s k) := by
      simp [toGLM_stabilityBlockEquiv]
    show Polynomial.C ((toGLM_rankOneRow m)
          (toGLM_stabilityBlockEquiv s (Sum.inr k))) = _
    rw [he, toGLM_rankOneRow_natAdd]
  rw [hrow_inl, hrow_inr]
  -- Top half: rewrite -(A * B * D) = (-A) * B * D so the resulting matrix
  -- matches the strategy form `(-A.adjugate) * (-(B.map C)) * D.adjugate`.
  rw [show
        (-((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate *
            (-(toGLM_stabilityMatrixPYHF m 0).map Polynomial.C) *
          (toGLM_stabilityMatrixPHF m 0).charmatrix.adjugate))
          =
        (-(toGLM_stabilityMatrixPY m 0).charmatrix.adjugate) *
            (-(toGLM_stabilityMatrixPYHF m 0).map Polynomial.C) *
          (toGLM_stabilityMatrixPHF m 0).charmatrix.adjugate from by
        rw [Matrix.neg_mul, Matrix.neg_mul]]

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

/-! ### Step C.5 — The active stability polynomial -/

/-- §521 Step C.5 — The **active stability polynomial** of an LMM-as-GLM,
defined as the resolvent denominator `D = 1 - z β_last` times the
characteristic polynomial of the active past-`y` block of the GLM
stability matrix **at `z = 0`** (only the prefactor `D` carries `z`
dependence; the underlying matrix is `PY(0)`).

Cycle 692 redefinition: previously the body used `PY(z)`, but the
explicit form's structural decomposition (cycles 666 / 680 / 688 / 690)
naturally produces `(toGLM_stabilityMatrixPY m 0).charpoly`. The
`PY(z)` and `PY(0)` charpolys differ in general because `PY(z)` rescales
the bottom row by `1/D`, so the redefinition makes the general headline
identity `D · charpoly = X^s · activeStabilityPolyPoly − residual`
(`D_mul_toGLM_charpoly_eq_X_pow_mul_active_plus_residual`) clean.

NOTE: With this `PY(0)`-flavoured definition, `activeStabilityPolyPoly`
no longer collapses to `stabilityPolyPoly` under BDF. The BDF headline
in classical scalar form is provided directly as
`D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_of_bdf`. -/
noncomputable def activeStabilityPolyPoly (m : LMM s) (z : ℂ) : Polynomial ℂ :=
  (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) •
    (toGLM_stabilityMatrixPY m 0).charpoly

/-- §521 Step C.5 — BDF specialisation of the GLM stability charpoly in
the classical scalar form: `C D · charpoly = X^s · stabilityPolyPoly`
under BDF. Direct combination of `toGLM_stabilityMatrix_charpoly_of_bdf`
(cycle 643) and `toGLM_stabilityMatrixPY_charpoly_eq_stabilityPolyPoly_of_bdf`
(`OpenMath/LMMAsGLM/Stability.lean` line 944).

This replaces the cycle-668 BDF lemma
`D_mul_toGLM_charpoly_eq_X_pow_mul_active_of_bdf`, which after the
cycle-692 redefinition of `activeStabilityPolyPoly` would no longer
hold (the `PY(z)`-vs-`PY(0)` rescaling of the bottom row produces a
non-vanishing residual under BDF). -/
theorem D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_of_bdf
    (m : LMM s) (z : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) :
    Polynomial.C (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        (m.toGLM.stabilityMatrix z).charpoly =
      (Polynomial.X : Polynomial ℂ) ^ s * m.stabilityPolyPoly z := by
  rw [toGLM_stabilityMatrix_charpoly_of_bdf m z hbdf]
  rw [show Polynomial.C (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
            ((toGLM_stabilityMatrixPY m z).charpoly *
              (Polynomial.X : Polynomial ℂ) ^ s) =
        ((1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) •
            (toGLM_stabilityMatrixPY m z).charpoly) *
          (Polynomial.X : Polynomial ℂ) ^ s by
    rw [Polynomial.smul_eq_C_mul]; ring]
  rw [toGLM_stabilityMatrixPY_charpoly_eq_stabilityPolyPoly_of_bdf m z hbdf hz]
  ring

/-- §521 Step C.5 — At `z = 0`, the past-`h*f` block charpoly is the
pure `X^s` factor (no BDF hypothesis). Direct `z = 0` specialisation of
the general `toGLM_stabilityMatrixPHF_charpoly`: every summand in the
bottom-row companion correction has an explicit `z` factor and so
vanishes. -/
theorem toGLM_stabilityMatrixPHF_zero_charpoly (m : LMM s) :
    (toGLM_stabilityMatrixPHF m 0).charpoly =
      (Polynomial.X : Polynomial ℂ) ^ s := by
  rw [toGLM_stabilityMatrixPHF_charpoly m 0]
  simp

/-- §521 Step C.5 — The `PY(0).charpoly · PHF(0).charpoly` summand of
`toGLM_stabilityMatrix_charpoly_explicit` factors as
`X^s · PY(0).charpoly`, isolating the `X^s` extraction on the
"non-rank-one-correction" half of the explicit form. -/
theorem toGLM_V_active_charpoly_eq_X_pow_s_mul_PY (m : LMM s) :
    m.toGLM.Vℂ.charpoly =
      (Polynomial.X : Polynomial ℂ) ^ s *
        (toGLM_stabilityMatrixPY m 0).charpoly := by
  rw [toGLM_V_active_charpoly, toGLM_stabilityMatrixPHF_zero_charpoly]
  ring

/-- §521 Step C.5 — RowY as `updatedDet · X^s`. Immediate from
`toGLM_stabilityCharpolyRowY_eq_explicit` and
`toGLM_stabilityMatrixPHF_zero_charpoly`. -/
theorem toGLM_stabilityCharpolyRowY_eq_X_pow_s_mul
    (m : LMM s) (hs : 0 < s) :
    toGLM_stabilityCharpolyRowY m =
      ((toGLM_stabilityMatrixPY m 0).charmatrix.updateRow
          ⟨s - 1, by omega⟩
          (fun k => Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ))).det *
        (Polynomial.X : Polynomial ℂ) ^ s := by
  rw [toGLM_stabilityCharpolyRowY_eq_explicit m hs,
      toGLM_stabilityMatrixPHF_zero_charpoly]

/-- §521 Step C.5 — The RowY-quotient polynomial: the determinant of the
`PY(0)` charmatrix with its last past-`y` row replaced by the `-α`
coefficients. By `toGLM_stabilityCharpolyRowY_eq_X_pow_s_mul`, the
product `rowYQuot m * X ^ s = toGLM_stabilityCharpolyRowY m`. -/
noncomputable def rowYQuot (m : LMM s) : Polynomial ℂ :=
  if h : s = 0 then 0 else
    ((toGLM_stabilityMatrixPY m 0).charmatrix.updateRow
        ⟨s - 1, by omega⟩
        (fun k => Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ))).det

theorem rowYQuot_mul_X_pow_eq_RowY (m : LMM s) (hs : 0 < s) :
    rowYQuot m * (Polynomial.X : Polynomial ℂ) ^ s =
      toGLM_stabilityCharpolyRowY m := by
  rw [toGLM_stabilityCharpolyRowY_eq_X_pow_s_mul m hs]
  unfold rowYQuot
  rw [dif_neg (by omega : ¬ s = 0)]

/-- §521 Step C.5 — Under the BDF hypothesis (only `β_last` is non-zero),
the past-`h*f` adjugate row entry of the rank-one contraction vanishes.

Both summands of `toGLM_stabilityCharpolyRowF_eq_explicit` collapse:

* The β-summand row vector is `Polynomial.C (m.β (Fin.castSucc k))`,
  which is zero under BDF since `Fin.castSucc k ≠ Fin.last s`.
* The α-summand routes through `(toGLM_stabilityMatrixPYHF m 0).map C`,
  which is zero under BDF by `toGLM_stabilityMatrixPYHF_eq_zero_of_bdf`.
-/
theorem toGLM_stabilityCharpolyRowF_of_bdf
    (m : LMM s) (hs : 0 < s)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0) :
    toGLM_stabilityCharpolyRowF m = 0 := by
  classical
  rw [toGLM_stabilityCharpolyRowF_eq_explicit m hs]
  -- α-summand: PYHF(0) = 0 ⇒ entire matrix product = 0 ⇒ vecMul = 0.
  have hPYHF : (toGLM_stabilityMatrixPYHF m 0).map Polynomial.C = 0 := by
    rw [toGLM_stabilityMatrixPYHF_eq_zero_of_bdf m 0 hbdf]
    exact Matrix.map_zero _ Polynomial.C_0
  have hαsumm :
      Matrix.vecMul
          (fun k => Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ))
          (-(toGLM_stabilityMatrixPY m 0).charmatrix.adjugate *
            (-(toGLM_stabilityMatrixPYHF m 0).map Polynomial.C) *
            (toGLM_stabilityMatrixPHF m 0).charmatrix.adjugate)
          ⟨s - 1, by omega⟩ = 0 := by
    rw [hPYHF, neg_zero, Matrix.mul_zero, Matrix.zero_mul,
        Matrix.vecMul_zero]
    rfl
  -- β-summand: row vector is 0 under BDF.
  have hβrow :
      (fun k : Fin s => Polynomial.C ((m.β (Fin.castSucc k) : ℝ) : ℂ))
        = (0 : Fin s → Polynomial ℂ) := by
    funext k
    have hkne : (Fin.castSucc k : Fin (s + 1)) ≠ Fin.last s := by
      intro hl
      have : (k : ℕ) = s := by
        have := congrArg (Fin.val) hl
        simpa [Fin.castSucc, Fin.last] using this
      exact absurd this (by have := k.isLt; omega)
    have hβ : m.β (Fin.castSucc k) = 0 := hbdf (Fin.castSucc k) hkne
    simp [hβ]
  have hβsumm :
      Matrix.vecMul
          (fun k => Polynomial.C ((m.β (Fin.castSucc k) : ℝ) : ℂ))
          ((toGLM_stabilityMatrixPY m 0).charmatrix.det •
            (toGLM_stabilityMatrixPHF m 0).charmatrix.adjugate)
          ⟨s - 1, by omega⟩ = 0 := by
    rw [hβrow, Matrix.zero_vecMul]
    rfl
  rw [hαsumm, hβsumm, add_zero]

/-- §521 Step C.5 — BDF-branch X^s extraction from
`toGLM_stabilityMatrix_charpoly_explicit`: under BDF, the GLM stability
charpoly factors cleanly as `X^s · (PY.charpoly - resolvent · rowYQuot · zβ)`.

This is a real headline result for the BDF branch — a clean intermediate
target on the path to the eventual general iff bridge. The proof
combines:

* `toGLM_stabilityMatrixPHF_zero_charpoly` — `PHF(0).charpoly = X^s`,
* `rowYQuot_mul_X_pow_eq_RowY` — `RowY = rowYQuot · X^s`,
* `toGLM_stabilityCharpolyRowF_of_bdf` — `RowF = 0` under BDF.
-/
theorem toGLM_stabilityMatrix_charpoly_explicit_of_bdf
    (m : LMM s) (z : ℂ) (hs : 0 < s)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) :
    (m.toGLM.stabilityMatrix z).charpoly =
      (Polynomial.X : Polynomial ℂ) ^ s *
        ((toGLM_stabilityMatrixPY m 0).charpoly -
          Polynomial.C (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
            rowYQuot m *
            Polynomial.C (z * ((m.β (Fin.last s) : ℝ) : ℂ))) := by
  rw [toGLM_stabilityMatrix_charpoly_explicit m hz hs]
  rw [toGLM_stabilityMatrixPHF_zero_charpoly]
  rw [← rowYQuot_mul_X_pow_eq_RowY m hs]
  rw [toGLM_stabilityCharpolyRowF_of_bdf m hs hbdf]
  ring

/-! ### Step C.6 — General PHF(0) adjugate column closed form -/

/-- §521 Step C.6 — Closed form of `toGLM_stabilityMatrixPHF m 0` at
arbitrary entry: it is the strict upper-shift companion (no BDF
hypothesis needed; the `z = 0` substitution makes the bottom-row
coefficient vanish unconditionally). -/
theorem toGLM_stabilityMatrixPHF_zero_apply (m : LMM s) (j l : Fin s) :
    toGLM_stabilityMatrixPHF m 0 j l =
      (if (l : ℕ) = (j : ℕ) + 1 then (1 : ℂ) else 0) := by
  unfold toGLM_stabilityMatrixPHF
  by_cases hj : (j : ℕ) + 1 = s
  · rw [if_pos hj, zero_mul, zero_mul]
    rw [if_neg]
    intro hlj
    have hl_lt : (l : ℕ) < s := l.isLt
    omega
  · rw [if_neg hj]

/-- §521 Step C.6 — Explicit closed form of the entries of
`toGLM_stabilityMatrixPHF m 0`'s charmatrix: it is the
upper-bidiagonal polynomial matrix with `X` on the diagonal and `-1`
on the super-diagonal. -/
theorem toGLM_stabilityMatrixPHF_zero_charmatrix_apply
    (m : LMM s) (j l : Fin s) :
    (toGLM_stabilityMatrixPHF m 0).charmatrix j l =
      if (j : ℕ) = (l : ℕ) then (Polynomial.X : Polynomial ℂ)
      else if (l : ℕ) = (j : ℕ) + 1 then (-1 : Polynomial ℂ)
      else 0 := by
  rw [Matrix.charmatrix_apply, toGLM_stabilityMatrixPHF_zero_apply]
  by_cases hjl : j = l
  · subst hjl
    simp
  · have hjl' : (j : ℕ) ≠ (l : ℕ) := fun h => hjl (Fin.ext h)
    rw [if_neg hjl']
    by_cases hlj1 : (l : ℕ) = (j : ℕ) + 1
    · simp [hjl, hlj1]
    · simp [hjl, hlj1]

/-- §521 Step C.6 — The candidate explicit adjugate matrix for
`(toGLM_stabilityMatrixPHF m 0).charmatrix`: entries are powers of
`X` on and above the diagonal, zero below. -/
noncomputable def phfZeroCharmatrixAdjExplicit (s : ℕ) :
    Matrix (Fin s) (Fin s) (Polynomial ℂ) :=
  fun i j =>
    if (i : ℕ) ≤ (j : ℕ) then
      (Polynomial.X : Polynomial ℂ) ^ (s - 1 - ((j : ℕ) - (i : ℕ)))
    else 0

/-- §521 Step C.6 — Last column of the explicit adjugate is the
geometric power vector `(1, X, X², …, X^{s-1})`. -/
theorem phfZeroCharmatrixAdjExplicit_last_col (s : ℕ) (hs : 0 < s)
    (i : Fin s) :
    phfZeroCharmatrixAdjExplicit s i ⟨s - 1, by omega⟩ =
      (Polynomial.X : Polynomial ℂ) ^ (i : ℕ) := by
  unfold phfZeroCharmatrixAdjExplicit
  have hi_lt : (i : ℕ) < s := i.isLt
  have hi : (i : ℕ) ≤ s - 1 := by omega
  show (if (i : ℕ) ≤ s - 1 then
      (Polynomial.X : Polynomial ℂ) ^ (s - 1 - ((s - 1) - (i : ℕ)))
    else 0) = (Polynomial.X : Polynomial ℂ) ^ (i : ℕ)
  rw [if_pos hi]
  congr 1
  omega

/-- §521 Step C.6 — Cancellation: in an integral domain, if
`A * B = (det A) • 1` and `det A ≠ 0`, then `A.adjugate = B`.
The standard `A * adjugate A = (det A) • 1` and `adjugate A * A = (det A) • 1`
identities give `(det A) • B = (det A) • A.adjugate` after multiplication
by `adjugate A`; entry-wise cancellation by `det A` (non-zero in an
integral domain) finishes. -/
private theorem adjugate_eq_of_mul_eq_det_smul
    {ι R : Type*} [DecidableEq ι] [Fintype ι] [CommRing R]
    [NoZeroDivisors R]
    {A B : Matrix ι ι R} (hmul : A * B = A.det • (1 : Matrix ι ι R))
    (hdet : A.det ≠ 0) :
    A.adjugate = B := by
  have hsmul : A.det • B = A.det • A.adjugate := by
    calc A.det • B
        = (A.det • (1 : Matrix ι ι R)) * B := by
            rw [Matrix.smul_mul, Matrix.one_mul]
      _ = (A.adjugate * A) * B := by rw [Matrix.adjugate_mul]
      _ = A.adjugate * (A * B) := by rw [Matrix.mul_assoc]
      _ = A.adjugate * (A.det • (1 : Matrix ι ι R)) := by rw [hmul]
      _ = A.det • (A.adjugate * 1) := Matrix.mul_smul _ _ _
      _ = A.det • A.adjugate := by rw [Matrix.mul_one]
  ext i j
  have hij := congrFun (congrFun hsmul i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at hij
  exact (mul_left_cancel₀ hdet hij.symm)

/-- §521 Step C.6 — Multiplication identity: the past-`h*f` charmatrix
times the explicit adjugate-candidate equals `X^s • 1`. Bridge for
identifying `phfZeroCharmatrixAdjExplicit s` with the actual
adjugate via `adjugate_eq_of_mul_eq_det_smul`.

Proof strategy: each row `i` of `charmatrix` has at most two non-zero
entries — `X` at column `i`, and (when `(i:ℕ)+1 < s`) `-1` at column
`⟨(i:ℕ)+1, _⟩`. The matrix product in column `j` is therefore a sum
of at most two terms, which telescope to `X^s` on the diagonal and `0`
off the diagonal.
-/
theorem phfZeroCharmatrix_mul_adjExplicit (m : LMM s) :
    (toGLM_stabilityMatrixPHF m 0).charmatrix *
        phfZeroCharmatrixAdjExplicit s =
      ((Polynomial.X : Polynomial ℂ) ^ s) •
        (1 : Matrix (Fin s) (Fin s) (Polynomial ℂ)) := by
  classical
  refine Matrix.ext (fun i j => ?_)
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  -- Reduce charmatrix entries to the explicit closed form.
  have hcm : ∀ k : Fin s,
      (toGLM_stabilityMatrixPHF m 0).charmatrix i k =
        (if (i : ℕ) = (k : ℕ) then (Polynomial.X : Polynomial ℂ)
         else if (k : ℕ) = (i : ℕ) + 1 then (-1 : Polynomial ℂ)
         else 0) := fun k =>
    toGLM_stabilityMatrixPHF_zero_charmatrix_apply m i k
  conv_lhs =>
    enter [2, k]
    rw [hcm k]
  have hi_lt : (i : ℕ) < s := i.isLt
  have hj_lt : (j : ℕ) < s := j.isLt
  by_cases h_i_last : (i : ℕ) + 1 = s
  · -- Last row: only the diagonal contributes, so the sum collapses to
    -- `X * adjExplicit i j`.
    rw [Finset.sum_eq_single i]
    · -- evaluate at k = i
      have hii : ((i : ℕ) = (i : ℕ)) := rfl
      rw [if_pos hii]
      -- Need: X * adjExplicit i j = X^s * (if i = j then 1 else 0)
      unfold phfZeroCharmatrixAdjExplicit
      by_cases hij : i = j
      · subst hij
        have hi_le : (i : ℕ) ≤ (i : ℕ) := le_refl _
        rw [if_pos hi_le, if_pos rfl]
        rw [Nat.sub_self, Nat.sub_zero, mul_one]
        conv_rhs => rw [show s = (s - 1) + 1 from by omega]
        rw [pow_succ']
      · have hij' : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
        rw [if_neg hij]
        rw [mul_zero]
        -- Need: X * (...) = 0; show that adjExplicit i j = 0
        by_cases hij_le : (i : ℕ) ≤ (j : ℕ)
        · -- (i : ℕ) ≤ (j : ℕ), but i ≠ j ⇒ (i : ℕ) < (j : ℕ)
          -- but (i : ℕ) + 1 = s and (j : ℕ) < s ⇒ (j : ℕ) ≤ i, contradiction
          exfalso
          omega
        · rw [if_neg hij_le, mul_zero]
    · -- k ≠ i case: charmatrix i k = 0 because either (k : ℕ) ≠ (i : ℕ) and
      -- (k : ℕ) = (i : ℕ) + 1 = s would put k out of range.
      intro k _ hki
      have hki' : (i : ℕ) ≠ (k : ℕ) := fun h => hki (Fin.ext h.symm)
      rw [if_neg hki']
      have hk_lt : (k : ℕ) < s := k.isLt
      have hk_ne : (k : ℕ) ≠ (i : ℕ) + 1 := by omega
      rw [if_neg hk_ne, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · -- General row: i+1 < s. Two non-zero terms: k = i and k = ⟨i+1, _⟩.
    have h_i_lt : (i : ℕ) + 1 < s := by omega
    let i' : Fin s := ⟨(i : ℕ) + 1, h_i_lt⟩
    have hi'_val : (i' : ℕ) = (i : ℕ) + 1 := rfl
    have h_i_ne_i' : i ≠ i' := by
      intro h
      have hv := congrArg (Fin.val) h
      rw [hi'_val] at hv
      omega
    rw [Finset.sum_eq_add i i' h_i_ne_i']
    · -- Evaluate at k = i and k = i'.
      have hii : ((i : ℕ) = (i : ℕ)) := rfl
      rw [if_pos hii]
      have hii' : (i : ℕ) ≠ (i' : ℕ) := by rw [hi'_val]; omega
      rw [if_neg hii']
      rw [if_pos hi'_val]
      -- Now: X * adjExplicit i j + (-1) * adjExplicit i' j = X^s * 1_{i=j}
      unfold phfZeroCharmatrixAdjExplicit
      by_cases hij : i = j
      · subst hij
        have hii_le : (i : ℕ) ≤ (i : ℕ) := le_refl _
        rw [if_pos hii_le, if_pos rfl]
        have hi'i_not_le : ¬ ((i' : ℕ) ≤ (i : ℕ)) := by
          rw [hi'_val]; omega
        rw [if_neg hi'i_not_le]
        rw [Nat.sub_self, Nat.sub_zero]
        -- Goal: X * X^(s-1) + -1 * 0 = X^s * 1
        have hpow : (Polynomial.X : Polynomial ℂ) ^ s =
            Polynomial.X * Polynomial.X ^ (s - 1) := by
          conv_lhs => rw [show s = (s - 1) + 1 from by omega]
          rw [pow_succ']
        rw [hpow]
        ring
      · -- i ≠ j
        have hij' : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
        rw [if_neg hij]
        by_cases hij_le : (i : ℕ) ≤ (j : ℕ)
        · -- (i:ℕ) < (j:ℕ); (i'+1:ℕ) ≤ (j:ℕ) iff (i:ℕ)+1 ≤ (j:ℕ)
          have hij_lt : (i : ℕ) < (j : ℕ) := lt_of_le_of_ne hij_le hij'
          rw [if_pos hij_le]
          have hi'j_le : (i' : ℕ) ≤ (j : ℕ) := by rw [hi'_val]; omega
          rw [if_pos hi'j_le]
          -- Telescope: X * X^{s-1-(j-i)} - X^{s-1-(j-(i+1))} = 0.
          -- Note `s-1-(j-i') = (s-1-(j-i)) + 1` since `i' = i+1` and `i+1 ≤ j`.
          have hex : s - 1 - ((j : ℕ) - (i' : ℕ)) =
              (s - 1 - ((j : ℕ) - (i : ℕ))) + 1 := by
            have h1 : (i' : ℕ) = (i : ℕ) + 1 := hi'_val
            omega
          rw [hex, pow_succ']
          ring
        · -- (i:ℕ) > (j:ℕ); both adjExplicit terms are 0
          rw [if_neg hij_le]
          have hi'j_not_le : ¬ ((i' : ℕ) ≤ (j : ℕ)) := by
            rw [hi'_val]; omega
          rw [if_neg hi'j_not_le]
          ring
    · -- All k ≠ i, k ≠ i' have charmatrix entry 0.
      intro k _ ⟨hk_ne_i, hk_ne_i'⟩
      have hki' : (i : ℕ) ≠ (k : ℕ) := fun h => hk_ne_i (Fin.ext h.symm)
      rw [if_neg hki']
      have hk_ne_i'_val : (k : ℕ) ≠ (i : ℕ) + 1 := by
        intro h
        apply hk_ne_i'
        apply Fin.ext
        rw [hi'_val]
        exact h
      rw [if_neg hk_ne_i'_val, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
    · intro h
      exact absurd (Finset.mem_univ i') h

/-- §521 Step C.6 — Identification of the adjugate of the past-`h*f`
charmatrix at `z = 0` as the explicit closed form
`phfZeroCharmatrixAdjExplicit`. -/
theorem toGLM_stabilityMatrixPHF_zero_charmatrix_adjugate_eq
    (m : LMM s) :
    (toGLM_stabilityMatrixPHF m 0).charmatrix.adjugate =
      phfZeroCharmatrixAdjExplicit s := by
  classical
  have hdet : (toGLM_stabilityMatrixPHF m 0).charmatrix.det =
      (Polynomial.X : Polynomial ℂ) ^ s := by
    have := toGLM_stabilityMatrixPHF_zero_charpoly m
    rwa [Matrix.charpoly] at this
  have hne : (toGLM_stabilityMatrixPHF m 0).charmatrix.det ≠ 0 := by
    rw [hdet]
    exact pow_ne_zero _ Polynomial.X_ne_zero
  apply adjugate_eq_of_mul_eq_det_smul
  · rw [hdet]
    exact phfZeroCharmatrix_mul_adjExplicit m
  · exact hne

/-- §521 Step C.6 — Column ⟨s-1, _⟩ of the past-`h*f` charmatrix
adjugate at `z = 0` is the geometric power vector
`(1, X, X², …, X^{s-1})`.

Mirrors cycle 672's `rowYQuot_mul_X_pow_eq_RowY` step but on the
adjugate-side: this is the structural foundation for extracting an
`X^s` factor from the general (non-BDF) RowF in the upcoming
`rowFQuot_mul_X_pow_eq_RowF` lemma. -/
theorem toGLM_stabilityMatrixPHF_zero_charmatrix_adjugate_last_col
    (m : LMM s) (i : Fin s) :
    (toGLM_stabilityMatrixPHF m 0).charmatrix.adjugate i
        ⟨s - 1, by have := i.isLt; omega⟩ =
      (Polynomial.X : Polynomial ℂ) ^ (i : ℕ) := by
  rw [toGLM_stabilityMatrixPHF_zero_charmatrix_adjugate_eq m]
  exact phfZeroCharmatrixAdjExplicit_last_col s (by have := i.isLt; omega) i

/-! ### Step C.7 — General-RowF column closed forms -/

/-- §521 Step C.7 — Closed form of the β-summand of the past-`h*f`
adjugate-row entry. Routing the column ⟨s-1, _⟩ projection of the
scalar-smul `PY.charmatrix.det • PHF.charmatrix.adjugate` through cycle
674's `toGLM_stabilityMatrixPHF_zero_charmatrix_adjugate_last_col`
collapses each column entry to `PY.charpoly * X^k`, leaving the
geometric β-coefficient sum on the right. -/
theorem toGLM_stabilityCharpolyRowF_β_summand_eq
    (m : LMM s) (hs : 0 < s) :
    Matrix.vecMul
        (fun k : Fin s =>
          Polynomial.C ((m.β (Fin.castSucc k) : ℝ) : ℂ))
        ((toGLM_stabilityMatrixPY m 0).charmatrix.det •
          (toGLM_stabilityMatrixPHF m 0).charmatrix.adjugate)
        ⟨s - 1, by omega⟩
      = (toGLM_stabilityMatrixPY m 0).charpoly *
        ∑ k : Fin s,
          Polynomial.C ((m.β (Fin.castSucc k) : ℝ) : ℂ) *
            (Polynomial.X : Polynomial ℂ) ^ (k : ℕ) := by
  classical
  rw [Matrix.vecMul_smul, Pi.smul_apply, smul_eq_mul]
  rw [show (toGLM_stabilityMatrixPY m 0).charmatrix.det =
        (toGLM_stabilityMatrixPY m 0).charpoly from rfl]
  congr 1
  show ∑ k : Fin s,
        Polynomial.C ((m.β (Fin.castSucc k) : ℝ) : ℂ) *
        (toGLM_stabilityMatrixPHF m 0).charmatrix.adjugate k
          ⟨s - 1, by omega⟩
      = _
  apply Finset.sum_congr rfl
  intro k _
  rw [toGLM_stabilityMatrixPHF_zero_charmatrix_adjugate_last_col]

/-- §521 Step C.7 — Column ⟨s-1, _⟩ closed form of the α-summand of the
past-`h*f` adjugate-row entry. The matrix product
`(-PY.adj) * (-PYHF.map C) * PHF.adj` is reassociated via
`Matrix.vecMul_vecMul`, then the `PHF.adj` rightmost factor's
column ⟨s-1, _⟩ collapses to the geometric power vector `X^l` by
cycle 674's `toGLM_stabilityMatrixPHF_zero_charmatrix_adjugate_last_col`,
leaving the residual row vector
`(α-row) · (-PY.adj) · (-PYHF.map C)` paired with `X^l`. -/
theorem toGLM_stabilityCharpolyRowF_α_summand_col_eq
    (m : LMM s) (hs : 0 < s) :
    Matrix.vecMul
        (fun k : Fin s =>
          Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ))
        (-(toGLM_stabilityMatrixPY m 0).charmatrix.adjugate *
          (-(toGLM_stabilityMatrixPYHF m 0).map Polynomial.C) *
          (toGLM_stabilityMatrixPHF m 0).charmatrix.adjugate)
        ⟨s - 1, by omega⟩
      = ∑ l : Fin s,
          ( Matrix.vecMul
              (fun k =>
                Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ))
              (-(toGLM_stabilityMatrixPY m 0).charmatrix.adjugate *
                (-(toGLM_stabilityMatrixPYHF m 0).map Polynomial.C)) ) l *
          (Polynomial.X : Polynomial ℂ) ^ (l : ℕ) := by
  classical
  rw [← Matrix.vecMul_vecMul]
  show ∑ l : Fin s,
        Matrix.vecMul
            (fun k : Fin s =>
              Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ))
            (-(toGLM_stabilityMatrixPY m 0).charmatrix.adjugate *
              (-(toGLM_stabilityMatrixPYHF m 0).map Polynomial.C)) l *
          (toGLM_stabilityMatrixPHF m 0).charmatrix.adjugate l
            ⟨s - 1, by omega⟩
      = _
  apply Finset.sum_congr rfl
  intro l _
  rw [toGLM_stabilityMatrixPHF_zero_charmatrix_adjugate_last_col]

/-- §521 Step C.7 — Assembled closed form for the past-`h*f`
adjugate-row entry as the sum of two pieces:

* an α-summand expressed as a column-decomposed sum
  `∑ l, (residual) · X^l` (cycle 676's
  `toGLM_stabilityCharpolyRowF_α_summand_col_eq`); and
* a β-summand factored as `PY.charpoly · (∑ k, β_k · X^k)` (cycle
  676's `toGLM_stabilityCharpolyRowF_β_summand_eq`).

Direct chain: rewrite `toGLM_stabilityCharpolyRowF_eq_explicit` then
substitute both Step C.7 column closed forms. -/
theorem toGLM_stabilityCharpolyRowF_eq_summand_split
    (m : LMM s) (hs : 0 < s) :
    toGLM_stabilityCharpolyRowF m =
      ( ∑ l : Fin s,
          ( Matrix.vecMul
              (fun k => Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ))
              (-(toGLM_stabilityMatrixPY m 0).charmatrix.adjugate *
                (-(toGLM_stabilityMatrixPYHF m 0).map Polynomial.C)) ) l *
          (Polynomial.X : Polynomial ℂ) ^ (l : ℕ) )
      +
      (toGLM_stabilityMatrixPY m 0).charpoly *
        ∑ k : Fin s,
          Polynomial.C ((m.β (Fin.castSucc k) : ℝ) : ℂ) *
            (Polynomial.X : Polynomial ℂ) ^ (k : ℕ) := by
  rw [toGLM_stabilityCharpolyRowF_eq_explicit m hs,
      toGLM_stabilityCharpolyRowF_α_summand_col_eq m hs,
      toGLM_stabilityCharpolyRowF_β_summand_eq m hs]

/-- §521 Step C.7 sanity check — under the BDF hypothesis the assembled
closed form collapses to `0`, recovering
`toGLM_stabilityCharpolyRowF_of_bdf`. Re-export only; the proof is the
existing BDF-branch lemma. -/
theorem toGLM_stabilityCharpolyRowF_eq_summand_split_of_bdf
    (m : LMM s) (hs : 0 < s)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0) :
    toGLM_stabilityCharpolyRowF m = 0 :=
  toGLM_stabilityCharpolyRowF_of_bdf m hs hbdf

/-- §521 Step C.8 — Geometric β-coefficient polynomial used in the
β-summand of `toGLM_stabilityCharpolyRowF`. By cycle 680's
`toGLM_stabilityCharpolyRowF_eq_summand_split`, the β-summand factors as
`(toGLM_stabilityMatrixPY m 0).charpoly * rowFBetaPoly m`. -/
noncomputable def rowFBetaPoly (m : LMM s) : Polynomial ℂ :=
  ∑ k : Fin s,
    Polynomial.C ((m.β (Fin.castSucc k) : ℝ) : ℂ) *
      (Polynomial.X : Polynomial ℂ) ^ (k : ℕ)

/-- §521 Step C.8 — Restatement of `toGLM_stabilityCharpolyRowF_eq_summand_split`
with the β-summand factored as `PY.charpoly · rowFBetaPoly m`. -/
theorem toGLM_stabilityCharpolyRowF_eq_alpha_plus_PY_beta
    (m : LMM s) (hs : 0 < s) :
    toGLM_stabilityCharpolyRowF m =
      ( ∑ l : Fin s,
          ( Matrix.vecMul
              (fun k => Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ))
              (-(toGLM_stabilityMatrixPY m 0).charmatrix.adjugate *
                (-(toGLM_stabilityMatrixPYHF m 0).map Polynomial.C)) ) l *
          (Polynomial.X : Polynomial ℂ) ^ (l : ℕ) )
      +
      (toGLM_stabilityMatrixPY m 0).charpoly * rowFBetaPoly m := by
  rw [toGLM_stabilityCharpolyRowF_eq_summand_split m hs]
  rfl

/-- §521 Step C.8 — Degree bound for `rowFBetaPoly`: as a sum of
`Polynomial.C (β k) * X^k` with `k : Fin s`, the polynomial's degree is
strictly below `s`. The bound is stated in `Polynomial.degree`
(`WithBot ℕ`) form so that the empty case `s = 0` is captured by
`⊥ < (0 : WithBot ℕ)`. -/
theorem rowFBetaPoly_degree_lt (m : LMM s) :
    (rowFBetaPoly m).degree < (s : WithBot ℕ) := by
  classical
  unfold rowFBetaPoly
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr ?_
  intro k _
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
  exact_mod_cast k.isLt

/-- §521 Step C.9 — α-summand polynomial of
`toGLM_stabilityCharpolyRowF`. Mirrors cycle 682's `rowFBetaPoly`. By
`toGLM_stabilityCharpolyRowF_eq_alphaPoly_plus_PY_betaPoly`, the rank-one
row entry `toGLM_stabilityCharpolyRowF m` equals
`rowFAlphaPoly m + (toGLM_stabilityMatrixPY m 0).charpoly * rowFBetaPoly m`. -/
noncomputable def rowFAlphaPoly (m : LMM s) : Polynomial ℂ :=
  ∑ l : Fin s,
    ( Matrix.vecMul
        (fun k => Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ))
        (-(toGLM_stabilityMatrixPY m 0).charmatrix.adjugate *
          (-(toGLM_stabilityMatrixPYHF m 0).map Polynomial.C)) ) l *
      (Polynomial.X : Polynomial ℂ) ^ (l : ℕ)

/-- §521 Step C.9 — Restated `toGLM_stabilityCharpolyRowF_eq_summand_split`
with both summand polynomials named. Direct cycle 682 / cycle 680 chain. -/
theorem toGLM_stabilityCharpolyRowF_eq_alphaPoly_plus_PY_betaPoly
    (m : LMM s) (hs : 0 < s) :
    toGLM_stabilityCharpolyRowF m =
      rowFAlphaPoly m +
        (toGLM_stabilityMatrixPY m 0).charpoly * rowFBetaPoly m := by
  rw [toGLM_stabilityCharpolyRowF_eq_alpha_plus_PY_beta m hs]
  rfl

/-- §521 Step C.9 — Per-`l` residual polynomial in the α-summand
column-decomposition. Used so the degree analysis of `rowFAlphaPoly` in a
later cycle can quote a single named entry rather than re-expand the
nested `Matrix.vecMul`. -/
private noncomputable def rowFAlphaResidual (m : LMM s) : Fin s → Polynomial ℂ :=
  fun l =>
    Matrix.vecMul
        (fun k => Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ))
        (-(toGLM_stabilityMatrixPY m 0).charmatrix.adjugate *
          (-(toGLM_stabilityMatrixPYHF m 0).map Polynomial.C)) l

/-- §521 Step C.9 — `rowFAlphaPoly` factored through `rowFAlphaResidual`.
Trivial: closes by `unfold rowFAlphaPoly rowFAlphaResidual; rfl`. -/
private theorem rowFAlphaPoly_eq_residual_sum (m : LMM s) :
    rowFAlphaPoly m =
      ∑ l : Fin s,
        rowFAlphaResidual m l * (Polynomial.X : Polynomial ℂ) ^ (l : ℕ) := by
  unfold rowFAlphaPoly rowFAlphaResidual
  rfl

/-- §521 Step C.10 — Inline helper: each entry of the adjugate of a
characteristic matrix has `natDegree ≤ n` when the matrix has size `n+1`.
Standard fact: each `(charmatrix A).adjugate i j` is the determinant of an
`updateRow` of `(charmatrix A)`; row `j` is replaced by a degree-0 vector,
the remaining `n` rows have degree-`≤ 1` entries, hence the determinant
expansion has total degree `≤ n`. -/
private lemma charmatrix_adjugate_natDegree_le
    {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (i j : Fin (n+1)) :
    (A.charmatrix.adjugate i j).natDegree ≤ n := by
  classical
  rw [Matrix.adjugate_apply, Matrix.det_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun σ _ => ?_⟩
  refine (Polynomial.natDegree_smul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc ∑ k : Fin (n+1),
        ((A.charmatrix.updateRow j (Pi.single i (1 : Polynomial ℂ))) (σ k) k).natDegree
      ≤ ∑ k : Fin (n+1), if σ k = j then 0 else 1 := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          by_cases h : σ k = j
          · rw [if_pos h, Matrix.updateRow_apply, if_pos h]
            by_cases hki : k = i
            · subst hki; rw [Pi.single_eq_same]; exact Polynomial.natDegree_one.le
            · rw [Pi.single_eq_of_ne hki]; exact Polynomial.natDegree_zero.le
          · rw [if_neg h, Matrix.updateRow_apply, if_neg h]
            refine (Matrix.charmatrix_apply_natDegree_le _ _).trans ?_
            split_ifs <;> simp
    _ = n := by
          rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
              smul_eq_mul, mul_one]
          have hcard :
              (Finset.univ.filter (fun k : Fin (n+1) => σ k ≠ j)).card = n := by
            have h : (Finset.univ.filter (fun k : Fin (n+1) => σ k ≠ j))
                = Finset.univ.erase (σ.symm j) := by
              ext k
              simp [Finset.mem_filter, Finset.mem_erase, Equiv.eq_symm_apply (e := σ)]
            rw [h, Finset.card_erase_of_mem (Finset.mem_univ _),
                Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]
          exact hcard

/-- §521 Step C.10 — Degree wrapper around `charmatrix_adjugate_natDegree_le`. -/
private lemma charmatrix_adjugate_degree_lt
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (A.charmatrix.adjugate i j).degree < (n : WithBot ℕ) := by
  rcases n with _ | n
  · exact i.elim0
  refine Polynomial.degree_le_natDegree.trans_lt ?_
  exact_mod_cast Nat.lt_succ_of_le (charmatrix_adjugate_natDegree_le A i j)

/-- §521 Step C.10 — Inner helper: each entry of
`(-charmatrix.adjugate) * (-PYHF.map C)` has degree `< s`.  Each term of
the matrix product is `(-adj) * (-C ..)`, both of which have known degree
bounds: `adj` entry-wise `< s` (via `charmatrix_adjugate_degree_lt`),
`C ..` entry-wise `≤ 0`. -/
private theorem rowFAlphaResidual_matrix_entry_degree_lt
    (m : LMM s) (k l : Fin s) :
    ((-(toGLM_stabilityMatrixPY m 0).charmatrix.adjugate *
        (-(toGLM_stabilityMatrixPYHF m 0).map Polynomial.C)) k l).degree
        < (s : WithBot ℕ) := by
  classical
  rw [Matrix.mul_apply]
  refine (Polynomial.degree_sum_le _ _).trans_lt ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr ?_
  intro j _
  refine (Polynomial.degree_mul_le _ _).trans_lt ?_
  rw [Matrix.neg_apply, Polynomial.degree_neg,
      Matrix.neg_apply, Matrix.map_apply, Polynomial.degree_neg]
  have hadj : ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k j).degree
      < (s : WithBot ℕ) := charmatrix_adjugate_degree_lt _ _ _
  have hCB : (Polynomial.C ((toGLM_stabilityMatrixPYHF m 0) j l)).degree
      ≤ (0 : WithBot ℕ) := Polynomial.degree_C_le
  calc ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k j).degree
        + (Polynomial.C ((toGLM_stabilityMatrixPYHF m 0) j l)).degree
      ≤ ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k j).degree + 0 :=
          add_le_add (le_refl _) hCB
    _ = ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k j).degree := by simp
    _ < (s : WithBot ℕ) := hadj

/-- §521 Step C.10 — Degree bound for `rowFAlphaResidual m l`: each residual
entry is the `l`-th component of a `Matrix.vecMul` whose row is
`Polynomial.C`-valued (degree ≤ 0) and whose matrix factor is a product of
`(charmatrix.adjugate)` (each entry of degree `< s`) with a
`Polynomial.C`-valued matrix.  Hence the residual has degree `< s` (the
`s = 0` case is captured by `⊥ < (0 : WithBot ℕ)`). -/
private theorem rowFAlphaResidual_degree_lt (m : LMM s) (l : Fin s) :
    (rowFAlphaResidual m l).degree < (s : WithBot ℕ) := by
  classical
  unfold rowFAlphaResidual
  rw [Matrix.vecMul_eq_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine (Polynomial.degree_sum_le _ _).trans_lt ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr ?_
  intro k _
  refine (Polynomial.degree_mul_le _ _).trans_lt ?_
  have hC : (Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ)).degree ≤ (0 : WithBot ℕ) :=
    Polynomial.degree_C_le
  have hM := rowFAlphaResidual_matrix_entry_degree_lt m k l
  calc (Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ)).degree
        + ((-(toGLM_stabilityMatrixPY m 0).charmatrix.adjugate *
            (-(toGLM_stabilityMatrixPYHF m 0).map Polynomial.C)) k l).degree
      ≤ 0 + ((-(toGLM_stabilityMatrixPY m 0).charmatrix.adjugate *
            (-(toGLM_stabilityMatrixPYHF m 0).map Polynomial.C)) k l).degree :=
          add_le_add hC (le_refl _)
    _ = ((-(toGLM_stabilityMatrixPY m 0).charmatrix.adjugate *
            (-(toGLM_stabilityMatrixPYHF m 0).map Polynomial.C)) k l).degree := by
          rw [zero_add]
    _ < (s : WithBot ℕ) := hM

/-- §521 Step C.10 — Degree bound for `rowFAlphaPoly`. As a sum of
`rowFAlphaResidual m l * X^l` over `l : Fin s`, with each residual of
degree `< s` and `X^l` of degree `≤ l < s`, the polynomial's degree is
strictly below `2 * s - 1` (the `s = 0` case is captured by
`⊥ < (2 * 0 - 1 : WithBot ℕ)` which holds vacuously since the empty sum
has degree `⊥`). -/
theorem rowFAlphaPoly_degree_lt (m : LMM s) :
    (rowFAlphaPoly m).degree < ((2 * s - 1 : ℕ) : WithBot ℕ) := by
  classical
  rw [rowFAlphaPoly_eq_residual_sum]
  refine (Polynomial.degree_sum_le _ _).trans_lt ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr ?_
  intro l _
  refine (Polynomial.degree_mul_le _ _).trans_lt ?_
  rw [Polynomial.degree_X_pow]
  have hres : (rowFAlphaResidual m l).degree < (s : WithBot ℕ) :=
    rowFAlphaResidual_degree_lt m l
  -- (rowFAlphaResidual m l).degree + ↑l < ↑(s + l) ≤ ↑(2*s - 1)
  have hl : (l : ℕ) < s := l.isLt
  have hs : 0 < s := lt_of_le_of_lt (Nat.zero_le _) hl
  calc (rowFAlphaResidual m l).degree + ((l : ℕ) : WithBot ℕ)
      < (s : WithBot ℕ) + ((l : ℕ) : WithBot ℕ) := by
        exact WithBot.add_lt_add_right (WithBot.coe_ne_bot) hres
    _ = ((s + (l : ℕ) : ℕ) : WithBot ℕ) := by push_cast; rfl
    _ ≤ ((2 * s - 1 : ℕ) : WithBot ℕ) := by
        exact_mod_cast (by omega : s + (l : ℕ) ≤ 2 * s - 1)

/-- §521 Step C.11 — Fully-named consolidated form of
`toGLM_stabilityMatrix_charpoly_explicit`. Substitutes:
* `(toGLM_stabilityMatrixPHF m 0).charpoly = X^s`,
* `toGLM_stabilityCharpolyRowY m = rowYQuot m * X^s`,
* `toGLM_stabilityCharpolyRowF m =
     rowFAlphaPoly m + (toGLM_stabilityMatrixPY m 0).charpoly *
                       rowFBetaPoly m`,
into the cycle 666 explicit form. The result mentions only the named
polynomials `rowYQuot`, `rowFAlphaPoly`, `rowFBetaPoly`,
`(toGLM_stabilityMatrixPY m 0).charpoly`, and `Polynomial.X ^ s`. -/
theorem toGLM_stabilityMatrix_charpoly_named
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (m.toGLM.stabilityMatrix z).charpoly =
      (toGLM_stabilityMatrixPY m 0).charpoly *
          (Polynomial.X : Polynomial ℂ) ^ s -
        Polynomial.C (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
          ( rowYQuot m * (Polynomial.X : Polynomial ℂ) ^ s *
              Polynomial.C (z * ((m.β (Fin.last s) : ℝ) : ℂ))
          + ( rowFAlphaPoly m +
                (toGLM_stabilityMatrixPY m 0).charpoly *
                  rowFBetaPoly m ) *
              Polynomial.C z ) := by
  rw [toGLM_stabilityMatrix_charpoly_explicit m hz hs,
      toGLM_stabilityMatrixPHF_zero_charpoly,
      ← rowYQuot_mul_X_pow_eq_RowY m hs,
      toGLM_stabilityCharpolyRowF_eq_alphaPoly_plus_PY_betaPoly m hs]

/-- §521 Step C.11 stretch — Combined degree bound for the α + PY·β
named row decomposition of `toGLM_stabilityCharpolyRowF`. Used in the
eventual iff bridge to bound the rank-one correction polynomial. -/
theorem rowFNamedSum_degree_lt (m : LMM s) :
    ( rowFAlphaPoly m +
        (toGLM_stabilityMatrixPY m 0).charpoly * rowFBetaPoly m ).degree
      < ((2 * s : ℕ) : WithBot ℕ) := by
  refine (Polynomial.degree_add_le _ _).trans_lt ?_
  refine max_lt ?_ ?_
  · -- α-term: degree < 2*s - 1 ≤ 2*s
    refine (rowFAlphaPoly_degree_lt m).trans_le ?_
    exact_mod_cast (by omega : (2 * s - 1 : ℕ) ≤ 2 * s)
  · -- PY·β term
    refine (Polynomial.degree_mul_le _ _).trans_lt ?_
    have hβ : (rowFBetaPoly m).degree < (s : WithBot ℕ) := rowFBetaPoly_degree_lt m
    have hPne : (toGLM_stabilityMatrixPY m 0).charpoly ≠ 0 :=
      (Matrix.charpoly_monic _).ne_zero
    have hPdeg : (toGLM_stabilityMatrixPY m 0).charpoly.degree = (s : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree hPne, Matrix.charpoly_natDegree_eq_dim]
      simp
    rw [hPdeg]
    have h2s : ((2 * s : ℕ) : WithBot ℕ) = (s : WithBot ℕ) + (s : WithBot ℕ) := by
      push_cast; ring
    rw [h2s]
    exact WithBot.add_lt_add_left WithBot.coe_ne_bot hβ

/-- §521 Step C.12a — `D · charpoly = X^s · (D · PY(0).charpoly) − residual`.

This lifts the BDF-only headline of cycle 668 to a general `s`-step
LMM by absorbing the cycle 688 named consolidated charpoly identity.
Multiplying the named form by `Polynomial.C D` collapses the rank-one
`Polynomial.C (1/D)` denominator to leave the residual as a clean
subtraction with no division.

After the cycle 692 redefinition of `activeStabilityPolyPoly` (which
now uses `PY(0)`), this identity is repackaged as
`D_mul_toGLM_charpoly_eq_X_pow_mul_active_plus_residual`. -/
theorem D_mul_toGLM_charpoly_eq_X_pow_mul_PY0_plus_residual
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    Polynomial.C (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        (m.toGLM.stabilityMatrix z).charpoly =
      (Polynomial.X : Polynomial ℂ) ^ s *
          (Polynomial.C (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
            (toGLM_stabilityMatrixPY m 0).charpoly) -
        ( rowYQuot m * (Polynomial.X : Polynomial ℂ) ^ s *
            Polynomial.C (z * ((m.β (Fin.last s) : ℝ) : ℂ))
        + ( rowFAlphaPoly m +
              (toGLM_stabilityMatrixPY m 0).charpoly *
                rowFBetaPoly m ) *
            Polynomial.C z ) := by
  rw [toGLM_stabilityMatrix_charpoly_named m hz hs]
  have hCD :
      Polynomial.C (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        Polynomial.C (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) = 1 := by
    rw [← Polynomial.C_mul, mul_one_div, div_self hz, Polynomial.C_1]
  linear_combination
    -hCD * ( rowYQuot m * (Polynomial.X : Polynomial ℂ) ^ s *
              Polynomial.C (z * ((m.β (Fin.last s) : ℝ) : ℂ))
            + ( rowFAlphaPoly m +
                  (toGLM_stabilityMatrixPY m 0).charpoly * rowFBetaPoly m ) *
                Polynomial.C z )

/-- §521 Step C.12 — General `s`-step LMM headline:
`D · charpoly = X^s · activeStabilityPolyPoly − residual` with the
matching residual degree bound supplied by `charpoly_residual_degree_lt`.
Direct restatement of `D_mul_toGLM_charpoly_eq_X_pow_mul_PY0_plus_residual`
under the cycle 692 redefinition of `activeStabilityPolyPoly` (which now
unfolds to `D • PY(0).charpoly`). -/
theorem D_mul_toGLM_charpoly_eq_X_pow_mul_active_plus_residual
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    Polynomial.C (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        (m.toGLM.stabilityMatrix z).charpoly =
      (Polynomial.X : Polynomial ℂ) ^ s * activeStabilityPolyPoly m z -
        ( rowYQuot m * (Polynomial.X : Polynomial ℂ) ^ s *
            Polynomial.C (z * ((m.β (Fin.last s) : ℝ) : ℂ))
        + ( rowFAlphaPoly m +
              (toGLM_stabilityMatrixPY m 0).charpoly *
                rowFBetaPoly m ) *
            Polynomial.C z ) := by
  rw [D_mul_toGLM_charpoly_eq_X_pow_mul_PY0_plus_residual m hz hs]
  unfold activeStabilityPolyPoly
  rw [Polynomial.smul_eq_C_mul]

/-- §521 Step C.12 helper — Degree bound for `rowYQuot`. The defining
determinant has one row replaced by a `Polynomial.C`-valued row (degree
≤ 0); the remaining `s - 1` rows are charmatrix rows (entry-wise
natDegree ≤ 1). The expansion `Matrix.det_apply` then yields total
natDegree `≤ s - 1`, hence degree `< s`. The `s = 0` case is captured
by `(0 : Polynomial ℂ).degree = ⊥ < 0`. -/
private theorem rowYQuot_natDegree_le (m : LMM s) :
    (rowYQuot m).natDegree ≤ s - 1 := by
  classical
  unfold rowYQuot
  by_cases hs0 : s = 0
  · subst hs0
    rw [dif_pos rfl]
    simp
  · rw [dif_neg hs0]
    have hspos : 0 < s := Nat.pos_of_ne_zero hs0
    rw [Matrix.det_apply]
    refine (Polynomial.natDegree_sum_le _ _).trans ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le _, fun σ _ => ?_⟩
    refine (Polynomial.natDegree_smul_le _ _).trans ?_
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc ∑ k : Fin s,
            (((toGLM_stabilityMatrixPY m 0).charmatrix.updateRow
                ⟨s - 1, by omega⟩
                (fun k' => Polynomial.C ((-m.α (Fin.castSucc k') : ℝ) : ℂ)))
              (σ k) k).natDegree
        ≤ ∑ k : Fin s, if σ k = ⟨s - 1, by omega⟩ then 0 else 1 := by
            refine Finset.sum_le_sum (fun k _ => ?_)
            by_cases h : σ k = ⟨s - 1, by omega⟩
            · rw [if_pos h, Matrix.updateRow_apply, if_pos h]
              simp [Polynomial.natDegree_C]
            · rw [if_neg h, Matrix.updateRow_apply, if_neg h]
              refine (Matrix.charmatrix_apply_natDegree_le _ _).trans ?_
              split_ifs <;> simp
      _ = s - 1 := by
            rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
                smul_eq_mul, mul_one]
            have h : (Finset.univ.filter
                        (fun k : Fin s => σ k ≠ ⟨s - 1, by omega⟩))
                  = Finset.univ.erase (σ.symm ⟨s - 1, by omega⟩) := by
              ext k
              simp [Finset.mem_filter, Finset.mem_erase,
                    Equiv.eq_symm_apply (e := σ)]
            rw [h, Finset.card_erase_of_mem (Finset.mem_univ _),
                Finset.card_univ, Fintype.card_fin]

/-- §521 Step C.12 helper — Degree wrapper around `rowYQuot_natDegree_le`. -/
theorem rowYQuot_degree_lt (m : LMM s) :
    (rowYQuot m).degree < (s : WithBot ℕ) := by
  classical
  by_cases hs0 : s = 0
  · subst hs0
    unfold rowYQuot
    rw [dif_pos rfl, Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  · have hspos : 0 < s := Nat.pos_of_ne_zero hs0
    refine Polynomial.degree_le_natDegree.trans_lt ?_
    have hnd : (rowYQuot m).natDegree ≤ s - 1 := rowYQuot_natDegree_le m
    exact_mod_cast Nat.lt_of_le_of_lt hnd (by omega : s - 1 < s)

/-- §521 Step C.12b — Combined degree bound for the full residual on the
RHS of `D_mul_toGLM_charpoly_eq_X_pow_mul_PY0_plus_residual`. The residual
splits into two summands:

* `rowYQuot · X^s · C(z β_last)`, with `rowYQuot` of degree `< s`,
  `X^s` of degree `s`, and `C` factor of degree `≤ 0`, total `< 2 s`.
* `(rowFAlphaPoly + PY(0).charpoly · rowFBetaPoly) · C z`, with the
  inner sum bounded by `rowFNamedSum_degree_lt` (`< 2 s`) and `C z` of
  degree `≤ 0`, total `< 2 s`. -/
theorem charpoly_residual_degree_lt
    (m : LMM s) (z : ℂ) :
    ( rowYQuot m * (Polynomial.X : Polynomial ℂ) ^ s *
        Polynomial.C (z * ((m.β (Fin.last s) : ℝ) : ℂ))
    + ( rowFAlphaPoly m +
          (toGLM_stabilityMatrixPY m 0).charpoly *
            rowFBetaPoly m ) *
        Polynomial.C z ).degree < ((2 * s : ℕ) : WithBot ℕ) := by
  refine (Polynomial.degree_add_le _ _).trans_lt ?_
  refine max_lt ?_ ?_
  · -- rowYQuot * X^s * C(zβ): degree < s + s = 2s.
    refine (Polynomial.degree_mul_le _ _).trans_lt ?_
    have hC : (Polynomial.C (z * ((m.β (Fin.last s) : ℝ) : ℂ))).degree
        ≤ (0 : WithBot ℕ) := Polynomial.degree_C_le
    have hY : (rowYQuot m * (Polynomial.X : Polynomial ℂ) ^ s).degree
        < ((2 * s : ℕ) : WithBot ℕ) := by
      refine (Polynomial.degree_mul_le _ _).trans_lt ?_
      rw [Polynomial.degree_X_pow]
      have hYQ : (rowYQuot m).degree < (s : WithBot ℕ) := rowYQuot_degree_lt m
      have h2s : ((2 * s : ℕ) : WithBot ℕ) = (s : WithBot ℕ) + (s : WithBot ℕ) := by
        push_cast; ring
      rw [h2s]
      exact WithBot.add_lt_add_right (WithBot.coe_ne_bot) hYQ
    calc (rowYQuot m * (Polynomial.X : Polynomial ℂ) ^ s).degree
            + (Polynomial.C (z * ((m.β (Fin.last s) : ℝ) : ℂ))).degree
        ≤ (rowYQuot m * (Polynomial.X : Polynomial ℂ) ^ s).degree + 0 :=
            add_le_add (le_refl _) hC
      _ = (rowYQuot m * (Polynomial.X : Polynomial ℂ) ^ s).degree := by simp
      _ < ((2 * s : ℕ) : WithBot ℕ) := hY
  · -- (rowFAlphaPoly + PY * rowFBetaPoly) * C z: degree < 2s.
    refine (Polynomial.degree_mul_le _ _).trans_lt ?_
    have hC : (Polynomial.C z).degree ≤ (0 : WithBot ℕ) := Polynomial.degree_C_le
    have hsum := rowFNamedSum_degree_lt m
    calc ( rowFAlphaPoly m +
            (toGLM_stabilityMatrixPY m 0).charpoly * rowFBetaPoly m ).degree
            + (Polynomial.C z).degree
        ≤ ( rowFAlphaPoly m +
              (toGLM_stabilityMatrixPY m 0).charpoly * rowFBetaPoly m ).degree
                + 0 :=
            add_le_add (le_refl _) hC
      _ = ( rowFAlphaPoly m +
              (toGLM_stabilityMatrixPY m 0).charpoly * rowFBetaPoly m ).degree := by simp
      _ < ((2 * s : ℕ) : WithBot ℕ) := hsum

/-- §521 Step C.13a — Closed form for the PY-block charpoly at `z = 0`.
Specialisation of `toGLM_stabilityMatrixPY_charpoly` (Stability.lean:864)
at `z = 0`, where the denominator `1 - 0 * β_last = 1` collapses the
`Polynomial.C` divisor to `1`. -/
theorem toGLM_stabilityMatrixPY_zero_charpoly_eq (m : LMM s) :
    (toGLM_stabilityMatrixPY m 0).charpoly =
      (Polynomial.X : Polynomial ℂ) ^ s -
        ∑ l : Fin s,
          Polynomial.C (((-m.α (Fin.castSucc l) : ℝ) : ℂ)) *
            Polynomial.X ^ (l : ℕ) := by
  have hz : (1 : ℂ) - 0 * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0 := by
    simp
  rw [toGLM_stabilityMatrixPY_charpoly m 0 hz]
  congr 1
  refine Finset.sum_congr rfl (fun l _ => ?_)
  congr 2
  field_simp
  ring

/-- §521 Step C.13b — General bridge between the active stability
polynomial and the textbook `stabilityPolyPoly`. They differ by a
`z`-times-correction term that vanishes coefficient-by-coefficient
when `β(castSucc l) = β_last · α(castSucc l)` (in particular under
BDF, where every `β(castSucc l) = 0` and the correction collapses to
`-C(z β_last) · ∑ C(α(castSucc l)) X^l`). -/
theorem activeStabilityPolyPoly_eq_stabilityPolyPoly_add_correction
    (m : LMM s) (z : ℂ) :
    activeStabilityPolyPoly m z =
      m.stabilityPolyPoly z +
        Polynomial.C z *
          ∑ l : Fin s,
            Polynomial.C
                (((m.β l.castSucc : ℝ) : ℂ) -
                  ((m.β (Fin.last s) : ℝ) : ℂ) *
                    ((m.α l.castSucc : ℝ) : ℂ)) *
              Polynomial.X ^ (l : ℕ) := by
  have hα_last : ((m.α (Fin.last s) : ℝ) : ℂ) = 1 := by
    rw [m.normalized]; push_cast; rfl
  -- Per-summand identity in scalars: this is the load-bearing computation.
  have hsum_eq :
      ∀ l : Fin s,
        Polynomial.C (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
            (Polynomial.C (((-m.α l.castSucc : ℝ) : ℂ)) *
              Polynomial.X ^ (l : ℕ)) =
          -(Polynomial.C
                (((m.α l.castSucc : ℝ) : ℂ) -
                  z * ((m.β l.castSucc : ℝ) : ℂ)) *
              Polynomial.X ^ (l : ℕ)) -
            Polynomial.C z *
              (Polynomial.C
                  (((m.β l.castSucc : ℝ) : ℂ) -
                    ((m.β (Fin.last s) : ℝ) : ℂ) *
                      ((m.α l.castSucc : ℝ) : ℂ)) *
                Polynomial.X ^ (l : ℕ)) := by
    intro l
    rw [← mul_assoc, ← Polynomial.C_mul, ← mul_assoc, ← Polynomial.C_mul,
      ← neg_mul, ← Polynomial.C_neg, ← sub_mul, ← Polynomial.C_sub]
    congr 2
    push_cast
    ring
  -- Now expand both sides and match.
  unfold activeStabilityPolyPoly stabilityPolyPoly
  rw [toGLM_stabilityMatrixPY_zero_charpoly_eq m, Polynomial.smul_eq_C_mul,
    Fin.sum_univ_castSucc (f := fun j : Fin (s + 1) =>
      Polynomial.C (((m.α j : ℝ) : ℂ) - z * ((m.β j : ℝ) : ℂ)) *
        Polynomial.X ^ (j : ℕ))]
  rw [hα_last, Fin.val_last]
  simp only [Fin.val_castSucc]
  rw [mul_sub, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun l _ => hsum_eq l)]
  rw [Finset.mul_sum]
  -- Goal:
  --   C(D) * X^s - ∑_l (-A_l - B_l) = ∑_l A_l + C(D)*X^s + ∑_l B_l
  rw [Finset.sum_congr rfl (fun (l : Fin s) _ =>
        show -(Polynomial.C (((m.α l.castSucc : ℝ) : ℂ) -
                z * ((m.β l.castSucc : ℝ) : ℂ)) * Polynomial.X ^ (l : ℕ)) -
            Polynomial.C z *
              (Polynomial.C (((m.β l.castSucc : ℝ) : ℂ) -
                  ((m.β (Fin.last s) : ℝ) : ℂ) *
                    ((m.α l.castSucc : ℝ) : ℂ)) *
                Polynomial.X ^ (l : ℕ)) =
          -(Polynomial.C (((m.α l.castSucc : ℝ) : ℂ) -
                z * ((m.β l.castSucc : ℝ) : ℂ)) * Polynomial.X ^ (l : ℕ) +
            Polynomial.C z *
              (Polynomial.C (((m.β l.castSucc : ℝ) : ℂ) -
                  ((m.β (Fin.last s) : ℝ) : ℂ) *
                    ((m.α l.castSucc : ℝ) : ℂ)) *
                Polynomial.X ^ (l : ℕ))) from by ring)]
  rw [Finset.sum_neg_distrib, sub_neg_eq_add]
  rw [show ∀ (f g : Fin s → Polynomial ℂ),
        ∑ l, (f l + g l) = (∑ l, f l) + ∑ l, g l from
      fun _ _ => Finset.sum_add_distrib]
  ring

/-- §521 Step C.14 — General `s`-step LMM headline in textbook form.
`D · charpoly = X^s · stabilityPolyPoly + X^s · C(z) · correction
                  − residual`, obtained by feeding the cycle 696
bridge `activeStabilityPolyPoly_eq_stabilityPolyPoly_add_correction`
into the cycle 690 active-form headline
`D_mul_toGLM_charpoly_eq_X_pow_mul_active_plus_residual`. The
correction sum vanishes coefficient-by-coefficient when
`β(castSucc l) = β_last · α(castSucc l)` (in particular under BDF),
recovering the cycle 643 BDF headline
`D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_of_bdf`. -/
theorem D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_plus_residual
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    Polynomial.C (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        (m.toGLM.stabilityMatrix z).charpoly =
      (Polynomial.X : Polynomial ℂ) ^ s * m.stabilityPolyPoly z
        + (Polynomial.X : Polynomial ℂ) ^ s *
            ( Polynomial.C z *
                ∑ l : Fin s,
                  Polynomial.C
                      (((m.β l.castSucc : ℝ) : ℂ) -
                        ((m.β (Fin.last s) : ℝ) : ℂ) *
                          ((m.α l.castSucc : ℝ) : ℂ)) *
                    Polynomial.X ^ (l : ℕ) )
        - ( rowYQuot m * (Polynomial.X : Polynomial ℂ) ^ s *
              Polynomial.C (z * ((m.β (Fin.last s) : ℝ) : ℂ))
          + ( rowFAlphaPoly m +
                (toGLM_stabilityMatrixPY m 0).charpoly *
                  rowFBetaPoly m ) *
              Polynomial.C z ) := by
  rw [D_mul_toGLM_charpoly_eq_X_pow_mul_active_plus_residual m hz hs,
      activeStabilityPolyPoly_eq_stabilityPolyPoly_add_correction m z]
  ring

/-- §521 Step C.15 — BDF consistency check between the cycle 698 general
LMM textbook headline and the cycle 643 BDF headline. The "extra"
`X^s · C(z) · correction − residual` terms in the general identity must
collapse to zero under BDF; equivalently, the residual equals the
`X^s · C(z) · correction` summand under BDF. Direct subtraction of the
two headlines. -/
theorem residual_eq_X_pow_mul_correction_of_bdf
    (m : LMM s) {z : ℂ}
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    rowYQuot m * (Polynomial.X : Polynomial ℂ) ^ s *
        Polynomial.C (z * ((m.β (Fin.last s) : ℝ) : ℂ))
      + ( rowFAlphaPoly m +
            (toGLM_stabilityMatrixPY m 0).charpoly *
              rowFBetaPoly m ) *
          Polynomial.C z
    =
    (Polynomial.X : Polynomial ℂ) ^ s *
      ( Polynomial.C z *
          ∑ l : Fin s,
            Polynomial.C
                (((m.β l.castSucc : ℝ) : ℂ) -
                  ((m.β (Fin.last s) : ℝ) : ℂ) *
                    ((m.α l.castSucc : ℝ) : ℂ)) *
              Polynomial.X ^ (l : ℕ) ) := by
  have hgen :=
    D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_plus_residual m hz hs
  have hbd :=
    D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_of_bdf m z hbdf hz
  linear_combination hgen - hbd

/-- §521 Step C.16 — Scalar evaluation of the cycle 698 textbook
headline at an arbitrary complex point `ξ`. Distributes
`Polynomial.eval ξ` over the polynomial identity, exposing the
matrix charpoly evaluation in terms of the textbook scalar
stability function. -/
theorem D_mul_toGLM_charpoly_eval_eq
    (m : LMM s) {z : ℂ} (ξ : ℂ)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval ξ =
      ξ^s * (m.stabilityPolyPoly z).eval ξ
        + ξ^s * (z *
            ∑ l : Fin s,
              ( ((m.β l.castSucc : ℝ) : ℂ)
                  - ((m.β (Fin.last s) : ℝ) : ℂ) *
                    ((m.α l.castSucc : ℝ) : ℂ) ) * ξ^(l : ℕ))
        - ( (rowYQuot m).eval ξ * ξ^s *
              (z * ((m.β (Fin.last s) : ℝ) : ℂ))
          + ( (rowFAlphaPoly m).eval ξ +
                ((toGLM_stabilityMatrixPY m 0).charpoly).eval ξ *
                  (rowFBetaPoly m).eval ξ ) * z ) := by
  have h :=
    D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_plus_residual m hz hs
  have := congrArg (Polynomial.eval ξ) h
  simpa [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_finset_sum] using this

/-- §521 Step C.17 — Under BDF, for every `ξ ≠ 0` and every `z` with
non-zero denominator `D = 1 - z·β_last`, the GLM stability-matrix
characteristic polynomial vanishes at `ξ` iff the textbook scalar
stability polynomial `stabilityPolyPoly z` vanishes at `ξ`. The
non-zero hypothesis on `ξ` discards the `X^s` factor on the RHS of
`D · charpoly = X^s · stabilityPolyPoly`. Direct evaluation of the
cycle 643 BDF headline at `ξ`. -/
theorem toGLM_charpoly_eval_eq_zero_iff_stabilityPoly_of_bdf
    (m : LMM s) {z : ℂ} (ξ : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0)
    (hξ : ξ ≠ 0) :
    ((m.toGLM.stabilityMatrix z).charpoly).eval ξ = 0 ↔
      (m.stabilityPolyPoly z).eval ξ = 0 := by
  have h := D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_of_bdf
              m z hbdf hz
  have heval := congrArg (Polynomial.eval ξ) h
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X] at heval
  have hξs : ξ ^ s ≠ 0 := pow_ne_zero _ hξ
  constructor
  · intro hcp
    rw [hcp, mul_zero] at heval
    exact (mul_eq_zero.mp heval.symm).resolve_left hξs
  · intro hsp
    rw [hsp, mul_zero] at heval
    exact (mul_eq_zero.mp heval).resolve_left hz

/-- §521 Step C.17 contrapositive — Under BDF, the GLM matrix charpoly
is non-vanishing at every non-zero `ξ` iff the textbook scalar
stability polynomial is non-vanishing at every non-zero `ξ`. Useful
form for the unit-disk root-counting argument that drives
`LMM.toGLM_isAStable_iff`. -/
theorem toGLM_charpoly_eval_ne_zero_iff_stabilityPoly_of_bdf
    (m : LMM s) {z : ℂ} (ξ : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0)
    (hξ : ξ ≠ 0) :
    ((m.toGLM.stabilityMatrix z).charpoly).eval ξ ≠ 0 ↔
      (m.stabilityPolyPoly z).eval ξ ≠ 0 :=
  (toGLM_charpoly_eval_eq_zero_iff_stabilityPoly_of_bdf
     m ξ hbdf hz hξ).not

/-- §521 Step C.18 — Under BDF, with `s ≥ 1` and non-zero denominator
`D = 1 - z β_last`, the GLM stability-matrix characteristic polynomial
vanishes at `ξ = 0`. This is the boundary case excluded from Step C.17
(cycle 702) and pins down the spurious-root structure of the BDF
charpoly: every zero of `(m.toGLM.stabilityMatrix z).charpoly` other
than `ξ = 0` is a zero of `m.stabilityPolyPoly z`. Direct evaluation of
the cycle 643 BDF headline `D · charpoly = X^s · stabilityPolyPoly` at
`ξ = 0`, where `X^s` collapses to `0^s = 0` for `s ≥ 1`. -/
theorem toGLM_charpoly_eval_zero_eq_zero_of_bdf
    (m : LMM s) {z : ℂ}
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0)
    (hs : 0 < s) :
    ((m.toGLM.stabilityMatrix z).charpoly).eval 0 = 0 := by
  have h := D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_of_bdf
              m z hbdf hz
  have heval := congrArg (Polynomial.eval (0 : ℂ)) h
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X] at heval
  rw [zero_pow hs.ne', zero_mul] at heval
  exact (mul_eq_zero.mp heval).resolve_left hz

/-- §521 Step C.19 — Under BDF, with `s ≥ 1` (from `[NeZero s]`) and
non-zero denominator `D = 1 - z β_last`, the GLM stability-matrix
characteristic polynomial vanishes at `ξ` iff `ξ = 0` or
`m.stabilityPolyPoly z` vanishes at `ξ`. Combines Step C.17 (cycle 702)
non-zero-roots scalar bridge and Step C.18 (cycle 704) `ξ = 0` boundary
case into a unified eval-form iff with no side condition on `ξ`.
Mirrors the IsRoot-form `toGLM_stabilityMatrix_eigenvalue_iff_of_bdf`
in scalar evaluation form. -/
theorem toGLM_charpoly_eval_eq_zero_iff_of_bdf [NeZero s]
    (m : LMM s) {z : ℂ} (ξ : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) :
    ((m.toGLM.stabilityMatrix z).charpoly).eval ξ = 0 ↔
      ξ = 0 ∨ (m.stabilityPolyPoly z).eval ξ = 0 := by
  rw [← Polynomial.IsRoot.def,
      toGLM_stabilityMatrix_eigenvalue_iff_of_bdf m z hbdf hz,
      ← stabilityPolyPoly_eval]

/-- §521 Step C.20 — Eval-form contrapositive of the unified BDF iff
(cycle 706 / Step C.19). The GLM stability-matrix charpoly is non-zero
at `ξ` iff `ξ ≠ 0` AND the textbook scalar stability polynomial is
non-zero at `ξ`. This is the De Morgan dual of Step C.19 and the
natural input to the unit-disk root-counting argument that drives
`LMM.toGLM_isAStable_iff` for general BDFs. -/
theorem toGLM_charpoly_eval_ne_zero_iff_of_bdf [NeZero s]
    (m : LMM s) {z : ℂ} (ξ : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) :
    ((m.toGLM.stabilityMatrix z).charpoly).eval ξ ≠ 0 ↔
      ξ ≠ 0 ∧ (m.stabilityPolyPoly z).eval ξ ≠ 0 := by
  rw [Ne, toGLM_charpoly_eval_eq_zero_iff_of_bdf m ξ hbdf hz, not_or]

/-- §521 Step D.1 — General (non-BDF) ξ = 0 evaluation of the cycle 698
textbook headline. With `s ≥ 1`, the three `X^s · …` summands collapse,
leaving a closed form for the constant term `D · charpoly(0)` purely
in terms of the `rowFAlphaPoly`, `rowFBetaPoly`, and `PY(0).charpoly`
evaluators at zero. Under BDF this constant collapses further to zero
(cycle 704 / Step C.18) because both `rowFAlphaPoly` and `rowFBetaPoly`
vanish; the general identity isolates exactly which terms could
contribute a non-spurious ξ = 0 root for non-BDF methods. -/
theorem D_mul_toGLM_charpoly_eval_zero_eq
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 0 =
      - ( (rowFAlphaPoly m).eval 0
            + ((toGLM_stabilityMatrixPY m 0).charpoly).eval 0
                * (rowFBetaPoly m).eval 0 ) * z := by
  have h := D_mul_toGLM_charpoly_eval_eq m (z := z) (ξ := 0) hz hs
  have h0 : (0 : ℂ) ^ s = 0 := zero_pow hs.ne'
  rw [h0] at h
  linear_combination h

/-- §521 Step D.2 — Alternative proof of Step C.18 (cycle 704)
`toGLM_charpoly_eval_zero_eq_zero_of_bdf` via the new general-form
identity `D_mul_toGLM_charpoly_eval_zero_eq` (Step D.1). Under BDF,
both `rowFAlphaPoly m` and `rowFBetaPoly m` vanish identically (cycle
672 BDF row collapse + the BDF β-coefficients vanishing on
`Fin.castSucc`), so the constant term of `D · charpoly` produced by
Step D.1 collapses to zero. This routes through the general headline
rather than directly through the BDF charpoly headline used by
Step C.18. -/
theorem D_mul_toGLM_charpoly_eval_zero_eq_zero_of_bdf
    (m : LMM s) {z : ℂ}
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 0 = 0 := by
  rw [D_mul_toGLM_charpoly_eval_zero_eq m hz hs]
  have hBeta : rowFBetaPoly m = 0 := by
    unfold rowFBetaPoly
    apply Finset.sum_eq_zero
    intro k _
    have hβ : m.β (Fin.castSucc k) = 0 :=
      hbdf _ (Fin.castSucc_lt_last k).ne
    rw [hβ]
    simp
  have hRowF : toGLM_stabilityCharpolyRowF m = 0 :=
    toGLM_stabilityCharpolyRowF_of_bdf m hs hbdf
  have hSplit :=
    toGLM_stabilityCharpolyRowF_eq_alphaPoly_plus_PY_betaPoly m hs
  rw [hRowF, hBeta, mul_zero, add_zero] at hSplit
  have hAlpha : rowFAlphaPoly m = 0 := hSplit.symm
  rw [hAlpha, hBeta]
  simp

/-- §521 Step D.4 — Constant-term evaluation of `rowFBetaPoly`. The
geometric `∑ k : Fin s, C(β (castSucc k)) * X^k` evaluated at `0`
collapses to the single `k = 0` summand because `0^k = 0` for `k ≥ 1`,
isolating the bare `β 0` coefficient. Companion to `rowFBetaPoly_eval_one`
for the unit-disk boundary argument behind `LMM.toGLM_isAStable_iff`. -/
theorem rowFBetaPoly_eval_zero (m : LMM s) (hs : 0 < s) :
    (rowFBetaPoly m).eval 0 =
      ((m.β (Fin.castSucc ⟨0, hs⟩) : ℝ) : ℂ) := by
  unfold rowFBetaPoly
  rw [Polynomial.eval_finset_sum]
  rw [Finset.sum_eq_single (⟨0, hs⟩ : Fin s)]
  · simp
  · intro k _ hk
    have hk' : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
    simp [zero_pow hk']
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- §521 Step D.5 — Unit-circle evaluation of `rowFBetaPoly`. All
`1^k = 1` factors collapse, leaving the bare coefficient sum
`∑ k : Fin s, β(castSucc k)`. Companion to `rowFBetaPoly_eval_zero`
for the unit-disk boundary argument behind
`LMM.toGLM_isAStable_iff`. No `s ≥ 1` hypothesis is needed: at `s = 0`
both sides are the empty sum. -/
theorem rowFBetaPoly_eval_one (m : LMM s) :
    (rowFBetaPoly m).eval 1 =
      ∑ k : Fin s, ((m.β (Fin.castSucc k) : ℝ) : ℂ) := by
  unfold rowFBetaPoly
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  simp

/-- §521 Step D.3 — General (non-BDF) `ξ = 1` evaluation of the cycle 698
textbook headline. The unit-circle boundary point `ξ = 1` is the natural
input to the boundary-locus argument behind `LMM.toGLM_isAStable_iff`:
all `1^k = 1` powers collapse, isolating the `ξ = 1` value of the GLM
charpoly purely in terms of `m.stabilityPolyPoly z` evaluated at `1`
and linear corrections in `rowYQuot`, `rowFAlphaPoly`, and
`rowFBetaPoly`. -/
theorem D_mul_toGLM_charpoly_eval_one_eq
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 1 =
      (m.stabilityPolyPoly z).eval 1
        + z *
            ∑ l : Fin s,
              ( ((m.β l.castSucc : ℝ) : ℂ)
                  - ((m.β (Fin.last s) : ℝ) : ℂ) *
                    ((m.α l.castSucc : ℝ) : ℂ) )
        - ( (rowYQuot m).eval 1 *
              (z * ((m.β (Fin.last s) : ℝ) : ℂ))
          + ( (rowFAlphaPoly m).eval 1 +
                ((toGLM_stabilityMatrixPY m 0).charpoly).eval 1 *
                  (rowFBetaPoly m).eval 1 ) * z ) := by
  have h := D_mul_toGLM_charpoly_eval_eq m (z := z) (ξ := 1) hz hs
  have h1 : (1 : ℂ) ^ s = 1 := one_pow s
  rw [h1] at h
  simp only [one_pow, mul_one, one_mul] at h
  linear_combination h

/-- §521 Step D.6 — Constant-term evaluation of `(PY(0)).charpoly`. The
sum `X^s - ∑ l : Fin s, C((-α(castSucc l) : ℂ)) * X^l` evaluated at `0`
collapses: `X^s` becomes `0` (for `s ≥ 1`) and only the `l = 0` summand
of the corrective sum survives, contributing `-(-α 0) = α 0`. -/
theorem toGLM_stabilityMatrixPY_zero_charpoly_eval_zero
    (m : LMM s) (hs : 0 < s) :
    ((toGLM_stabilityMatrixPY m 0).charpoly).eval 0 =
      ((m.α (Fin.castSucc ⟨0, hs⟩) : ℝ) : ℂ) := by
  rw [toGLM_stabilityMatrixPY_zero_charpoly_eq m]
  rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_finset_sum]
  rw [zero_pow hs.ne']
  rw [Finset.sum_eq_single (⟨0, hs⟩ : Fin s)]
  · simp
  · intro k _ hk
    have hk' : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
    simp [zero_pow hk']
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- §521 Step D.7 — Unit-circle evaluation of `(PY(0)).charpoly`. All
`1^k = 1` powers collapse, leaving
`1 - ∑ l : Fin s, -α(castSucc l) = 1 + ∑ l : Fin s, α(castSucc l)`.
Companion to `toGLM_stabilityMatrixPY_zero_charpoly_eval_zero` for the
unit-disk boundary argument behind `LMM.toGLM_isAStable_iff`. No
`s ≥ 1` hypothesis is needed: at `s = 0`, both sides collapse to
`1`. -/
theorem toGLM_stabilityMatrixPY_zero_charpoly_eval_one (m : LMM s) :
    ((toGLM_stabilityMatrixPY m 0).charpoly).eval 1 =
      1 + ∑ l : Fin s, ((m.α (Fin.castSucc l) : ℝ) : ℂ) := by
  rw [toGLM_stabilityMatrixPY_zero_charpoly_eq m]
  rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_finset_sum, one_pow]
  have hsum :
      ∑ l : Fin s,
          (Polynomial.C ((-m.α (Fin.castSucc l) : ℝ) : ℂ) *
            (Polynomial.X : Polynomial ℂ) ^ (l : ℕ)).eval 1
        = -∑ l : Fin s, ((m.α (Fin.castSucc l) : ℝ) : ℂ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro l _
    simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
  rw [hsum]; ring

/-- §521 Step D.8 — Fully concrete coefficient-form of the cycle 708
`ξ = 0` evaluation. Substitutes the closed forms
`(PY(0)).charpoly.eval 0 = α 0` (Step D.6) and
`rowFBetaPoly.eval 0 = β 0` (Step D.4) into the cycle 708 identity
`D_mul_toGLM_charpoly_eval_zero_eq`. The constant term of the GLM
stability matrix charpoly (rescaled by `D`) reduces to a closed form
in `(rowFAlphaPoly m).eval 0`, the bare `α 0` and `β 0` coefficients,
and `z`. -/
theorem D_mul_toGLM_charpoly_eval_zero_concrete
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 0 =
      - ( (rowFAlphaPoly m).eval 0
            + ((m.α (Fin.castSucc ⟨0, hs⟩) : ℝ) : ℂ)
                * ((m.β (Fin.castSucc ⟨0, hs⟩) : ℝ) : ℂ) ) * z := by
  rw [D_mul_toGLM_charpoly_eval_zero_eq m hz hs,
      toGLM_stabilityMatrixPY_zero_charpoly_eval_zero m hs,
      rowFBetaPoly_eval_zero m hs]

/-- §521 Step D.9 — Fully concrete coefficient-form of the cycle 710
`ξ = 1` evaluation. Substitutes the closed forms
`(PY(0)).charpoly.eval 1 = 1 + ∑ α(castSucc l)` (Step D.7) and
`rowFBetaPoly.eval 1 = ∑ β(castSucc k)` (Step D.5) into the cycle 710
identity `D_mul_toGLM_charpoly_eval_one_eq`. The unit-circle value of
the GLM stability matrix charpoly (rescaled by `D`) is now expressed
purely in terms of `m.stabilityPolyPoly z` evaluated at `1`, the bare
α/β coefficient sums, and the abstract residuals
`(rowYQuot m).eval 1` and `(rowFAlphaPoly m).eval 1`. -/
theorem D_mul_toGLM_charpoly_eval_one_concrete
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 1 =
      (m.stabilityPolyPoly z).eval 1
        + z *
            ∑ l : Fin s,
              ( ((m.β l.castSucc : ℝ) : ℂ)
                  - ((m.β (Fin.last s) : ℝ) : ℂ) *
                    ((m.α l.castSucc : ℝ) : ℂ) )
        - ( (rowYQuot m).eval 1 *
              (z * ((m.β (Fin.last s) : ℝ) : ℂ))
          + ( (rowFAlphaPoly m).eval 1 +
                (1 + ∑ l : Fin s, ((m.α (Fin.castSucc l) : ℝ) : ℂ)) *
                  (∑ k : Fin s, ((m.β (Fin.castSucc k) : ℝ) : ℂ)) ) * z ) := by
  rw [D_mul_toGLM_charpoly_eval_one_eq m hz hs,
      toGLM_stabilityMatrixPY_zero_charpoly_eval_one m,
      rowFBetaPoly_eval_one m]

/-- §521 Step D.9b — BDF specialisation of `D_mul_toGLM_charpoly_eval_one_concrete`.
Under BDF, every `β (Fin.castSucc k) = 0`, so
`∑ k : Fin s, β(castSucc k) = 0` and the corrective factor
`(1 + ∑ α(castSucc l)) * (∑ β(castSucc k))` vanishes. Provides a
sanity check that the cycle 700 BDF `ξ = 1` identity is consistent
with the new general-form D.9 substitution. -/
theorem D_mul_toGLM_charpoly_eval_one_concrete_of_bdf
    (m : LMM s) {z : ℂ}
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 1 =
      (m.stabilityPolyPoly z).eval 1
        + z *
            ∑ l : Fin s,
              ( ((m.β l.castSucc : ℝ) : ℂ)
                  - ((m.β (Fin.last s) : ℝ) : ℂ) *
                    ((m.α l.castSucc : ℝ) : ℂ) )
        - ( (rowYQuot m).eval 1 *
              (z * ((m.β (Fin.last s) : ℝ) : ℂ))
          + (rowFAlphaPoly m).eval 1 * z ) := by
  rw [D_mul_toGLM_charpoly_eval_one_concrete m hz hs]
  have hBetaSum : ∑ k : Fin s, ((m.β (Fin.castSucc k) : ℝ) : ℂ) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have hβ : m.β (Fin.castSucc k) = 0 :=
      hbdf _ (Fin.castSucc_lt_last k).ne
    rw [hβ]; simp
  rw [hBetaSum]
  ring

/-- §521 Step D.10a — Constant-term evaluation of `rowFAlphaPoly`
collapses to the single `l = 0` summand of the residual decomposition.
The cycle 687 `rowFAlphaPoly_eq_residual_sum` expresses
`rowFAlphaPoly m = ∑ l : Fin s, rowFAlphaResidual m l * X^l`; at
`X = 0`, `0^l = 0` for `l ≥ 1`, leaving only the `l = 0` term whose
`X^0` factor is `1`. The `rowFAlphaResidual` evaluation itself
(`Matrix.vecMul` against `charmatrix.adjugate * map C`) is left
abstract — that hard computation is for a future cycle. -/
theorem rowFAlphaPoly_eval_zero_eq_residual_zero
    (m : LMM s) (hs : 0 < s) :
    (rowFAlphaPoly m).eval 0 =
      (rowFAlphaResidual m ⟨0, hs⟩).eval 0 := by
  rw [rowFAlphaPoly_eq_residual_sum]
  rw [Polynomial.eval_finset_sum]
  rw [Finset.sum_eq_single (⟨0, hs⟩ : Fin s)]
  · simp
  · intro k _ hk
    have hk' : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
    simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      zero_pow hk']
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- §521 Step D.10b — Unit-circle evaluation of `rowFAlphaPoly`. All
`1^l = 1` factors collapse, leaving `∑ l : Fin s, (rowFAlphaResidual m l).eval 1`.
Companion to `rowFAlphaPoly_eval_zero_eq_residual_zero` for the
unit-disk boundary argument. No `s ≥ 1` hypothesis needed. -/
theorem rowFAlphaPoly_eval_one_eq_residual_sum (m : LMM s) :
    (rowFAlphaPoly m).eval 1 =
      ∑ l : Fin s, (rowFAlphaResidual m l).eval 1 := by
  rw [rowFAlphaPoly_eq_residual_sum]
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro l _
  simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

/-- §521 Step D.11a — Substitute the cycle 716 D.10a evaluation
`(rowFAlphaPoly m).eval 0 = (rowFAlphaResidual m ⟨0, hs⟩).eval 0`
into the cycle 712 D.8 closed form
`D_mul_toGLM_charpoly_eval_zero_concrete`. The `(rowFAlphaPoly m).eval 0`
term collapses to a single residual evaluation; the rest of D.8 stays
unchanged. -/
theorem D_mul_toGLM_charpoly_eval_zero_substituted
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 0 =
      - ( (rowFAlphaResidual m ⟨0, hs⟩).eval 0
            + ((m.α (Fin.castSucc ⟨0, hs⟩) : ℝ) : ℂ)
                * ((m.β (Fin.castSucc ⟨0, hs⟩) : ℝ) : ℂ) ) * z := by
  rw [D_mul_toGLM_charpoly_eval_zero_concrete m hz hs,
      rowFAlphaPoly_eval_zero_eq_residual_zero m hs]

/-- §521 Step D.11b — Substitute the cycle 716 D.10b evaluation
`(rowFAlphaPoly m).eval 1 = ∑ l : Fin s, (rowFAlphaResidual m l).eval 1`
into the cycle 714 D.9 closed form
`D_mul_toGLM_charpoly_eval_one_concrete`. -/
theorem D_mul_toGLM_charpoly_eval_one_substituted
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 1 =
      (m.stabilityPolyPoly z).eval 1
        + z *
            ∑ l : Fin s,
              ( ((m.β l.castSucc : ℝ) : ℂ)
                  - ((m.β (Fin.last s) : ℝ) : ℂ) *
                    ((m.α l.castSucc : ℝ) : ℂ) )
        - ( (rowYQuot m).eval 1 *
              (z * ((m.β (Fin.last s) : ℝ) : ℂ))
          + ( (∑ l : Fin s, (rowFAlphaResidual m l).eval 1) +
                (1 + ∑ l : Fin s, ((m.α (Fin.castSucc l) : ℝ) : ℂ)) *
                  (∑ k : Fin s, ((m.β (Fin.castSucc k) : ℝ) : ℂ)) ) * z ) := by
  rw [D_mul_toGLM_charpoly_eval_one_concrete m hz hs,
      rowFAlphaPoly_eval_one_eq_residual_sum m]

/-- §521 Step D.11c — BDF specialisation of D.11b. Under BDF,
`∑ k : Fin s, β(castSucc k) = 0`, so the corrective product term in
D.11b vanishes (same simplification used in D.9b). -/
theorem D_mul_toGLM_charpoly_eval_one_substituted_of_bdf
    (m : LMM s) {z : ℂ}
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 1 =
      (m.stabilityPolyPoly z).eval 1
        + z *
            ∑ l : Fin s,
              ( ((m.β l.castSucc : ℝ) : ℂ)
                  - ((m.β (Fin.last s) : ℝ) : ℂ) *
                    ((m.α l.castSucc : ℝ) : ℂ) )
        - ( (rowYQuot m).eval 1 *
              (z * ((m.β (Fin.last s) : ℝ) : ℂ))
          + (∑ l : Fin s, (rowFAlphaResidual m l).eval 1) * z ) := by
  rw [D_mul_toGLM_charpoly_eval_one_substituted m hz hs]
  have hBetaSum : ∑ k : Fin s, ((m.β (Fin.castSucc k) : ℝ) : ℂ) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have hβ : m.β (Fin.castSucc k) = 0 :=
      hbdf _ (Fin.castSucc_lt_last k).ne
    rw [hβ]; simp
  rw [hBetaSum]; ring

/-- §521 Step D.12a — Discharge `dif_neg` branch of `rowYQuot.eval 0`. -/
theorem rowYQuot_eval_zero_eq (m : LMM s) (hs : 0 < s) :
    (rowYQuot m).eval 0 =
      (((toGLM_stabilityMatrixPY m 0).charmatrix.updateRow
          ⟨s - 1, by omega⟩
          (fun k =>
            Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ))).det).eval 0 := by
  unfold rowYQuot
  rw [dif_neg hs.ne']

/-- §521 Step D.12b — Discharge `dif_neg` branch of `rowYQuot.eval 1`. -/
theorem rowYQuot_eval_one_eq (m : LMM s) (hs : 0 < s) :
    (rowYQuot m).eval 1 =
      (((toGLM_stabilityMatrixPY m 0).charmatrix.updateRow
          ⟨s - 1, by omega⟩
          (fun k =>
            Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ))).det).eval 1 := by
  unfold rowYQuot
  rw [dif_neg hs.ne']

/-- §521 Step D.13 — Cofactor expansion of `rowYQuot` along the `-α`
updated row, recasting the determinant as a sum of `Polynomial.C`-times-
adjugate-entry contributions. -/
theorem rowYQuot_eq_adjugate_sum (m : LMM s) (hs : 0 < s) :
    rowYQuot m =
      ∑ k : Fin s,
        Polynomial.C ((-m.α (Fin.castSucc k) : ℝ) : ℂ) *
          (toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k
            ⟨s - 1, by omega⟩ := by
  unfold rowYQuot
  rw [dif_neg hs.ne', ← Matrix.cramer_transpose_apply,
      Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec_eq_sum]
  simp [Matrix.adjugate_transpose, mul_comm]

/-- §521 Step D.14a — Push `Polynomial.eval ξ` through `rowYQuot_eq_adjugate_sum`
to obtain the cofactor sum at any complex point `ξ`. -/
theorem rowYQuot_eval_eq_sum (m : LMM s) (hs : 0 < s) (ξ : ℂ) :
    (rowYQuot m).eval ξ =
      ∑ k : Fin s,
        ((-m.α (Fin.castSucc k) : ℝ) : ℂ) *
          ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k
              ⟨s - 1, by omega⟩).eval ξ := by
  rw [rowYQuot_eq_adjugate_sum m hs]
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_C]

/-- §521 Step D.14b — Specialisation of `rowYQuot_eval_eq_sum` at `ξ = 0`. -/
theorem rowYQuot_eval_zero_eq_sum (m : LMM s) (hs : 0 < s) :
    (rowYQuot m).eval 0 =
      ∑ k : Fin s,
        ((-m.α (Fin.castSucc k) : ℝ) : ℂ) *
          ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k
              ⟨s - 1, by omega⟩).eval 0 :=
  rowYQuot_eval_eq_sum m hs 0

/-- §521 Step D.14c — Specialisation of `rowYQuot_eval_eq_sum` at `ξ = 1`. -/
theorem rowYQuot_eval_one_eq_sum (m : LMM s) (hs : 0 < s) :
    (rowYQuot m).eval 1 =
      ∑ k : Fin s,
        ((-m.α (Fin.castSucc k) : ℝ) : ℂ) *
          ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k
              ⟨s - 1, by omega⟩).eval 1 :=
  rowYQuot_eval_eq_sum m hs 1

/-- §521 Step D.14d — BDF wrapper for `rowYQuot_eval_one_eq_sum`. The
`hbdf` hypothesis is unused at this seam; downstream callers see a
BDF-flavoured name. -/
theorem rowYQuot_eval_one_eq_sum_of_bdf
    (m : LMM s) (hs : 0 < s)
    (_hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0) :
    (rowYQuot m).eval 1 =
      ∑ k : Fin s,
        ((-m.α (Fin.castSucc k) : ℝ) : ℂ) *
          ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k
              ⟨s - 1, by omega⟩).eval 1 :=
  rowYQuot_eval_one_eq_sum m hs

/-- §521 Step D.15 — `rowFAlphaResidual m l` expanded as a double sum
over `(k, j) : Fin s × Fin s` of `Polynomial.C`-coefficients times a
single charmatrix adjugate entry.  Mirrors cycle 720's
`rowYQuot_eq_adjugate_sum` for the rowF side.  The leading
`-α(castSucc k)` is inherited from the `rowFAlphaResidual` definition
(the inner two negations on `adjugate` and `PYHF.map C` cancel via
`neg_mul_neg`; the outer `-α` factor remains). -/
private theorem rowFAlphaResidual_eq_double_sum
    (m : LMM s) (l : Fin s) :
    rowFAlphaResidual m l =
      ∑ k : Fin s, ∑ j : Fin s,
        Polynomial.C
            ( ((-m.α (Fin.castSucc k) : ℝ) : ℂ)
                * ((toGLM_stabilityMatrixPYHF m 0) j l) )
          * (toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k j := by
  unfold rowFAlphaResidual
  rw [Matrix.vecMul_eq_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.mul_apply]
  simp only [Matrix.neg_apply, Matrix.map_apply, neg_mul_neg, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Polynomial.C_mul]
  ring

/-- §521 Step D.16a — Push `Polynomial.eval ξ` through D.15's cofactor
expansion of `rowFAlphaResidual`. -/
private theorem rowFAlphaResidual_eval_eq_double_sum
    (m : LMM s) (l : Fin s) (ξ : ℂ) :
    (rowFAlphaResidual m l).eval ξ =
      ∑ k : Fin s, ∑ j : Fin s,
        ( ((-m.α (Fin.castSucc k) : ℝ) : ℂ)
            * ((toGLM_stabilityMatrixPYHF m 0) j l) )
          * ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k j).eval ξ := by
  rw [rowFAlphaResidual_eq_double_sum m l]
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_C]

/-- §521 Step D.16b — `ξ = 0` specialisation of D.16a. -/
private theorem rowFAlphaResidual_eval_zero_eq_double_sum
    (m : LMM s) (l : Fin s) :
    (rowFAlphaResidual m l).eval 0 =
      ∑ k : Fin s, ∑ j : Fin s,
        ( ((-m.α (Fin.castSucc k) : ℝ) : ℂ)
            * ((toGLM_stabilityMatrixPYHF m 0) j l) )
          * ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k j).eval 0 :=
  rowFAlphaResidual_eval_eq_double_sum m l 0

/-- §521 Step D.16c — `ξ = 1` specialisation of D.16a. -/
private theorem rowFAlphaResidual_eval_one_eq_double_sum
    (m : LMM s) (l : Fin s) :
    (rowFAlphaResidual m l).eval 1 =
      ∑ k : Fin s, ∑ j : Fin s,
        ( ((-m.α (Fin.castSucc k) : ℝ) : ℂ)
            * ((toGLM_stabilityMatrixPYHF m 0) j l) )
          * ((toGLM_stabilityMatrixPY m 0).charmatrix.adjugate k j).eval 1 :=
  rowFAlphaResidual_eval_eq_double_sum m l 1

/-- §521 Step D.16d — Under BDF, `rowFAlphaResidual m l` evaluates to
zero at `ξ = 1`, because the entire `PYHF` block vanishes (cycle 643's
`toGLM_stabilityMatrixPYHF_eq_zero_of_bdf`). -/
private theorem rowFAlphaResidual_eval_one_of_bdf_eq_zero
    (m : LMM s)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (l : Fin s) :
    (rowFAlphaResidual m l).eval 1 = 0 := by
  rw [rowFAlphaResidual_eval_one_eq_double_sum m l]
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro j _
  have hPYHF : (toGLM_stabilityMatrixPYHF m 0) j l = 0 := by
    have := toGLM_stabilityMatrixPYHF_eq_zero_of_bdf m 0 hbdf
    exact congrFun (congrFun this j) l
  rw [hPYHF]
  ring

/-- §521 Step E.1 — Substitute D.16d into D.11c: under BDF, the
`∑ l, (rowFAlphaResidual m l).eval 1` summand collapses to zero,
yielding the cleaner BDF unit-circle identity. -/
theorem D_mul_toGLM_charpoly_eval_one_collapsed_of_bdf
    (m : LMM s) {z : ℂ}
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 1 =
      (m.stabilityPolyPoly z).eval 1
        + z *
            ∑ l : Fin s,
              ( ((m.β l.castSucc : ℝ) : ℂ)
                  - ((m.β (Fin.last s) : ℝ) : ℂ) *
                    ((m.α l.castSucc : ℝ) : ℂ) )
        - (rowYQuot m).eval 1 *
            (z * ((m.β (Fin.last s) : ℝ) : ℂ)) := by
  rw [D_mul_toGLM_charpoly_eval_one_substituted_of_bdf m hbdf hz hs]
  have hSum : ∑ l : Fin s, (rowFAlphaResidual m l).eval 1 = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    exact rowFAlphaResidual_eval_one_of_bdf_eq_zero m hbdf l
  rw [hSum]; ring

/-- §521 Step E.2 — Under BDF, β(castSucc l) = 0 for all l : Fin s,
so the bracketed sum in E.1 collapses to a single term. -/
theorem D_mul_toGLM_charpoly_eval_one_reduced_of_bdf
    (m : LMM s) {z : ℂ}
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 1 =
      (m.stabilityPolyPoly z).eval 1
        - z * ((m.β (Fin.last s) : ℝ) : ℂ) *
            ∑ l : Fin s, ((m.α l.castSucc : ℝ) : ℂ)
        - (rowYQuot m).eval 1 *
            (z * ((m.β (Fin.last s) : ℝ) : ℂ)) := by
  rw [D_mul_toGLM_charpoly_eval_one_collapsed_of_bdf m hbdf hz hs]
  have hβSum :
      ∑ l : Fin s,
          ( ((m.β l.castSucc : ℝ) : ℂ)
            - ((m.β (Fin.last s) : ℝ) : ℂ) *
              ((m.α l.castSucc : ℝ) : ℂ) )
        = -((m.β (Fin.last s) : ℝ) : ℂ) *
            ∑ l : Fin s, ((m.α l.castSucc : ℝ) : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hβ : m.β (Fin.castSucc l) = 0 :=
      hbdf _ (Fin.castSucc_lt_last l).ne
    rw [hβ]
    push_cast
    ring
  rw [hβSum]; ring

/-- §521 Step E.3 — Mirror of D.16d at ξ = 0: under BDF, the entire
PYHF block vanishes (cycle 645), so each `rowFAlphaResidual l`
evaluates to zero at any point including ξ = 0. -/
private theorem rowFAlphaResidual_eval_zero_of_bdf_eq_zero
    (m : LMM s)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (l : Fin s) :
    (rowFAlphaResidual m l).eval 0 = 0 := by
  rw [rowFAlphaResidual_eval_zero_eq_double_sum m l]
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro j _
  have hPYHF : (toGLM_stabilityMatrixPYHF m 0) j l = 0 := by
    have := toGLM_stabilityMatrixPYHF_eq_zero_of_bdf m 0 hbdf
    exact congrFun (congrFun this j) l
  rw [hPYHF]; ring

/-- §521 Step E.4 — Under BDF, the rescaled charpoly vanishes at
ξ = 0. Combine D.11a with E.3 (rowFAlphaResidual vanishes at 0)
and the BDF condition `β(castSucc ⟨0,hs⟩) = 0`. -/
theorem D_mul_toGLM_charpoly_eval_zero_collapsed_of_bdf
    (m : LMM s) {z : ℂ}
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        ((m.toGLM.stabilityMatrix z).charpoly).eval 0 = 0 := by
  rw [D_mul_toGLM_charpoly_eval_zero_substituted m hz hs]
  have h1 : (rowFAlphaResidual m ⟨0, hs⟩).eval 0 = 0 :=
    rowFAlphaResidual_eval_zero_of_bdf_eq_zero m hbdf ⟨0, hs⟩
  have hβ : m.β (Fin.castSucc ⟨0, hs⟩) = 0 :=
    hbdf _ (Fin.castSucc_lt_last _).ne
  rw [h1, hβ]
  push_cast; ring

end LMM
