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
stability matrix.

This is the natural general-`z` companion of the classical scalar
stability polynomial `LMM.stabilityPolyPoly`, to which it reduces under
the BDF hypothesis (see
`activeStabilityPolyPoly_eq_stabilityPolyPoly_of_bdf`). -/
noncomputable def activeStabilityPolyPoly (m : LMM s) (z : ℂ) : Polynomial ℂ :=
  (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) •
    (toGLM_stabilityMatrixPY m z).charpoly

/-- §521 Step C.5 — BDF sanity lemma: under the BDF hypothesis on `β`
(all entries except `β_last` vanish), the active stability polynomial
collapses to the classical scalar stability polynomial. Direct restatement
of `LMM.toGLM_stabilityMatrixPY_charpoly_eq_stabilityPolyPoly_of_bdf` via
the new definition. -/
theorem activeStabilityPolyPoly_eq_stabilityPolyPoly_of_bdf
    (m : LMM s) (z : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) :
    activeStabilityPolyPoly m z = m.stabilityPolyPoly z :=
  toGLM_stabilityMatrixPY_charpoly_eq_stabilityPolyPoly_of_bdf m z hbdf hz

/-- §521 Step C.5 — BDF specialisation of the headline identity
`D · charpoly = X^s · activeStabilityPolyPoly`. Under the BDF hypothesis
the cycle 643 lemma `toGLM_stabilityMatrix_charpoly_of_bdf` factors the
full GLM stability charpoly as `PY.charpoly · X^s`, so multiplying both
sides by `Polynomial.C D` reorders them into the active-stability form.

The general (non-BDF) version remains the next sub-step toward the §521
iff bridge: it requires extracting the `Polynomial.X^s` factor from the
rank-one adjugate contraction in
`toGLM_stabilityMatrix_charpoly_explicit`. -/
theorem D_mul_toGLM_charpoly_eq_X_pow_mul_active_of_bdf
    (m : LMM s) (z : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0) :
    Polynomial.C (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        (m.toGLM.stabilityMatrix z).charpoly =
      (Polynomial.X : Polynomial ℂ) ^ s * activeStabilityPolyPoly m z := by
  rw [toGLM_stabilityMatrix_charpoly_of_bdf m z hbdf]
  unfold activeStabilityPolyPoly
  rw [Polynomial.smul_eq_C_mul]
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

end LMM
