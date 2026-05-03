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

end LMM
