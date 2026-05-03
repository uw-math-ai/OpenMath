import OpenMath.LMMAsGLM

/-!
# Butcher §521 — Stability-matrix infrastructure for LMM-as-GLM

This module collects the §521 stability-matrix block decomposition,
companion-form charpoly identities, BDF specialisations, the
LMM-side A-stability iff bridge for BDF families, and the concrete
A-stability transports for backward Euler, the trapezoidal rule, and
BDF2.

Extracted from `OpenMath/LMMAsGLM.lean` to keep the parent file under
the project's hard line cap.

Reference: J. C. Butcher, *Numerical Methods for Ordinary Differential
Equations*, 2nd ed., §521.
-/

open Finset Real

namespace LMM

variable {s : ℕ}

/-- §503 sanity check for §520: because an LMM embeds as a one-stage GLM,
the stability-matrix entry collapses to the single stage resolvent factor.
The surrounding `toGLM` blocks retain the literal §503 row/column shape. -/
theorem toGLM_stabilityMatrix_apply (m : LMM s) (z : ℂ) (k l : Fin (2 * s)) :
    m.toGLM.stabilityMatrix z k l =
      m.toGLM.Vℂ k l +
        z *
          (m.toGLM.Bℂ k 0 *
            (((1 : Matrix (Fin 1) (Fin 1) ℂ) - z • m.toGLM.Aℂ)⁻¹ 0 0) *
            m.toGLM.Uℂ 0 l) := by
  rw [GeneralLinearMethod.stabilityMatrix_apply]
  simp

/-- §521 prep — on a non-last past-`y` shift row, the stability matrix
agrees with `m.toGLM.Vℂ` because the `B`-block contribution vanishes. -/
theorem toGLM_stabilityMatrix_castAdd_shift_apply (m : LMM s) (z : ℂ)
    (j : Fin s) (hj : (j : ℕ) + 1 ≠ s) (l : Fin (2 * s)) :
    m.toGLM.stabilityMatrix z
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) l =
      m.toGLM.Vℂ (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) l := by
  rw [toGLM_stabilityMatrix_apply]
  have hB : m.toGLM.Bℂ
      (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) 0 = 0 := by
    show ((m.toGLM.B
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) 0 : ℝ) : ℂ) = 0
    rw [toGLM_B_castAdd_shift_apply m j hj]
    simp
  rw [hB]
  ring

/-- §521 prep — on a non-last past-`h*f` shift row, the stability matrix
agrees with `m.toGLM.Vℂ` because the `B`-block contribution vanishes. -/
theorem toGLM_stabilityMatrix_natAdd_shift_apply (m : LMM s) (z : ℂ)
    (j : Fin s) (hj : (j : ℕ) + 1 ≠ s) (l : Fin (2 * s)) :
    m.toGLM.stabilityMatrix z
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) l =
      m.toGLM.Vℂ (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) l := by
  rw [toGLM_stabilityMatrix_apply]
  have hB : m.toGLM.Bℂ
      (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) 0 = 0 := by
    show ((m.toGLM.B
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) 0 : ℝ) : ℂ) = 0
    rw [toGLM_B_natAdd_shift_apply m j hj]
    simp
  rw [hB]
  ring

/-- §521 prep — on the last past-`y` row (the `y_{n+s}` output row),
the stability matrix sums the `Vℂ` part (the `α` / `β` LMM coefficients
on past-`y` and past-`h*f` slots) with the implicit-stage resolvent
contribution `z * β(last) * resolvent * Uℂ 0 l`. -/
theorem toGLM_stabilityMatrix_castAdd_last_apply (m : LMM s) (z : ℂ)
    (j : Fin s) (hj : (j : ℕ) + 1 = s) (l : Fin (2 * s)) :
    m.toGLM.stabilityMatrix z
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) l =
      m.toGLM.Vℂ (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) l +
        z * ((m.β (Fin.last s) : ℝ) : ℂ) *
          (((1 : Matrix (Fin 1) (Fin 1) ℂ) - z • m.toGLM.Aℂ)⁻¹ 0 0) *
          m.toGLM.Uℂ 0 l := by
  rw [toGLM_stabilityMatrix_apply]
  have hB : m.toGLM.Bℂ
      (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) 0 =
        ((m.β (Fin.last s) : ℝ) : ℂ) := by
    show ((m.toGLM.B
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) 0 : ℝ) : ℂ) = _
    rw [toGLM_B_castAdd_last_apply m j hj]
  rw [hB]
  ring

/-- §521 prep — on the last past-`h*f` row (the `h·f_{n+s}` output row),
the stability matrix has *no* `Vℂ` contribution (cycle 620 lemma) and
reduces to a pure resolvent-times-`Uℂ` term. -/
theorem toGLM_stabilityMatrix_natAdd_last_apply (m : LMM s) (z : ℂ)
    (j : Fin s) (hj : (j : ℕ) + 1 = s) (l : Fin (2 * s)) :
    m.toGLM.stabilityMatrix z
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) l =
      z *
          (((1 : Matrix (Fin 1) (Fin 1) ℂ) - z • m.toGLM.Aℂ)⁻¹ 0 0) *
          m.toGLM.Uℂ 0 l := by
  rw [toGLM_stabilityMatrix_apply]
  have hV : m.toGLM.Vℂ
      (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) l = 0 := by
    show ((m.toGLM.V
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) l : ℝ) : ℂ) = 0
    rw [toGLM_V_natAdd_last_apply m j hj]
    simp
  have hB : m.toGLM.Bℂ
      (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) 0 = 1 := by
    show ((m.toGLM.B
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) 0 : ℝ) : ℂ) = 1
    rw [toGLM_B_natAdd_last_apply m j hj]
    simp
  rw [hV, hB]
  ring

/-- §521 prep — the `1×1` `A`-block of the LMM-as-GLM embedding is
the implicit-stage coefficient `m.β (Fin.last s)`, lifted to ℂ. -/
@[simp] theorem toGLM_Aℂ_apply (m : LMM s) :
    m.toGLM.Aℂ 0 0 = ((m.β (Fin.last s) : ℝ) : ℂ) := by
  show ((m.toGLM.A 0 0 : ℝ) : ℂ) = _
  rw [toGLM_A_apply]

/-- §521 prep — the `1×1` GLM resolvent collapses to a scalar
inverse in `z` and `m.β (Fin.last s)`. -/
theorem toGLM_resolvent_apply (m : LMM s) (z : ℂ) :
    (((1 : Matrix (Fin 1) (Fin 1) ℂ) - z • m.toGLM.Aℂ)⁻¹ 0 0)
      = 1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) := by
  have hsub : (1 : Matrix (Fin 1) (Fin 1) ℂ) - z • m.toGLM.Aℂ =
      !![1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)] := by
    ext i j
    fin_cases i; fin_cases j
    show (1 : ℂ) - z * m.toGLM.Aℂ 0 0 = _
    rw [toGLM_Aℂ_apply]
    simp
  rw [hsub, Matrix.inv_def]
  simp [Matrix.adjugate_fin_one]

/-- §521 prep — past-`y` half of the `Uℂ` block: the complex-lifted
LMM-as-GLM `U` row reads off `-m.α (Fin.castSucc k)` on past-`y` slots. -/
@[simp] theorem toGLM_Uℂ_castAdd (m : LMM s) (k : Fin s) :
    m.toGLM.Uℂ 0 (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s k))
      = ((-m.α (Fin.castSucc k) : ℝ) : ℂ) := by
  show ((m.toGLM.U 0
      (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s k)) : ℝ) : ℂ) = _
  simp only [toGLM]
  have hcol :
      Fin.cast (Nat.two_mul s)
          (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s k)) =
        Fin.castAdd s k := by
    ext; simp
  rw [hcol, Fin.addCases_left]

/-- §521 prep — past-`h*f` half of the `Uℂ` block: the complex-lifted
LMM-as-GLM `U` row reads off `m.β (Fin.castSucc k)` on past-`h*f` slots. -/
@[simp] theorem toGLM_Uℂ_natAdd (m : LMM s) (k : Fin s) :
    m.toGLM.Uℂ 0 (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s k))
      = ((m.β (Fin.castSucc k) : ℝ) : ℂ) := by
  show ((m.toGLM.U 0
      (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s k)) : ℝ) : ℂ) = _
  simp only [toGLM]
  have hcol :
      Fin.cast (Nat.two_mul s)
          (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s k)) =
        Fin.natAdd s k := by
    ext; simp
  rw [hcol, Fin.addCases_right]

/-- §521 — closed scalar entry on (last past-`y` row, past-`y` column). -/
theorem toGLM_stabilityMatrix_castAdd_last_castAdd_apply (m : LMM s) (z : ℂ)
    (j : Fin s) (hj : (j : ℕ) + 1 = s) (l : Fin s) :
    m.toGLM.stabilityMatrix z
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) =
      ((-m.α (Fin.castSucc l) : ℝ) : ℂ) +
        z * ((m.β (Fin.last s) : ℝ) : ℂ) *
          (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
          ((-m.α (Fin.castSucc l) : ℝ) : ℂ) := by
  rw [toGLM_stabilityMatrix_castAdd_last_apply m z j hj]
  rw [toGLM_resolvent_apply, toGLM_Uℂ_castAdd]
  have hV : m.toGLM.Vℂ
      (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
      (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) =
        ((-m.α (Fin.castSucc l) : ℝ) : ℂ) := by
    show ((m.toGLM.V
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) : ℝ) : ℂ) = _
    rw [toGLM_V_castAdd_last_castAdd_apply m j hj]
  rw [hV]

/-- §521 — closed scalar entry on (last past-`y` row, past-`h*f` column). -/
theorem toGLM_stabilityMatrix_castAdd_last_natAdd_apply (m : LMM s) (z : ℂ)
    (j : Fin s) (hj : (j : ℕ) + 1 = s) (l : Fin s) :
    m.toGLM.stabilityMatrix z
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l)) =
      ((m.β (Fin.castSucc l) : ℝ) : ℂ) +
        z * ((m.β (Fin.last s) : ℝ) : ℂ) *
          (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
          ((m.β (Fin.castSucc l) : ℝ) : ℂ) := by
  rw [toGLM_stabilityMatrix_castAdd_last_apply m z j hj]
  rw [toGLM_resolvent_apply, toGLM_Uℂ_natAdd]
  have hV : m.toGLM.Vℂ
      (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
      (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l)) =
        ((m.β (Fin.castSucc l) : ℝ) : ℂ) := by
    show ((m.toGLM.V
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l)) : ℝ) : ℂ) = _
    rw [toGLM_V_castAdd_last_natAdd_apply m j hj]
  rw [hV]

/-- §521 — closed scalar entry on (last past-`h*f` row, past-`y` column). -/
theorem toGLM_stabilityMatrix_natAdd_last_castAdd_apply (m : LMM s) (z : ℂ)
    (j : Fin s) (hj : (j : ℕ) + 1 = s) (l : Fin s) :
    m.toGLM.stabilityMatrix z
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) =
      z * (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
        ((-m.α (Fin.castSucc l) : ℝ) : ℂ) := by
  rw [toGLM_stabilityMatrix_natAdd_last_apply m z j hj]
  rw [toGLM_resolvent_apply, toGLM_Uℂ_castAdd]

/-- §521 — closed scalar entry on (last past-`h*f` row, past-`h*f` column). -/
theorem toGLM_stabilityMatrix_natAdd_last_natAdd_apply (m : LMM s) (z : ℂ)
    (j : Fin s) (hj : (j : ℕ) + 1 = s) (l : Fin s) :
    m.toGLM.stabilityMatrix z
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l)) =
      z * (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
        ((m.β (Fin.castSucc l) : ℝ) : ℂ) := by
  rw [toGLM_stabilityMatrix_natAdd_last_apply m z j hj]
  rw [toGLM_resolvent_apply, toGLM_Uℂ_natAdd]

/-- §521 block reindexing: split the `2*s` GLM state into past-`y`
and past-`h*f` halves. -/
noncomputable def toGLM_stabilityBlockEquiv (s : ℕ) :
    Fin s ⊕ Fin s ≃ Fin (2 * s) :=
  finSumFinEquiv.trans (finCongr (Nat.two_mul s).symm)

@[simp] theorem toGLM_stabilityBlockEquiv_symm_castAdd (j : Fin s) :
    (toGLM_stabilityBlockEquiv s).symm
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j)) =
      Sum.inl j := by
  simp [toGLM_stabilityBlockEquiv]

@[simp] theorem toGLM_stabilityBlockEquiv_symm_natAdd (j : Fin s) :
    (toGLM_stabilityBlockEquiv s).symm
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j)) =
      Sum.inr j := by
  simp [toGLM_stabilityBlockEquiv]
  apply finSumFinEquiv.injective
  ext
  simp [Fin.addNat, Fin.natAdd, Nat.add_comm]

@[simp] theorem toGLM_stabilityBlockEquiv_symm_addNat (j : Fin s) :
    (toGLM_stabilityBlockEquiv s).symm
        (Fin.cast (Nat.two_mul s).symm (j.addNat s)) =
      Sum.inr j := by
  simp [toGLM_stabilityBlockEquiv]
  apply finSumFinEquiv.injective
  ext
  simp [Fin.addNat, Fin.natAdd, Nat.add_comm]

/-- §521 block form: past-`y` rows against past-`y` columns. -/
noncomputable def toGLM_stabilityMatrixPY (m : LMM s) (z : ℂ) :
    Matrix (Fin s) (Fin s) ℂ := fun j l =>
  if (j : ℕ) + 1 = s then
    ((-m.α (Fin.castSucc l) : ℝ) : ℂ) +
      z * ((m.β (Fin.last s) : ℝ) : ℂ) *
        (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
        ((-m.α (Fin.castSucc l) : ℝ) : ℂ)
  else if (l : ℕ) = (j : ℕ) + 1 then (1 : ℂ) else 0

/-- §521 block form: past-`y` rows against past-`h*f` columns. -/
noncomputable def toGLM_stabilityMatrixPYHF (m : LMM s) (z : ℂ) :
    Matrix (Fin s) (Fin s) ℂ := fun j l =>
  if (j : ℕ) + 1 = s then
    ((m.β (Fin.castSucc l) : ℝ) : ℂ) +
      z * ((m.β (Fin.last s) : ℝ) : ℂ) *
        (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
        ((m.β (Fin.castSucc l) : ℝ) : ℂ)
  else 0

/-- §521 block form: past-`h*f` rows against past-`y` columns. -/
noncomputable def toGLM_stabilityMatrixPHFY (m : LMM s) (z : ℂ) :
    Matrix (Fin s) (Fin s) ℂ := fun j l =>
  if (j : ℕ) + 1 = s then
    z * (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
      ((-m.α (Fin.castSucc l) : ℝ) : ℂ)
  else 0

/-- §521 block form: past-`h*f` rows against past-`h*f` columns. -/
noncomputable def toGLM_stabilityMatrixPHF (m : LMM s) (z : ℂ) :
    Matrix (Fin s) (Fin s) ℂ := fun j l =>
  if (j : ℕ) + 1 = s then
    z * (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
      ((m.β (Fin.castSucc l) : ℝ) : ℂ)
  else if (l : ℕ) = (j : ℕ) + 1 then (1 : ℂ) else 0

theorem toGLM_stabilityMatrix_castAdd_castAdd_apply (m : LMM s) (z : ℂ)
    (j l : Fin s) :
    m.toGLM.stabilityMatrix z
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) =
      toGLM_stabilityMatrixPY m z j l := by
  unfold toGLM_stabilityMatrixPY
  by_cases hj : (j : ℕ) + 1 = s
  · rw [if_pos hj]
    exact toGLM_stabilityMatrix_castAdd_last_castAdd_apply m z j hj l
  · rw [if_neg hj]
    rw [toGLM_stabilityMatrix_castAdd_shift_apply m z j hj]
    show ((m.toGLM.V
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) : ℝ) : ℂ) =
      if (l : ℕ) = (j : ℕ) + 1 then (1 : ℂ) else 0
    rw [toGLM_V_castAdd_shift_apply m j hj]
    by_cases hlj : (l : ℕ) = (j : ℕ) + 1 <;> simp [Fin.castAdd, hlj]

theorem toGLM_stabilityMatrix_castAdd_natAdd_apply (m : LMM s) (z : ℂ)
    (j l : Fin s) :
    m.toGLM.stabilityMatrix z
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l)) =
      toGLM_stabilityMatrixPYHF m z j l := by
  unfold toGLM_stabilityMatrixPYHF
  by_cases hj : (j : ℕ) + 1 = s
  · rw [if_pos hj]
    exact toGLM_stabilityMatrix_castAdd_last_natAdd_apply m z j hj l
  · rw [if_neg hj]
    rw [toGLM_stabilityMatrix_castAdd_shift_apply m z j hj]
    show ((m.toGLM.V
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l)) : ℝ) : ℂ) = 0
    rw [toGLM_V_castAdd_shift_apply m j hj]
    rw [if_neg]
    · norm_num
    · simp [Fin.natAdd]
      omega

theorem toGLM_stabilityMatrix_natAdd_castAdd_apply (m : LMM s) (z : ℂ)
    (j l : Fin s) :
    m.toGLM.stabilityMatrix z
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) =
      toGLM_stabilityMatrixPHFY m z j l := by
  unfold toGLM_stabilityMatrixPHFY
  by_cases hj : (j : ℕ) + 1 = s
  · rw [if_pos hj]
    exact toGLM_stabilityMatrix_natAdd_last_castAdd_apply m z j hj l
  · rw [if_neg hj]
    rw [toGLM_stabilityMatrix_natAdd_shift_apply m z j hj]
    show ((m.toGLM.V
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s l)) : ℝ) : ℂ) = 0
    rw [toGLM_V_natAdd_shift_apply m j hj]
    rw [if_neg]
    · norm_num
    · simp [Fin.castAdd]
      omega

theorem toGLM_stabilityMatrix_natAdd_natAdd_apply (m : LMM s) (z : ℂ)
    (j l : Fin s) :
    m.toGLM.stabilityMatrix z
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l)) =
      toGLM_stabilityMatrixPHF m z j l := by
  unfold toGLM_stabilityMatrixPHF
  by_cases hj : (j : ℕ) + 1 = s
  · rw [if_pos hj]
    exact toGLM_stabilityMatrix_natAdd_last_natAdd_apply m z j hj l
  · rw [if_neg hj]
    rw [toGLM_stabilityMatrix_natAdd_shift_apply m z j hj]
    show ((m.toGLM.V
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j))
        (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s l)) : ℝ) : ℂ) =
      if (l : ℕ) = (j : ℕ) + 1 then (1 : ℂ) else 0
    rw [toGLM_V_natAdd_shift_apply m j hj]
    by_cases hlj : (l : ℕ) = (j : ℕ) + 1
    · rw [if_pos (by simp [Fin.natAdd]; omega), if_pos hlj]
      norm_num
    · rw [if_neg (by simp [Fin.natAdd]; omega), if_neg hlj]
      norm_num

/-- §521 — Reindexing the LMM-as-GLM stability matrix by the past-`y` /
past-`h*f` split exposes the four closed-form `s × s` blocks. -/
theorem toGLM_stabilityMatrix_eq_fromBlocks (m : LMM s) (z : ℂ) :
    m.toGLM.stabilityMatrix z =
      Matrix.reindex (toGLM_stabilityBlockEquiv s) (toGLM_stabilityBlockEquiv s)
        (Matrix.fromBlocks
          (toGLM_stabilityMatrixPY m z) (toGLM_stabilityMatrixPYHF m z)
          (toGLM_stabilityMatrixPHFY m z) (toGLM_stabilityMatrixPHF m z)) := by
  let blocks : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℂ :=
    Matrix.fromBlocks
      (toGLM_stabilityMatrixPY m z) (toGLM_stabilityMatrixPYHF m z)
      (toGLM_stabilityMatrixPHFY m z) (toGLM_stabilityMatrixPHF m z)
  suffices h :
      ∀ kc lc : Fin (s + s),
        m.toGLM.stabilityMatrix z
            (Fin.cast (Nat.two_mul s).symm kc)
            (Fin.cast (Nat.two_mul s).symm lc) =
          (Matrix.reindex (toGLM_stabilityBlockEquiv s) (toGLM_stabilityBlockEquiv s)
            blocks)
            (Fin.cast (Nat.two_mul s).symm kc)
            (Fin.cast (Nat.two_mul s).symm lc) by
    ext k l
    simpa [blocks] using h (Fin.cast (Nat.two_mul s) k) (Fin.cast (Nat.two_mul s) l)
  intro kc lc
  refine kc.addCases (motive := fun kc' =>
      m.toGLM.stabilityMatrix z
          (Fin.cast (Nat.two_mul s).symm kc')
          (Fin.cast (Nat.two_mul s).symm lc) =
        (Matrix.reindex (toGLM_stabilityBlockEquiv s) (toGLM_stabilityBlockEquiv s)
          blocks)
          (Fin.cast (Nat.two_mul s).symm kc')
          (Fin.cast (Nat.two_mul s).symm lc)) ?_ ?_
  · intro j
    refine lc.addCases (motive := fun lc' =>
        m.toGLM.stabilityMatrix z
            (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
            (Fin.cast (Nat.two_mul s).symm lc') =
          (Matrix.reindex (toGLM_stabilityBlockEquiv s) (toGLM_stabilityBlockEquiv s)
            blocks)
            (Fin.cast (Nat.two_mul s).symm (Fin.castAdd s j))
            (Fin.cast (Nat.two_mul s).symm lc')) ?_ ?_
    · intro l
      simpa [blocks, Matrix.reindex, Matrix.fromBlocks]
        using toGLM_stabilityMatrix_castAdd_castAdd_apply m z j l
    · intro l
      simpa [blocks, Matrix.reindex, Matrix.fromBlocks]
        using toGLM_stabilityMatrix_castAdd_natAdd_apply m z j l
  · intro j
    refine lc.addCases (motive := fun lc' =>
        m.toGLM.stabilityMatrix z
            (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j))
            (Fin.cast (Nat.two_mul s).symm lc') =
          (Matrix.reindex (toGLM_stabilityBlockEquiv s) (toGLM_stabilityBlockEquiv s)
            blocks)
            (Fin.cast (Nat.two_mul s).symm (Fin.natAdd s j))
            (Fin.cast (Nat.two_mul s).symm lc')) ?_ ?_
    · intro l
      simpa [blocks, Matrix.reindex, Matrix.fromBlocks]
        using toGLM_stabilityMatrix_natAdd_castAdd_apply m z j l
    · intro l
      simpa [blocks, Matrix.reindex, Matrix.fromBlocks]
        using toGLM_stabilityMatrix_natAdd_natAdd_apply m z j l

/-- §521 — In a non-final past-`y` row of the PY block, the entry is the
pure shift indicator: `1` at the next column, `0` otherwise. -/
theorem toGLM_stabilityMatrixPY_apply_shift
    (m : LMM s) (z : ℂ) (j : Fin s) (hj : (j : ℕ) + 1 ≠ s) (l : Fin s) :
    toGLM_stabilityMatrixPY m z j l =
      (if (l : ℕ) = (j : ℕ) + 1 then (1 : ℂ) else 0) := by
  unfold toGLM_stabilityMatrixPY
  rw [if_neg hj]

/-- §521 — In the final past-`y` row of the PY block, the entry simplifies to
`-α l / (1 - z · β_s)` once the resolvent denominator is non-zero. -/
theorem toGLM_stabilityMatrixPY_apply_last_of_bdf
    (m : LMM s) (z : ℂ)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0)
    (j : Fin s) (hj : (j : ℕ) + 1 = s) (l : Fin s) :
    toGLM_stabilityMatrixPY m z j l =
      ((-m.α (Fin.castSucc l) : ℝ) : ℂ) /
        (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) := by
  unfold toGLM_stabilityMatrixPY
  rw [if_pos hj]
  field_simp
  ring

/-- §521 rank-one base matrix: the complex lift of the underlying `V` shift
block. -/
noncomputable def toGLM_V_active_lift (m : LMM s) :
    Matrix (Fin (2 * s)) (Fin (2 * s)) ℂ :=
  m.toGLM.Vℂ

/-- §521 rank-one correction column: only the implicit output rows can
consume the one-stage resolvent. -/
noncomputable def toGLM_rankOneColumn (m : LMM s) (z : ℂ) :
    Fin (2 * s) → ℂ := fun k => z * m.toGLM.Bℂ k 0

/-- §521 rank-one correction row: the one-stage `U` row over past data. -/
noncomputable def toGLM_rankOneRow (m : LMM s) :
    Fin (2 * s) → ℂ := fun l => m.toGLM.Uℂ 0 l

/-- §521 rank-one correction for the one-stage LMM-as-GLM stability matrix. -/
noncomputable def toGLM_rankOneCorrection (m : LMM s) (z : ℂ) :
    Matrix (Fin (2 * s)) (Fin (2 * s)) ℂ :=
  Matrix.vecMulVec (toGLM_rankOneColumn m z) (toGLM_rankOneRow m)

/-- §521 — The one-stage resolvent contribution to the LMM-as-GLM stability
matrix is a rank-one update of the complex `V` block. -/
theorem toGLM_stabilityMatrix_eq_V_active_plus_rank_one
    (m : LMM s) (z : ℂ) (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) :
    m.toGLM.stabilityMatrix z =
      toGLM_V_active_lift m +
        (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) •
          toGLM_rankOneCorrection m z := by
  have _ := hz
  ext k l
  rw [toGLM_stabilityMatrix_apply, toGLM_resolvent_apply]
  simp [toGLM_V_active_lift, toGLM_rankOneCorrection, toGLM_rankOneColumn,
    toGLM_rankOneRow, Matrix.vecMulVec_apply]
  ring

/-- §521 — Under the BDF hypothesis, the past-`y` rows have no dependence on
past `h*f` columns. -/
theorem toGLM_stabilityMatrixPYHF_eq_zero_of_bdf
    (m : LMM s) (z : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0) :
    toGLM_stabilityMatrixPYHF m z = 0 := by
  ext j l
  change toGLM_stabilityMatrixPYHF m z j l = (0 : ℂ)
  unfold toGLM_stabilityMatrixPYHF
  by_cases hj : (j : ℕ) + 1 = s
  · rw [if_pos hj]
    have hlne : (Fin.castSucc l) ≠ Fin.last s := by
      intro hl
      have : (l : ℕ) = s := by
        have := congrArg (Fin.val) hl
        simpa [Fin.castSucc, Fin.last] using this
      exact absurd this (by have := l.isLt; omega)
    have hβ : m.β (Fin.castSucc l) = 0 := hbdf (Fin.castSucc l) hlne
    rw [hβ]
    push_cast
    ring_nf
  · rw [if_neg hj]

/-- §521 — Under the BDF hypothesis (only the last `β` coefficient is
non-zero), the past-`h*f` block of the LMM-as-GLM stability matrix
collapses to the pure shift companion: no `z`-dependence, no resolvent
prefactor. -/
theorem toGLM_stabilityMatrixPHF_apply_of_bdf
    (m : LMM s) (z : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (j l : Fin s) :
    toGLM_stabilityMatrixPHF m z j l =
      (if (l : ℕ) = (j : ℕ) + 1 then (1 : ℂ) else 0) := by
  unfold toGLM_stabilityMatrixPHF
  by_cases hj : (j : ℕ) + 1 = s
  · rw [if_pos hj]
    have hlne : (Fin.castSucc l) ≠ Fin.last s := by
      intro hl
      have : (l : ℕ) = s := by
        have := congrArg (Fin.val) hl
        simpa [Fin.castSucc, Fin.last] using this
      exact absurd this (by have := l.isLt; omega)
    have hβ : m.β (Fin.castSucc l) = 0 := hbdf (Fin.castSucc l) hlne
    rw [hβ]
    push_cast
    rw [if_neg]
    · ring
    · intro hlj
      have hl_lt : (l : ℕ) < s := l.isLt
      omega
  · rw [if_neg hj]

/-- §521 — Under the BDF hypothesis, the past-`h*f` block is upper
triangular in the `Fin s` order. Off-diagonal nonzero entries live
strictly above the diagonal at `(l : ℕ) = (j : ℕ) + 1`. -/
theorem toGLM_stabilityMatrixPHF_blockTriangular_of_bdf
    (m : LMM s) (z : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0) :
    (toGLM_stabilityMatrixPHF m z).BlockTriangular id := by
  intro j l hlt
  rw [toGLM_stabilityMatrixPHF_apply_of_bdf m z hbdf j l]
  rw [if_neg]
  intro h
  -- `hlt : id l < id j`, i.e. `(l : ℕ) < (j : ℕ)`; `h : (l : ℕ) = (j : ℕ) + 1`
  simp [id] at hlt
  omega

/-- §521 — Under the BDF hypothesis, the past-`h*f` block has
characteristic polynomial `X^s`. The diagonal of the upper-triangular
matrix is identically zero (since `(j : ℕ) ≠ (j : ℕ) + 1`), so each
linear factor in the diagonal product collapses to `X`. -/
theorem toGLM_stabilityMatrixPHF_charpoly_of_bdf
    (m : LMM s) (z : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0) :
    (toGLM_stabilityMatrixPHF m z).charpoly =
      (Polynomial.X : Polynomial ℂ) ^ s := by
  rw [Matrix.charpoly_of_upperTriangular _
        (toGLM_stabilityMatrixPHF_blockTriangular_of_bdf m z hbdf)]
  have hdiag : ∀ j : Fin s,
      (Polynomial.X - Polynomial.C (toGLM_stabilityMatrixPHF m z j j)) =
      (Polynomial.X : Polynomial ℂ) := by
    intro j
    rw [toGLM_stabilityMatrixPHF_apply_of_bdf m z hbdf j j]
    rw [if_neg (by omega)]
    simp
  simp [hdiag, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- §521 — For BDF-type LMMs, the full LMM-as-GLM stability matrix has the
same characteristic polynomial as the active past-`y` block, multiplied by
the nilpotent past-`h*f` shift factor. -/
theorem toGLM_stabilityMatrix_charpoly_of_bdf
    (m : LMM s) (z : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0) :
    (m.toGLM.stabilityMatrix z).charpoly =
      (toGLM_stabilityMatrixPY m z).charpoly *
        (Polynomial.X : Polynomial ℂ) ^ s := by
  rw [toGLM_stabilityMatrix_eq_fromBlocks m z]
  rw [Matrix.charpoly_reindex]
  rw [toGLM_stabilityMatrixPYHF_eq_zero_of_bdf m z hbdf]
  rw [Matrix.charpoly_fromBlocks_zero₁₂]
  rw [toGLM_stabilityMatrixPHF_charpoly_of_bdf m z hbdf]

/-- §521 helper: the bottom-row companion matrix with shift rows above it. -/
private noncomputable def toGLM_stabilityMatrixPYCompanion (a : Fin s → ℂ) :
    Matrix (Fin s) (Fin s) ℂ := fun j l =>
  if (j : ℕ) + 1 = s then a l
  else if (l : ℕ) = (j : ℕ) + 1 then 1 else 0

/-- §521 helper: characteristic polynomial of the bottom-row companion shape
used by the BDF past-`y` block. -/
private theorem toGLM_stabilityMatrixPYCompanion_charpoly (a : Fin s → ℂ) :
    (toGLM_stabilityMatrixPYCompanion a).charpoly =
      (Polynomial.X : Polynomial ℂ) ^ s -
        ∑ l : Fin s, Polynomial.C (a l) * Polynomial.X ^ (l : ℕ) := by
  induction s with
  | zero =>
      simp [Matrix.charpoly]
  | succ n ih =>
      cases n with
      | zero =>
          simp [Matrix.charpoly, toGLM_stabilityMatrixPYCompanion]
      | succ n =>
          rw [Matrix.charpoly, Matrix.det_succ_column_zero]
          have htail :
              (toGLM_stabilityMatrixPYCompanion a).charmatrix.submatrix Fin.succ Fin.succ =
                (toGLM_stabilityMatrixPYCompanion
                  (fun i : Fin (n + 1) => a i.succ)).charmatrix := by
            ext i j k
            by_cases hij : i = j
            · subst j
              simp [Matrix.charmatrix, toGLM_stabilityMatrixPYCompanion]
            · have hsij : i.succ ≠ j.succ := by
                intro h
                exact hij (Fin.succ_injective _ h)
              simp [Matrix.charmatrix, toGLM_stabilityMatrixPYCompanion, hij, hsij]
          have htail_det :
              ((toGLM_stabilityMatrixPYCompanion a).charmatrix.submatrix
                  Fin.succ Fin.succ).det =
                (toGLM_stabilityMatrixPYCompanion
                  (fun i : Fin (n + 1) => a i.succ)).charpoly := by
            rw [htail, Matrix.charpoly]
          have hlast :
              ((toGLM_stabilityMatrixPYCompanion a).charmatrix.submatrix
                  Fin.castSucc Fin.succ).det =
                (-1 : Polynomial ℂ) ^ (n + 1) := by
            let B :=
              (toGLM_stabilityMatrixPYCompanion a).charmatrix.submatrix
                Fin.castSucc Fin.succ
            have htri : B.BlockTriangular OrderDual.toDual := by
              intro i j hij
              have hij' : (i : ℕ) < (j : ℕ) := by simpa using hij
              have hi_not : (i : ℕ) ≠ n + 1 := by omega
              have hji_ne : (j : ℕ) ≠ (i : ℕ) := by omega
              have hdiagOff :
                  (Fin.castSucc i : Fin (n + 1 + 1)) ≠
                    (Fin.succ j : Fin (n + 1 + 1)) := by
                intro h
                have hv := congrArg Fin.val h
                simp at hv
                omega
              simp [B, Matrix.charmatrix, toGLM_stabilityMatrixPYCompanion,
                hi_not, hji_ne, hdiagOff]
            rw [Matrix.det_of_lowerTriangular B htri]
            have hdiag : ∀ i : Fin (n + 1), B i i = (-1 : Polynomial ℂ) := by
              intro i
              have hne :
                  (Fin.castSucc i : Fin (n + 1 + 1)) ≠
                    (Fin.succ i : Fin (n + 1 + 1)) := by
                intro h
                have hv := congrArg Fin.val h
                simp at hv
              have hi_not : (i : ℕ) ≠ n + 1 := by omega
              simp [B, Matrix.charmatrix, toGLM_stabilityMatrixPYCompanion,
                hne, hi_not]
            simp [hdiag, Finset.prod_const, Fintype.card_fin]
          have hnotLast : ∀ x : Fin n, (x : ℕ) ≠ n := by
            intro x
            omega
          rw [Fin.sum_univ_succ]
          rw [Fin.sum_univ_castSucc]
          simp [toGLM_stabilityMatrixPYCompanion, htail_det, hlast, hnotLast]
          rw [ih (fun i : Fin (n + 1) => a i.succ)]
          conv_lhs =>
            rw [Fin.sum_univ_succ]
          conv_rhs =>
            rw [Fin.sum_univ_succ]
            rw [Fin.sum_univ_succ]
          simp
          have hsign :
              (-1 : Polynomial ℂ) ^ (n + 1) * Polynomial.C (a 0) *
                  (-1) ^ (n + 1) =
                Polynomial.C (a 0) := by
            calc
              (-1 : Polynomial ℂ) ^ (n + 1) * Polynomial.C (a 0) *
                    (-1) ^ (n + 1)
                  = Polynomial.C (a 0) *
                      (((-1 : Polynomial ℂ) ^ (n + 1)) *
                        ((-1) ^ (n + 1))) := by
                    ring
              _ = Polynomial.C (a 0) * ((-1 : Polynomial ℂ) ^ (2 * (n + 1))) := by
                    rw [← pow_add]
                    have hpow : (n + 1) + (n + 1) = 2 * (n + 1) := by omega
                    rw [hpow]
              _ = Polynomial.C (a 0) := by
                    rw [pow_mul]
                    simp
          rw [hsign]
          simp_rw [mul_sub, mul_add, Finset.mul_sum]
          have hpow_main :
              Polynomial.X * Polynomial.X ^ (n + 1) =
                (Polynomial.X : Polynomial ℂ) ^ (n + 1 + 1) := by
            rw [← pow_succ']
          have hsum_pow :
              (∑ i : Fin n,
                  Polynomial.X *
                    (Polynomial.C (a i.succ.succ) *
                      Polynomial.X ^ ((i : ℕ) + 1))) =
                ∑ i : Fin n,
                  Polynomial.C (a i.succ.succ) *
                    Polynomial.X ^ ((i : ℕ) + 1 + 1) := by
            apply Finset.sum_congr rfl
            intro i _
            calc
              Polynomial.X *
                    (Polynomial.C (a i.succ.succ) *
                      Polynomial.X ^ ((i : ℕ) + 1))
                  = Polynomial.C (a i.succ.succ) *
                      (Polynomial.X * Polynomial.X ^ ((i : ℕ) + 1)) := by
                    ring
              _ = Polynomial.C (a i.succ.succ) *
                    Polynomial.X ^ ((i : ℕ) + 1 + 1) := by
                    rw [← pow_succ']
          rw [hpow_main, hsum_pow]
          ring_nf

/-- §521 — General LMM PHF block as the bottom-row companion matrix with
coefficients `z · β_castSucc l / D` (no BDF hypothesis). The PHF block has
the exact shape of `toGLM_stabilityMatrixPYCompanion` by definition. -/
private theorem toGLM_stabilityMatrixPHF_eq_companion
    (m : LMM s) (z : ℂ) :
    toGLM_stabilityMatrixPHF m z =
      toGLM_stabilityMatrixPYCompanion
        (fun l : Fin s =>
          z * (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
            ((m.β (Fin.castSucc l) : ℝ) : ℂ)) := by
  rfl

/-- §521 — General LMM PHF block characteristic polynomial (drops the BDF
hypothesis from cycle 643's `_of_bdf`). The bottom row carries
`z · β_castSucc l / D` entries where `D = 1 - z · β_last`. -/
theorem toGLM_stabilityMatrixPHF_charpoly (m : LMM s) (z : ℂ) :
    (toGLM_stabilityMatrixPHF m z).charpoly =
      (Polynomial.X : Polynomial ℂ) ^ s -
        ∑ l : Fin s,
          Polynomial.C
            (z * (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
              ((m.β (Fin.castSucc l) : ℝ) : ℂ)) *
            Polynomial.X ^ (l : ℕ) := by
  rw [toGLM_stabilityMatrixPHF_eq_companion]
  exact toGLM_stabilityMatrixPYCompanion_charpoly _

/-- §521 — BDF specialisation of the general PHF charpoly. Recovers
`toGLM_stabilityMatrixPHF_charpoly_of_bdf` as a one-liner consequence of the
general theorem. Kept as a `'`-suffixed sanity check; the original
`_of_bdf` (proved via upper-triangularity) is preserved unchanged. -/
theorem toGLM_stabilityMatrixPHF_charpoly_of_bdf'
    (m : LMM s) (z : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0) :
    (toGLM_stabilityMatrixPHF m z).charpoly =
      (Polynomial.X : Polynomial ℂ) ^ s := by
  rw [toGLM_stabilityMatrixPHF_charpoly]
  have hβ : ∀ l : Fin s, m.β (Fin.castSucc l) = 0 := by
    intro l
    refine hbdf (Fin.castSucc l) ?_
    intro h
    have hv := congrArg Fin.val h
    have hl_lt : (l : ℕ) < s := l.isLt
    simp [Fin.castSucc, Fin.last] at hv
    omega
  simp [hβ]

/-- §521 — Under the BDF denominator hypothesis, the active past-`y` block is
the bottom-row companion matrix with coefficients `-α_l / (1 - z β_s)`. -/
private theorem toGLM_stabilityMatrixPY_eq_companion_of_bdf
    (m : LMM s) (z : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) :
    toGLM_stabilityMatrixPY m z =
      toGLM_stabilityMatrixPYCompanion
        (fun l : Fin s =>
          (((-m.α (Fin.castSucc l) : ℝ) : ℂ) /
            (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)))) := by
  have _ := hbdf
  ext j l
  by_cases hj : (j : ℕ) + 1 = s
  · rw [toGLM_stabilityMatrixPY_apply_last_of_bdf m z hz j hj l]
    simp [toGLM_stabilityMatrixPYCompanion, hj]
  · rw [toGLM_stabilityMatrixPY_apply_shift m z j hj l]
    simp [toGLM_stabilityMatrixPYCompanion, hj]

/-- §521 — For BDF-type LMMs, the active past-`y` block has the expected
monic companion characteristic polynomial. -/
theorem toGLM_stabilityMatrixPY_charpoly_of_bdf
    (m : LMM s) (z : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) :
    (toGLM_stabilityMatrixPY m z).charpoly =
      (Polynomial.X : Polynomial ℂ) ^ s -
        ∑ l : Fin s,
          Polynomial.C
            (((-m.α (Fin.castSucc l) : ℝ) : ℂ) /
              (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
            Polynomial.X ^ (l : ℕ) := by
  rw [toGLM_stabilityMatrixPY_eq_companion_of_bdf m z hbdf hz]
  exact toGLM_stabilityMatrixPYCompanion_charpoly
    (fun l : Fin s =>
      (((-m.α (Fin.castSucc l) : ℝ) : ℂ) /
        (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))))

/-- §521 — In the final past-`y` row of the PY block, the entry simplifies to
`-α l / (1 - z · β_s)` once the resolvent denominator is non-zero. This
generalises `toGLM_stabilityMatrixPY_apply_last_of_bdf` by dropping the
unused `hbdf` argument. -/
theorem toGLM_stabilityMatrixPY_apply_last
    (m : LMM s) (z : ℂ)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0)
    (j : Fin s) (hj : (j : ℕ) + 1 = s) (l : Fin s) :
    toGLM_stabilityMatrixPY m z j l =
      ((-m.α (Fin.castSucc l) : ℝ) : ℂ) /
        (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) := by
  unfold toGLM_stabilityMatrixPY
  rw [if_pos hj]
  field_simp
  ring

/-- §521 — General LMM PY block as the bottom-row companion matrix with
coefficients `-α_l / (1 - z β_s)` (drops the BDF hypothesis from
`toGLM_stabilityMatrixPY_eq_companion_of_bdf`). -/
private theorem toGLM_stabilityMatrixPY_eq_companion
    (m : LMM s) (z : ℂ)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) :
    toGLM_stabilityMatrixPY m z =
      toGLM_stabilityMatrixPYCompanion
        (fun l : Fin s =>
          (((-m.α (Fin.castSucc l) : ℝ) : ℂ) /
            (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)))) := by
  ext j l
  by_cases hj : (j : ℕ) + 1 = s
  · rw [toGLM_stabilityMatrixPY_apply_last m z hz j hj l]
    simp [toGLM_stabilityMatrixPYCompanion, hj]
  · rw [toGLM_stabilityMatrixPY_apply_shift m z j hj l]
    simp [toGLM_stabilityMatrixPYCompanion, hj]

/-- §521 — General LMM PY block charpoly (drops the BDF hypothesis from
`toGLM_stabilityMatrixPY_charpoly_of_bdf`). -/
theorem toGLM_stabilityMatrixPY_charpoly
    (m : LMM s) (z : ℂ)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) :
    (toGLM_stabilityMatrixPY m z).charpoly =
      (Polynomial.X : Polynomial ℂ) ^ s -
        ∑ l : Fin s,
          Polynomial.C
            (((-m.α (Fin.castSucc l) : ℝ) : ℂ) /
              (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
            Polynomial.X ^ (l : ℕ) := by
  rw [toGLM_stabilityMatrixPY_eq_companion m z hz]
  exact toGLM_stabilityMatrixPYCompanion_charpoly _

/-- §521 — At `z = 0`, the past-`h*f` rows against past-`y` columns vanish
in the LMM-as-GLM block decomposition. The opposite off-diagonal block does
not vanish in general; it contains the structural `β` entries from `Vℂ`. -/
theorem toGLM_stabilityMatrixPHFY_zero (m : LMM s) :
    toGLM_stabilityMatrixPHFY m 0 = 0 := by
  ext j l
  simp [toGLM_stabilityMatrixPHFY]

/-- §521 — Block form of the active `Vℂ` matrix at `z = 0`. The lower-left
off-diagonal block is zero, while the upper-right block is the nonzero
structural past-`y`/past-`h*f` block `toGLM_stabilityMatrixPYHF m 0`. -/
theorem toGLM_V_active_lift_eq_fromBlocks_zero (m : LMM s) :
    m.toGLM.Vℂ =
      Matrix.reindex (toGLM_stabilityBlockEquiv s) (toGLM_stabilityBlockEquiv s)
        (Matrix.fromBlocks
          (toGLM_stabilityMatrixPY m 0) (toGLM_stabilityMatrixPYHF m 0)
          0 (toGLM_stabilityMatrixPHF m 0)) := by
  rw [← GeneralLinearMethod.stabilityMatrix_zero m.toGLM,
    toGLM_stabilityMatrix_eq_fromBlocks m 0, toGLM_stabilityMatrixPHFY_zero m]

/-- §521 — The active `Vℂ` characteristic polynomial factors into the two
diagonal block characteristic polynomials at `z = 0`. This uses the
lower-left zero block; no BDF hypothesis is required. -/
theorem toGLM_V_active_charpoly (m : LMM s) :
    m.toGLM.Vℂ.charpoly =
      (toGLM_stabilityMatrixPY m 0).charpoly *
        (toGLM_stabilityMatrixPHF m 0).charpoly := by
  rw [toGLM_V_active_lift_eq_fromBlocks_zero m, Matrix.charpoly_reindex,
    Matrix.charpoly_fromBlocks_zero₂₁]

/-- §521 — Polynomial-valued LMM stability polynomial at fixed `z`:
package `ρ(X) - z · σ(X)` as a polynomial in `X` (a polynomial of
degree at most `s`) rather than a scalar function of `ξ`. -/
noncomputable def stabilityPolyPoly (m : LMM s) (z : ℂ) : Polynomial ℂ :=
  ∑ j : Fin (s + 1),
    Polynomial.C (((m.α j : ℝ) : ℂ) - z * ((m.β j : ℝ) : ℂ)) *
      Polynomial.X ^ (j : ℕ)

/-- §521 — Evaluating `stabilityPolyPoly` at `ξ` recovers the scalar
`stabilityPoly` defined in `OpenMath/MultistepMethods.lean`. -/
theorem stabilityPolyPoly_eval (m : LMM s) (ξ z : ℂ) :
    (m.stabilityPolyPoly z).eval ξ = m.stabilityPoly ξ z := by
  unfold stabilityPolyPoly stabilityPoly rhoC sigmaC
  rw [Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- §521 — Degree bookkeeping for `stabilityPolyPoly`: it is a polynomial
of degree at most `s` (the number of steps). -/
theorem stabilityPolyPoly_natDegree_le (m : LMM s) (z : ℂ) :
    (m.stabilityPolyPoly z).natDegree ≤ s := by
  unfold stabilityPolyPoly
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, ?_⟩
  intro j _
  refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
  exact Nat.le_of_lt_succ j.isLt

/-- §521 — BDF specialisation bridge: under the BDF hypothesis, the
characteristic polynomial of the active past-`y` block of the GLM
stability matrix is proportional to `stabilityPolyPoly`. The non-zero
proportionality constant is `1 - z · β_last`. -/
theorem toGLM_stabilityMatrixPY_charpoly_eq_stabilityPolyPoly_of_bdf
    (m : LMM s) (z : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) :
    (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) •
        (toGLM_stabilityMatrixPY m z).charpoly =
      m.stabilityPolyPoly z := by
  set c : ℂ := 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) with hc_def
  rw [toGLM_stabilityMatrixPY_charpoly_of_bdf m z hbdf hz]
  unfold stabilityPolyPoly
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  have hbeta_cast : ∀ l : Fin s, m.β (Fin.castSucc l) = 0 := fun l =>
    hbdf (Fin.castSucc l) (Fin.castSucc_lt_last l).ne
  have halpha_last : m.α (Fin.last s) = 1 := m.normalized
  have hRHS_sum :
      (∑ l : Fin s,
          Polynomial.C (((m.α (Fin.castSucc l) : ℝ) : ℂ) -
              z * ((m.β (Fin.castSucc l) : ℝ) : ℂ)) *
            Polynomial.X ^ (l : ℕ)) =
        ∑ l : Fin s,
          Polynomial.C ((m.α (Fin.castSucc l) : ℝ) : ℂ) *
            Polynomial.X ^ (l : ℕ) := by
    apply Finset.sum_congr rfl
    intro l _
    have hb0 : ((m.β (Fin.castSucc l) : ℝ) : ℂ) = 0 := by
      rw [hbeta_cast l]; norm_cast
    rw [hb0, mul_zero, sub_zero]
  rw [hRHS_sum, halpha_last]
  have hC_last : (((1 : ℝ) : ℂ) - z * ((m.β (Fin.last s) : ℝ) : ℂ)) = c := by
    rw [hc_def]; push_cast; ring
  rw [hC_last]
  rw [smul_sub, Polynomial.smul_eq_C_mul, Finset.smul_sum]
  have hLHS_sum :
      (∑ l : Fin s,
          c • (Polynomial.C (((-m.α (Fin.castSucc l) : ℝ) : ℂ) / c) *
              Polynomial.X ^ (l : ℕ))) =
        ∑ l : Fin s,
          -(Polynomial.C ((m.α (Fin.castSucc l) : ℝ) : ℂ) *
              Polynomial.X ^ (l : ℕ)) := by
    apply Finset.sum_congr rfl
    intro l _
    rw [Polynomial.smul_eq_C_mul, ← mul_assoc, ← Polynomial.C_mul]
    rw [show c * (((-m.α (Fin.castSucc l) : ℝ) : ℂ) / c) =
        -((m.α (Fin.castSucc l) : ℝ) : ℂ) by
      field_simp; push_cast; ring]
    rw [Polynomial.C_neg]
    ring
  rw [hLHS_sum, Finset.sum_neg_distrib]
  ring

/-- §521 — Under the BDF denominator hypothesis, roots of the active
past-`y` block characteristic polynomial are exactly the roots of the
LMM scalar stability polynomial. -/
theorem toGLM_stabilityMatrixPY_charpoly_isRoot_iff_stabilityPoly_of_bdf
    (m : LMM s) (z : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (ξ : ℂ) :
    (toGLM_stabilityMatrixPY m z).charpoly.IsRoot ξ ↔
      m.stabilityPoly ξ z = 0 := by
  rw [Polynomial.IsRoot.def]
  have h_eval := congrArg (fun p : Polynomial ℂ => p.eval ξ)
    (toGLM_stabilityMatrixPY_charpoly_eq_stabilityPolyPoly_of_bdf m z hbdf hz)
  simp [Polynomial.eval_smul, smul_eq_mul, stabilityPolyPoly_eval] at h_eval
  constructor
  · intro hroot
    rw [← h_eval, hroot, mul_zero]
  · intro hstab
    have hmul :
        (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
            ((toGLM_stabilityMatrixPY m z).charpoly.eval ξ) = 0 := by
      rw [h_eval, hstab]
    exact (mul_eq_zero.mp hmul).resolve_left hz

/-- §521 — For nonzero-step BDF-type LMMs, roots of the full GLM
stability-matrix characteristic polynomial are either the nilpotent
past-`h*f` root `0` or roots of the LMM scalar stability polynomial. -/
theorem toGLM_stabilityMatrix_eigenvalue_iff_of_bdf [NeZero s]
    (m : LMM s) (z : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (ξ : ℂ) :
    (m.toGLM.stabilityMatrix z).charpoly.IsRoot ξ ↔
      ξ = 0 ∨ m.stabilityPoly ξ z = 0 := by
  rw [toGLM_stabilityMatrix_charpoly_of_bdf m z hbdf]
  rw [Polynomial.root_mul]
  rw [toGLM_stabilityMatrixPY_charpoly_isRoot_iff_stabilityPoly_of_bdf m z hbdf hz ξ]
  have hxroot : ((Polynomial.X : Polynomial ℂ) ^ s).IsRoot ξ ↔ ξ = 0 := by
    rw [Polynomial.IsRoot.def]
    simpa [Polynomial.eval_pow, Polynomial.eval_X] using
      (pow_eq_zero_iff (NeZero.ne s) : ξ ^ s = 0 ↔ ξ = 0)
  rw [hxroot]
  exact or_comm

/-- §521 — BDF specialisation: classical LMM A-stability transports through
the §503 LMM-as-GLM embedding. The denominator hypothesis is kept explicit;
for concrete BDF methods it follows from positivity of the last `β`
coefficient on the closed left half-plane. -/
theorem toGLM_isAStable_of_bdf
    (m : LMM s) (ha : m.IsAStable)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hβ_last : ∀ z : ℂ, z.re ≤ 0 →
      1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) :
    m.toGLM.IsAStable := by
  intro z hz_re μ hμ
  by_cases hs : s = 0
  · subst s
    have hchar := toGLM_stabilityMatrix_charpoly_of_bdf m z hbdf
    rw [hchar] at hμ
    simp at hμ
  · haveI : NeZero s := ⟨hs⟩
    rcases (toGLM_stabilityMatrix_eigenvalue_iff_of_bdf
        m z hbdf (hβ_last z hz_re) μ).1 hμ with hzero | hstab
    · rw [hzero]
      simp
    · exact ha z hz_re μ hstab

/-- §521 — BDF specialisation: the §503 LMM-as-GLM embedding preserves
A-stability in both directions. The denominator hypothesis is the same
as for `toGLM_isAStable_of_bdf`. -/
theorem toGLM_isAStable_iff_of_bdf
    (m : LMM s)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hβ_last : ∀ z : ℂ, z.re ≤ 0 →
      1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) :
    m.toGLM.IsAStable ↔ m.IsAStable := by
  refine ⟨fun hG => ?_, fun ha => toGLM_isAStable_of_bdf m ha hbdf hβ_last⟩
  intro z hz_re ξ hξ
  by_cases hs : s = 0
  · subst hs
    -- For `s = 0` the stability polynomial collapses to `1 - z · β_last`,
    -- which `hβ_last` rules out on the closed left half-plane. Hence the
    -- root hypothesis `hξ` is contradictory.
    exfalso
    apply hβ_last z hz_re
    have hα0 : m.α 0 = 1 := by
      have := m.normalized
      simpa [Fin.last] using this
    have hξ' : (1 : ℂ) - z * ((m.β 0 : ℝ) : ℂ) = 0 := by
      have := hξ
      simp [LMM.stabilityPoly, LMM.rhoC, LMM.sigmaC, hα0] at this
      exact this
    simpa [Fin.last] using hξ'
  · haveI : NeZero s := ⟨hs⟩
    apply hG z hz_re ξ
    rw [toGLM_stabilityMatrix_eigenvalue_iff_of_bdf m z hbdf (hβ_last z hz_re)]
    exact Or.inr hξ

/-- §521 — BDF3 is **not** A-stable in the GLM sense. Direct consequence
of the BDF iff bridge `toGLM_isAStable_iff_of_bdf` and the classical
result `bdf3_not_aStable` (Dahlquist's second barrier). -/
theorem bdf3_toGLM_not_isAStable : ¬ bdf3.toGLM.IsAStable := by
  intro hG
  apply bdf3_not_aStable
  refine (toGLM_isAStable_iff_of_bdf bdf3 ?hbdf ?hβ).mp hG
  case hbdf =>
    intro l hl
    fin_cases l <;> simp [bdf3, Fin.last] at hl ⊢
  case hβ =>
    intro z hz_re h
    have hβ_val : (bdf3.β (Fin.last 3) : ℝ) = 6 / 11 := by
      simp [bdf3, Fin.last]
    rw [hβ_val] at h
    have hre := congrArg Complex.re h
    simp [Complex.sub_re, Complex.mul_re] at hre
    linarith

/-- §521 — BDF4 is **not** A-stable in the GLM sense. Direct consequence
of the BDF iff bridge `toGLM_isAStable_iff_of_bdf` and the classical
result `bdf4_not_aStable` (Dahlquist's second barrier). -/
theorem bdf4_toGLM_not_isAStable : ¬ bdf4.toGLM.IsAStable := by
  intro hG
  apply bdf4_not_aStable
  refine (toGLM_isAStable_iff_of_bdf bdf4 ?hbdf ?hβ).mp hG
  case hbdf =>
    intro l hl
    fin_cases l <;> simp [bdf4, Fin.last] at hl ⊢
  case hβ =>
    intro z hz_re h
    have hβ_val : (bdf4.β (Fin.last 4) : ℝ) = 12 / 25 := by
      simp [bdf4, Fin.last]
    rw [hβ_val] at h
    have hre := congrArg Complex.re h
    simp [Complex.sub_re, Complex.mul_re] at hre
    linarith

/-- §521 — Rank-one characteristic polynomial formula for the LMM-as-GLM
stability matrix, before simplifying the sparse dot-product term. -/
theorem toGLM_stabilityMatrix_charpoly_rankOne
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) :
    (m.toGLM.stabilityMatrix z).charpoly
      = (toGLM_V_active_lift m).charpoly
        - dotProduct (fun j => Polynomial.C ((toGLM_rankOneRow m) j))
            (((toGLM_V_active_lift m).charmatrix).adjugate.mulVec
               (fun i => Polynomial.C
                 (((1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) •
                    toGLM_rankOneColumn m z) i))) := by
  rw [toGLM_stabilityMatrix_eq_V_active_plus_rank_one m z hz]
  have hcorr :
      (1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) •
          toGLM_rankOneCorrection m z =
        Matrix.vecMulVec
          ((1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) •
            toGLM_rankOneColumn m z)
          (toGLM_rankOneRow m) := by
    ext i j
    simp [toGLM_rankOneCorrection, Matrix.vecMulVec_apply, Pi.smul_apply,
      smul_eq_mul, mul_assoc]
  rw [hcorr]
  exact Matrix.charpoly_add_vecMulVec (toGLM_V_active_lift m)
    ((1 / (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) • toGLM_rankOneColumn m z)
    (toGLM_rankOneRow m)

end LMM

/-- §521 — Backward Euler is A-stable in the GLM sense after the §503
embedding. One-shot consequence of the BDF iff bridge
`toGLM_isAStable_iff_of_bdf` and `backwardEuler_aStable`. -/
theorem backwardEuler_toGLM_isAStable :
    backwardEuler.toGLM.IsAStable := by
  refine (LMM.toGLM_isAStable_iff_of_bdf backwardEuler ?hbdf ?hβ).mpr
    backwardEuler_aStable
  case hbdf =>
    intro l hl
    fin_cases l <;> simp [backwardEuler, Fin.last] at hl ⊢
  case hβ =>
    intro z hz_re h
    have hβ_val : (backwardEuler.β (Fin.last 1) : ℝ) = 1 := by
      simp [backwardEuler, Fin.last]
    rw [hβ_val] at h
    have hre := congrArg Complex.re h
    simp [Complex.sub_re] at hre
    linarith

/-- §521 — The trapezoidal rule is A-stable in the GLM sense after the
§503 embedding. At `s = 1`, the `2 × 2` stability matrix is rank one with
trace `(2 + z)/(2 - z)`, so its characteristic polynomial factors as
`X * (X - C ((2 + z)/(2 - z)))`. -/
theorem trapezoidalRule_toGLM_isAStable :
    trapezoidalRule.toGLM.IsAStable := by
  intro z hz μ hμ
  have hne : (2 : ℂ) - z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [Complex.sub_re] at hre
    linarith
  have hM : trapezoidalRule.toGLM.stabilityMatrix z =
      !![2 / (2 - z), 1 / (2 - z);
        2 * z / (2 - z), z / (2 - z)] := by
    ext k l
    rw [LMM.toGLM_stabilityMatrix_apply]
    have hAℂ : trapezoidalRule.toGLM.Aℂ = !![(1 / 2 : ℂ)] := by
      ext i j
      fin_cases i; fin_cases j
      show (trapezoidalRule.β (Fin.last 1) : ℂ) = (!![(1 / 2 : ℂ)]) 0 0
      simp [trapezoidalRule]
    rw [hAℂ]
    have hsub : (1 : Matrix (Fin 1) (Fin 1) ℂ) - z • !![(1 / 2 : ℂ)] =
        !![1 - z / 2] := by
      ext i j
      fin_cases i; fin_cases j
      simp
      ring
    rw [hsub]
    have hinv : (!![1 - z / 2] : Matrix (Fin 1) (Fin 1) ℂ)⁻¹ 0 0 =
        1 / (1 - z / 2) := by
      rw [Matrix.inv_def]
      simp [Matrix.adjugate_fin_one]
    rw [hinv]
    fin_cases k <;> fin_cases l <;>
      simp [LMM.toGLM, trapezoidalRule, Fin.addCases, Fin.cast,
        GeneralLinearMethod.Vℂ, GeneralLinearMethod.Bℂ, GeneralLinearMethod.Uℂ,
        Fin.last]
    all_goals
      field_simp [hne]
      try ring
  rw [hM] at hμ
  have hchar :
      (!![2 / (2 - z), 1 / (2 - z);
        2 * z / (2 - z), z / (2 - z)] : Matrix (Fin 2) (Fin 2) ℂ).charpoly =
        Polynomial.X * (Polynomial.X - Polynomial.C ((2 + z) / (2 - z))) := by
    have htrace :
        (!![2 / (2 - z), 1 / (2 - z);
          2 * z / (2 - z), z / (2 - z)] : Matrix (Fin 2) (Fin 2) ℂ).trace =
          (2 + z) / (2 - z) := by
      simp [Matrix.trace]
      field_simp [hne]
    have hdet :
        (!![2 / (2 - z), 1 / (2 - z);
          2 * z / (2 - z), z / (2 - z)] : Matrix (Fin 2) (Fin 2) ℂ).det = 0 := by
      rw [Matrix.det_fin_two]
      simp
      field_simp [hne]
      ring
    rw [Matrix.charpoly_fin_two, htrace, hdet]
    simp
    rw [mul_sub]
    rw [mul_comm Polynomial.X (Polynomial.C ((2 + z) / (2 - z)))]
    ring
  rw [hchar] at hμ
  rw [Polynomial.IsRoot] at hμ
  simp at hμ
  rcases hμ with hμ0 | hμ1
  · rw [hμ0]; simp
  · have hμeq : μ = (2 + z) / (2 - z) := sub_eq_zero.mp hμ1
    rw [hμeq]
    have h_denom_pos : (0 : ℝ) < ‖(2 : ℂ) - z‖ := norm_pos_iff.mpr hne
    have h_nsq_le : ‖(2 : ℂ) + z‖ ^ 2 ≤ ‖(2 : ℂ) - z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re,
        Complex.add_im, Complex.sub_im]
      norm_num
      nlinarith
    have h_num_le : ‖(2 : ℂ) + z‖ ≤ ‖(2 : ℂ) - z‖ := by
      nlinarith [norm_nonneg ((2 : ℂ) + z), norm_nonneg ((2 : ℂ) - z),
        sq_nonneg (‖(2 : ℂ) - z‖ - ‖(2 : ℂ) + z‖)]
    rw [norm_div]
    exact (div_le_one h_denom_pos).mpr h_num_le

/-- §521 — BDF2 is A-stable in the GLM sense after the §503 embedding.
One-shot consequence of the BDF iff bridge `toGLM_isAStable_iff_of_bdf`
and `bdf2_aStable`. -/
theorem bdf2_toGLM_isAStable :
    bdf2.toGLM.IsAStable := by
  refine (LMM.toGLM_isAStable_iff_of_bdf bdf2 ?hbdf ?hβ).mpr bdf2_aStable
  case hbdf =>
    intro l hl
    fin_cases l <;> simp [bdf2, Fin.last] at hl ⊢
  case hβ =>
    intro z hz_re h
    have hβ_val : (bdf2.β (Fin.last 2) : ℝ) = 2 / 3 := by
      simp [bdf2, Fin.last]
    rw [hβ_val] at h
    have hre := congrArg Complex.re h
    simp [Complex.sub_re, Complex.mul_re] at hre
    linarith
