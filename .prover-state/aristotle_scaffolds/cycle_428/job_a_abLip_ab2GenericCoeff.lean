import OpenMath.LMMABGenericConvergence

namespace LMM

/-- AB2 coefficient vector for the generic AB scaffold:
`α 0 = -1/2`, `α 1 = 3/2`. -/
noncomputable def ab2GenericCoeff_cycle428 : Fin 2 → ℝ := ![-(1 / 2 : ℝ), (3 / 2 : ℝ)]

@[simp] lemma ab2GenericCoeff_cycle428_zero :
    ab2GenericCoeff_cycle428 0 = -(1 / 2 : ℝ) := rfl

@[simp] lemma ab2GenericCoeff_cycle428_one :
    ab2GenericCoeff_cycle428 1 = (3 / 2 : ℝ) := rfl

/-- The effective Lipschitz constant for the generic AB scaffold at the
AB2 coefficient tuple is `2 · L`. -/
theorem cycle428_abLip_ab2GenericCoeff (L : ℝ) :
    abLip 2 ab2GenericCoeff_cycle428 L = 2 * L := by
  sorry

end LMM
