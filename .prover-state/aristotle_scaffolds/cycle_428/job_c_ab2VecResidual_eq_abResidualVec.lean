import OpenMath.LMMAB2Convergence
import OpenMath.LMMABGenericConvergence

namespace LMM

noncomputable def ab2GenericCoeff_cycle428C : Fin 2 → ℝ :=
  ![-(1 / 2 : ℝ), (3 / 2 : ℝ)]

@[simp] lemma ab2GenericCoeff_cycle428C_zero :
    ab2GenericCoeff_cycle428C 0 = -(1 / 2 : ℝ) := rfl

@[simp] lemma ab2GenericCoeff_cycle428C_one :
    ab2GenericCoeff_cycle428C 1 = (3 / 2 : ℝ) := rfl

/-- Bridge: the AB2 vector residual at base point `t₀ + n · h` equals the
generic AB vector residual at index `n`.

The AB2 residual is
`y(t + 2h) − y(t + h) − h • ((3/2) • y'(t + h) − (1/2) • y'(t))`
and the generic residual at `(s, n) = (2, n)` with `t = t₀ + n h` reads
`y(t₀ + (n+2)h) − y(t₀ + (n+1)h) − h • ∑_j α_j • y'(t₀ + (n+j)h)`. -/
theorem cycle428_ab2VecResidual_eq_abResidualVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (y : ℝ → E) (t₀ : ℝ) (n : ℕ) :
    ab2VecResidual h (t₀ + (n : ℝ) * h) y
      = abResidualVec 2 ab2GenericCoeff_cycle428C h y t₀ n := by
  sorry

end LMM
