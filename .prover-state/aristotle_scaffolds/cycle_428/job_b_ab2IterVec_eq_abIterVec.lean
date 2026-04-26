import OpenMath.LMMAB2Convergence
import OpenMath.LMMABGenericConvergence

namespace LMM

/-- AB2 coefficient vector for the generic AB scaffold:
`α 0 = -1/2`, `α 1 = 3/2`. -/
noncomputable def ab2GenericCoeff_cycle428B : Fin 2 → ℝ :=
  ![-(1 / 2 : ℝ), (3 / 2 : ℝ)]

@[simp] lemma ab2GenericCoeff_cycle428B_zero :
    ab2GenericCoeff_cycle428B 0 = -(1 / 2 : ℝ) := rfl

@[simp] lemma ab2GenericCoeff_cycle428B_one :
    ab2GenericCoeff_cycle428B 1 = (3 / 2 : ℝ) := rfl

/-- Bridge: the AB2 vector iteration is the generic vector AB iteration
at `s = 2` with `α = ab2GenericCoeff` and starting samples `![y₀, y₁]`.

The AB2 recurrence is
`y_{n+2} = y_{n+1} + h • ((3/2) • f(t_{n+1}, y_{n+1}) − (1/2) • f(t_n, y_n))`
which is the generic recurrence
`y_{n+2} = y_{n+1} + h • ∑_{j : Fin 2} α_j • f(t_{n+j}, y_{n+j})`
with `α 0 = -1/2`, `α 1 = 3/2`. -/
theorem cycle428_ab2IterVec_eq_abIterVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ : E) (n : ℕ) :
    ab2IterVec h f t₀ y₀ y₁ n
      = abIterVec 2 ab2GenericCoeff_cycle428B h f t₀ ![y₀, y₁] n := by
  sorry

end LMM
