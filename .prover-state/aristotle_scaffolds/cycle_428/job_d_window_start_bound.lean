import OpenMath.LMMAB2Convergence
import OpenMath.LMMABGenericConvergence

namespace LMM

noncomputable def ab2GenericCoeff_cycle428D : Fin 2 → ℝ :=
  ![-(1 / 2 : ℝ), (3 / 2 : ℝ)]

@[simp] lemma ab2GenericCoeff_cycle428D_zero :
    ab2GenericCoeff_cycle428D 0 = -(1 / 2 : ℝ) := rfl

@[simp] lemma ab2GenericCoeff_cycle428D_one :
    ab2GenericCoeff_cycle428D 1 = (3 / 2 : ℝ) := rfl

/-- The window-max error at index 0 is bounded by the per-sample starting
error `ε₀`, given individual bounds at indices 0 and 1. The starting samples
are arranged as `![y₀, y₁] : Fin 2 → E`. -/
theorem cycle428_ab2Vec_window_start_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ : E) (y : ℝ → E)
    {ε₀ : ℝ}
    (he0_bd : ‖y₀ - y t₀‖ ≤ ε₀)
    (he1_bd : ‖y₁ - y (t₀ + h)‖ ≤ ε₀) :
    abErrWindowVec (show (1:ℕ) ≤ 2 by norm_num)
        ab2GenericCoeff_cycle428D h f t₀ ![y₀, y₁] y 0
      ≤ ε₀ := by
  sorry

end LMM
