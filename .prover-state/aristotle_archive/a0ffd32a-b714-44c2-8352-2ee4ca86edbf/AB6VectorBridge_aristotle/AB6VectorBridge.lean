import Mathlib
import OpenMath.LMMABGenericConvergence
import OpenMath.LMMAB6VectorConvergence

/-! # AB6 vector bridge lemmas

These lemmas relate the concrete AB6 iteration / residual to the generic
AB scaffold instantiated at `s = 6` with the standard AB6 coefficient
vector `ab6GenericCoeff`.
-/

open Finset BigOperators

namespace LMM

/-- AB6 coefficient vector for the generic AB scaffold, oldest-to-newest. -/
noncomputable def ab6GenericCoeff : Fin 6 → ℝ :=
  ![-(475 : ℝ) / 1440, (2877 : ℝ) / 1440, -(7298 : ℝ) / 1440,
    (9982 : ℝ) / 1440, -(7923 : ℝ) / 1440, (4277 : ℝ) / 1440]

/-
The concrete AB6 vector iteration equals the generic AB iteration at `s = 6`.
-/
theorem ab6IterVec_eq_abIterVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ y₄ y₅ : E) (n : ℕ) :
    ab6IterVec h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ n
      = abIterVec 6 ab6GenericCoeff h f t₀ ![y₀, y₁, y₂, y₃, y₄, y₅] n := by
  induction' n using Nat.strong_induction_on with n ih;
  by_cases hn : n < 6;
  · interval_cases n <;> simp +decide [ ab6IterVec, abIterVec ];
  · rcases n with ( _ | _ | _ | _ | _ | _ | n ) <;> simp_all +decide;
    rw [ ab6IterVec, abIterVec ];
    simp +decide [ Fin.sum_univ_six, ab6GenericCoeff ];
    rw [ ih _ ( by linarith ), ih _ ( by linarith ), ih _ ( by linarith ), ih _ ( by linarith ), ih _ ( by linarith ), ih _ ( by linarith ) ];
    congr

/-
The concrete AB6 vector residual at `t₀ + n·h` equals the generic AB residual.
-/
theorem ab6VecResidual_eq_abResidualVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (y : ℝ → E) (t₀ : ℝ) (n : ℕ) :
    ab6VecResidual h (t₀ + (n : ℝ) * h) y
      = abResidualVec 6 ab6GenericCoeff h y t₀ n := by
  unfold ab6VecResidual abResidualVec ab6GenericCoeff;
  norm_num [ Fin.sum_univ_succ ];
  grind

end LMM