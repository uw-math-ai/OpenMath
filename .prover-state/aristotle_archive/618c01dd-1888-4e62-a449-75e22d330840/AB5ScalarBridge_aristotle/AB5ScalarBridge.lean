import Mathlib
import OpenMath.LMMABGenericConvergence
import OpenMath.LMMAB5Convergence

/-! # AB5 scalar bridge lemmas

These two lemmas connect the explicit scalar AB5 definitions (`ab5Iter`, explicit
residual expression) with the generic s-step AB framework (`abIter`, `abResidual`)
instantiated at `s = 5` with `ab5GenericCoeff`.
-/

namespace LMM

/-
The scalar AB5 iteration equals the generic AB iteration at `s = 5`.
-/
theorem ab5Iter_eq_abIter
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ : ℝ) (n : ℕ) :
    ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ n
      = abIter 5 ab5GenericCoeff h f t₀ ![y₀, y₁, y₂, y₃, y₄] n := by
  induction' n using Nat.strong_induction_on with n ih;
  by_cases hn : n < 5;
  · interval_cases n <;> unfold ab5Iter abIter <;> norm_num;
  · unfold abIter;
    rcases n with ( _ | _ | _ | _ | _ | n ) <;> simp_all +decide [ Fin.sum_univ_succ ];
    unfold ab5Iter;
    simp_all +decide [ ab5GenericCoeff ];
    grind

/-
The scalar AB5 truncation residual at `t₀ + n·h` equals the generic AB residual.
-/
theorem ab5Residual_eq_abResidual
    (h : ℝ) (y : ℝ → ℝ) (t₀ : ℝ) (n : ℕ) :
    y (t₀ + (n : ℝ) * h + 5 * h) - y (t₀ + (n : ℝ) * h + 4 * h)
      - h * ((1901 / 720) * deriv y (t₀ + (n : ℝ) * h + 4 * h)
            - (2774 / 720) * deriv y (t₀ + (n : ℝ) * h + 3 * h)
            + (2616 / 720) * deriv y (t₀ + (n : ℝ) * h + 2 * h)
            - (1274 / 720) * deriv y (t₀ + (n : ℝ) * h + h)
            + (251 / 720) * deriv y (t₀ + (n : ℝ) * h))
      = abResidual 5 ab5GenericCoeff h y t₀ n := by
  unfold abResidual;
  norm_num [ Fin.sum_univ_succ, ab5GenericCoeff ] ; ring

end LMM