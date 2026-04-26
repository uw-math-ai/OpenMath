import Mathlib
import OpenMath.LMMABGenericConvergence
import OpenMath.LMMAB6ScalarConvergence

/-! Cycle 432 AB6 scalar bridge stubs. -/

namespace LMM

/-- AB6 coefficient vector for the generic AB scaffold, oldest-to-newest. -/
noncomputable def ab6GenericCoeff : Fin 6 → ℝ :=
  ![-(475 : ℝ) / 1440, (2877 : ℝ) / 1440, -(7298 : ℝ) / 1440,
    (9982 : ℝ) / 1440, -(7923 : ℝ) / 1440, (4277 : ℝ) / 1440]

theorem ab6_lip_eq (L : ℝ) :
    abLip 6 ab6GenericCoeff L = (114 / 5) * L := by
  unfold abLip ab6GenericCoeff;
  norm_num [ Fin.sum_univ_succ, abs_of_pos ]

theorem ab6_iter_eq_abIter
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ : ℝ) (n : ℕ) :
    ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ n
      = abIter 6 ab6GenericCoeff h f t₀ ![y₀, y₁, y₂, y₃, y₄, y₅] n := by
  unfold abIter;
  induction' n using Nat.strong_induction_on with n ih;
  by_cases hn : n < 6;
  · interval_cases n <;> rfl;
  · rcases n with ( _ | _ | _ | _ | _ | _ | n ) <;> norm_num [ Fin.sum_univ_succ ] at *;
    unfold ab6Iter;
    rw [ Nat.strongRecOn_eq ];
    simp +arith +decide [ Fin.succ, ab6GenericCoeff ] at *;
    grind

theorem ab6_residual_eq_abResidual
    (h : ℝ) (y : ℝ → ℝ) (t₀ : ℝ) (n : ℕ) :
    y (t₀ + (n : ℝ) * h + 6 * h) - y (t₀ + (n : ℝ) * h + 5 * h)
      - h * ((4277 / 1440) * deriv y (t₀ + (n : ℝ) * h + 5 * h)
            - (7923 / 1440) * deriv y (t₀ + (n : ℝ) * h + 4 * h)
            + (9982 / 1440) * deriv y (t₀ + (n : ℝ) * h + 3 * h)
            - (7298 / 1440) * deriv y (t₀ + (n : ℝ) * h + 2 * h)
            + (2877 / 1440) * deriv y (t₀ + (n : ℝ) * h + h)
            - (475 / 1440) * deriv y (t₀ + (n : ℝ) * h))
      = abResidual 6 ab6GenericCoeff h y t₀ n := by
  -- We unfold `abResidual` and let `simp` reduce the `Fin` index arithmetic and `Matrix.cons` access.
  -- This brings both sides to the same form before we finish with `ring`.
  unfold abResidual; simp [ab6GenericCoeff, Fin.sum_univ_six, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring_nf

end LMM