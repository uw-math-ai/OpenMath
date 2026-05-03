import Mathlib

/-! Cycle 091 — Aristotle batch for `def:512A` helpers.

Self-contained file with the GLM structure inlined and three helper
lemmas as `sorry`s. Aristotle should fill in `isGLMSolution_zero_iff`,
`zero_isGLMSolution_zero`, and `zero_seq_homogeneous_V`.
-/

open Matrix
open scoped BigOperators

structure GeneralLinearMethod (s r : ℕ) where
  A : Matrix (Fin s) (Fin s) ℝ
  U : Matrix (Fin s) (Fin r) ℝ
  B : Matrix (Fin r) (Fin s) ℝ
  V : Matrix (Fin r) (Fin r) ℝ

def GeneralLinearMethod.IsGLMSolution {s r : ℕ}
    (M : GeneralLinearMethod s r) (h : ℝ) (f : ℝ → ℝ)
    (y_seq : ℕ → Fin r → ℝ) : Prop :=
  ∀ n : ℕ, ∃ Y : Fin s → ℝ,
    (∀ i, Y i = (∑ j, M.A i j * (h * f (Y j)))
                + (∑ j, M.U i j * y_seq n j))
    ∧ (∀ i, y_seq (n + 1) i = (∑ j, M.B i j * (h * f (Y j)))
                              + (∑ j, M.V i j * y_seq n j))

/-- Helper 1 — for `f ≡ 0`, the GLM iteration reduces to the
homogeneous V-recurrence. -/
theorem isGLMSolution_zero_iff {s r : ℕ}
    (M : GeneralLinearMethod s r) (h : ℝ) (y_seq : ℕ → Fin r → ℝ) :
    M.IsGLMSolution h (fun _ => 0) y_seq ↔
    ∀ n : ℕ, ∀ i : Fin r,
      y_seq (n + 1) i = ∑ j : Fin r, M.V i j * y_seq n j := by
  sorry

/-- Helper 2 — the constantly-zero sequence is a GLM iteration of any
GLM at any stepsize for the trivial autonomous RHS `f ≡ 0`. -/
theorem zero_isGLMSolution_zero {s r : ℕ}
    (M : GeneralLinearMethod s r) (h : ℝ) :
    M.IsGLMSolution h (fun _ => 0) (fun _ _ => 0) := by
  sorry

/-- Bonus — the constantly-zero `y_seq` solves the homogeneous
V-recurrence for any GLM. -/
theorem zero_seq_homogeneous_V {s r : ℕ}
    (M : GeneralLinearMethod s r) :
    ∀ n : ℕ, ∀ i : Fin r,
      ((fun (_ : ℕ) (_ : Fin r) => (0 : ℝ)) (n + 1)) i =
        ∑ j : Fin r, M.V i j * ((fun (_ : ℕ) (_ : Fin r) => (0 : ℝ)) n) j := by
  sorry
