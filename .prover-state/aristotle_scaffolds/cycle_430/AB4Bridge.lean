import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.LMMABGenericConvergence
import OpenMath.LMMAB4Convergence

/-! Cycle 430 AB4 vector bridge stubs (defensive Aristotle batch). The
manual proofs already closed in the live file; this file restates the
bridges with `sorry` so Aristotle has a chance to produce alternate
short proofs. -/

namespace LMM

noncomputable def ab4GenericCoeffStub : Fin 4 → ℝ :=
  ![-(9 : ℝ) / 24, (37 : ℝ) / 24, -(59 : ℝ) / 24, (55 : ℝ) / 24]

example (L : ℝ) :
    abLip 4 ab4GenericCoeffStub L = (20 / 3) * L := by
  sorry

example
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ : E) (n : ℕ) :
    ab4IterVec h f t₀ y₀ y₁ y₂ y₃ n
      = abIterVec 4 ab4GenericCoeffStub h f t₀ ![y₀, y₁, y₂, y₃] n := by
  sorry

example
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (y : ℝ → E) (t₀ : ℝ) (n : ℕ) :
    ab4VecResidual h (t₀ + (n : ℝ) * h) y
      = abResidualVec 4 ab4GenericCoeffStub h y t₀ n := by
  sorry

end LMM
