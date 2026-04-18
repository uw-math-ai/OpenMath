import Mathlib

/-! # Butcher Tableaux and simplifying assumptions

This file defines Butcher tableaux for Runge–Kutta methods and the B(η) simplifying
assumption (quadrature order condition).
-/

/-- A Butcher tableau with `s` stages over `ℚ`. -/
structure ButcherTableau (s : ℕ) where
  /-- Node coefficients -/
  c : Fin s → ℚ
  /-- Runge–Kutta matrix -/
  A : Fin s → Fin s → ℚ
  /-- Weight coefficients -/
  b : Fin s → ℚ

namespace ButcherTableau

variable {s : ℕ}

/-- A Butcher tableau satisfies the B(η) simplifying assumption when the quadrature
    order conditions hold up to order η:
    ∀ q ∈ {1, …, η},  ∑ i, b i * (c i) ^ (q - 1) = 1 / q. -/
def SatisfiesB (t : ButcherTableau s) (η : ℕ) : Prop :=
  ∀ q : ℕ, 1 ≤ q → q ≤ η → ∑ i : Fin s, t.b i * t.c i ^ (q - 1) = 1 / (q : ℚ)

end ButcherTableau
