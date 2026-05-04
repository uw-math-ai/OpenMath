import OpenMath.GeneralLinearMethod
import OpenMath.RKAsGLM
import OpenMath.SymplecticRK
import OpenMath.GaussLegendre3

/-!
# Butcher §525 — G-symplectic general linear methods

A general linear method `(A, U, B, V)` is **G-symplectic** when the
discrete update preserves a quadratic invariant of the augmented
state, in the same sense that a symplectic Runge–Kutta method
(Butcher §37) preserves a quadratic invariant of the ODE state. The
existence of a symmetric weight matrix `G` and a stage weight vector
`D` such that the three Bochev–Scovel-style identities below hold is
the structural §525 condition.

Reference: J. C. Butcher, *Numerical Methods for Ordinary Differential
Equations*, 2nd ed., §525.
-/

open Finset

namespace GeneralLinearMethod

variable {s r : ℕ}

/-- **Butcher §525** — A general linear method `(A, U, B, V)` is
**G-symplectic** if there exist a symmetric weight matrix
`G : Fin r → Fin r → ℝ` and a stage weight vector `D : Fin s → ℝ`
such that:

* (stage symplecticity)
  `D i * A i j + D j * A j i = ∑ k₁ k₂, B k₁ i * G k₁ k₂ * B k₂ j`,
* (input/output compatibility)
  `D i * U i k = ∑ k₁ k₂, B k₁ i * G k₁ k₂ * V k₂ k`,
* (output preservation)
  `∑ i j, V i k₁ * G i j * V j k₂ = G k₁ k₂`. -/
def IsGSymplectic (m : GeneralLinearMethod s r) : Prop :=
  ∃ (G : Fin r → Fin r → ℝ) (D : Fin s → ℝ),
    (∀ i j : Fin r, G i j = G j i) ∧
    (∀ i j : Fin s,
      D i * m.A i j + D j * m.A j i =
        ∑ k₁ : Fin r, ∑ k₂ : Fin r, m.B k₁ i * G k₁ k₂ * m.B k₂ j) ∧
    (∀ (i : Fin s) (k : Fin r),
      D i * m.U i k =
        ∑ k₁ : Fin r, ∑ k₂ : Fin r, m.B k₁ i * G k₁ k₂ * m.V k₂ k) ∧
    (∀ k₁ k₂ : Fin r,
      (∑ i : Fin r, ∑ j : Fin r, m.V i k₁ * G i j * m.V j k₂) = G k₁ k₂)

end GeneralLinearMethod

namespace ButcherTableau

variable {s : ℕ}

/-- **§525 / §502 bridge** — The RK-as-GLM embedding of a symplectic
Runge–Kutta method is a G-symplectic GLM, with `G k₁ k₂ := 1` and
`D := t.b`. -/
theorem toGLM_isGSymplectic_of_isSymplectic
    {t : ButcherTableau s} (h : t.IsSymplectic) :
    (t.toGLM).IsGSymplectic := by
  refine ⟨fun _ _ => (1 : ℝ), t.b, ?_, ?_, ?_, ?_⟩
  · intro _ _; rfl
  · intro i j
    have hd := h i j
    simp only [symplecticDefect] at hd
    simp [toGLM_A, toGLM_B]
    linarith
  · intro i k
    simp [toGLM_U, toGLM_B, toGLM_V]
  · intro k₁ k₂
    simp [toGLM_V]

/-- The 1-stage Gauss–Legendre method (implicit midpoint) embeds as a
G-symplectic GLM. -/
theorem rkGaussLegendre1_toGLM_isGSymplectic :
    (rkGaussLegendre1.toGLM).IsGSymplectic :=
  rkGaussLegendre1.toGLM_isGSymplectic_of_isSymplectic
    rkGaussLegendre1_isSymplectic

/-- The 2-stage Gauss–Legendre method embeds as a G-symplectic GLM. -/
theorem rkGaussLegendre2_toGLM_isGSymplectic :
    (rkGaussLegendre2.toGLM).IsGSymplectic :=
  rkGaussLegendre2.toGLM_isGSymplectic_of_isSymplectic
    rkGaussLegendre2_isSymplectic

/-- The 3-stage Gauss–Legendre method embeds as a G-symplectic GLM. -/
theorem rkGaussLegendre3_toGLM_isGSymplectic :
    (rkGaussLegendre3.toGLM).IsGSymplectic :=
  rkGaussLegendre3.toGLM_isGSymplectic_of_isSymplectic
    rkGaussLegendre3_isSymplectic

end ButcherTableau
