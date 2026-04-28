import OpenMath.MultistepMethods
import OpenMath.OneLegMethods
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# G-stability for One-Leg Methods (Butcher §45)

This file records the scalar one-leg `G`-stability interface used for the
trapezoidal one-leg method. Vector-valued ODEs are deliberately left to a
future extension.

Reference: Butcher, *Numerical Methods for Ordinary Differential Equations*
(2nd ed.), §451.
-/

open Finset Matrix

/-- The square of the `G`-seminorm associated to a matrix `G`. -/
def gNormSq {s : ℕ} (G : Matrix (Fin s) (Fin s) ℝ) (U : Fin s → ℝ) : ℝ :=
  U ⬝ᵥ (G *ᵥ U)

namespace OneLegMethod

variable {s : ℕ}

/-- The sum of the `β`-coefficients. -/
noncomputable def betaTotal (m : OneLegMethod s) : ℝ :=
  ∑ j : Fin (s + 1), m.β j

/-- The one-leg weighted scalar state, using the normalized `β` coefficients. -/
noncomputable def weightedState (m : OneLegMethod s) (Y : Fin (s + 1) → ℝ) : ℝ :=
  ∑ j : Fin (s + 1), (m.β j / m.betaTotal) * Y j

/-- The old `s`-vector stored before an `s`-step one-leg update. -/
def oldState (Y : Fin (s + 1) → ℝ) : Fin s → ℝ :=
  fun i => Y i.castSucc

/-- The new `s`-vector stored after an `s`-step one-leg update. -/
def newState (Y : Fin (s + 1) → ℝ) : Fin s → ℝ :=
  fun i => Y i.succ

/-- Scalar `G`-stability for a one-leg method.

The `energy_bound` field is the one-step `G`-norm inequality. The
`contractive` field records the corresponding contraction under the scalar
monotonicity condition `F * weightedState ≤ 0`.
-/
structure IsGStable (m : OneLegMethod s) (G : Matrix (Fin s) (Fin s) ℝ) : Prop where
  /-- The matrix defining the seminorm is positive semidefinite. -/
  posSemidef : G.PosSemidef
  /-- One-step `G`-norm bound for a scalar one-leg update. -/
  energy_bound :
    ∀ (h F : ℝ) (Y : Fin (s + 1) → ℝ),
      (∑ j : Fin (s + 1), m.α j * Y j = h * m.betaTotal * F) →
        gNormSq G (newState Y) ≤
          gNormSq G (oldState Y) + 2 * h * m.betaTotal * F * m.weightedState Y
  /-- Contractivity when the scalar vector field is monotone at the one-leg state. -/
  contractive :
    ∀ (h F : ℝ) (Y : Fin (s + 1) → ℝ),
      0 ≤ h →
      0 ≤ m.betaTotal →
      (∑ j : Fin (s + 1), m.α j * Y j = h * m.betaTotal * F) →
      F * m.weightedState Y ≤ 0 →
        gNormSq G (newState Y) ≤ gNormSq G (oldState Y)

/-! ## Trapezoidal one-leg method -/

/-- The trapezoidal one-leg method is `G`-stable for the `1 x 1` identity matrix. -/
theorem trapezoid_isGStable_with_G_one :
    IsGStable trapezoid (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  refine ⟨Matrix.PosSemidef.one, ?_, ?_⟩
  · intro h F Y hstep
    simp [gNormSq, newState, oldState, weightedState, betaTotal, trapezoid,
      Fin.sum_univ_two, dotProduct, Matrix.mulVec] at hstep ⊢
    norm_num at hstep ⊢
    have hstep' : h * F = Y 1 - Y 0 := by linarith
    have hrewrite :
        2 * h * F * (1 / 2 * Y 0 + 1 / 2 * Y 1) =
          2 * (Y 1 - Y 0) * (1 / 2 * Y 0 + 1 / 2 * Y 1) := by
      calc
        2 * h * F * (1 / 2 * Y 0 + 1 / 2 * Y 1) =
            2 * (h * F) * (1 / 2 * Y 0 + 1 / 2 * Y 1) := by ring
        _ = 2 * (Y 1 - Y 0) * (1 / 2 * Y 0 + 1 / 2 * Y 1) := by rw [hstep']
    calc
      Y 1 * Y 1 = Y 0 * Y 0 + 2 * h * F * (1 / 2 * Y 0 + 1 / 2 * Y 1) := by
        rw [hrewrite]
        ring
      _ ≤ Y 0 * Y 0 + 2 * h * F * (1 / 2 * Y 0 + 1 / 2 * Y 1) := le_rfl
  · intro h F Y hh _hβ hstep hmono
    simp [gNormSq, newState, oldState, weightedState, betaTotal, trapezoid,
      Fin.sum_univ_two, dotProduct, Matrix.mulVec] at hstep hmono ⊢
    norm_num at hstep hmono ⊢
    have hstep' : h * F = Y 1 - Y 0 := by linarith
    have hcoef_nonneg : 0 ≤ 2 * h := by nlinarith
    have hcorr_nonpos : 2 * h * F * (1 / 2 * Y 0 + 1 / 2 * Y 1) ≤ 0 := by
      have hmul :
          (2 * h) * (F * (1 / 2 * Y 0 + 1 / 2 * Y 1)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hcoef_nonneg hmono
      simpa [mul_assoc] using hmul
    have hdiff :
        Y 1 * Y 1 - Y 0 * Y 0 =
          2 * h * F * (1 / 2 * Y 0 + 1 / 2 * Y 1) := by
      have hrewrite :
          2 * h * F * (1 / 2 * Y 0 + 1 / 2 * Y 1) =
            2 * (Y 1 - Y 0) * (1 / 2 * Y 0 + 1 / 2 * Y 1) := by
        calc
          2 * h * F * (1 / 2 * Y 0 + 1 / 2 * Y 1) =
              2 * (h * F) * (1 / 2 * Y 0 + 1 / 2 * Y 1) := by ring
          _ = 2 * (Y 1 - Y 0) * (1 / 2 * Y 0 + 1 / 2 * Y 1) := by rw [hstep']
      rw [hrewrite]
      ring
    nlinarith

end OneLegMethod
