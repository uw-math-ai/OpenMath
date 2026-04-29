import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Linear systems of differential equations (Butcher §111)

The autonomous linear initial-value problem
`y'(x) = A · y(x), y(x₀) = y₀` has the closed-form solution
`y(x) = exp((x − x₀) • A) · y₀`.

For commuting matrices `A`, `B` we additionally have
`exp((s + t) • A) = exp(s • A) * exp(t • A)`, recovering the
one-parameter group law of the matrix exponential.

Reference: Butcher, *Numerical Methods for Ordinary Differential
Equations* (2nd ed.), §111.
-/

open Matrix NormedSpace
open scoped Matrix.Norms.Operator

namespace LinearODE

variable {n : ℕ}

/-- Closed-form solution `y(x) := exp((x − x₀) • A) · y₀` of the linear
IVP `y' = A y`, `y(x₀) = y₀`. -/
noncomputable def closedFormSolution
    (A : Matrix (Fin n) (Fin n) ℝ) (x₀ : ℝ) (y₀ : Fin n → ℝ)
    (x : ℝ) : Fin n → ℝ :=
  NormedSpace.exp ((x - x₀) • A) *ᵥ y₀

/-- The closed-form solution attains the initial condition at `x = x₀`. -/
theorem closedFormSolution_initial
    (A : Matrix (Fin n) (Fin n) ℝ) (x₀ : ℝ) (y₀ : Fin n → ℝ) :
    closedFormSolution A x₀ y₀ x₀ = y₀ := by
  simp [closedFormSolution]

/-- Right-multiplication by a fixed vector, packaged as a continuous linear map. -/
noncomputable def mulVecRightCLM (y : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M *ᵥ y
      map_add' := fun M N => Matrix.add_mulVec M N y
      map_smul' := fun c M => Matrix.smul_mulVec c M y }

@[simp] lemma mulVecRightCLM_apply (y : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    mulVecRightCLM y M = M *ᵥ y := rfl

/-- Time derivative: `(d/dx) y(x) = A · y(x)`. -/
theorem closedFormSolution_hasDerivAt
    (A : Matrix (Fin n) (Fin n) ℝ) (x₀ : ℝ) (y₀ : Fin n → ℝ) (x : ℝ) :
    HasDerivAt (fun t => closedFormSolution A x₀ y₀ t)
      (A *ᵥ closedFormSolution A x₀ y₀ x) x := by
  have h_id : HasDerivAt (fun t : ℝ => t - x₀) 1 x :=
    (hasDerivAt_id x).sub_const x₀
  have h_exp : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A))
      (A * NormedSpace.exp ((x - x₀) • A)) (x - x₀) :=
    hasDerivAt_exp_smul_const' (𝕂 := ℝ) A (x - x₀)
  have h_comp : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t - x₀) • A))
      (A * NormedSpace.exp ((x - x₀) • A)) x := by
    have := HasDerivAt.scomp x h_exp h_id
    simpa using this
  have h_fderiv :
      HasFDerivAt (fun M : Matrix (Fin n) (Fin n) ℝ => M *ᵥ y₀)
        (mulVecRightCLM y₀) (NormedSpace.exp ((x - x₀) • A)) :=
    (mulVecRightCLM y₀).hasFDerivAt
  have h_mulVec := HasFDerivAt.comp_hasDerivAt x h_fderiv h_comp
  simp only [mulVecRightCLM_apply, Function.comp_def] at h_mulVec
  simpa [closedFormSolution, ← Matrix.mulVec_mulVec] using h_mulVec

/-- One-parameter group law for the matrix exponential of `A`. -/
theorem exp_smul_add (A : Matrix (Fin n) (Fin n) ℝ) (s t : ℝ) :
    NormedSpace.exp ((s + t) • A) =
      NormedSpace.exp (s • A) * NormedSpace.exp (t • A) := by
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl A).smul_left s).smul_right t)

end LinearODE
