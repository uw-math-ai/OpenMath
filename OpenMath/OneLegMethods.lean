import OpenMath.MultistepMethods

/-!
# One-Leg Methods (Butcher §45)

One-leg methods use the same coefficient data as a linear multistep method, but
evaluate the vector field at the single weighted point determined by the
`β`-coefficients.

Reference: Butcher, *Numerical Methods for Ordinary Differential Equations*
(2nd ed.), §450.
-/

/-! ## One-leg method data -/

/-- A one-leg `s`-step method.

The coefficient data are the same as for an `LMM s`. The intended scalar
one-leg step is
`Σⱼ αⱼ y_{n+j} = h * (Σⱼ βⱼ) *
  f (Σⱼ (βⱼ / Σₖ βₖ) x_{n+j}) (Σⱼ (βⱼ / Σₖ βₖ) y_{n+j})`.
-/
structure OneLegMethod (s : ℕ) where
  /-- Coefficients of the solution values `y_{n+j}`. -/
  α : Fin (s + 1) → ℝ
  /-- Coefficients determining the one-leg evaluation point. -/
  β : Fin (s + 1) → ℝ
  /-- The leading coefficient is normalized to `1`. -/
  normalized : α (Fin.last s) = 1

namespace OneLegMethod

variable {s : ℕ}

/-- Forget a one-leg method to its underlying linear multistep coefficient data. -/
def toLMM (m : OneLegMethod s) : LMM s where
  α := m.α
  β := m.β
  normalized := m.normalized

end OneLegMethod

namespace LMM

variable {s : ℕ}

/-- Regard linear multistep coefficient data as a one-leg method. -/
def toOneLeg (m : LMM s) : OneLegMethod s where
  α := m.α
  β := m.β
  normalized := m.normalized

end LMM

namespace OneLegMethod

variable {s : ℕ}

/-- The coefficient-level round trip from one-leg methods to LMMs and back. -/
@[simp]
theorem toLMM_toOneLeg (m : OneLegMethod s) : m.toLMM.toOneLeg = m := by
  rfl

end OneLegMethod

namespace LMM

variable {s : ℕ}

/-- The coefficient-level round trip from LMMs to one-leg methods and back. -/
@[simp]
theorem toOneLeg_toLMM (m : LMM s) : m.toOneLeg.toLMM = m := by
  rfl

end LMM

namespace OneLegMethod

/-! ## Standard one-leg methods -/

/-- The trapezoidal one-leg method (`θ = 1/2`), with the same coefficient
data as `trapezoidalRule`. -/
noncomputable def trapezoid : OneLegMethod 1 where
  α := ![-1, 1]
  β := ![1 / 2, 1 / 2]
  normalized := by simp [Fin.last]

/-- Forgetting the trapezoidal one-leg method gives the existing trapezoidal LMM. -/
theorem trapezoid_toLMM_eq_lmm_trapezoid :
    trapezoid.toLMM = trapezoidalRule := by
  rfl

end OneLegMethod
