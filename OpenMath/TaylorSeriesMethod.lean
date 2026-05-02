import OpenMath.OneStepConvergence

/-!
# Taylor series methods (Butcher §250)

Abstract Taylor series method of order `p`, parametrised by an
arbitrary higher-derivative supply `D : ℕ → ℝ → E → E` representing the
iterated total derivatives `y^{(k)}` along the flow of `y' = f(x, y)`.

For `p = 1` the method reduces to forward Euler, and for `p = 2` it is
the standard order-2 Taylor scheme.
-/

namespace TaylorSeriesMethod

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Order-`p` Taylor series method increment. The data `D k x y` represents the
`k`-th total derivative `y^{(k)}(x)` evaluated along the flow of `y' = f(x, y)`
at `(x, y)`. The method advances by truncating the Taylor expansion of
`y(x + h)` after the `p`-th term. The summand at index `k ∈ Finset.range p`
carries the `(k+1)`-th derivative weighted by `h^k / (k+1)!`. -/
noncomputable def increment (p : ℕ) (D : ℕ → ℝ → E → E)
    (x : ℝ) (y : E) (h : ℝ) : E :=
  ∑ k ∈ Finset.range p, (h ^ k / (k + 1).factorial) • D (k + 1) x y

/-- Packaging as a `OneStepMethod`. -/
noncomputable def toOneStepMethod (p : ℕ) (D : ℕ → ℝ → E → E) :
    OneStepMethod E :=
  { Φ := increment p D }

/-- Order-1 Taylor method increment: `Φ(x, y, h) = D 1 x y`. -/
@[simp] theorem increment_one (D : ℕ → ℝ → E → E)
    (x : ℝ) (y : E) (h : ℝ) :
    increment 1 D x y h = D 1 x y := by
  simp [increment, Nat.factorial]

/-- Order-2 Taylor method increment:
`Φ(x, y, h) = D 1 x y + (h / 2) • D 2 x y`. -/
theorem increment_two (D : ℕ → ℝ → E → E)
    (x : ℝ) (y : E) (h : ℝ) :
    increment 2 D x y h
      = D 1 x y + (h / 2) • D 2 x y := by
  simp [increment, Finset.sum_range_succ, Nat.factorial]
  norm_num

/-- The Taylor method of order `p ≥ 1` is consistent with the ODE
`y' = f(x, y)` when `D 1 = f`. -/
theorem isConsistent_of_first_derivative (p : ℕ) (hp : 1 ≤ p)
    (D : ℕ → ℝ → E → E) (f : ℝ → E → E)
    (hD1 : ∀ x y, D 1 x y = f x y) :
    (toOneStepMethod p D).IsConsistent f := by
  intro x y
  show increment p D x y 0 = f x y
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hp)
  rw [increment, Finset.sum_range_succ']
  have hzero : ∀ k ∈ Finset.range q,
      ((0 : ℝ) ^ (k + 1) / (k + 1 + 1).factorial) • D (k + 1 + 1) x y
        = (0 : E) := by
    intro k _
    simp [zero_pow (Nat.succ_ne_zero k)]
  rw [Finset.sum_eq_zero hzero]
  simp [Nat.factorial, hD1]

end TaylorSeriesMethod
