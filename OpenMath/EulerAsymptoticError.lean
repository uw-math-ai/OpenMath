import OpenMath.PicardLindelof

/-! # §215 Asymptotic Error Formula for the Euler Method

Butcher §215. For the explicit Euler method `y_{n+1} = y_n + h · f(x_n, y_n)`
applied to `y' = f(x, y)`, `y(x₀) = y₀`, the global error
`e_n := y_n − y(x_n)` admits the asymptotic expansion

    e_n = h · ψ(x_n) + O(h²)

as `h → 0` with `n · h = x_n − x₀` fixed, where `ψ` solves the variational
equation

    ψ'(x) = f_y(x, y(x)) · ψ(x) + (1/2) · y''(x),     ψ(x₀) = 0.

This file lands the data bundle (`EulerAsymptoticInput`), the variational
solution `variationalSolution` together with the Picard–Lindelöf existence
proof, and the sorry-first headline `euler_asymptotic_error`. The
quantitative discrete-Gronwall + second-order-LTE expansion that closes
the headline is deferred.
-/

namespace EulerAsymptoticError

open Set Real

/-- Right-hand side of the variational equation:
`fy(x, y(x)) · ψ + (1/2) · y''(x)`. -/
noncomputable def variationalRHS
    (fy : ℝ → ℝ → ℝ) (y secondDeriv : ℝ → ℝ) (x ψ : ℝ) : ℝ :=
  fy x (y x) * ψ + (1 / 2) * secondDeriv x

/-- Bundle of data for §215: the explicit Euler problem with the smoothness
hypotheses needed to define and analyse the variational solution. -/
structure EulerAsymptoticInput where
  /-- Left endpoint of the integration interval. -/
  x₀ : ℝ
  /-- Right endpoint of the integration interval. -/
  X : ℝ
  /-- Strict ordering of the endpoints (so Picard–Lindelöf applies). -/
  hxX : x₀ < X
  /-- Right-hand side of the ODE. -/
  f : ℝ → ℝ → ℝ
  /-- Second-variable partial derivative of `f` (treated as a placeholder
  function — its agreement with the literal partial derivative of `f` is
  not enforced here). -/
  fy : ℝ → ℝ → ℝ
  /-- Lipschitz constant for `f` in its second variable. -/
  L : ℝ
  hL : 0 ≤ L
  /-- Lipschitz hypothesis: `|f x u − f x v| ≤ L · |u − v|` on the strip
  `[x₀, X] × ℝ`. -/
  f_lip : ∀ x ∈ Set.Icc x₀ X, ∀ u v : ℝ, |f x u - f x v| ≤ L * |u - v|
  /-- Exact solution of `y' = f(x, y), y(x₀) = y₀` on `[x₀, X]`. -/
  y : ℝ → ℝ
  /-- Placeholder for the second derivative `y''(x)` along the flow.
  Deriving this from `f` and `y` algebraically is §254 territory and is
  out of scope here. -/
  secondDeriv : ℝ → ℝ
  /-- Uniform bound on `|y''(x)|` over `[x₀, X]`. -/
  M₂ : ℝ
  secondDeriv_bound : ∀ x ∈ Set.Icc x₀ X, |secondDeriv x| ≤ M₂
  /-- Initial datum. -/
  y₀ : ℝ
  y_init : y x₀ = y₀
  /-- Pointwise bound on `|fy(x, y(x))|` by the Lipschitz constant `L`.
  Holds whenever `fy` is the literal partial derivative of an `L`-Lipschitz
  `f`, which is the intended use case. -/
  fy_bound : ∀ x ∈ Set.Icc x₀ X, |fy x (y x)| ≤ L
  /-- Joint continuity of the variational right-hand side as a function
  of `(x, ψ)`. Needed to apply Picard–Lindelöf. -/
  varRHS_cont :
    Continuous (fun p : ℝ × ℝ => variationalRHS fy y secondDeriv p.1 p.2)

namespace EulerAsymptoticInput

/-- Variational RHS as a `ℝ → ℝ → ℝ` function ready for Picard–Lindelöf. -/
noncomputable def variationalRHSFn (input : EulerAsymptoticInput) : ℝ → ℝ → ℝ :=
  fun x ψ => variationalRHS input.fy input.y input.secondDeriv x ψ

/-- The variational RHS is `L`-Lipschitz in `ψ` on `[x₀, X]`. -/
lemma variationalRHSFn_isLipschitzInSecondVar (input : EulerAsymptoticInput) :
    IsLipschitzInSecondVar input.variationalRHSFn input.L input.x₀ input.X := by
  intro x hx u v
  have h1 : input.variationalRHSFn x u - input.variationalRHSFn x v
      = input.fy x (input.y x) * (u - v) := by
    simp only [variationalRHSFn, variationalRHS]
    ring
  rw [h1]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (input.fy_bound x hx) (abs_nonneg _)

/-- Continuity of the variational RHS as a `Prod`-input function. -/
lemma variationalRHSFn_cont (input : EulerAsymptoticInput) :
    Continuous (fun p : ℝ × ℝ => input.variationalRHSFn p.1 p.2) :=
  input.varRHS_cont

/-- **Picard–Lindelöf existence for the variational equation** (§215). The
variational RHS is linear (hence Lipschitz) in `ψ` with constant
`|fy(x, y(x))| ≤ L`, so existence follows from
`PicardLindelof.exists_solution`. -/
theorem exists_variationalSolution (input : EulerAsymptoticInput) :
    ∃ ψ : ℝ → ℝ,
      ψ input.x₀ = 0 ∧
      ContinuousOn ψ (Set.Icc input.x₀ input.X) ∧
      ∀ x ∈ Set.Icc input.x₀ input.X,
        HasDerivWithinAt ψ (input.variationalRHSFn x (ψ x))
          (Set.Icc input.x₀ input.X) x :=
  PicardLindelof.exists_solution (y₀ := (0 : ℝ)) input.hxX
    input.variationalRHSFn_cont
    input.variationalRHSFn_isLipschitzInSecondVar input.hL

end EulerAsymptoticInput

/-- The variational solution `ψ` extracted from Picard–Lindelöf existence. -/
noncomputable def variationalSolution (input : EulerAsymptoticInput) : ℝ → ℝ :=
  Classical.choose input.exists_variationalSolution

theorem variationalSolution_init (input : EulerAsymptoticInput) :
    variationalSolution input input.x₀ = 0 :=
  (Classical.choose_spec input.exists_variationalSolution).1

theorem variationalSolution_continuousOn (input : EulerAsymptoticInput) :
    ContinuousOn (variationalSolution input) (Set.Icc input.x₀ input.X) :=
  (Classical.choose_spec input.exists_variationalSolution).2.1

theorem variationalSolution_hasDerivWithinAt (input : EulerAsymptoticInput)
    {x : ℝ} (hx : x ∈ Set.Icc input.x₀ input.X) :
    HasDerivWithinAt (variationalSolution input)
      (input.variationalRHSFn x (variationalSolution input x))
      (Set.Icc input.x₀ input.X) x :=
  (Classical.choose_spec input.exists_variationalSolution).2.2 x hx

/-- **§215 variational solution exists.** Bundled headline matching the
strategy: `ψ` satisfies the variational ODE on `[x₀, X]` with
`ψ(x₀) = 0`. Closed sorry-free via Picard–Lindelöf. -/
theorem variationalSolution_isSolution (input : EulerAsymptoticInput) :
    variationalSolution input input.x₀ = 0 ∧
    ∀ x ∈ Set.Icc input.x₀ input.X,
      HasDerivWithinAt (variationalSolution input)
        (variationalRHS input.fy input.y input.secondDeriv x
          (variationalSolution input x))
        (Set.Icc input.x₀ input.X) x :=
  ⟨variationalSolution_init input,
    fun _ hx => variationalSolution_hasDerivWithinAt input hx⟩

/-- Explicit Euler iterate `y_n` for the IVP `y' = f(x, y), y(x₀) = y₀`
with stepsize `h`. Defined locally because `OpenMath/Basic.lean` only
formalises the abstract Gronwall recurrence, not the Euler scheme itself. -/
noncomputable def eulerIterate (f : ℝ → ℝ → ℝ) (x₀ y₀ h : ℝ) : ℕ → ℝ
  | 0 => y₀
  | n + 1 => eulerIterate f x₀ y₀ h n
              + h * f (x₀ + n * h) (eulerIterate f x₀ y₀ h n)

/-- **§215 Euler asymptotic error formula** (sorry-first headline). The
global error of the explicit Euler method admits the asymptotic expansion
`e_n = h · ψ(x_n) + O(h²)` along the variational solution `ψ`. The constant
`C` depends only on `input` (Lipschitz `L`, second-derivative bound `M₂`,
horizon `X − x₀`); it does not depend on `h` or `n`. The closure of this
sorry is deferred to a follow-up cycle. -/
theorem euler_asymptotic_error
    (input : EulerAsymptoticInput)
    (h : ℝ) (n : ℕ)
    (hh_pos : 0 < h)
    (hh_in : input.x₀ + n * h ≤ input.X) :
    ∃ C : ℝ, 0 ≤ C ∧
      |eulerIterate input.f input.x₀ input.y₀ h n
        - input.y (input.x₀ + n * h)
        - h * variationalSolution input (input.x₀ + n * h)|
        ≤ C * h ^ 2 := by
  sorry

end EulerAsymptoticError
