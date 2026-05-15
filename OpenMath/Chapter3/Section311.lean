import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import OpenMath.Chapter3.Section301
import OpenMath.Chapter3.Section310

/-!
# Butcher §311 — Taylor expansion of the exact solution (foundational layer)

This file opens §311 ("The Taylor expansion of the exact solution",
Butcher 3rd ed., p. 174) with the foundational infrastructure that
underlies `lem:311A`, `thm:311B`, and `thm:311C`.

## Scope of this cycle

The textbook `lem:311A` is a combinatorial labelling statement: given an
ordered vertex set `S = S₀ ∪ {s}` and a tree `t ∈ T_{S₀}^*`, the time
derivative of `F(|t|)(y(x))` equals a sum of `F(|u|)(y(x))` over labelled
trees `u` obtained by attaching `s` to `t` in every possible way. The
full statement requires a labelled-tree quotient infrastructure
(`def:300C`) that has not yet been formalised and is multi-cycle scope.

What we ship in this file is the **order-1 special case of the Taylor
expansion** that `lem:311A` underwrites in §311: namely, the fact that
the first-order B-series truncation `y₀ + h • f(y₀)` approximates the
exact ODE solution `yex(x₀ + h)` with quadratic remainder under
`ContDiff ℝ 2` regularity. In Butcher's notation this corresponds to
the order-1 term `(h^|τ| / σ(τ)) · α(τ) · F(τ)(y₀) = h · 1 · 1 · f(y₀)`
of the B-series for the exact-solution operator `E` (cf. `def:312A`),
with `τ = •` the single-vertex tree (Butcher §300).

`lean_status.json` retains `lem:311A` as `unformalized`: the file only
ships the order-1 specialisation, not the full combinatorial labelling
lemma.

## Contents

* `F_tau_eval` — base case of `def:310A`: `F(τ)(y₀) = f(y₀)`.
* `bseriesOrderOne` — first-order B-series truncation `y₀ + h • f(y₀)`.
* `lem_311A_order_one` — the order-1 Taylor expansion: the difference
  `yex(x₀ + h) - bseriesOrderOne f y₀ h` is `O(h²)` near `0`.
* A non-vacuity `example` consuming `lem_311A_order_one` with `f := id`.

## Proof recipe

`lem_311A_order_one` is a direct simplification of cycle 154's
`explicitEulerGLM_hasOrderOne_trivialStarting`
(`OpenMath/Chapter5/Section530.lean` line ~1284). That theorem
bounds `((y₀ + h f y₀) + h f(y₀ + h f y₀)) - (yex(x₀+h) + h f(yex(x₀+h)))`
as `O(h²)` using a two-piece decomposition `T1 + T2`. Here we keep only
`T1 = (y₀ + h f y₀) - yex(x₀+h)` (up to sign), bound it via the
second-order Taylor remainder, and observe that no `T2` (no `f`-correction
term) appears in the B-series-1 setting — the Lipschitz hypothesis on
`f` is therefore unnecessary.
-/

namespace OpenMath.Chapter3.Section311

open OpenMath.Chapter3.Section310

/-- **Base case of `def:310A`.** The elementary differential at the
single-vertex tree `τ = •` (formalised as `RootedTree.vertex = mk []`)
evaluates to `f(y₀)`.

In Butcher's notation this is the recursive base
`F(τ)(y) = f(y)` (Butcher §310, equation 310g). The Lean proof reduces
`elementaryDiff f y₀ (mk [])` through the recursive definition to
`iteratedFDeriv ℝ 0 f y₀ (Fin.elim0 ∘ id)`, which is `f y₀` by
`iteratedFDeriv_zero_apply`. -/
theorem F_tau_eval {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (f : N → N) (y₀ : N) :
    elementaryDiff f y₀ RootedTree.vertex = f y₀ := by
  show elementaryDiff f y₀ (RootedTree.mk []) = f y₀
  unfold elementaryDiff
  exact iteratedFDeriv_zero_apply _

/-- **First-order B-series truncation.** The order-1 term of the
exact-solution B-series expansion is

`y₀ + (h^|τ| / σ(τ)) · α(τ) · F(τ)(y₀) = y₀ + h · 1 · 1 · f(y₀)`.

This function expresses the truncation explicitly, ready to be compared
with the exact solution via `lem_311A_order_one`.

Polymorphic in any real normed space `N`; for `N := ℝ` (used by
`lem_311A_order_one`) the smul `h • f y₀` reduces to multiplication
`h * f y₀`. -/
noncomputable def bseriesOrderOne
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (f : N → N) (y₀ : N) (h : ℝ) : N :=
  y₀ + h • f y₀

/-- **Order-1 Taylor expansion of the exact solution
(p = 1 special case of `lem:311A` / `thm:311B`).**

Under the hypotheses
* `yex x₀ = y₀` (the exact solution passes through `(x₀, y₀)`),
* `ContDiff ℝ 2 yex` (twice continuously differentiable),
* `∀ x, HasDerivAt yex (f (yex x)) x` (`yex` satisfies the ODE
  `y'(x) = f(y(x))`),

the residual between the exact solution and the first-order B-series
truncation is quadratic in the step size near `0`:

`|yex(x₀ + h) - (y₀ + h • f(y₀))| = O(h²)`.

This is the order-1 specialisation of the Taylor-expansion content of
Butcher §311 (the full §311 lemma is a combinatorial labelling statement
that requires a labelled-tree quotient infrastructure not yet
formalised; see file docstring). The proof is a direct simplification
of cycle 154's `explicitEulerGLM_hasOrderOne_trivialStarting`
(no `f`-correction term, so Lipschitz on `f` is unneeded).

The conclusion is stated with `h ^ (1 + 1)` rather than `h ^ 2` to
mirror the `p + 1` convention used throughout the §530 order-of-method
infrastructure; the rewriting `h ^ (1 + 1) = h ^ 2` is performed
internally. -/
theorem lem_311A_order_one
    {f : ℝ → ℝ}
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C2 : ContDiff ℝ 2 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    (fun h : ℝ => yex (x₀ + h) - bseriesOrderOne f y₀ h)
      =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (1 + 1)) := by
  -- Step 0: rewrite the difference using `bseriesOrderOne`'s definition.
  have hrewrite :
      (fun h : ℝ => yex (x₀ + h) - bseriesOrderOne f y₀ h)
        = (fun h : ℝ => yex (x₀ + h) - (y₀ + h * f y₀)) := by
    funext h
    simp [bseriesOrderOne, smul_eq_mul]
  rw [hrewrite]
  -- Step 1: second-order Taylor remainder for yex at x₀.
  have htaylor :
      (fun x : ℝ => yex x - taylorWithinEval yex 2 Set.univ x₀ x)
        =o[nhds x₀] (fun x : ℝ => (x - x₀) ^ 2) := by
    have htaylorLoc := taylor_isLittleO (n := 2) (f := yex) (x₀ := x₀)
      (s := Set.univ) convex_univ (Set.mem_univ _) hyex_C2.contDiffOn
    simpa [nhdsWithin_univ] using htaylorLoc
  -- Step 2: evaluate the second-order Taylor polynomial at x₀ + h.
  have hT_eval : ∀ h : ℝ,
      taylorWithinEval yex 2 Set.univ x₀ (x₀ + h)
        = yex x₀ + h * iteratedDeriv 1 yex x₀
            + h ^ 2 / 2 * iteratedDeriv 2 yex x₀ := by
    intro h
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      iteratedDerivWithin_univ, iteratedDeriv_zero, Nat.factorial,
      Nat.cast_one, Nat.cast_mul, smul_eq_mul, pow_zero, pow_one,
      mul_one, one_mul, inv_one]
    ring
  -- Step 3: identify the first derivative at x₀ with `f y₀` using the ODE.
  have hderiv_x0 : iteratedDeriv 1 yex x₀ = f y₀ := by
    rw [iteratedDeriv_one]
    have hatx := (hyex_ode x₀).deriv
    rw [hyex_x₀] at hatx
    exact hatx
  -- Step 4: translate the Taylor remainder to a `nhds 0` statement.
  have htend : Filter.Tendsto (fun h : ℝ => x₀ + h) (nhds 0) (nhds x₀) := by
    have hcont : Continuous (fun h : ℝ => x₀ + h) :=
      continuous_const.add continuous_id
    simpa using hcont.tendsto 0
  have hres :
      (fun h : ℝ => yex (x₀ + h) - taylorWithinEval yex 2 Set.univ x₀ (x₀ + h))
        =o[nhds (0 : ℝ)] (fun h : ℝ => h ^ 2) := by
    have hcomp := htaylor.comp_tendsto htend
    refine hcomp.congr' (Filter.Eventually.of_forall fun _ => rfl)
      (Filter.Eventually.of_forall fun h => ?_)
    show ((x₀ + h) - x₀) ^ 2 = h ^ 2
    ring
  -- Step 5: rewrite the goal's difference into Taylor-residual + quadratic.
  have hdiff_eq :
      (fun h : ℝ => yex (x₀ + h) - (y₀ + h * f y₀))
        = (fun h : ℝ =>
            (yex (x₀ + h) - taylorWithinEval yex 2 Set.univ x₀ (x₀ + h))
              + h ^ 2 / 2 * iteratedDeriv 2 yex x₀) := by
    funext h
    rw [hT_eval h, hderiv_x0, hyex_x₀]
    ring
  rw [hdiff_eq]
  -- Step 6: the quadratic coefficient term is O(h²).
  have hquad : (fun h : ℝ => h ^ 2 / 2 * iteratedDeriv 2 yex x₀)
      =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ 2) := by
    have hbase := Asymptotics.isBigO_const_mul_self
      (iteratedDeriv 2 yex x₀ / 2) (fun h : ℝ => h ^ 2) (nhds 0)
    refine hbase.congr' (Filter.Eventually.of_forall fun h => ?_)
      (Filter.Eventually.of_forall fun _ => rfl)
    ring
  -- Step 7: combine and collapse h ^ (1 + 1) to h ^ 2.
  have hsum := hres.isBigO.add hquad
  have hpow : (fun h : ℝ => h ^ (1 + 1)) = (fun h : ℝ => h ^ 2) := by
    funext h; ring
  rw [hpow]
  exact hsum

/-- **Chain-rule identification of the second derivative under the ODE
constraint.** Under `yex' = f ∘ yex` (the ODE) and `yex x₀ = y₀`, the
second derivative of `yex` at `x₀` equals `f'(y₀) · f(y₀)`.

Proof: `iteratedDeriv 2 yex x₀ = deriv (deriv yex) x₀` (twice unrolling
`iteratedDeriv_succ`). From `hyex_ode`, `deriv yex` agrees pointwise
with `fun x => f (yex x)`; the chain rule
(`deriv_comp`) then produces `deriv f (yex x₀) · deriv yex x₀`, which
collapses to `deriv f y₀ · f y₀` via `hyex_x₀`. -/
private theorem iteratedDeriv_two_via_ode
    {f : ℝ → ℝ} (hf_C1 : ContDiff ℝ 1 f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C3 : ContDiff ℝ 3 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    iteratedDeriv 2 yex x₀ = deriv f y₀ * f y₀ := by
  have hf_diff : Differentiable ℝ f := hf_C1.differentiable_one
  have hyex_diff : Differentiable ℝ yex :=
    hyex_C3.differentiable (by norm_num)
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv_eq : deriv yex = fun x => f (yex x) := by
    funext x
    exact (hyex_ode x).deriv
  rw [hderiv_eq]
  have hcomp : deriv (fun x => f (yex x)) x₀
      = deriv f (yex x₀) * deriv yex x₀ :=
    deriv_comp x₀ hf_diff.differentiableAt hyex_diff.differentiableAt
  rw [hcomp, (hyex_ode x₀).deriv, hyex_x₀]

/-- **Order-2 Taylor expansion of the exact solution
(p = 2 special case of `lem:311A` / `thm:311B`).**

Under the hypotheses
* `ContDiff ℝ 1 f` (needed for the chain rule on `f ∘ yex`),
* `yex x₀ = y₀`,
* `ContDiff ℝ 3 yex` (third-order Taylor remainder requires C³),
* `∀ x, HasDerivAt yex (f (yex x)) x` (the ODE constraint),

the residual between the exact solution and the second-order Taylor
truncation is cubic in the step size near `0`:

`|yex(x₀ + h) - (y₀ + h·f(y₀) + (h²/2)·f'(y₀)·f(y₀))| = O(h³)`.

Stated for `ℝ → ℝ` scalars using the multiplicative form
`deriv f y₀ * f y₀`; the polymorphic version (using
`fderiv ℝ f y₀ (f y₀)`) is deferred to future cycles to avoid
multilinear-map plumbing here. The conclusion uses `h ^ (2 + 1)` to
match the `p + 1` convention of `lem_311A_order_one`. -/
theorem lem_311A_order_two
    {f : ℝ → ℝ} (hf_C1 : ContDiff ℝ 1 f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C3 : ContDiff ℝ 3 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    (fun h : ℝ => yex (x₀ + h) -
        (y₀ + h * f y₀ + h ^ 2 / 2 * (deriv f y₀ * f y₀)))
      =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (2 + 1)) := by
  -- Step 1: third-order Taylor remainder for yex at x₀.
  have htaylor :
      (fun x : ℝ => yex x - taylorWithinEval yex 3 Set.univ x₀ x)
        =o[nhds x₀] (fun x : ℝ => (x - x₀) ^ 3) := by
    have htaylorLoc := taylor_isLittleO (n := 3) (f := yex) (x₀ := x₀)
      (s := Set.univ) convex_univ (Set.mem_univ _) hyex_C3.contDiffOn
    simpa [nhdsWithin_univ] using htaylorLoc
  -- Step 2: evaluate the 3rd-order Taylor polynomial at x₀ + h.
  have hT_eval : ∀ h : ℝ,
      taylorWithinEval yex 3 Set.univ x₀ (x₀ + h)
        = yex x₀ + h * iteratedDeriv 1 yex x₀
            + h ^ 2 / 2 * iteratedDeriv 2 yex x₀
            + h ^ 3 / 6 * iteratedDeriv 3 yex x₀ := by
    intro h
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      iteratedDerivWithin_univ, iteratedDeriv_zero, Nat.factorial,
      Nat.cast_one, Nat.cast_mul, smul_eq_mul, pow_zero,
      pow_one, mul_one, one_mul, inv_one]
    ring
  -- Step 3: identify the first derivative at x₀ with f y₀.
  have hderiv1_x0 : iteratedDeriv 1 yex x₀ = f y₀ := by
    rw [iteratedDeriv_one]
    have hatx := (hyex_ode x₀).deriv
    rw [hyex_x₀] at hatx
    exact hatx
  -- Step 4: identify the second derivative at x₀ with deriv f y₀ * f y₀.
  have hderiv2_x0 : iteratedDeriv 2 yex x₀ = deriv f y₀ * f y₀ :=
    iteratedDeriv_two_via_ode hf_C1 hyex_x₀ hyex_C3 hyex_ode
  -- Step 5: translate the Taylor remainder to a `nhds 0` statement.
  have htend : Filter.Tendsto (fun h : ℝ => x₀ + h) (nhds 0) (nhds x₀) := by
    have hcont : Continuous (fun h : ℝ => x₀ + h) :=
      continuous_const.add continuous_id
    simpa using hcont.tendsto 0
  have hres :
      (fun h : ℝ => yex (x₀ + h) - taylorWithinEval yex 3 Set.univ x₀ (x₀ + h))
        =o[nhds (0 : ℝ)] (fun h : ℝ => h ^ 3) := by
    have hcomp := htaylor.comp_tendsto htend
    refine hcomp.congr' (Filter.Eventually.of_forall fun _ => rfl)
      (Filter.Eventually.of_forall fun h => ?_)
    show ((x₀ + h) - x₀) ^ 3 = h ^ 3
    ring
  -- Step 6: rewrite the goal's difference into Taylor-residual + cubic.
  have hdiff_eq :
      (fun h : ℝ => yex (x₀ + h) -
          (y₀ + h * f y₀ + h ^ 2 / 2 * (deriv f y₀ * f y₀)))
        = (fun h : ℝ =>
            (yex (x₀ + h) - taylorWithinEval yex 3 Set.univ x₀ (x₀ + h))
              + h ^ 3 / 6 * iteratedDeriv 3 yex x₀) := by
    funext h
    rw [hT_eval h, hderiv1_x0, hderiv2_x0, hyex_x₀]
    ring
  rw [hdiff_eq]
  -- Step 7: the cubic coefficient term is O(h³).
  have hcubic : (fun h : ℝ => h ^ 3 / 6 * iteratedDeriv 3 yex x₀)
      =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ 3) := by
    have hbase := Asymptotics.isBigO_const_mul_self
      (iteratedDeriv 3 yex x₀ / 6) (fun h : ℝ => h ^ 3) (nhds 0)
    refine hbase.congr' (Filter.Eventually.of_forall fun h => ?_)
      (Filter.Eventually.of_forall fun _ => rfl)
    ring
  -- Step 8: combine and collapse h ^ (2 + 1) to h ^ 3.
  have hsum := hres.isBigO.add hcubic
  have hpow : (fun h : ℝ => h ^ (2 + 1)) = (fun h : ℝ => h ^ 3) := by
    funext h; ring
  rw [hpow]
  exact hsum

/-- **Chain-rule identification of the third derivative under the ODE
constraint.** Under `yex' = f ∘ yex` (the ODE), `yex x₀ = y₀`,
`ContDiff ℝ 2 f` and `ContDiff ℝ 4 yex`, the third derivative of
`yex` at `x₀` equals `f''(y₀) · f(y₀)² + f'(y₀)² · f(y₀)`.

Proof sketch: `iteratedDeriv 3 yex x₀ = deriv (iteratedDeriv 2 yex) x₀`
via `iteratedDeriv_succ`. We then identify `iteratedDeriv 2 yex`
pointwise with `fun x => deriv f (yex x) * f (yex x)` (the polymorphic
version of `iteratedDeriv_two_via_ode`'s point-evaluation argument:
the chain-rule computation works at every `x`, not just `x₀`).
Finally we apply the product rule (`deriv_mul`) and chain rule
(`deriv_comp`) to extract the two terms, with `(hyex_ode x₀).deriv`
collapsing `deriv yex x₀ = f y₀`.

The `ContDiff ℝ 2 f` hypothesis is the minimum needed: `deriv f`
must be differentiable for the second chain-rule layer, which
follows from `ContDiff.differentiable_deriv_two`. -/
private theorem iteratedDeriv_three_via_ode
    {f : ℝ → ℝ} (hf_C2 : ContDiff ℝ 2 f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C4 : ContDiff ℝ 4 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    iteratedDeriv 3 yex x₀
      = deriv (deriv f) y₀ * (f y₀) ^ 2 + (deriv f y₀) ^ 2 * f y₀ := by
  have hf_C1 : ContDiff ℝ 1 f := hf_C2.of_le (by norm_num)
  have hf_diff : Differentiable ℝ f := hf_C1.differentiable_one
  have hderivf_diff : Differentiable ℝ (deriv f) :=
    hf_C2.differentiable_deriv_two
  have hyex_diff : Differentiable ℝ yex :=
    hyex_C4.differentiable (by norm_num)
  -- Step 1: pointwise identification of `iteratedDeriv 2 yex`.
  have hiter2 : iteratedDeriv 2 yex = fun x => deriv f (yex x) * f (yex x) := by
    funext x
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have hderiv_eq : deriv yex = fun x => f (yex x) := by
      funext x'
      exact (hyex_ode x').deriv
    rw [hderiv_eq]
    have hcomp : deriv (fun x => f (yex x)) x
        = deriv f (yex x) * deriv yex x :=
      deriv_comp x hf_diff.differentiableAt hyex_diff.differentiableAt
    rw [hcomp, (hyex_ode x).deriv]
  -- Step 2: peel off the outer derivative.
  rw [iteratedDeriv_succ, hiter2]
  -- Step 3: product rule on `(deriv f ∘ yex) * (f ∘ yex)`.
  have hdf_yex_diff : DifferentiableAt ℝ (fun x => deriv f (yex x)) x₀ :=
    (hderivf_diff.comp hyex_diff).differentiableAt
  have hf_yex_diff : DifferentiableAt ℝ (fun x => f (yex x)) x₀ :=
    (hf_diff.comp hyex_diff).differentiableAt
  have hprod : deriv (fun x => deriv f (yex x) * f (yex x)) x₀
      = deriv (fun x => deriv f (yex x)) x₀ * f (yex x₀)
        + deriv f (yex x₀) * deriv (fun x => f (yex x)) x₀ :=
    deriv_mul hdf_yex_diff hf_yex_diff
  rw [hprod]
  -- Step 4: chain rule on each factor.
  have hchain_df : deriv (fun x => deriv f (yex x)) x₀
      = deriv (deriv f) (yex x₀) * deriv yex x₀ :=
    deriv_comp x₀ hderivf_diff.differentiableAt hyex_diff.differentiableAt
  have hchain_f : deriv (fun x => f (yex x)) x₀
      = deriv f (yex x₀) * deriv yex x₀ :=
    deriv_comp x₀ hf_diff.differentiableAt hyex_diff.differentiableAt
  rw [hchain_df, hchain_f, (hyex_ode x₀).deriv, hyex_x₀]
  ring

/-- **Order-3 Taylor expansion of the exact solution
(p = 3 special case of `lem:311A` / `thm:311B`).**

Under the hypotheses
* `ContDiff ℝ 2 f` (needed for two chain-rule layers on `f ∘ yex`),
* `yex x₀ = y₀`,
* `ContDiff ℝ 4 yex` (fourth-order Taylor remainder requires C⁴),
* `∀ x, HasDerivAt yex (f (yex x)) x` (the ODE constraint),

the residual between the exact solution and the third-order Taylor
truncation is quartic in the step size near `0`:

`|yex(x₀ + h) - (y₀ + h·f + (h²/2)·f'·f + (h³/6)·(f''·f² + (f')²·f))|
 = O(h⁴)`,

with all derivatives evaluated at `y₀`.

In Butcher's B-series notation this corresponds to the order-3
truncation `y₀ + h·F(τ₁) + (h²/2)·F(τ₂) + (h³/6)·(F(τ₃) + F(τ₃'))`
for the four trees of order ≤ 3 (single vertex, cherry, broom₃,
and the second-order tree); the two cubic terms split according to
the elementary differentials at the two distinct trees of order 3
(cf. Butcher Table 310(II), rows r ≤ 3).

Stated for `ℝ → ℝ` scalars using the multiplicative form
`deriv f y₀ * f y₀`; the polymorphic version (using `fderiv ℝ f y₀`
and second-order derivatives) is deferred to future cycles. The
conclusion uses `h ^ (3 + 1)` to match the `p + 1` convention of
`lem_311A_order_one` and `lem_311A_order_two`. -/
theorem lem_311A_order_three
    {f : ℝ → ℝ} (hf_C2 : ContDiff ℝ 2 f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C4 : ContDiff ℝ 4 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    (fun h : ℝ => yex (x₀ + h) -
        (y₀ + h * f y₀ + h ^ 2 / 2 * (deriv f y₀ * f y₀)
          + h ^ 3 / 6 * (deriv (deriv f) y₀ * (f y₀) ^ 2
                          + (deriv f y₀) ^ 2 * f y₀)))
      =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (3 + 1)) := by
  have hf_C1 : ContDiff ℝ 1 f := hf_C2.of_le (by norm_num)
  have hyex_C3 : ContDiff ℝ 3 yex := hyex_C4.of_le (by norm_num)
  -- Step 1: fourth-order Taylor remainder for yex at x₀.
  have htaylor :
      (fun x : ℝ => yex x - taylorWithinEval yex 4 Set.univ x₀ x)
        =o[nhds x₀] (fun x : ℝ => (x - x₀) ^ 4) := by
    have htaylorLoc := taylor_isLittleO (n := 4) (f := yex) (x₀ := x₀)
      (s := Set.univ) convex_univ (Set.mem_univ _) hyex_C4.contDiffOn
    simpa [nhdsWithin_univ] using htaylorLoc
  -- Step 2: evaluate the 4th-order Taylor polynomial at x₀ + h.
  have hT_eval : ∀ h : ℝ,
      taylorWithinEval yex 4 Set.univ x₀ (x₀ + h)
        = yex x₀ + h * iteratedDeriv 1 yex x₀
            + h ^ 2 / 2 * iteratedDeriv 2 yex x₀
            + h ^ 3 / 6 * iteratedDeriv 3 yex x₀
            + h ^ 4 / 24 * iteratedDeriv 4 yex x₀ := by
    intro h
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      iteratedDerivWithin_univ, iteratedDeriv_zero, Nat.factorial,
      Nat.cast_one, Nat.cast_mul, smul_eq_mul, pow_zero,
      pow_one, mul_one, one_mul, inv_one]
    ring
  -- Step 3: identify the first derivative at x₀ with f y₀.
  have hderiv1_x0 : iteratedDeriv 1 yex x₀ = f y₀ := by
    rw [iteratedDeriv_one]
    have hatx := (hyex_ode x₀).deriv
    rw [hyex_x₀] at hatx
    exact hatx
  -- Step 4: identify the second derivative at x₀.
  have hderiv2_x0 : iteratedDeriv 2 yex x₀ = deriv f y₀ * f y₀ :=
    iteratedDeriv_two_via_ode hf_C1 hyex_x₀ hyex_C3 hyex_ode
  -- Step 5: identify the third derivative at x₀.
  have hderiv3_x0 : iteratedDeriv 3 yex x₀
      = deriv (deriv f) y₀ * (f y₀) ^ 2 + (deriv f y₀) ^ 2 * f y₀ :=
    iteratedDeriv_three_via_ode hf_C2 hyex_x₀ hyex_C4 hyex_ode
  -- Step 6: translate the Taylor remainder to a `nhds 0` statement.
  have htend : Filter.Tendsto (fun h : ℝ => x₀ + h) (nhds 0) (nhds x₀) := by
    have hcont : Continuous (fun h : ℝ => x₀ + h) :=
      continuous_const.add continuous_id
    simpa using hcont.tendsto 0
  have hres :
      (fun h : ℝ => yex (x₀ + h) - taylorWithinEval yex 4 Set.univ x₀ (x₀ + h))
        =o[nhds (0 : ℝ)] (fun h : ℝ => h ^ 4) := by
    have hcomp := htaylor.comp_tendsto htend
    refine hcomp.congr' (Filter.Eventually.of_forall fun _ => rfl)
      (Filter.Eventually.of_forall fun h => ?_)
    show ((x₀ + h) - x₀) ^ 4 = h ^ 4
    ring
  -- Step 7: rewrite the goal's difference into Taylor-residual + quartic.
  have hdiff_eq :
      (fun h : ℝ => yex (x₀ + h) -
          (y₀ + h * f y₀ + h ^ 2 / 2 * (deriv f y₀ * f y₀)
            + h ^ 3 / 6 * (deriv (deriv f) y₀ * (f y₀) ^ 2
                            + (deriv f y₀) ^ 2 * f y₀)))
        = (fun h : ℝ =>
            (yex (x₀ + h) - taylorWithinEval yex 4 Set.univ x₀ (x₀ + h))
              + h ^ 4 / 24 * iteratedDeriv 4 yex x₀) := by
    funext h
    rw [hT_eval h, hderiv1_x0, hderiv2_x0, hderiv3_x0, hyex_x₀]
    ring
  rw [hdiff_eq]
  -- Step 8: the quartic coefficient term is O(h⁴).
  have hquartic : (fun h : ℝ => h ^ 4 / 24 * iteratedDeriv 4 yex x₀)
      =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ 4) := by
    have hbase := Asymptotics.isBigO_const_mul_self
      (iteratedDeriv 4 yex x₀ / 24) (fun h : ℝ => h ^ 4) (nhds 0)
    refine hbase.congr' (Filter.Eventually.of_forall fun h => ?_)
      (Filter.Eventually.of_forall fun _ => rfl)
    ring
  -- Step 9: combine and collapse h ^ (3 + 1) to h ^ 4.
  have hsum := hres.isBigO.add hquartic
  have hpow : (fun h : ℝ => h ^ (3 + 1)) = (fun h : ℝ => h ^ 4) := by
    funext h; ring
  rw [hpow]
  exact hsum

/-- **Non-vacuity witness.** With the zero vector field `f := 0` and the
constant exact solution `yex := y₀`, all three hypotheses of
`lem_311A_order_one` are satisfied:
* `yex x₀ = y₀` is `rfl`,
* `ContDiff ℝ 2 (fun _ => y₀)` follows from `contDiff_const`,
* `HasDerivAt (fun _ => y₀) 0 x` follows from `hasDerivAt_const` and
  `f (yex x) = 0` is `rfl`.

The conclusion specialises to `(fun h => 0) =O (fun h => h²)`, which is
trivially true. This confirms that `lem_311A_order_one`'s hypothesis set
is simultaneously satisfiable. -/
example (x₀ y₀ : ℝ) :
    (fun h : ℝ => (fun _ : ℝ => y₀) (x₀ + h)
                    - bseriesOrderOne (fun _ : ℝ => (0 : ℝ)) y₀ h)
      =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (1 + 1)) :=
  lem_311A_order_one (f := fun _ : ℝ => (0 : ℝ)) (yex := fun _ : ℝ => y₀)
    (x₀ := x₀) (y₀ := y₀) rfl contDiff_const (fun x => hasDerivAt_const x y₀)

/-- **Non-vacuity witness for `lem_311A_order_three`.** With the zero
vector field `f := 0` and the constant exact solution `yex := y₀`,
all hypotheses of `lem_311A_order_three` are satisfied:
* `ContDiff ℝ 2 (fun _ => 0)` follows from `contDiff_const`,
* `yex x₀ = y₀` is `rfl`,
* `ContDiff ℝ 4 (fun _ => y₀)` follows from `contDiff_const`,
* `HasDerivAt (fun _ => y₀) 0 x` is `hasDerivAt_const`.

The conclusion specialises to a trivially-zero residual: with the
zero field, `f y₀ = 0`, `deriv f y₀ = 0`, `deriv (deriv f) y₀ = 0`,
so the entire B-series collapses to `y₀` and the difference is
identically zero. -/
example (x₀ y₀ : ℝ) :
    (fun h : ℝ => (fun _ : ℝ => y₀) (x₀ + h) -
        (y₀ + h * (fun _ : ℝ => (0 : ℝ)) y₀
          + h ^ 2 / 2
              * (deriv (fun _ : ℝ => (0 : ℝ)) y₀
                  * (fun _ : ℝ => (0 : ℝ)) y₀)
          + h ^ 3 / 6
              * (deriv (deriv (fun _ : ℝ => (0 : ℝ))) y₀
                    * ((fun _ : ℝ => (0 : ℝ)) y₀) ^ 2
                  + (deriv (fun _ : ℝ => (0 : ℝ)) y₀) ^ 2
                    * (fun _ : ℝ => (0 : ℝ)) y₀)))
      =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (3 + 1)) :=
  lem_311A_order_three (f := fun _ : ℝ => (0 : ℝ)) (yex := fun _ : ℝ => y₀)
    (x₀ := x₀) (y₀ := y₀) contDiff_const rfl contDiff_const
    (fun x => hasDerivAt_const x y₀)

/-- **Cross-section bridge (cycle 256 P3).** The cycle-256
`bseriesAlphaPartialSum` evaluated at the singleton `{vertex}` equals
the `h • f y₀` contribution of cycle-248's `bseriesOrderOne`. A
convenience theorem: it is NOT a textbook lemma, so it has no
`entity_id` label per the cycle-248 faithfulness convention. -/
theorem bseriesAlphaPartialSum_singleton_vertex_eq
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    OpenMath.Chapter3.Section310.RootedTree.bseriesAlphaPartialSum
        f y₀ h {OpenMath.Chapter3.Section310.RootedTree.vertex}
      = h • f y₀ := by
  rw [OpenMath.Chapter3.Section310.RootedTree.bseriesAlphaPartialSum,
      Finset.sum_singleton,
      OpenMath.Chapter3.Section310.RootedTree.bseriesAlphaTerm_vertex]

end OpenMath.Chapter3.Section311
