import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
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

end OpenMath.Chapter3.Section311
