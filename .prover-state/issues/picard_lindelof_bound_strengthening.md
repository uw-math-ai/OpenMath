# Issue: `ode_solution_exists` strengthens Butcher's hypothesis with a uniform bound

## Blocker

Butcher's `thm:110C` hypothesis is "Lipschitz in `y` (globally) and continuous
in `x`" on `[a, b] × ℝ^N`. Mathlib's `IsPicardLindelof` (in
`Mathlib/Analysis/ODE/PicardLindelof.lean`) requires, in addition:

* a uniform bound `‖f t y‖ ≤ M` on `[a, b] × closedBall y₀ a_rad`, and
* the geometric constraint `M * (b - a) ≤ a_rad`.

Both are needed by the local-existence wrapper
`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`, which Mathlib
exposes as the only off-the-shelf existence theorem for ODE solutions on a
closed interval. Mathlib does not (currently) provide a global-Lipschitz
wrapper that yields existence on the *full* `[a, b]` from Butcher's
hypotheses alone.

## Why a uniform bound is mathematically present but not free in Mathlib

Under Butcher's hypotheses (continuous in `x`, *global* Lipschitz in `y`):

* `f · y₀` is continuous on the compact `[a, b]`, hence bounded by some
  `M₀ : ℝ`.
* For `y ∈ closedBall y₀ R`,
  `‖f t y‖ ≤ ‖f t y₀‖ + L * ‖y - y₀‖ ≤ M₀ + L * R`.
* So on `[a, b] × closedBall y₀ R`, `f` is bounded by `M(R) := M₀ + L * R`.

The Picard constraint `M(R) * (b - a) ≤ R` then becomes
`R ≥ M₀ * (b - a) / (1 - L * (b - a))`, which only solves when
`L * (b - a) < 1`.

Beyond that (i.e. for arbitrary `[a, b]`), one has to:

1. Apply `IsPicardLindelof` on a sub-interval `[a, a + Δ]` with `LΔ < 1`.
2. Use Grönwall to bound `‖y(a + Δ)‖` and re-set up `IsPicardLindelof`
   with a fresh ball around `y(a + Δ)`.
3. Iterate finitely many times to cover `[a, b]`.

This concatenation step is non-trivial Lean infrastructure (requires
careful gluing of `HasDerivWithinAt` data across subinterval boundaries
and a Grönwall-based a-priori bound) and was judged out of scope for
cycle 008.

## Current status

`OpenMath.Chapter1.Section110.ode_solution_exists` therefore takes the
bound and the radius as **explicit hypotheses**:

```lean
(a_rad M_norm : ℝ≥0)
(hf_cont : ∀ y ∈ Metric.closedBall y₀ a_rad,
    ContinuousOn (fun x => f x y) (Set.Icc a b))
(hf_bound : ∀ x ∈ Set.Icc a b, ∀ y ∈ Metric.closedBall y₀ a_rad,
    ‖f x y‖ ≤ M_norm)
(h_radius : M_norm * (b - a) ≤ a_rad)
```

Compared with Butcher, this is a **strengthening** (additional hypotheses
that the textbook does not state). The combined `ode_existence_uniqueness`
inherits the same strengthening.

`ode_solution_unique` is not affected — it uses Mathlib's
`ODE_solution_unique_of_mem_Icc_right`, which only needs Lipschitz, and
matches Butcher exactly.

## What was tried

* Searched Mathlib (`IsPicardLindelof`, `ODE_solution_unique` and
  surrounding API) for a global-Lipschitz existence wrapper. Only the
  local-radius `IsPicardLindelof` flavour is available.
* Considered deriving a uniform bound from Butcher's hypotheses + a fixed
  ball radius (closed-form `M(R) = M₀ + L * R`). This works only when
  `L * (b - a) < 1`, so it does not lift to the full `[a, b]` for general
  Lipschitz constants and intervals.

## Possible solutions for a future cycle

1. **Concatenate `IsPicardLindelof` solutions.** Build a helper lemma in
   `OpenMath/Chapter1/Section110.lean` that, given the Butcher hypotheses,
   constructs `IsPicardLindelof` instances on sub-intervals and glues
   their solutions via uniqueness on overlaps. The a-priori bound from
   Grönwall (`norm_le_gronwallBound_of_norm_deriv_right_le` in
   `Mathlib/Analysis/ODE/Gronwall.lean`) bounds `‖y(t)‖` on `[a, b]`,
   which constrains the size of the ball at each step.
2. **Upstream a Mathlib PR.** A `IsPicardLindelof.of_global_lipschitz`
   wrapper would be the right place. Worth a Mathlib RFC if the time
   investment is justified.
3. **Accept the strengthening permanently.** In the textbook, the bound
   exists implicitly; flagging it as a hypothesis (rather than deriving
   it) is mathematically sound. The cost is a less-pretty signature for
   downstream consumers.

## Affected files

* `OpenMath/Chapter1/Section110.lean` — `ode_solution_exists` and
  `ode_existence_uniqueness`.

## Affected downstream theorems

* `thm:111A` (inhomogeneous IVP, §111) — will inherit the same
  strengthening unless concatenation is built first.
* `thm:112B` (one-sided Lipschitz bound, §112) — uses Grönwall directly,
  may not be affected.
* `lem:319A` (Chapter 3) — depends on existence; would inherit.

## Recommendation

For cycles 009 and 010 (which target `thm:111A` and `thm:112B`), accept
the strengthening as an inherited hypothesis. Schedule the concatenation
infrastructure as a dedicated multi-cycle project after the §110–§112
cluster lands.
