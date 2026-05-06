# Issue: def:530B sorry-first scaffold not viable as single-cycle deliverable

## Blocker

Definition 530B (Butcher §530, p. 432) — "method `M` has order `p`
relative to a non-degenerate starting method `S` if the results found
from `SM` and `ES` agree to within `O(h^{p+1})`" — requires defining
two operators:

* `applyStartingThenStep` (textbook `SM`): apply each constituent
  generalized RK method `Sᵢ` to scalar `y₀` to produce `r` initial
  approximations, then carry out one GLM step.
* `applyExactThenStarting` (textbook `ES`): advance the exact
  solution by time `h`, then apply each `Sᵢ` to that scalar.

Both operator bodies require **multivariate fixed-point arguments**
to solve the implicit stage equations of each `Sᵢ`. They are NOT
decomposable into named sub-helpers — they are indivisible
fixed-point computations.

Cycle 149 attempted a sorry-first scaffold:

* `noncomputable def applyStartingThenStep` with `sorry` body.
* `noncomputable def applyExactThenStarting` with `sorry` body.
* `def HasOrderRelativeTo` (the predicate, no sorry).
* `theorem explicitEulerGLM_hasOrderZero_trivialStarting` non-vacuity
  witness with `sorry` body (depends on the operator-body sorries).

Sorry count went 0 → 3 (regression −2). Cycle 150 rolled back per
the cycle 138 → cycle 139 precedent (which rolled back the sorry'd
general-n statement of thm:550A added in cycle 138).

## Context

The cycle 149 scaffold was structurally sound — the predicate
encodes Butcher's "agree to within `O(h^{p+1})`" verbatim via
`Asymptotics.IsBigO (nhds (0 : ℝ))` of the difference vector
`SM(y₀, h) - ES(y₀, h) : Fin r → ℝ` against `h^{p+1}`. The
non-vacuity witness was for the most degenerate non-trivial shape:
`(s, r) = (1, 1)` explicit Euler GLM × `r = 1` trivial starting
method, claiming order `p = 0`. Once the operator bodies close, the
witness becomes a one- or two-line argument (both sides equal `y₀`
at `h = 0`, so the difference is continuous and vanishes at `0`).

The structural problem: **the sorry-first workflow assumes the
to-be-closed body decomposes into named sub-lemmas that can be
proved one-by-one**. The cycle-149 operator bodies do not — they
are atomic fixed-point computations.

## What was tried

* Cycle 149 worker wrote the four sorry-first declarations in
  `OpenMath/Chapter5/Section530.lean` (lines ~327-400 in cycle
  149's file state) plus three new imports
  (`Mathlib.Analysis.Asymptotics.Defs`,
  `Mathlib.Analysis.Calculus.Deriv.Basic`,
  `OpenMath.Chapter5.Section510`).
* Cycle 149 worker's own analysis: closure needs Path A
  (explicit-only restricted operators, ~2-3 cycles) or Path B
  (general implicit via fixed-point, ~3-5 cycles).

## Possible solutions

### Path A — Explicit-only operators with `IsExplicit` predicate

Restrict to the explicit case where `A^{(i)}` is strictly lower
triangular for every constituent method `Sᵢ`. Then the stage
equations `Yⱼ = y₀ + h · Σₖ A^{(i)}ⱼₖ · f(Yₖ)` are not implicit —
they can be evaluated by direct recursion on `j = 0, 1, …, sᵢ-1`.

Plan:
1. Cycle N: introduce `def IsExplicit (M : GeneralizedRungeKuttaMethod s) : Prop`
   capturing strict-lower-triangular `A`. Witness: `trivialGeneralizedRK`,
   `nontrivialTwoStageGRK` are explicit; build a non-explicit
   counterexample (e.g. implicit-midpoint-style with `A 0 0 = 1/2`).
2. Cycle N+1: define `applyStartingThenStep_explicit` and
   `applyExactThenStarting_explicit` with hypothesis
   `∀ i, IsExplicit (S.method i)`. Body: direct recursion on stage
   index — each stage's `Y_j` is a `Finset.sum` over already-computed
   stages `Y_0, …, Y_{j-1}`.
3. Cycle N+2: define `HasOrderRelativeTo_explicit` and prove the
   non-vacuity witness for explicit Euler × trivialStartingMethod.

Total: ~2-3 cycles. Limitation: does not capture implicit methods
(e.g. backward Euler from cycle 142, implicit midpoint from cycle
135). Future cycles would need a separate definitional path for
implicit methods if those become target entities.

### Path B — General implicit via `ContractingWith` / `Function.IsFixedPt`

Use Mathlib's fixed-point machinery. The stage equation
`Y = y₀·𝟙 + h · A · F(Y)` (where `F y j = f y` componentwise) is a
fixed point of the map `T(Y) = y₀·𝟙 + h · A · F(Y)`. For sufficiently
small `h` and Lipschitz `f`, `T` is a contraction; uniqueness +
existence follow from Banach.

Plan:
1. Cycle N: introduce a Lipschitz hypothesis on `f`. Use
   `ContractingWith.fixedPoint` to define
   `stageVector : ℝ → ℝ → (Fin s → ℝ) → Fin s → ℝ`.
2. Cycle N+1: extend to `Sᵢ(y₀, h)` then to `applyStartingThenStep`.
3. Cycle N+2: define `applyExactThenStarting` (similar but the input
   is `yex(x₀ + h)` instead of `y₀`, and there's an additional
   exact-flow application step).
4. Cycle N+3: prove `HasOrderRelativeTo` non-vacuity for explicit
   Euler × trivialStartingMethod. This requires a Taylor expansion
   argument; the `O(h)` bound is straightforward but Lean
   formalization is non-trivial.
5. Cycle N+4: optional — prove order `p = 1` for explicit Euler
   relative to trivialStartingMethod (the textbook claim).

Total: ~3-5 cycles. Captures both explicit and implicit methods.
Heavy on `Asymptotics` / `HasDerivAt` / `Continuous` machinery.

## Closure remark on the non-vacuity witness

Once the operator bodies close (Path A or B), the cycle 149 witness
`explicitEulerGLM_hasOrderZero_trivialStarting` is essentially
mechanical:

* Explicit Euler GLM has `(s, r) = (1, 1)` with `b₀ = 1, b = 1, A = 0`
  → `M`-step is `y_out = y_in + h·f(y_in)`.
* `trivialStartingMethod` is `r = 1` with the trivial 1-stage
  generalized RK `b₀ = 1, b = 1, A = 0` → `S`-application is
  `y_out = y_in + h·f(y_in)`.
* Composing: `SM(y₀, h)` first applies `S` to `y₀` giving
  `y₀ + h·f(y₀)`, then takes one `M`-step: but the `M`-step of an
  `r = 1` GLM on the `r`-vector `(y₀ + h·f(y₀))` reuses that scalar
  — so `SM(y₀, h) = (y₀ + h·f(y₀))` as a `Fin 1 → ℝ` vector.
* `ES(y₀, h)` first advances `yex` by `h` to `yex(x₀ + h)`, then
  applies `S` to that scalar: `S(yex(x₀+h), h) = yex(x₀+h) + h·f(yex(x₀+h))`.
* Difference: `SM - ES = (y₀ + h·f(y₀)) - (yex(x₀+h) + h·f(yex(x₀+h)))`.
* By `yex(x₀) = y₀` and `yex' = f ∘ yex`, Taylor:
  `yex(x₀+h) = y₀ + h·f(y₀) + O(h²)`. So
  `SM - ES = -O(h²) + h·(f(y₀) - f(yex(x₀+h)))`. The second term
  is `h · O(h)` (by Lipschitz `f` × `yex(x₀+h) - y₀ = O(h)`), so
  `SM - ES = O(h²)`, dominating the required `O(h^{0+1}) = O(h)`.

This closed-form analysis suggests the witness is genuine (not
vacuous) once operators close — it's not the case that
`HasOrderRelativeTo` always trivially holds for all `M, S, p`.

## Cycle plan

* **Cycle 150**: rollback (this issue file documents the rollback
  rationale). No further def:530B work.
* **Cycle 151+**: planner decides Path A vs Path B based on which
  upstream theorems (e.g. order conditions in §530+) require which
  scope.

## Cross-reference

`def:530B` blocks (per dependency graph):
* `def:530C` (variants of order)
* §530+ order-condition theorems (cycle-by-cycle as planner targets
  them).
