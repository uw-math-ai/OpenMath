# Cycle 008 Results

## Worked on

`thm:110C` — *Existence and uniqueness of solutions* (Butcher §110, p. 44).
Three new theorems added to `OpenMath/Chapter1/Section110.lean`:

* `ode_solution_unique` — uniqueness half (closed `Icc a b`).
* `ode_solution_exists` — existence half (with documented `‖f‖`-bound
  strengthening).
* `ode_existence_uniqueness` — combined `∃ y, ... ∧ ∀ z, ...` packaging.

## Approach

Followed the cycle-008 strategy step-by-step:

1. Re-read `extraction/formalization_data/entities/thm_110C.json` and
   anchored on the verbatim `statement_latex`.
2. Audited the Mathlib ODE API:
   `Mathlib/Analysis/ODE/PicardLindelof.lean`
   (`IsPicardLindelof`, `exists_eq_forall_mem_Icc_hasDerivWithinAt₀`)
   for existence, and `Mathlib/Analysis/ODE/Gronwall.lean`
   (`ODE_solution_unique_of_mem_Icc_right`) for uniqueness.
3. Wrote the three theorem statements and discovered that the
   straightforward translations *closed* directly via Mathlib without
   needing Aristotle: uniqueness reduces to the `Icc_right` Mathlib
   theorem after a `LipschitzWith.lipschitzOnWith` shim, existence to a
   hand-built `IsPicardLindelof` record, and the combined packaging
   reduces to existence + uniqueness with a small `nhdsWithin` bridge
   from `Icc a b` to `Ici x` for `x ∈ Ico a b`.
4. Compiled. Initial errors: `𝓝` notation out of scope (fixed by
   `open scoped Topology`), an unused-simp-arg warning, and a wrong
   keyword-argument name in `Filter.mem_of_superset`. All three were
   trivially fixed.
5. Verified `#print axioms` for each theorem: only `propext`,
   `Classical.choice`, `Quot.sound`. No `sorryAx`, no new `axiom`.

**Aristotle was not invoked this cycle.** The strategy mandates Aristotle
for any `sorry`s; the scaffold compiled with zero `sorry`s on the first
real attempt, so there was nothing to submit. (The Aristotle-first rule
is a tool for closing `sorry`s, not a quota.)

## Result

**SUCCESS.** All three theorems ship sorry-free, axiom-clean (only
`propext`, `Classical.choice`, `Quot.sound`), with `lake build OpenMath`
green.

* `lake env lean OpenMath/Chapter1/Section110.lean`: exit 0, no
  diagnostics.
* `lake build`: exit 0 (`Built OpenMath`).
* `#print axioms` on all three: standard kernel axioms only.

`extraction/formalization_data/lean_status.json` updated:
`thm:110C` → `formalized`, pointing at
`OpenMath.Chapter1.Section110.ode_existence_uniqueness`.

## Faithfulness check

### `ode_solution_unique`

* Entity: `thm:110C` (uniqueness half of Butcher's combined statement).
* Textbook statement (from `entities/thm_110C.json`,
  `statement_latex`):
  > Consider an initial value problem
  > \( y'(x) = f(x, y(x)),\quad y(a) = y_0, \)
  > where \( f : [a, b] \times \mathbb{R}^N \to \mathbb{R}^N \) is
  > continuous in its first variable and satisfies a Lipschitz
  > condition in its second variable. Then there exists a **unique**
  > solution to this problem.
* Lean statement captures: **same content** for the uniqueness half.
  Hypotheses match exactly: `LipschitzInSecond (Icc a b) L f` is
  `∀ x ∈ Icc a b, LipschitzWith L (f x)`, which is Butcher's Lipschitz
  condition; `ContinuousOn y (Icc a b)` is the natural continuity
  shape; the derivative hypothesis
  `∀ x ∈ Ico a b, HasDerivWithinAt y (f x (y x)) (Ici x) x` is
  Mathlib's standard right-derivative formulation, equivalent to
  Butcher's `y'(x) = f(x, y(x))`.
* Tautology check: conclusion `EqOn y z (Icc a b)` is not in the
  hypotheses. **Pass.**
* Identity check: proof body is a `refine` calling
  `ODE_solution_unique_of_mem_Icc_right` with three sub-goals.
  Real reduction work, not `exact h`. **Pass.**
* Hypothesis-strength check: hypotheses match Butcher exactly; no
  extras. **Pass.**

### `ode_solution_exists`

* Entity: `thm:110C` (existence half).
* Textbook statement: same as above (existence half).
* Lean statement captures: **stronger** than Butcher.
  * Justification: Mathlib's `IsPicardLindelof` is *local* and requires
    `‖f t y‖ ≤ M` on `closedBall y₀ a_rad` plus `M * (b - a) ≤ a_rad`.
    Butcher's hypothesis (global Lipschitz, no `‖f‖`-bound) implies
    such a bound exists for *each* fixed ball, but constructing it on
    the *full* `[a, b]` requires concatenating local solutions —
    multi-cycle infrastructure.
  * Strengthening explicitly documented in `ode_solution_exists`
    docstring and in
    `.prover-state/issues/picard_lindelof_bound_strengthening.md`.
* Tautology check: conclusion `∃ y, y a = y₀ ∧ ∀ x ∈ Icc a b, ...`
  is not in the hypotheses. **Pass.**
* Identity check: proof constructs an `IsPicardLindelof` record and
  invokes `exists_eq_forall_mem_Icc_hasDerivWithinAt₀`. Real
  reduction work. **Pass.**
* Hypothesis-strength check: extra `a_rad`, `M_norm`, `hf_cont` (per
  ball), `hf_bound`, `h_radius` documented in docstring as a
  Mathlib-API limitation, not silently introduced. **Pass with
  documented divergence.**

### `ode_existence_uniqueness`

* Entity: `thm:110C` (combined existence + uniqueness).
* Textbook statement: as above (full statement).
* Lean statement captures: **stronger** than Butcher (inherits
  `ode_solution_exists`'s `‖f‖`-bound strengthening). Same uniqueness
  shape as `ode_solution_unique`.
* Tautology check: conclusion `∃ y, (existence) ∧ (uniqueness)` is
  not in the hypotheses. **Pass.**
* Identity check: proof glues `ode_solution_exists` and
  `ode_solution_unique` via a `nhdsWithin` bridge from `Icc a b` to
  `Ici x` derivatives. Real reduction work. **Pass.**
* Hypothesis-strength check: same as `ode_solution_exists`
  (documented strengthening). **Pass with documented divergence.**

### `LipschitzInSecond` and `contraction_fixedPoint`

Pre-existing from cycles 001 and 003. Not modified. Verified
they're still `formalized` in `lean_status.json`.

## Dead ends

* Considered using `ContractingWith` directly (Butcher's textbook proof
  via the Bielecki weighted-sup norm). The textbook proof would have
  required: defining the function space `C([a,b], ℝ^N)` with the
  Bielecki norm, proving completeness, defining `φ`, proving `φ` is a
  contraction with constant `L/K < 1` for `K > L`, then invoking
  `lem:110B` (`contraction_fixedPoint`). This is several hundred lines
  of Lean. **Rejected** in favour of the Mathlib `IsPicardLindelof`
  wrapper, which already does the equivalent contraction (via the
  `next^[n]` iterate trick instead of the Bielecki weighted norm).
  Documented in `ode_solution_exists` docstring why we deviate from
  Butcher's proof method.
* Considered weakening `ode_solution_exists` to a *local* existence
  statement (matching `IsPicardLindelof` literally without the
  `M * (b - a) ≤ a_rad` global constraint). **Rejected** because it
  would no longer give Butcher's full-interval conclusion. The
  documented strengthening preserves the full-interval conclusion at
  the cost of two extra hypotheses.

## Discovery

* **Mathlib's `IsPicardLindelof` does not directly support a global
  Lipschitz hypothesis.** This is the gap behind the
  `picard_lindelof_bound_strengthening.md` issue. Future cycles
  targeting `thm:111A`, `thm:112B`, `lem:319A` will inherit this
  strengthening unless the gap is closed.
* **`HasDerivWithinAt` set-bridging via `mono_of_mem_nhdsWithin`.** For
  the `Icc → Ici` conversion at interior points of the interval, the
  right tool is `HasDerivWithinAt.mono_of_mem_nhdsWithin` plus
  `mem_nhdsWithin_iff_exists_mem_nhds_inter`. Specifically:
  `Set.Icc a b ∈ 𝓝[Set.Ici x] x` for `x ∈ Ico a b` is shown by
  exhibiting the sub-superset `Set.Ico x b ⊆ Set.Icc a b` and using
  `Iio_mem_nhds hx.2`. This pattern will likely recur in `thm:111A`.
* **Aristotle isn't always needed.** When the textbook proof maps
  cleanly onto a single Mathlib wrapper, hand-coding is faster than the
  Aristotle round-trip. The Aristotle rule is a `sorry`-closure tool,
  not a daily quota.

## Suggested next approach

Cycle 009 should target **`thm:111A`** (inhomogeneous-term variant,
§111). Per the dependency graph, it is a thin wrapper on `thm:110C`
and immediately exercises this cycle's existence/uniqueness API.
Expected shape:

* Statement: same Picard–Lindelöf conclusion but with `f(x, y) =
  A(x) y + b(x)` for continuous `A : ℝ → Matrix N N ℝ` and
  `b : ℝ → ℝ^N`.
* Proof: derive `LipschitzInSecond (Icc a b) (operatorNorm A) f` from
  the matrix bound, then invoke `ode_existence_uniqueness` directly.
* Caveat: will inherit the `‖f‖`-bound strengthening from
  `ode_solution_exists`. For matrix-times-vector RHS, the bound is
  trivial: `‖A(x) y + b(x)‖ ≤ ‖A(x)‖ * ‖y‖ + ‖b(x)‖`.

After `thm:111A`, cycle 010 should target **`thm:112B`** (one-sided
Lipschitz Grönwall bound). This uses `Mathlib/Analysis/ODE/Gronwall.lean`'s
`norm_le_gronwallBound_of_norm_deriv_right_le` directly and does **not**
inherit the `‖f‖`-bound strengthening (uniqueness-only argument).

The bigger structural item, **`picard_lindelof_bound_strengthening.md`**
(global-Lipschitz wrapper for `IsPicardLindelof`), should be planned as
a multi-cycle infrastructure project after the §110–§112 cluster. The
Jordan/Schur cluster (`jordan_canonical_form_missing.md`) is still the
next bigger blocker on the §142 side.
