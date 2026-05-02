# Cycle 063 Results

## Worked on

Three private adapter lemmas at the autonomous/non-autonomous boundary of
Butcher §406D, placed immediately above the cycle 062 autonomous theorem
in `OpenMath/Chapter4/Section404.lean`:

1. `lipschitzInSecond_univ_toLipschitzWith` — converts the non-autonomous
   `LipschitzInSecond Set.univ L f` predicate into the per-`x`
   `LipschitzWith L (f x)` form the cycle 040–062 helper chain consumes.
2. `f_yex_bound_on_Icc` — extracts a uniform bound on `[min x₀ x, max x₀ x]`
   for `t ↦ |f t (yex t)|` from joint continuity of `f` and continuity of
   `yex`, via `IsCompact.exists_isMaxOn`.
3. `hstart_shape_bridge` — bridges the textbook starting-data shape
   `start h i → y₀` to the per-`h` shape `yex (x₀ + j·h) − start h j → 0`
   using `ContinuousAt yex x₀` and `yex x₀ = y₀`.

Also wrote the multi-cycle refactor plan to
`.prover-state/issues/non_autonomous_lift_plan.md` (cycle 064–067 schedule
for lifting the 19 cycle 040–062 helpers from `f : ℝ → ℝ` to
`f : ℝ → ℝ → ℝ`), and submitted the three adapters to Aristotle as a
backup cross-check (project `14413b45-bf5e-4995-8451-d540ee72671a`).

The line-4012 (now line 4110) sorry — the textbook `IsConvergent` lift —
remains the cycle 064–067 target per the strategy.

## Approach

* Adapter 1 closes by definitional unfolding: `LipschitzInSecond` is
  defined as `∀ x ∈ s, LipschitzWith L (f x)` in
  `OpenMath/Chapter1/Section110.lean:45`, so the proof is the term
  `hf_lip x (Set.mem_univ _)`.
* Adapter 2 builds the continuous composition
  `t ↦ |f t (yex t)| = |Function.uncurry f (t, yex t)|` via
  `Continuous.prodMk` (Mathlib's camelCase name; `prod_mk` does not
  exist in current Mathlib), then applies
  `IsCompact.exists_isMaxOn` on `isCompact_Icc` with non-emptiness
  from `Set.nonempty_Icc.mpr min_le_max`. The maximizer's value is
  the bound (non-negative since it is an absolute value).
* Adapter 3 builds the limit `h ↦ x₀ + j·h → x₀` via
  `Continuous.tendsto` on
  `(continuous_const.add (continuous_const.mul continuous_id))` at
  `0` (avoiding `fun_prop` because `Filter.Tendsto` is not
  `@[fun_prop]`-tagged), composes with `hyex_cont_x₀.tendsto` to get
  `yex (x₀ + j·h) → y₀`, then subtracts `hstart j`.

## Result

SUCCESS — `lake env lean OpenMath/Chapter4/Section404.lean` exits with
exit code 0; only pre-existing warnings (`hM`, `hh`, `hMmax0` unused
from cycles 045/046/050) and the documented sorry at line 4110 remain.

The three adapter lemmas are pure topology/continuity boilerplate
(no new mathematics, no new dependencies, no new axiom usage).

Aristotle independently produced the same proofs (with equivalent
tactics — `IsCompact.exists_bound_of_continuousOn` vs my
`IsCompact.exists_isMaxOn` for adapter 2; `trivial` vs
`Set.mem_univ _` for adapter 1's `Set.univ` membership). I kept my
manual versions because they were already in-tree and compiling
when Aristotle returned.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `lipschitzInSecond_univ_toLipschitzWith` (private adapter — internal scaffolding, not a Butcher entity)

* Entity ID and textbook statement: N/A — this is internal scaffolding,
  not a Butcher-named concept.
* Lean statement captures: a definitional unfolding bridge.
  `LipschitzInSecond Set.univ L f` ↔ `∀ x, LipschitzWith L (f x)`
  by definition of `LipschitzInSecond` (`∀ x ∈ s, …`) and
  `Set.mem_univ`. No mathematical content.
* Tautology check: hypothesis is `LipschitzInSecond Set.univ L f`;
  conclusion is `LipschitzWith L (f x)`. Different propositions
  (one quantified, one fixed-`x`); the proof projects the
  quantifier. Not vacuous.

### `f_yex_bound_on_Icc` (private adapter — internal scaffolding)

* Entity ID and textbook statement: N/A — internal scaffolding.
  Butcher's textbook uses `M = max …` over the trajectory's compact
  interval implicitly; this lemma makes that compactness explicit.
* Lean statement captures: a *compact-restricted* bound on the
  interval `[min x₀ x, max x₀ x]`. The autonomous theorem
  `stable_consistent_isConvergent_autonomous` currently hypothesises
  the global form `∀ t : ℝ, |f (yex t)| ≤ M_bound`; the
  cycle 064+ refactor will adapt the helper chain to consume the
  compact-restricted form (which matches what the textbook actually
  delivers).
* Hypothesis strength check: requires *joint* continuity of `f`
  (`Continuous (Function.uncurry f)`), strictly more than the
  separate-variable continuity Butcher discusses. This is the
  Mathlib-standard formulation and matches what the
  `IsConvergent` predicate provides via
  `Continuous (Function.uncurry f)` at line 308.
* Tautology check: hypothesis is joint continuity + continuity of
  `yex`; conclusion is `∃ M_bound, ∀ t ∈ Icc, |f t (yex t)| ≤ M_bound`.
  The proof does real work (compactness extraction).

### `hstart_shape_bridge` (private adapter — internal scaffolding)

* Entity ID and textbook statement: N/A — internal scaffolding.
* Lean statement captures: equivalence of two starting-data
  formulations under the `IsConvergent` predicate's standing
  assumptions (`yex x₀ = y₀` from `def:402A`'s
  `yex x₀ = y₀` clause; `ContinuousAt yex x₀` extractable from
  `def:402A`'s `HasDerivAt` clause via `HasDerivAt.continuousAt`).
* Hypothesis strength check: hypotheses are exactly those `IsConvergent`
  provides; no over-strengthening.
* Tautology check: hypothesis is `start h i → y₀` (textbook shape);
  conclusion is `yex (x₀ + j·h) − start h j → 0` (per-`h` shape).
  Different propositions; the proof composes continuity at `x₀`
  with the textbook hypothesis. Not vacuous.

## Dead ends

* **`continuous_id.prod_mk`**: Mathlib renamed this to
  `continuous_id.prodMk` (camelCase). The first build attempt failed
  with `Invalid field 'prod_mk'`. Fixed by switching to `prodMk`.
* **`fun_prop` for `Filter.Tendsto`**: tried `by fun_prop` to derive
  `Tendsto (fun h => x₀ + j·h) (𝓝 0) (𝓝 (x₀ + j·0))`. `Filter.Tendsto`
  is not `@[fun_prop]`-tagged, so `fun_prop` rejects the goal.
  Worked around by building `Continuous (fun h => x₀ + j·h)` (which
  *is* a `fun_prop` goal — and even directly compositional) and
  applying `Continuous.tendsto` at `0`.
* **`tendsto_const_nhds.mul Filter.tendsto_id`**: failed with
  `typeclass instance problem is stuck — ContinuousMul ?m.93`
  because Lean could not unify the carrier type from the
  surrounding context. The `Continuous` route avoids this entirely
  since the carrier is fixed by `continuous_id : Continuous (id : ℝ → ℝ)`.

## Discovery

* Mathlib's `Continuous.prodMk` (camelCase) is the right pairing API
  for cycle 064+'s `Function.uncurry f` rewrites — `prod_mk`
  (snake_case) is gone.
* `Filter.Tendsto` is not `@[fun_prop]`. Use `Continuous.tendsto`
  on a `by continuity`-or-`by fun_prop` discharge of the
  underlying `Continuous` goal, then chain with `simpa` to land
  on the desired `nhds`-target.
* Aristotle handles compact-bound extractions via
  `IsCompact.exists_bound_of_continuousOn` (a real-valued
  `‖·‖`-bound API) rather than `IsCompact.exists_isMaxOn`
  (the maximum-attaining variant). For cycle 064+ helpers that
  thread an explicit `M_bound`, the `exists_bound` route is
  slightly shorter and avoids needing the maximizer's witness.

## Suggested next approach

Per the issue file `non_autonomous_lift_plan.md`, cycle 064 should
lift the §406B sub-lemmas (5 helpers, ~150 lines, lines 568–923 of
`Section404.lean`) from `{f : ℝ → ℝ}` to `{f : ℝ → ℝ → ℝ}` using
the cycle 063 adapters as the boundary. The adapters are now in
place; cycle 064 only needs to thread them through the §406B
proofs and update the hypothesis types.

Concrete cycle 064 deliverables (per the issue file):

* `exact_solution_norm_bound` (line 568) — non-autonomous variant.
* `residual_integral_form` (line 624) — non-autonomous variant.
* `residual_bound` (line 692) — non-autonomous variant.
* `deriv_diff_bound` (line 790) — non-autonomous variant.
* `localTruncationError_bound` = `lem:406B` (line 923) — non-autonomous
  variant; this is the §406B textbook target.

Each is a 1:1 rename of `f y` to `f t y`, plus a `LipschitzInSecond
Set.univ L f` hypothesis (consumed via cycle 063's adapter 1). Aristotle
should be batch-submitted for the §406B variants since they are
mechanical translations.

Recommendation: keep cycle 064 scope to ~150 lines (one cluster from
the issue file) to maintain the cycle 061/062 small-decomposed-win
cadence. Avoid bundling clusters across cycles 064–067.
