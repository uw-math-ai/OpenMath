# Issue: Non-autonomous lift of `stable_consistent_isConvergent`

## Status

Cycle 062 closed `LinearMultistepMethod.stable_consistent_isConvergent_autonomous`
(autonomous-IVP form, scalar `f : ℝ → ℝ`) at
`OpenMath/Chapter4/Section404.lean:3863`. The textbook `IsConvergent`
predicate (def:402A, line 305) is non-autonomous (`f : ℝ → ℝ → ℝ`).
The lift to `LinearMultistepMethod.stable_consistent_isConvergent`
(line 4012) requires re-deriving 19 helpers from the cycle 040–062
chain to accept `f : ℝ → ℝ → ℝ` with `LipschitzInSecond Set.univ L f`.

## Cycle 063 deliverables (the boundary adapters)

* `lipschitzInSecond_univ_toLipschitzWith` — converts the
  non-autonomous Lipschitz predicate to the per-`x` autonomous form
  the helper chain consumes.
* `f_yex_bound_on_Icc` — extracts a uniform bound on `[x₀, x]` from
  joint continuity of `f` and continuity of `yex`.
* `hstart_shape_bridge` — bridges the textbook `start h i → y₀`
  shape to the per-`h` `yex (x₀+j·h) − Yh h j → 0` shape.

These three adapters form the autonomous/non-autonomous boundary;
the cycle 064+ refactor builds on them.

## Cycle 064–067 refactor plan (bottom-up)

Each helper currently takes `{f : ℝ → ℝ}` and uses autonomous `f y`
calls. The non-autonomous variant takes `{f : ℝ → ℝ → ℝ}` and uses
`f t y`, with a `LipschitzInSecond` (or per-`x` `LipschitzWith`)
hypothesis. List in dependency order:

### Cycle 064 — lift §406B sub-lemmas (~150 lines)

* `exact_solution_norm_bound` (line 568)
* `residual_integral_form` (line 624)
* `residual_bound` (line 692)
* `deriv_diff_bound` (line 790)
* `localTruncationError_bound` = `lem:406B` (line 923)

### Cycle 065 — lift §406D recurrence helpers (~200 lines)

* `T1_bound` (line 1180)
* `T2_term_bound` (line 1200)
* `globalError_step_bound` (line 1241)
* `globalError_recurrence_form` (line 2544)
* `globalError_recurrence_form_explicit` (line 3249)

### Cycle 066 — lift cycle 057–061 squeeze helpers (~100 lines)

* `globalError_outer_squeeze_a_term`
* `globalError_outer_squeeze_c_term`
* `bOf_tendsto_at_zero`, `cOf_tendsto_at_zero`,
  `aOf_tendsto_zero`, `bOf_limit_pos`

### Cycle 067 — close `stable_consistent_isConvergent` (~80 lines)

Lift `globalError_closed_form_autonomous_explicit` to non-autonomous
and prove `stable_consistent_isConvergent` directly, using:
* the cycle 063 adapters (Lipschitz, bound, hstart bridge);
* the cycle 064–066 lifted helpers.

## Why a refactor cycle by cycle (not one big cycle)

* Cycle 060 (~430 lines, single-cycle target) regressed (score −1)
  because complexity outpaced verification. Cycle 061 (3 wrappers,
  +1) and cycle 062 (autonomous theorem + wrapper, +2) showed that
  small decomposed wins land cleanly.
* The 19 helpers form 4 natural clusters along the dependency
  chain. Each cluster is ~80–200 lines.
* Aristotle batch-submits at each cluster boundary keep the manual
  effort O(50–100 lines per cycle).

## Hypothesis adaptation rules

For each helper:

* `{f : ℝ → ℝ}` → `{f : ℝ → ℝ → ℝ}`.
* `(hf_lip : LipschitzWith L.toNNReal f)` → either
  `(hf_lip : LipschitzInSecond Set.univ L f)` (and use cycle 063's
  `lipschitzInSecond_univ_toLipschitzWith` adapter inside the body)
  or per-`x` `(hf_lip : ∀ x, LipschitzWith L.toNNReal (f x))`.
* `(hyex_ode : ∀ t, deriv yex t = f (yex t))` →
  `(hyex_ode : ∀ t, deriv yex t = f t (yex t))`.
* `(hf_yex_bound : ∀ t, |f (yex t)| ≤ M_bound)` →
  `(hf_yex_bound : ∀ t ∈ Set.Icc x₀ x, |f t (yex t)| ≤ M_bound)`
  (compact-restricted) plus, where the helper indexes off the
  trajectory, the appropriate restriction.
* `(hY : M.IsLMMSolution h x₀ (fun _ y => f y) Y)` →
  `(hY : M.IsLMMSolution h x₀ f Y)`.

## Cross-references

* `extraction/formalization_data/entities/thm_406D.json` — textbook
  statement (non-autonomous).
* `OpenMath/Chapter4/Section404.lean:3863` — autonomous theorem
  (cycle 062).
* `OpenMath/Chapter4/Section404.lean:4012` — the sorry to close
  (cycle 067).
* `.prover-state/task_results/cycle_062.md` — original lift
  estimate (200–400 lines, "no deep new mathematics").
