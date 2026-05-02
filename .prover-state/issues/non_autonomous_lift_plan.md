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

* `exact_solution_norm_bound` (line 568) — **LANDED cycle 064** as
  `exact_solution_norm_bound_nonauto` (1:1 port, no Lipschitz).
* `residual_integral_form` (line 624) — **LANDED cycle 064** as
  `residual_integral_form_nonauto` (1:1 port, no Lipschitz).
* `residual_bound` (line 692) — **LANDED cycle 065** as
  `residual_bound_nonauto` (joint-Lipschitz, bound shape
  `(1/2) i² h² L_joint (1+M_bound)`).
* `deriv_diff_bound` (line 790) — **LANDED cycle 065** as
  `deriv_diff_bound_nonauto` (joint-Lipschitz, bound shape
  `i h L_joint (1+M_bound)`).
* `localTruncationError_bound` = `lem:406B` (line 923) — **LANDED
  cycle 065** as `LinearMultistepMethod.localTruncationError_bound_nonauto`
  (joint-Lipschitz, faithful re-parameterisation of `lem:406B`).
* Plus α/β-sum wrappers
  `localTruncationError_α_sum_bound_nonauto`,
  `localTruncationError_β_sum_bound_nonauto` and helper
  `joint_lipschitz_pair_bound`.

**RESOLVED in cycle 065**: cluster 1 of the 064–067 refactor is
complete. The cycle 065 fallback (deferring α/β + main theorem to
cycle 066) was NOT triggered — all 6 lemmas landed within the
~200-line budget.

### Cycle 064 deferral note: joint-Lipschitz hypothesis

Cycle 064 traced the autonomous `residual_bound` (line 692–782) and
`deriv_diff_bound` (line 789–822) Lipschitz invocations. In each case
the two `f`-applications differ in their *time* argument, not just
their spatial argument:

* `residual_bound`: `|f (y(x+hξ)) − f (y x)|` becomes
  `|f (x+hξ) (y(x+hξ)) − f x (y x)|`. Time args: `x+hξ` vs `x`.
* `deriv_diff_bound`: `|f (y x) − f (y(x−ih))|` becomes
  `|f x (y x) − f (x−ih) (y(x−ih))|`. Time args: `x` vs `x−ih`.

`LipschitzInSecond Set.univ L f` (cycle 063 adapter) is Lipschitz in
the *spatial* argument only, uniformly in `t`, so it does NOT bound
`|f t₁ y₁ − f t₂ y₂|` when `t₁ ≠ t₂`.

**Cycle 065 plan**: introduce a joint-Lipschitz hypothesis on the
uncurried `f` (e.g. `LipschitzWith L_joint.toNNReal (Function.uncurry f)`,
or jointly `(L_t, L_y)`-Lipschitz with separate constants) and apply
it uniformly to `residual_bound_nonauto`, `deriv_diff_bound_nonauto`,
and `localTruncationError_bound_nonauto`. Do not introduce piecemeal
across one helper at a time — the three helpers form a tight
algebraic chain and must share the hypothesis form.

### Cycle 066 — lift §406D recurrence helpers (~200 lines)

* `T1_bound` (line 1180) — **LANDED cycle 066** as `T1_bound_nonauto`
  (joint-Lipschitz collapsed at coinciding time arg; bound shape
  `h L_joint |β₀| · |a−b|`).
* `T2_bound` (line 1199) — **LANDED cycle 066** as `T2_bound_nonauto`
  (per-summand joint-Lipschitz collapsed at coinciding time arg;
  bound shape `h L_joint Σ|β| · Mmax`).
* `T3_bound` (line 1239) — **LANDED cycle 066** as `T3_bound_nonauto`
  (trivial wrapper of cycle 065's `localTruncationError_bound_nonauto`).
* `globalError_decomposition` (line 1094) — **LANDED cycle 066** as
  `globalError_decomposition_nonauto` (private helper, mirror of the
  autonomous algebraic identity (406d) with `f t (yex t)` substitution).
* `globalError_recurrence_bound` (line 1268) — **LANDED cycle 066**
  as `LinearMultistepMethod.globalError_recurrence_bound_nonauto`
  (per-term form, composes T1/T2/T3 + decomposition lift).
* `globalError_recurrence_bound_textbook` (line 1331) — **LANDED
  cycle 066** as
  `LinearMultistepMethod.globalError_recurrence_bound_textbook_nonauto`
  (textbook form; `(1−hL_joint|β₀|)`-inversion mirroring autonomous).

**RESOLVED in cycle 066**: cluster 2 of the 064–067 refactor is
complete. All 6 new lemmas (5 strategy targets + 1 private decomposition
helper) landed within the cycle's budget. The cycle 066 fallback
(deferring (4) and (5) to cycle 067) was NOT triggered.

### Cycle 067 — lift §406D recurrence-form intermediates (~474 lines)

* **Re-scoped on cycle 067**: the named squeeze helpers
  (`globalError_outer_squeeze_a_term`,
  `globalError_outer_squeeze_c_term`, `bOf_tendsto_at_zero`,
  `cOf_tendsto_at_zero`, `aOf_tendsto_zero`, `bOf_limit_pos`) are
  already shape-agnostic (they take `{a b c : ℝ → ℝ}` or scalar
  `Θ L M_bound` directly). The actual cluster-3 lift work was the
  two intermediate helpers that take an autonomous `f : ℝ → ℝ`.
* `globalError_per_step_sum_form` (line 2542) — **LANDED cycle 067**
  as `globalError_per_step_sum_form_nonauto` (~50 LOC; thin wrapper
  of cycle 066's `globalError_recurrence_bound_textbook_nonauto`
  with `Mmax := ∑ |ε(n−(j+1))|` specialisation).
* `globalError_recurrence_form_explicit` (line 3249) — **LANDED
  cycle 067** as `globalError_recurrence_form_explicit_nonauto`
  (~420 LOC; mechanical 1:1 port under `L ↦ L_joint`,
  `M_bound ↦ (1 + M_bound)`, and the `globalError_per_step_sum_form
  ↦ globalError_per_step_sum_form_nonauto` swap).

**RESOLVED in cycle 067**: cluster 3 is complete. Total LOC delta
+474, within the 500-LOC ceiling. The shape-agnostic squeeze
helpers above are reused verbatim by cycle 068.

### Cycle 068 — close `stable_consistent_isConvergent` (~80 lines)

Compose `globalError_recurrence_form_explicit_nonauto` (cycle 067)
+ `discrete_gronwall_exp_bound` (cycle 050) + the existing
shape-agnostic squeeze helpers (`globalError_outer_squeeze_*`,
`bOf_tendsto_at_zero`, `cOf_tendsto_at_zero`, `aOf_tendsto_zero`,
`bOf_limit_pos`) under the cycle 063 boundary adapters
(`lipschitzInSecond_univ_toLipschitzWith`, `f_yex_bound_on_Icc`,
`hstart_shape_bridge`). Cycle 068's strategy will determine whether
a joint-Lipschitz adapter (uncurried `f` from `LipschitzInSecond`
+ continuity) needs to be added to the cycle 063 set.

(Schedule slipped one cycle relative to the original cycle 063 plan
because cycle 064 deferred §406B helpers 3/4/5 to cycle 065.)

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
* `OpenMath/Chapter4/Section404.lean:5398` — the sorry to close
  (cycle 068, after cycle 067 cluster-3 lift).
* `.prover-state/task_results/cycle_062.md` — original lift
  estimate (200–400 lines, "no deep new mathematics").
