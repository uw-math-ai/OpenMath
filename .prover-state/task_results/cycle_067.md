# Cycle 067 Results

## Worked on
Cluster 3 of the cycle 064–069 four-cluster non-autonomous lift plan
for `LinearMultistepMethod.stable_consistent_isConvergent`
(`OpenMath/Chapter4/Section404.lean:5398`, formerly :4928).

The strategy re-scoped this cluster: the named squeeze helpers
(`globalError_outer_squeeze_a_term`,
`globalError_outer_squeeze_c_term`, `bOf_tendsto_at_zero`,
`cOf_tendsto_at_zero`, `aOf_tendsto_zero`, `bOf_limit_pos`) are
already shape-agnostic — they take `{a b c : ℝ → ℝ}` or scalar
`Θ L M_bound` directly with no `f`-shape data. The actual cluster
work is to lift the two intermediate helpers that *do* take an
autonomous `f : ℝ → ℝ`:

1. `globalError_per_step_sum_form` (line 2542)
2. `globalError_recurrence_form_explicit` (line 3249)

## Approach

### Step 0 — Aristotle status check (one-shot)

Polled project `55543850-b9f1-4dab-9d34-e65f732f030c` once per the
CLAUDE.md cadence rule. Status: COMPLETE (cycle 065 submission for
alternative `residual_bound_nonauto` / `deriv_diff_bound_nonauto`
proofs). Did **not** swap in — the cycle 065 manual proofs are
already validated by the cycle 066 build and consumed by the cycle
066 recurrence cluster, so a swap would be redundant churn.

### Step 1 — `globalError_per_step_sum_form_nonauto`

Inserted immediately after `globalError_recurrence_bound_textbook_nonauto`
(autonomous source: line 2542; new lemma at line 4772). Specialises
cycle 066's `globalError_recurrence_bound_textbook_nonauto` to
`Mmax := ∑_{j : Fin k} |ε(n − (j+1))|` (the sum of recent errors)
via a `Finset.single_le_sum` argument that bounds each summand by
the full sum. Verified `lake env lean OpenMath/Chapter4/Section404.lean`
exit-0 before proceeding.

### Step 2 — `globalError_recurrence_form_explicit_nonauto`

Inserted immediately after Step 1 (autonomous source: line 3249;
new lemma at line 4828). Mechanical 1:1 port of the autonomous
~430-line body with the eight strategy-prescribed substitutions:

1. `hL` → `hL_joint`
2. `hf_lip` → `hf_lip_joint`
3. `(fun _ y => f y)` → `f` (the `IsLMMSolution` shape)
4. Call to `globalError_per_step_sum_form` → `globalError_per_step_sum_form_nonauto`
5. `Cbase` definition: `L` → `L_joint`
6. `Dbase` definition: `L * M_bound` → `L_joint * (1 + M_bound)`
7. `hDbase_nn`: `hM` → `(by linarith : (0:ℝ) ≤ 1 + M_bound)`
8. `h_RHS_eq` rewrite: `L * M_bound` → `L_joint * (1 + M_bound)`

All other infrastructure — `theta`, `yPrime`, `linRec`,
`globalError_eq_linRec`, `globalError_closed_form`,
`sum_theta_psi_contraction`, `recentSum_swap_bound`, `aOf, bOf, cOf`,
the `n < k` vs `n ≥ k` case split, the `linarith`/`nlinarith`/`ring`
closes — port verbatim.

## Result

**SUCCESS.** Both new lemmas land. Build clean
(`lake env lean OpenMath/Chapter4/Section404.lean` exits 0 with only
pre-existing warnings; no new sorrys). Sorry count unchanged at 1
(the cycle 068 target at line 5398).

LOC delta: +474 (well under the strategy's 500-LOC ceiling).

## Faithfulness check

For `globalError_per_step_sum_form_nonauto`:
- Entity ID: not a Butcher entity; intermediate helper for §406D.
  The autonomous source at line 2542 is itself a non-Butcher
  helper, and this is the joint-Lipschitz lift.
- Lean statement captures: equivalent to the autonomous version
  under the shape lift `L ↦ L_joint`, `M_bound ↦ (1 + M_bound)`
  inherited from cycle 065's joint-Lipschitz hypothesis form.
- Tautology check: bound, not a hypothesis. ✓
- Identity check: substantive — the `Finset.single_le_sum`
  reduction is real work (specialises the cycle 066 textbook
  bound via a per-summand inequality). ✓
- Hypothesis strength check: matches cycle 066's
  `globalError_recurrence_bound_textbook_nonauto`. Joint-Lipschitz
  is the natural non-autonomous analogue of cycle 045's per-`x`
  `LipschitzWith`. ✓

For `globalError_recurrence_form_explicit_nonauto`:
- Entity ID: not a Butcher entity; analytical assembly for
  `thm:406D` (Butcher §406D, p. 347).
- Lean statement captures: same content as the autonomous version
  under `L ↦ L_joint`, `M_bound ↦ (1 + M_bound)`. The `aOf, bOf,
  cOf` returned bounds use `L_joint` and `(1 + M_bound)` in their
  scalar slots, exactly matching the autonomous shape with the
  joint-Lipschitz substitution.
- Tautology check: bound, not a hypothesis. ✓
- Identity check: substantive — bundles `globalError_closed_form`,
  `sum_theta_psi_contraction`, and `recentSum_swap_bound` into the
  `aOf, bOf, cOf` shape consumed by `discrete_gronwall_exp_bound`.
  ✓
- Hypothesis strength check: same hypotheses as the autonomous
  version, lifted via the cycle 065 joint-Lipschitz form. No
  hypothesis is stronger than required for the proof. ✓
- Absent theorem check: the cycle 068 closure is not promised
  inline; only as a strategy commitment in
  `.prover-state/issues/non_autonomous_lift_plan.md`. ✓

Definition-smuggling check: no new `def`/`structure` introduced,
only two new private lemmas. ✓

## Dead ends

None. Both ports went through on first attempt — build clean
after the initial Step 1 insertion and again after Step 2. The
strategy's substitution list was complete; no Mathlib gaps surfaced.

## Discovery

* The autonomous `globalError_recurrence_form_explicit` body
  (autonomous lines 3274–3683) is genuinely shape-agnostic in all
  its named sub-lemma calls except the explicit
  `globalError_per_step_sum_form` invocation. Once the per-step
  helper is lifted, the recurrence-form lift reduces to the eight
  textual substitutions above. This is a useful pattern for
  cycle 068's closure planning: identify the *unique* `f`-shape
  call site in each candidate lift, port the dependency first,
  then port the consumer.
* The cycle 065 `M_bound ↦ (1 + M_bound)` shape carries cleanly
  through the cycle 066 textbook-form helper into the cycle 067
  recurrence-form helper. The `aOf, bOf, cOf` definitions never
  needed parallel `_nonauto` versions — they are scalar in
  `L, M_bound` and the lift just feeds different scalars.
* `lake env lean OpenMath/Chapter4/Section404.lean` runtime is
  still well under the heartbeat ceiling at this file size; no
  decomposition needed for the heavy `_explicit_nonauto` body.

## Suggested next approach

Cycle 068 should close `LinearMultistepMethod.stable_consistent_isConvergent`
at line 5398. The full ingredient list is now:

1. `globalError_recurrence_form_explicit_nonauto` (cycle 067) — the
   `aOf, bOf, cOf` recurrence shape under joint-Lipschitz.
2. `discrete_gronwall_exp_bound` (cycle 050) — closed-form Grönwall.
3. Shape-agnostic squeeze helpers
   (`globalError_outer_squeeze_a_term`,
   `globalError_outer_squeeze_c_term`, `bOf_tendsto_at_zero`,
   `cOf_tendsto_at_zero`, `aOf_tendsto_zero`, `bOf_limit_pos`).
4. Cycle 063 boundary adapters
   (`lipschitzInSecond_univ_toLipschitzWith`, `f_yex_bound_on_Icc`,
   `hstart_shape_bridge`).

The remaining open question is whether a joint-Lipschitz adapter
(uncurried `f` from `LipschitzInSecond Set.univ L f` + joint
continuity) needs to be added to the cycle 063 set, since
`LipschitzInSecond` is spatial-only. Cycle 068's first step should
be to scope this — build the autonomous-form mirror call site and
inspect what hypothesis the helper chain consumes, then derive (or
strengthen the textbook hypothesis to) joint-Lipschitz on
`Function.uncurry f`. The autonomous closure
`stable_consistent_isConvergent_autonomous` (line 4779 in current
file, formerly :3863) is the template to mirror.

Estimated LOC: ~80 (per the original cycle 064 plan), or ~120 if a
new joint-Lipschitz adapter is needed.
