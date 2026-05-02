# Cycle 066 Results

## Worked on

§406D recurrence cluster non-autonomous lift (cluster 2 of the cycle
064–068 four-cluster lift plan). Lifted the five autonomous helpers
the strategy specified, plus a private decomposition helper required
by the recurrence-bound lift:

1. `T3_bound_nonauto` (trivial wrapper of cycle 065's
   `localTruncationError_bound_nonauto`).
2. `T1_bound_nonauto` (joint-Lipschitz pair bound collapsed at
   coinciding time argument).
3. `T2_bound_nonauto` (per-summand joint-Lipschitz pair bound
   collapsed at coinciding time argument).
4. `globalError_decomposition_nonauto` (private helper; mirror of the
   autonomous algebraic identity (406d) with `f t (yex t)`
   substitution. Required because the autonomous
   `globalError_decomposition` cannot be reused for non-autonomous
   `f` — its RHS bakes in autonomous `f (yex …)` applications which
   evaluate at distinct time arguments).
5. `LinearMultistepMethod.globalError_recurrence_bound_nonauto`
   (per-term bound; composes T1/T2/T3 + decomposition lift via
   abs_add_le triangle inequality).
6. `LinearMultistepMethod.globalError_recurrence_bound_textbook_nonauto`
   (textbook form; `(1 − h L_joint |β₀|)`-inversion mirroring the
   autonomous algebra).

## Approach

Followed the cycle 066 strategy closely:

1. **Step 1 — Aristotle status check.** Project
   `55543850-b9f1-4dab-9d34-e65f732f030c` was IN_PROGRESS at 1%.
   Per strategy, skipped without re-polling and proceeded to Step 2.
2. **Step 2 — bottom-up lift.** Implemented in the cycle 066 strategy
   order:
   - T3 (trivial, ~15 lines including docstring).
   - T1 (joint-Lipschitz collapsed via `joint_lipschitz_pair_bound`
     with `t₁ = t₂`, then `|t-t| = 0`; bound shape unchanged from
     autonomous with `L ↦ L_joint`).
   - T2 (per-summand T1 pattern; bound shape unchanged).
   - **Decision point reached on `globalError_decomposition`.**
     The strategy claimed `globalError_decomposition` was
     "non-autonomous-friendly via `IsLMMSolution h x₀ f Y`", but
     inspection at line 1094 confirmed it takes autonomous
     `f : ℝ → ℝ` and the RHS bakes in `f (yex …)` applications.
     A non-autonomous variant was required. Mirrored the autonomous
     proof structure verbatim (~85 LOC) substituting
     `f t (yex t)` for `f (yex t)` and adapting the
     `Fin.sum_univ_succ` β-sum unfolding to the non-autonomous
     `IsLMMSolution` shape. The strategy's "do not replace" rule
     was respected — the autonomous `globalError_decomposition`
     is preserved unchanged.
   - `globalError_recurrence_bound_nonauto` (~50 lines, mechanical
     composition mirroring the autonomous proof at line 1268).
   - `globalError_recurrence_bound_textbook_nonauto` (~95 lines,
     mechanical inversion mirroring the autonomous proof at line
     1331).
3. **Step 3 — pre-commit faithfulness check.** All six new lemmas
   pass the four checks (see Faithfulness check below).
   `lake env lean OpenMath/Chapter4/Section404.lean` exits 0; the
   single sorry at line 4928 (`stable_consistent_isConvergent`,
   cycle 068 target) is unchanged.
4. **Step 4 — cycle 067 Aristotle submission.** Skipped.
   Cycle 066 budget already at ~325 LOC; preparing a cycle 067
   self-contained Aristotle file would add another ~200 LOC of
   helper duplication. Defer to cycle 067 itself.
5. **Step 5 — task results + plan update + commit.** This file plus
   `.prover-state/issues/non_autonomous_lift_plan.md` cluster 2
   block updated to RESOLVED.

The cycle 066 hard-line (defer (4)+(5) if (1)+(2)+(3) > 150 lines)
was NOT triggered: T1+T2+T3 came in at ~80 LOC including docstrings,
leaving ample budget for (4)+(5) and the inserted `_decomposition_nonauto`
helper.

## Result

SUCCESS — all 6 deliverables landed (5 strategy targets + 1 private
decomposition helper required by item 5).

* Build: `lake env lean OpenMath/Chapter4/Section404.lean` exit 0.
* Sorrys: 1 (line 4928, `stable_consistent_isConvergent`, cycle 068
  target — unchanged from cycle 065).
* New code: ~325 lines total (slightly over the strategy's ~250-line
  ceiling, driven by the inserted `_decomposition_nonauto` helper
  the strategy did not anticipate). Still well under the cycle 060
  red-flag threshold (~430 lines).
* No new `axiom` / `constant` / raised `maxHeartbeats`.
* No autonomous helper modified. The cycle 044 chain (T1_bound,
  T2_bound, T3_bound, globalError_decomposition,
  globalError_recurrence_bound, globalError_recurrence_bound_textbook)
  at lines 1094, 1180, 1199, 1239, 1268, 1331 is preserved verbatim.

## Faithfulness check

### `T3_bound_nonauto` (helper 1)

* Entity ID: sub-lemma of §406D recurrence cluster (Butcher §406,
  p. 347); not directly named in the textbook.
* Textbook content: `T_3 = L(yex, x_n, h)`, bounded by `D h^2` via
  `lem:406B`.
* Lean statement captures: SAME content with `L · M_bound ↦
  L_joint · (1 + M_bound)`, inherited from cycle 065's
  `localTruncationError_bound_nonauto`. Faithful re-parameterisation.
* Tautology check: bound, not a hypothesis.
* Identity check: trivial wrapper of `localTruncationError_bound_nonauto`,
  same as autonomous T3_bound which wraps `localTruncationError_bound`.
  Real work delegated to the wrapped lemma (which itself decomposes
  into α/β-sum bounds via cycle 065's helpers).
* Hypothesis strength: joint-Lipschitz on `Function.uncurry f` is the
  natural non-autonomous analogue.

### `T1_bound_nonauto` (helper 2)

* Entity ID: sub-lemma of §406D recurrence cluster.
* Textbook content: `|h β_0 (f y_a − f y_b)| ≤ h L |β_0| · |y_a − y_b|`.
* Lean statement captures: SAME content with `L ↦ L_joint`. The
  bound shape does NOT pick up an `(1 + M_bound)` factor because the
  two `f`-applications evaluate at the *same* time argument
  `t = x₀ + n·h` (the current step time), so the joint-Lipschitz
  pair bound `|f t₁ y₁ − f t₂ y₂| ≤ L_joint · (|t₁−t₂| + |y₁−y₂|)`
  collapses (`|t-t|=0`) to the spatial-only bound. Faithful.
* Tautology check: bound, not a hypothesis.
* Identity check: substantive — joint-Lipschitz pair bound + abs_mul
  + mul_le_mul, mirroring the autonomous T1_bound proof.
* Hypothesis strength: joint-Lipschitz; same as helper 1.

### `T2_bound_nonauto` (helper 3)

* Entity ID: sub-lemma of §406D recurrence cluster.
* Textbook content: `|h Σ β_i (f y_{a,i} − f y_{b,i})| ≤
  h L Σ|β_i| · Mmax`.
* Lean statement captures: SAME content with `L ↦ L_joint`. Per
  summand, the two `f`-applications evaluate at the same time `t_i`
  (the `(n − i+1)`-th step time), so per-summand joint-Lipschitz
  collapses identically to T1's case. Faithful.
* Tautology check: bound, not a hypothesis.
* Identity check: substantive — `Finset.abs_sum_le_sum_abs` + per-
  summand T1-like bound, mirroring autonomous T2_bound.
* Hypothesis strength: joint-Lipschitz; same as helper 1.

### `globalError_decomposition_nonauto` (private helper)

* Entity ID: not a Butcher entity; the discrete analogue of (406d).
* Textbook content: `n_n − Σ α_i n_{n−i} = T_1 + T_2 + T_3` where
  the `T_i` are the f-difference and LTE terms (Butcher's algebraic
  identity (406d), p. 347).
* Lean statement captures: SAME content with `f y` replaced by `f t y`
  (autonomous to non-autonomous lift). The `IsLMMSolution h x₀ f Y`
  hypothesis takes the non-autonomous `f` directly (no `fun _ y => f y`
  wrapper). The `localTruncationError yex` term is unchanged
  (it uses `deriv yex` which equals `f t (yex t)` in non-autonomous
  form via `hyex_ode`).
* Tautology check: equality, not a hypothesis.
* Identity check: substantive — re-indexes `IsLMMSolution`, peels
  `i=0` from both sums, substitutes `deriv yex t = f t (yex t)`,
  then `linarith` to close. Mirrors autonomous proof structure
  verbatim.
* Hypothesis strength: takes the same `IsLMMSolution h x₀ f Y` shape
  the cycle 068 close needs; no extra hypothesis required.

### `LinearMultistepMethod.globalError_recurrence_bound_nonauto` (helper 4)

* Entity ID: `thm:406C` (Butcher §406, p. 347, partial form).
* Textbook quote (from `entities/thm_406C.json`):
  > "Let `n` denote the vector `n = y(x_n) − y_n`. Then for `h_0`
  > sufficiently small so that `h_0 |β_0| L < 1` and `h < h_0`,
  > there exist constants `C` and `D` such that
  >   `‖n − Σ α_i n_{−i}‖ ≤ C h max ‖n_{−i}‖ + D h^2`. (406c)"
* Lean statement captures: PARTIAL form (per-term, before the
  `(1 − h L |β_0|)` inversion that produces the textbook (406c) form).
  Bound shape matches the autonomous version with `L · M_bound ↦
  L_joint · (1 + M_bound)`. Faithful re-parameterisation.
* Tautology check: bound, not a hypothesis.
* Identity check: substantive — composes T1/T2/T3 via `abs_add_le`
  + `add_le_add` + `globalError_decomposition_nonauto`, mirroring
  the autonomous proof at line 1268.
* Hypothesis strength: joint Lipschitz; same as helpers 1–3.

### `LinearMultistepMethod.globalError_recurrence_bound_textbook_nonauto` (helper 5)

* Entity ID: `thm:406C` (Butcher §406, p. 347, textbook form).
* Lean statement captures: TEXTBOOK form; under the smallness
  hypothesis `h L_joint |β_0| < 1`, the per-term bound is absorbed
  via `(1 − h L_joint |β_0|)`-inversion. Bound shape matches
  autonomous with `L ↦ L_joint`, `M_bound ↦ (1 + M_bound)`.
  Faithful (the textbook is non-autonomous; this is the primary
  textbook form, with the autonomous variant being a specialisation).
* Tautology check: bound, not a hypothesis.
* Identity check: substantive — reverse-triangle `|n_n| ≤ B + A`,
  scale by `c`, `nlinarith` chain, divide by `(1−c)`. Mirrors the
  autonomous proof at line 1331.
* Hypothesis strength: joint Lipschitz + smallness; same as autonomous
  with `L ↦ L_joint`.

## Dead ends

None this cycle. The strategy's claim that `globalError_decomposition`
was "non-autonomous-friendly" was inaccurate (it takes autonomous
`f : ℝ → ℝ`), but the workaround (write a parallel
`_decomposition_nonauto` mirror) was straightforward and preserved
the autonomous variant per the strategy's "do not replace" rule.

## Discovery

* The autonomous algebraic decomposition (Butcher's (406d)) lifts
  near-mechanically to non-autonomous form: replace `f y` with
  `f t y` everywhere, adapt the `Fin.sum_univ_succ` β-sum unfolding
  to the non-autonomous `IsLMMSolution` (which already has `f t y`
  in its definition), and the `linarith [hYm]` close still goes
  through. No extra algebraic content is introduced; the lift is
  purely a re-indexing of which time arguments appear inside `f`.
* The cycle 065 strategy's "L · M ↦ L_joint · (1 + M_bound)" shape
  carries through cleanly: T1/T2 (single time arg per `f`-pair) keep
  the autonomous shape with `L ↦ L_joint`; T3 inherits the
  `(1 + M_bound)` factor from `localTruncationError_bound_nonauto`.
  The recurrence and textbook bounds compose these without further
  shape change.
* The cycle 066 strategy's claim about `globalError_decomposition`
  being non-autonomous-friendly should be reconciled: the issue plan
  notes it is *consumable* by the lifted recurrence chain provided a
  parallel `_nonauto` variant exists. Updating the issue plan with
  this clarification (cluster 2 RESOLVED) — see also cycle 068's
  remaining work.

## Suggested next approach

For cycle 067 (cluster 3, squeeze helpers):

1. The cluster is `globalError_outer_squeeze_a_term`,
   `globalError_outer_squeeze_c_term`, plus the four Tendsto-wrapper
   helpers `bOf_tendsto_at_zero`, `cOf_tendsto_at_zero`,
   `aOf_tendsto_zero`, `bOf_limit_pos`. ~100 lines per the cycle
   064 plan estimate.
2. These helpers are *pure ℝ-analysis squeeze arguments* that do not
   depend on the `f`-shape. The autonomous versions (lines ~2311,
   ~2383, ~2554, ~3225, ~3262, ~3708) accept `f : ℝ → ℝ` only because
   they consume the autonomous `globalError_recurrence_form_explicit`
   chain. The cycle 067 lift requires:
   - Either parametrising them by the lifted recurrence form (clean
     but requires `globalError_recurrence_form_explicit_nonauto`
     to land first, ~100 LOC), or
   - Inlining the closed-form Grönwall closure for the non-autonomous
     case (compact, ~80 LOC, but couples with cycle 068's close).
   Cycle 067 should follow whichever path the strategy author
   prefers.
3. **Aristotle: check the cycle 065 submission first** at the start
   of cycle 067 (project ID
   `55543850-b9f1-4dab-9d34-e65f732f030c`). Per CLAUDE.md cadence,
   one check is enough; if IN_PROGRESS, skip and proceed.

For cycle 068 (close `stable_consistent_isConvergent`, ~80 lines):

1. The current sorry at line 4928 takes `f` as `LipschitzInSecond`
   (cycle 063 adapter form). The cycle 068 close needs to:
   - Convert `LipschitzInSecond Set.univ L f` to joint-Lipschitz on
     `Function.uncurry f`. This may require an additional adapter
     (joint-Lipschitz from per-`x` Lipschitz + `f` continuous on
     a compact); not in the cycle 063 adapter set.
   - Apply the cycle 067 squeeze cluster to derive the convergence.
   - Use cycle 063's `hstart_shape_bridge` to convert the textbook
     `start h i → y₀` shape to the per-`h` form.
2. The cycle 068 cluster is ~80 lines per the cycle 064 plan but
   may grow if the joint-Lipschitz adapter is non-trivial.

## Aristotle status (Step 1)

Project `55543850-b9f1-4dab-9d34-e65f732f030c` (cycle 065 alternative
proof attempt for `residual_bound_nonauto` and
`deriv_diff_bound_nonauto`): IN_PROGRESS at 1% complete (created
2026-05-02 04:48 UTC, last updated 2026-05-02 05:00 UTC).
Per CLAUDE.md cadence, no further polling this cycle. Cycle 067
should check at start.

## Code metrics

* Lines added: ~325 (5 strategy targets + 1 private decomposition
  helper + section header). Marginally over the strategy's 250-line
  ceiling but driven by the unanticipated decomposition lift.
* Lines modified in autonomous helpers: 0.
* `axiom`/`constant` introduced: 0.
* `maxHeartbeats` raised: no.
* New theorems with `sorry`: 0.
