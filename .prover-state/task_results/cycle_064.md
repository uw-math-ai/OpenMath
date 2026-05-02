# Cycle 064 Results

## Worked on

§406B sub-lemma cluster, non-autonomous lift to `f : ℝ → ℝ → ℝ`. The
strategy named 5 helpers (1:1 ports of `exact_solution_norm_bound`,
`residual_integral_form`, `residual_bound`, `deriv_diff_bound`,
`localTruncationError_bound`). Helpers 1 and 2 landed; helpers 3, 4, 5
deferred to cycle 065 per the strategy's decision protocol.

## Approach

1. Read the autonomous helpers at lines 567–1033 of
   `OpenMath/Chapter4/Section404.lean`.
2. Traced the time arguments through every Lipschitz invocation in
   helpers 3, 4, 5 (decision step in the strategy):
   * `residual_bound` (line 741–748): applies `hf_lip` to
     `f (y(x+hξ))` vs `f (y x)`. Non-autonomously: time args are
     `x+hξ` vs `x` — DIFFERENT.
   * `deriv_diff_bound` (line 802–808): applies `hf_lip` to `f (y x)`
     vs `f (y(x-ih))`. Non-autonomously: time args are `x` vs `x-ih`
     — DIFFERENT.
   * `localTruncationError_bound` (line 1005) is the integration of
     helpers 3 and 4, so inherits the issue.
3. Per the strategy's decision protocol §3 (and CLAUDE.md
   pre-commit faithfulness check on hypothesis strength): defer
   helpers 3/4/5 to cycle 065 under a joint-Lipschitz hypothesis on
   `Function.uncurry f`, applied uniformly across the three.
4. Ported helpers 1 (`exact_solution_norm_bound`) and 2
   (`residual_integral_form`) by replacing every `f (y t)` with
   `f t (y t)`. The FTC and change-of-variables arguments are
   identical; only the integrand identity changed.
5. Verified `lake env lean OpenMath/Chapter4/Section404.lean` exits
   cleanly with the only `sorry` remaining at the line-4254
   `stable_consistent_isConvergent` (cycle 067 target). The
   `unused variable` warnings at lines 3969 and 4030 mirror the
   autonomous versions at lines 568 and 627, confirming the
   1:1-faithful lift.
6. Updated `.prover-state/issues/non_autonomous_lift_plan.md` with
   the cycle 064 status and the cycle 065 joint-Lipschitz plan.

## Result

SUCCESS — minimum deliverable met. Helpers 1 and 2 land as
`exact_solution_norm_bound_nonauto` and `residual_integral_form_nonauto`,
inserted as `private lemma`s immediately after the cycle 063 adapter
block and before the cycle 062 autonomous theorem. Helpers 3/4/5
deferred to cycle 065 with a written justification (joint-Lipschitz
required, traced from autonomous proofs).

* Build: `lake env lean OpenMath/Chapter4/Section404.lean` exit 0.
* Sorrys: 1 (line 4254, `stable_consistent_isConvergent`, cycle 067
  target — unchanged from cycle 063).
* New code: ~140 lines (under the 200-line cap from cycle 060's
  lesson).
* No new `axiom` / `constant` / raised `maxHeartbeats`.
* The autonomous helpers at lines 567, 624, 692, 790, 923, 1005 are
  preserved and still consumed by
  `stable_consistent_isConvergent_autonomous`.

## Faithfulness check

### `exact_solution_norm_bound_nonauto` (helper 1)

* Entity ID: not a Butcher-named lemma (it is a sub-lemma of
  `lem:406B`, see the §406 block header at line 540 of the autonomous
  file). Same status as the autonomous `exact_solution_norm_bound`.
* Textbook role: pointwise bound `|y(x+hξ) − y x| ≤ h|ξ|·M_bound`
  on the exact solution under `y' = f` and `‖f∘y‖ ≤ M_bound`.
* Lean statement captures: same content as autonomous version, with
  `f (y t)` → `f t (y t)` (the textbook IVP `y' = f(t, y)` shape).
* Tautology check: conclusion `|y(x+hξ) − y x| ≤ h(-ξ)M_bound` is a
  bound, not a hypothesis.
* Identity check: proof is FTC + `norm_integral_le_…`, not `exact h`.
* Hypothesis strength: `hy_C1` (C¹) matches the autonomous version's
  faithfulness note (textbook implicitly requires C¹ for FTC); no
  strengthening relative to the autonomous helper.

### `residual_integral_form_nonauto` (helper 2)

* Entity ID: not a Butcher-named lemma (sub-lemma of `lem:406B`).
* Textbook role: integral form for the residual `y(x) − y(x−ih) − ih·y'(x)`.
* Lean statement captures: same content as autonomous version, with
  `f (y t)` → `f t (y t)` and integrand `f (y(x+hξ)) − f (y x)` →
  `f (x+hξ) (y(x+hξ)) − f x (y x)`.
* Tautology check: conclusion is an algebraic identity, not a
  hypothesis.
* Identity check: proof is FTC + change of variables (`smul_integral_comp_mul_add`),
  not `exact h`.
* Hypothesis strength: identical hypotheses to the autonomous
  version (with `f (y t) → f t (y t)`); no strengthening.

## Dead ends

None this cycle — the trace step in the strategy preempted the
joint-Lipschitz issue, so no time was wasted attempting to land
helpers 3/4/5 with a `LipschitzInSecond` hypothesis that cannot
bound time-shifted residuals.

## Discovery

* The §406B helpers split cleanly along the FTC-vs-Lipschitz
  boundary: helpers 1, 2 are pure FTC and lift 1:1; helpers 3, 4, 5
  invoke Lipschitz with time-shifted arguments and need joint
  Lipschitz on `Function.uncurry f`. This split was anticipated in
  the cycle 064 strategy but not pre-committed; cycle 064's trace
  confirmed it cleanly.
* The autonomous-helper preservation (per the strategy's
  "do NOT delete or rename" rule) means cycle 064 introduces ~140
  new lines without touching the existing 470 lines of §406B
  autonomous helpers; the autonomous-IVP form remains the cleaner
  proof of `stable_consistent_isConvergent_autonomous` and stays
  the cycle 062 deliverable.
* No Aristotle batch was submitted this cycle: the strategy gates
  Aristotle on helpers 3/4/5 deferral; per the deferral, the
  joint-Lipschitz hypothesis form must first be designed
  (cycle 065's first deliverable) before submitting helpers 3/4/5.
  Submitting them with the wrong hypothesis form would waste
  Aristotle compute and produce sorry-able-but-not-merge-able
  proofs.

## Suggested next approach

For cycle 065 (joint-Lipschitz §406B helpers):

1. Decide the joint-Lipschitz form. Two options:
   * `(hf_lip_joint : LipschitzWith L_joint.toNNReal (Function.uncurry f))`
     — single constant, simplest.
   * `(hf_lip_t : LipschitzWith L_t.toNNReal (fun t => f t y₀))` and
     `(hf_lip_y : LipschitzInSecond Set.univ L_y f)` — separate
     spatial and temporal constants, finer but algebraically
     heavier.
   The single-constant form is recommended; the §406B bounds will
   absorb the sub-optimality into the leading constant of the
   final `D` in `lem:406B`.
2. Port `residual_bound` with the joint-Lipschitz hypothesis. The
   key replacement: `|f (y(x+hξ)) − f (y x)| ≤ L · |y(x+hξ) − y x|`
   becomes
   `|f (x+hξ) (y(x+hξ)) − f x (y x)| ≤ L_joint · ‖((x+hξ, y(x+hξ)) − (x, y x))‖`.
   Bound the L²/L∞ pair-norm by the sum of the time-shift `|hξ|` and
   the spatial-shift `|y(x+hξ) − y x|`. The latter is bounded by
   helper 1 (`exact_solution_norm_bound_nonauto`).
3. Port `deriv_diff_bound` similarly: the time shift is `i*h`.
4. Port `localTruncationError_bound` to use the new `_α_sum_bound_nonauto`
   and `_β_sum_bound_nonauto` helpers built on top of helpers 3, 4.
   The final bound will pick up extra `h` factors from the time-shift
   absorbed into `L_joint`; the formula reduces to the autonomous
   form when `L_joint` is chosen as `max(0, L_y)`.
5. Aristotle batch: submit `residual_bound_nonauto`,
   `deriv_diff_bound_nonauto`, `localTruncationError_bound_nonauto`
   as a single project. CLAUDE.md cadence: submit, sleep 30 min,
   check at the start of cycle 066.
6. Verify the autonomous helpers still compile (they should — they
   are not touched).

For cycle 066: cluster 3 (cycle 057–061 squeeze helpers).
For cycle 067: close `stable_consistent_isConvergent` directly.

The cycle 064 commit is small (~140 lines), in line with the
cycle 060 lesson and matching the cycle 061/062 cadence. Cycle 065
will be ~200 lines, the upper end of the §406B cluster's budget.
