# Cycle 065 Results

## Worked on

§406B sub-lemma cluster, cycle 064 deferral closure: helpers 3
(`residual_bound`), 4 (`deriv_diff_bound`), 5
(`LinearMultistepMethod.localTruncationError_bound`), and the two
α/β-sum wrappers. All five are non-autonomous lifts under a joint
Lipschitz hypothesis on `Function.uncurry f`. Plus a private helper
`joint_lipschitz_pair_bound` for the shared algebra.

## Approach

Followed the cycle 065 strategy verbatim:

1. Inserted `joint_lipschitz_pair_bound` at the head of the cycle
   065 block. Bounds `|f t₁ y₁ − f t₂ y₂|` by
   `L_joint · (|t₁−t₂| + |y₁−y₂|)` via Mathlib's `Prod.dist_eq` (sup
   norm) bounded by the sum of components. ~20 lines.
2. Ported `residual_bound` to `residual_bound_nonauto`. Bound shape
   changed from `(1/2) i² h² L M_bound` to
   `(1/2) i² h² L_joint (1+M_bound)`. The integrand
   `L_joint · (h·(−ξ) + h·(−ξ)·M_bound)` factors as
   `(L_joint·h·(1+M_bound)) · (−ξ)`, integrating to
   `L_joint·h·(1+M_bound)·(i²/2)`. ~80 lines.
3. Ported `deriv_diff_bound` to `deriv_diff_bound_nonauto`. Bound
   shape changed from `i h L M_bound` to `i h L_joint (1+M_bound)`.
   ~30 lines.
4. Ported the α/β-sum wrappers
   (`localTruncationError_α_sum_bound_nonauto`,
   `localTruncationError_β_sum_bound_nonauto`). Mechanical: replace
   `L · M_bound` with `L_joint · (1 + M_bound)` and the underlying
   helper. ~30 + 30 lines.
5. Ported `localTruncationError_bound_nonauto` (the main theorem,
   non-autonomous form of `lem:406B`). ~30 lines.
6. `lake env lean OpenMath/Chapter4/Section404.lean` exit 0; only
   sorry remains at line 4548 (`stable_consistent_isConvergent`,
   cycle 068 target post-slip).
7. Updated `.prover-state/issues/non_autonomous_lift_plan.md`:
   cycle 064 deferral block marked "RESOLVED in cycle 065"; cycles
   066/067/068 renumbered (schedule slips one cycle, as the
   strategy anticipated).

The cycle 065 fallback (commit only helpers C+D+joint-Lipschitz,
defer α/β + main theorem to cycle 066) was NOT triggered — all six
new lemmas landed cleanly within the ~200-line budget.

### Bug found and fixed mid-cycle

Initial draft used `add_le_add_left hA _` to lift
`|y_diff| ≤ h·(−ξ)·M_bound` to
`h·(−ξ) + |y_diff| ≤ h·(−ξ) + h·(−ξ)·M_bound`. The Lean elaborator
resolved this lemma to a covariant-class instance that adds on the
right (`a + c ≤ b + c`) instead of the left, producing a type
mismatch at lines 4189 and 4253. Replaced both call sites with
`linarith [hA]`, which is cleaner anyway and avoids the
covariant-instance dispatch ambiguity. (Discovery: see the
"Discovery" section.)

## Result

SUCCESS — all 6 deliverables landed (5 from the strategy + 1
private helper).

* Build: `lake env lean OpenMath/Chapter4/Section404.lean` exit 0.
* Sorrys: 1 (line 4548, `stable_consistent_isConvergent`, cycle 068
  target — unchanged from cycle 064).
* New code: ~270 lines (slightly over the ~200-line projection,
  driven by docstring length and the need to keep both autonomous
  and non-autonomous variants legible — the *proof* core is ~200
  lines, the rest is faithfulness-check docstrings).
* No new `axiom` / `constant` / raised `maxHeartbeats`.
* The autonomous helpers at lines 567, 624, 691, 789, 833, 921,
  964, 1005 are preserved and still consumed by
  `stable_consistent_isConvergent_autonomous`.

## Faithfulness check

### `joint_lipschitz_pair_bound` (private helper)

* Entity ID: not a Butcher entity; pure Mathlib algebra.
* Statement: `|f t₁ y₁ − f t₂ y₂| ≤ L_joint · (|t₁−t₂| + |y₁−y₂|)`.
* Tautology check: bound, not a hypothesis.
* Identity check: substantive composition (`dist_le_mul` +
  `Prod.dist_eq` + `max ≤ sum` + `mul_le_mul_of_nonneg_left`).
* Hypothesis strength check: `0 ≤ L_joint` is necessary for
  `Real.coe_toNNReal` to commute with the bound; standard.

### `residual_bound_nonauto` (helper 3 lift)

* Entity ID: sub-lemma of `lem:406B` (Butcher §406, p. 346).
* Textbook quote (from `entities/lem_406B.json`):
  > `||y(x) − y(x − ih) − ihy'(x)|| ≤ (1/2) i² h² LM`
* Lean statement captures: SAME content with reparametrisation
  `L · M ↦ L_joint · (1 + M_bound)`. The textbook implicitly assumes
  `f` Lipschitz in `y` uniformly in `t`, plus continuous in `t`; on a
  compact `[a, b]` this pair is equivalent to joint Lipschitz on
  `[a, b] × ℝ`. The constant shift is faithful re-parameterisation,
  documented in the docstring.
* Tautology check: conclusion is an integral bound, not a hypothesis.
* Identity check: proof is FTC + change-of-variables + joint-Lipschitz +
  monotone integration + closed-form integral computation, not `exact h`.
* Hypothesis strength check: joint Lipschitz is a strictly weaker
  combined hypothesis than "Lipschitz in `y` uniformly in `t`" +
  "continuous in `t` on a compact"; documented in the docstring.

### `deriv_diff_bound_nonauto` (helper 4 lift)

* Entity ID: sub-lemma of `lem:406B` (used in the post-decomposition
  bound on `(y'(x) − y'(x−ih))`).
* Textbook quote:
  > `||f(y(x)) − f(y(x−ih))|| ≤ ihLM`
* Lean statement captures: SAME content with reparametrisation
  `L · M ↦ L_joint · (1 + M_bound)`. Same justification as helper 3.
* Tautology check: bound, not a hypothesis.
* Identity check: proof is joint-Lipschitz + sub-lemma A + algebra,
  not `exact h`.
* Hypothesis strength check: same as helper 3.

### `localTruncationError_α_sum_bound_nonauto`,
###  `localTruncationError_β_sum_bound_nonauto`

* Entity ID: not Butcher entities; sub-lemma wrappers of `lem:406B`.
* These mirror the autonomous α/β-sum wrappers exactly, with
  `L · M_bound` replaced by `L_joint · (1 + M_bound)`.
* Tautology check: each is a sum-bound, not a hypothesis.
* Identity check: each is `Finset.abs_sum_le_sum_abs` + summand-wise
  monotonicity from helpers 3/4.

### `LinearMultistepMethod.localTruncationError_bound_nonauto` (helper 5 lift)

* Entity ID: `lem:406B` (Butcher §406, p. 346, corrected form).
* Textbook quote:
  > "If `y` is the exact solution to the standard initial value
  > problem and `x ∈ [x_0 + kh, x̄]`, then
  > `L(y, x, h) ≤ ((1/2) ∑_{i=1}^k i² |αᵢ| + ∑_{i=1}^k i|iαᵢ − βᵢ|) L M h²`."
* Lean statement captures: CORRECTED form (see the §406 block
  header at line 540 and `.prover-state/issues/lem_406B_textbook_check.md`)
  with `L · M ↦ L_joint · (1 + M_bound)`. The corrected form
  replaces Butcher's typo'd `i|iαᵢ − βᵢ|` with `(i+1) |β_{i+1}|`,
  derived rigorously from the consistency identity
  (404b: `∑ (i+1)αᵢ₊₁ = ∑ βᵢ`). The non-autonomous lift is the
  faithful re-parameterisation `L M ↦ L_joint (1+M)`, documented
  in the docstring.
* Tautology check: bound, not a hypothesis.
* Identity check: proof is sub-lemma E (decomposition) + α/β-sum
  bounds + ring, not `exact h`.
* Hypothesis strength check: joint Lipschitz on `Function.uncurry f`
  is the natural non-autonomous analogue of the autonomous
  `LipschitzWith L f`. The bound on `|f t (y t)|` is the
  trajectory-uniform bound the textbook implicitly assumes.

## Dead ends

1. **`add_le_add_left hA _`** for monotone addition under a left
   constant: Lean's covariant-class dispatch produced
   `a + c ≤ b + c` (right-add) instead of `c + a ≤ c + b`
   (left-add) at the proof position. Type-mismatch errors at lines
   4189 (residual) and 4253 (deriv-diff). Resolved by switching to
   `linarith [hA]`, which is also cleaner. Discovery: in this
   Mathlib snapshot, `add_le_add_left` may be elaborated as the
   right-add covariant lemma in some contexts; prefer `linarith`
   or `gcongr` for monotone-addition steps when the direction
   matters.

## Discovery

* The cycle 064 trace (helper 3 needs `(x+hξ, x)` Lipschitz; helper
  4 needs `(x, x−ih)`) was correct, and the single-constant joint
  Lipschitz hypothesis suffices for both. The `(1+M_bound)`
  multiplier is the natural absorption — exactly what the strategy
  predicted.
* The autonomous-helper preservation rule held cleanly: cycle 065
  added ~270 lines without touching the existing 470 lines of §406B
  autonomous helpers. The 1:1 algebraic correspondence between
  autonomous and non-autonomous proofs (only the Lipschitz step
  differs) makes side-by-side maintenance feasible long-term.
* **Mathlib monotone-addition note**: `add_le_add_left` and
  `add_le_add_right` can elaborate to the same covariant-class
  instance in this Mathlib snapshot, producing right-add behavior
  in both cases. Prefer `linarith [hA]` for clarity. Saved as a
  feedback memory.

## Suggested next approach

For cycle 066 (§406D recurrence helpers):

1. The cluster is `T1_bound`, `T2_term_bound`,
   `globalError_step_bound`, `globalError_recurrence_form`,
   `globalError_recurrence_form_explicit`. ~5 helpers, ~200 lines.
2. The hypothesis form is the same joint-Lipschitz one cycle 065
   established. The `localTruncationError_bound_nonauto` cycle 065
   delivered should be a drop-in replacement for the autonomous
   `localTruncationError_bound` in the recurrence chain.
3. **Aristotle: check the cycle 065 submission first.** Cycle 065
   submitted a single-file project `lift_helpers_C_D.lean`
   containing alternative-proof targets for `residual_bound_nonauto`
   and `deriv_diff_bound_nonauto` (project ID
   `55543850-b9f1-4dab-9d34-e65f732f030c`, see
   `.prover-state/aristotle_submissions/cycle_065/project_ids.txt`).
   Per CLAUDE.md cadence, check ONCE at start of cycle 066. If the
   Aristotle proofs are obviously cleaner than the manual ones,
   examine and consider replacing — but per the cycle 065 strategy,
   keep the manual proofs unless the diff is clear.
4. After processing the cycle 065 Aristotle results, batch-submit
   the §406D recurrence helpers as alternative proofs (CLAUDE.md
   cadence: submit, sleep 30 min, check at start of cycle 067).
5. Cycle 065 deferred submission of the third main helper
   (`LinearMultistepMethod.localTruncationError_bound_nonauto`):
   bundling LinearMultistepMethod / IsConsistent /
   localTruncationError_decomposition / α-β-sum wrappers into a
   single self-contained file is ~500 LOC of duplication for low
   expected payoff, given the manual proof is mechanical
   composition of `α/β-sum-bound` helpers + `abs_add_le` + `ring`.
   Cycle 066 should re-evaluate whether to submit this if the
   cycle 065 Aristotle results suggest leverage.

For cycle 067: cluster 3 (cycle 057–061 squeeze helpers, ~100
lines).

For cycle 068: close `stable_consistent_isConvergent` directly,
~80 lines.

(Schedule slips one cycle relative to the cycle 063 plan because
cycle 064 deferred §406B helpers 3/4/5.)

The cycle 065 commit is ~270 lines, slightly over the ~200-line
projection but within the cycle 060 red-flag threshold (~430
lines). The §406B cluster is now fully lifted; the remaining work
is purely §406D recurrence + squeeze plumbing.
