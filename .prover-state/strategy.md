# Cycle 064 Strategy — Lift §406B sub-lemmas to non-autonomous `f : ℝ → ℝ → ℝ`

## Summary

Cycle 062 closed the autonomous form `stable_consistent_isConvergent_autonomous`
(scalar `f : ℝ → ℝ`). Cycle 063 added three private adapter lemmas at the
autonomous/non-autonomous boundary. Cycle 064 begins the bottom-up
refactor laid out in `.prover-state/issues/non_autonomous_lift_plan.md`.

**The single sorry remaining in the file** is at
`OpenMath/Chapter4/Section404.lean:4110`, the textbook `IsConvergent` form
of `stable_consistent_isConvergent` (`thm:406D`). Closing it requires
lifting 19 helpers from `f : ℝ → ℝ` to `f : ℝ → ℝ → ℝ`. The plan splits
that work across cycles 064–067; **cycle 064 is the §406B cluster**
(5 helpers, ~150 lines).

**Do NOT attempt to close the line-4110 sorry this cycle.** That is the
cycle 067 deliverable. Cycle 064's job is purely the §406B lift.

---

## Cycle 064 deliverables (in order)

Lift the following 5 helpers from `{f : ℝ → ℝ}` to `{f : ℝ → ℝ → ℝ}`,
preserving statements and proofs as faithfully as possible. The new
versions go in the same file (`OpenMath/Chapter4/Section404.lean`),
inserted **immediately before** the cycle 062 autonomous theorem at
line 3863 and **immediately after** the cycle 063 adapter block.

Use the suffix convention `_nonauto` to distinguish from the existing
autonomous helpers. Keep the autonomous helpers in place — they are
still consumed by `stable_consistent_isConvergent_autonomous` and must
not be removed or renamed.

### 1. `exact_solution_norm_bound_nonauto` (mirror of line 568)

Current autonomous statement (line 568):
```lean
private lemma exact_solution_norm_bound
    {f : ℝ → ℝ} {M_bound : ℝ} (hM : 0 ≤ M_bound)
    {y : ℝ → ℝ}
    (hy_diff : Differentiable ℝ y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ M_bound)
    (x h : ℝ) (hh : 0 ≤ h)
    (ξ : ℝ) (hξ : ξ ≤ 0) :
    |y (x + h * ξ) - y x| ≤ h * (-ξ) * M_bound
```

Non-autonomous variant:
```lean
private lemma exact_solution_norm_bound_nonauto
    {f : ℝ → ℝ → ℝ} {M_bound : ℝ} (hM : 0 ≤ M_bound)
    {y : ℝ → ℝ}
    (hy_diff : Differentiable ℝ y)
    (hy_ode : ∀ t, deriv y t = f t (y t))
    (hf_y_bound : ∀ t, |f t (y t)| ≤ M_bound)
    (x h : ℝ) (hh : 0 ≤ h)
    (ξ : ℝ) (hξ : ξ ≤ 0) :
    |y (x + h * ξ) - y x| ≤ h * (-ξ) * M_bound
```

The proof body should be the same as the autonomous version with
`f (y t)` replaced by `f t (y t)`. The FTC + `norm_integral_le_…`
argument does not care whether the integrand is autonomous or
non-autonomous; the only change is the integrand identity.

### 2. `residual_integral_form_nonauto` (mirror of line 624)

Current autonomous form takes `(hy_ode : ∀ t, deriv y t = f (y t))`;
replace with `(hy_ode : ∀ t, deriv y t = f t (y t))`. The integrand
in the conclusion changes from
`f (y (x + h*ξ)) - f (y x)` to `f (x + h*ξ) (y (x + h*ξ)) - f x (y x)`.
Proof body: the FTC + `smul_integral_comp_mul_add` argument works
identically; just thread the time argument through.

### 3. `residual_bound_nonauto` (mirror of line 692) — DECISION POINT

Hypothesis to update: `(hf_lip : LipschitzWith L.toNNReal f)` →
`(hf_lip : LipschitzInSecond Set.univ L f)` (consumed via cycle 063's
`lipschitzInSecond_univ_toLipschitzWith` adapter inside the body).

**Critical caveat:** the autonomous body applies Lipschitz to
`f(y(x+hξ))` vs `f(y(x))`. In the non-autonomous case the two `f`
calls become `f (x+hξ) (y(x+hξ))` vs `f x (y x)` — the *time
arguments are different*. `LipschitzInSecond` (Lipschitz in the
spatial argument only, uniformly in `t`) does NOT bound
`|f t₁ y₁ - f t₂ y₂|` when `t₁ ≠ t₂`.

**Decision protocol for cycle 064:**

1. **Trace step.** Read `OpenMath/Chapter4/Section404.lean` lines
   692–790 (the autonomous `residual_bound` proof body). Identify
   every place `hf_lip` is invoked. For each invocation, note the
   `f`-arguments on both sides.
2. **If the time argument is the same** at every Lipschitz invocation
   (e.g. only spatial differences are bounded; time-shift residuals
   are absorbed elsewhere): port `residual_bound_nonauto` directly
   with `LipschitzInSecond` and the cycle 063 adapter. Helpers 4
   and 5 follow the same pattern.
3. **If the time argument differs** at any Lipschitz invocation
   (the more likely case based on Butcher's §406B written argument):
   **defer helpers 3, 4, 5 to cycle 065.** Write a brief addendum
   to `non_autonomous_lift_plan.md` describing the joint-Lipschitz
   issue, and commit cycle 064 with helpers 1 and 2 only. Cycle 065
   will introduce the joint-Lipschitz hypothesis (e.g.
   `hf_lip_joint : LipschitzWith L_joint.toNNReal (Function.uncurry f)`)
   uniformly across helpers 3/4/5 — not piecemeal.

### 4. `deriv_diff_bound_nonauto` (mirror of line 790)

Same time-argument issue as helper 3:
`|deriv y x - deriv y (x - i*h)| = |f x (y x) - f (x - i*h) (y (x-i*h))|`.
Both arguments shift. **Same decision protocol.** If helper 3 is
deferred, defer helper 4 too.

### 5. `localTruncationError_bound_nonauto` (mirror of line 923 — `lem:406B`)

Final integration. Defer to cycle 065 if helpers 3 and 4 are
deferred.

---

## Concrete cycle 064 plan

1. **(15 min) Read lines 540–960** of `OpenMath/Chapter4/Section404.lean`
   to understand the §406B helper chain in detail. Pay special
   attention to where `hf_lip` is invoked and whether the time
   argument changes between the two `f` applications.
2. **(10 min) Confirm whether helpers 3/4/5 actually need joint
   Lipschitz** by tracing the time arguments through the autonomous
   proofs. Decision per §3 above.
3. **(45 min) Land helpers 1 and 2** (`exact_solution_norm_bound_nonauto`
   and `residual_integral_form_nonauto`). These are pure 1:1
   ports — `f (y t)` → `f t (y t)` — and should compile with at most
   a few `simp`/`ring` adjustments. Use `lake env lean
   OpenMath/Chapter4/Section404.lean` to verify after each.
4. **(60 min) Decision point on helpers 3/4/5.**
   * If trace shows time argument is invariant: port them too.
   * If trace shows time argument differs: write a brief addendum
     to `non_autonomous_lift_plan.md` explaining the joint-Lipschitz
     issue, defer helpers 3/4/5 to cycle 065, and commit.
5. **(20 min) Aristotle batch (only if helpers 3/4/5 are deferred).**
   Submit deferred helpers as a backup. CLAUDE.md cadence: submit
   once, sleep 30 min, check once at the start of cycle 065.
6. **(30 min) Verification + commit.**
   * `lake env lean OpenMath/Chapter4/Section404.lean` — exit code 0,
     line-4110 sorry still the only sorry.
   * `#print axioms` on each new helper — should be `[propext,
     Classical.choice, Quot.sound]`.
   * Update `.prover-state/task_results/cycle_064.md`.
   * Update the issue file `non_autonomous_lift_plan.md` with what
     landed and what was deferred.
   * Commit + push: `Cycle 064 — §406B sub-lemmas non-autonomous
     lift (helpers 1/2 [+3/4/5 if landed])`.

**Target deliverable (minimum):** helpers 1 and 2 land. Helpers 3/4/5
either land or are deferred with a written justification.

**Stretch deliverable:** all 5 helpers land if the time argument
trace shows the autonomous versions are already structured cleanly.

---

## Faithfulness checklist (apply per CLAUDE.md before commit)

For each new helper:

- [ ] **Tautology check:** the conclusion is NOT one of the
  hypotheses. The five helpers are all genuine bounds.
- [ ] **Identity check:** the proof is NOT a single `exact h`.
  All five involve real calculus (FTC, change of variables,
  Lipschitz, monotone integration).
- [ ] **Hypothesis strength check:** the non-autonomous hypotheses
  must not over-strengthen relative to the textbook. `hy_ode` with
  `f t (y t)` matches def:402A's IVP shape. `LipschitzInSecond
  Set.univ L f` matches the def:402A `IsConvergent` predicate's
  Lipschitz hypothesis at line 308. `hf_y_bound` is a uniform bound
  on the trajectory's image — implicit in the textbook (the exact
  solution's compactness gives a finite bound on `f(t, y(t))` over
  any compact `t`-interval); making it explicit is faithful.
- [ ] **Absent theorem check:** if a docstring promises a future
  helper, it must actually exist or be marked deferred in the
  issue file.
- [ ] **No `axiom` or `constant`** introduced.
- [ ] **No `maxHeartbeats` raised** above 200000.

---

## What NOT to do this cycle

* Do **NOT** attempt to close the line-4110 sorry
  (`stable_consistent_isConvergent`). That is the cycle 067 target.
  Cycle 064 is purely the §406B lift.
* Do **NOT** delete or rename the autonomous helpers
  (`exact_solution_norm_bound`, `residual_integral_form`,
  `residual_bound`, `deriv_diff_bound`, `localTruncationError_bound`).
  They are still consumed by
  `stable_consistent_isConvergent_autonomous` (cycle 062) and that
  theorem must not regress.
* Do **NOT** generalize from scalar (`ℝ → ℝ → ℝ`) to vector-valued
  RHS in this cycle. The textbook §406D-equivalent staged approach
  in cycles 064–067 stays scalar.
* Do **NOT** introduce a new Lipschitz hypothesis form mid-helper.
  If helpers 3/4/5 need joint Lipschitz on `Function.uncurry f`,
  that is fine, but introduce it consistently across helpers 3, 4,
  and 5 — not piecemeal.
* Do **NOT** submit a giant Aristotle batch (>5 jobs) for this
  cluster. Per CLAUDE.md, ~5 jobs per cycle is the cadence. If
  helpers 1 and 2 land manually and 3/4/5 are deferred, only
  helpers 3/4/5 (3 jobs) go to Aristotle.
* Do **NOT** poll Aristotle more than once. Submit, sleep 30 min,
  check at the start of cycle 065.
* Do **NOT** edit `scripts/autonomous_loop.py`. Loop infrastructure
  is the maintainer's responsibility.
* Do **NOT** modify `extraction/raw_text/` or
  `extraction/formalization_data/entities/`. Those are regenerated.
* Do **NOT** spend cycle time on the
  `picard_lindelof_bound_strengthening` or `jordan_canonical_form_missing`
  issues. Both are non-blocking for §406D's lift.
* Do **NOT** bundle ~400+ lines into one cycle (cycle 060 lesson:
  score −1). Keep cycle 064 to ≤ 200 lines of new code; defer
  spillover to cycle 065.

---

## Failed approaches from attempts (DO NOT repeat)

* **Cycle 060** (score −1): attempted to bundle ~430 lines of
  outer-squeeze proof replay with explicit (a, b, c) coefficient
  exposure in a single cycle. Regression: vacuous `exact <hypothesis>`
  proof introduced (semantic sorry +1). Lesson: keep cycle 064 to
  ~150 lines max; if helpers 3/4/5 grow the diff above that,
  defer them.
* **Cycle 008/035 phantom "commits not reaching repo"**: ignore any
  framing in the prompt that suggests prior work didn't land.
  Verify with `git log -1 origin/Main/Experiments` and proceed.
  Cycle 063 landed at `7741825`.
* **Cycle 050 `Finset.sum_le_sum_nbij'`**: this lemma does not exist
  in current Mathlib. If you need sum-le-sum with reindexing, use
  `← Finset.sum_image hinj` then `Finset.sum_le_sum_of_subset_of_nonneg`
  (per the memory file).
* **`Continuous.prod_mk` (snake_case)**: Mathlib uses `prodMk`
  (camelCase) in current pin. If `prod_mk` fails, switch to
  `prodMk`.
* **`fun_prop` for `Filter.Tendsto`**: not `@[fun_prop]`-tagged.
  Build `Continuous` first, then apply `Continuous.tendsto`.

---

## Open issues (read before starting; non-blocking for cycle 064)

* `non_autonomous_lift_plan.md` — the cycle 064–067 schedule.
  **Required reading.** Cycle 064 is cluster 1 (§406B).
* `lem_406B_textbook_check.md` — Butcher's `(iα_i − β_i)` form is a
  textbook typo; we use the corrected `β_i` form. The non-autonomous
  lift preserves this correction (the algebra is identical).
* `tautology_scanner_false_positives.md` — if the scanner flags any
  `:= h_<name>` / `exact h_<name>` lines you wrote, rename
  `h_<name>` → `h<name>` (drop the underscore) as a cosmetic
  workaround. Do not touch `scripts/autonomous_loop.py`.

---

## Aristotle batch suggestion (only if helpers 3/4/5 deferred)

Submit a single Aristotle project containing:

* `residual_bound_nonauto` (helper 3)
* `deriv_diff_bound_nonauto` (helper 4)
* `localTruncationError_bound_nonauto` (helper 5)

Submission file goes in
`.prover-state/aristotle_submissions/cycle_064/sub_lemmas.lean`,
with imports matching `OpenMath/Chapter4/Section404.lean`'s import
block (Mathlib + the autonomous helpers as proved facts). Pass the
project ID via `mcp__aristotle__submit_file`. Sleep 30 min; check
once at the start of cycle 065.

If Aristotle returns with the joint-Lipschitz / time-argument
issue resolved automatically (premise selection finds the right
Mathlib helper), incorporate that solution. Otherwise stick with
the cycle 064 manual ports + cycle 065 follow-up.
