# Strategy — Cycle 041

## Status

**Cycle 040 IS committed.** The branch tip `4154007` ("Cycle 040 —
lem:406B sorry-first scaffold + sub-lemma E proved") landed
`OpenMath/Chapter4/Section404.lean` (212 net new lines), the typo
issue file, and the sorry-first scaffold. The cycle-040 evaluator
score of `-2 (REVERTED)` is the same `attempts.md`-propagation
phantom diagnosed in cycles 008/014/015 and re-confirmed in
`.prover-state/issues/consultant_advice_cycle_040.md` §A.
**Do NOT redo cycle 040 work.** Verify the state with:

```bash
git log -1 --format='%H %s'                # → 4154007 Cycle 040 …
git rev-parse HEAD                          # → 4154007…
git rev-parse origin/Main/Experiments       # → 4154007…  (same SHA)
git diff --stat HEAD~1 HEAD                 # → 8 files, +1304 / -285
```

If all four pass, the phantom is confirmed; proceed with the proof
work below.

## Open sorries (post-cycle-040)

`OpenMath/Chapter4/Section404.lean` has five sorries, all inside
`lem:406B`'s sorry-first scaffold:

| Line | Lemma                              | Status |
|------|------------------------------------|--------|
| 525  | `exact_solution_norm_bound`  (A)   | sorry  |
| 541  | `residual_integral_form`     (B)   | sorry  |
| 559  | `residual_bound`             (C)   | sorry  |
| 577  | `deriv_diff_bound`           (D)   | sorry  |
| 692  | `localTruncationError_bound` (main)| sorry  |

(Sub-lemma E `localTruncationError_decomposition` is fully proved at
lines 588–666. Do not touch it.)

## Cycle 041 target

**Goal: close sub-lemma D, then sub-lemma A.** This satisfies the
cycle-040 multi-cycle plan's "structure + 2 sub-lemmas closed"
ceiling with margin and matches the consultant's
`consultant_advice_cycle_040.md` §E primary plan.

### Step 0 — Poll Aristotle ONCE

Run `mcp__aristotle__get_status` for project
`53d674e4-20e3-43e8-9600-0b189c62c8f5` exactly once at the start of
the cycle.

* If the project has returned proofs for any of A/B/C/D, copy them
  in via `mcp__aristotle__extract_result` and verify each
  individually with `lake env lean OpenMath/Chapter4/Section404.lean`
  + axiom check. Keep the manual sub-lemma E proof; do not replace
  it with an Aristotle proof.
* If the project is still `IN_PROGRESS` (it was at 4 % at end of
  cycle 040, ≈ 1 h after submission), do NOT poll again. Proceed
  directly to manual proofs of D and A. Log the status in
  cycle_041.md and move on.
* If the project is `FAILED` or `COMPLETED` with no usable proofs,
  proceed with manual proofs.

CLAUDE.md is explicit: one poll per cycle. No retry loops.

### Step 1 — Manually prove sub-lemma D `deriv_diff_bound` (line 577)

Easiest of the four; only depends on sub-lemma A's *statement* (not
its proof), so even with A still `sorry` this compiles.

**Mathematical argument** (consultant note §D.4):

```
|y'(x) − y'(x − ih)| = |f(y(x)) − f(y(x − ih))|     [hy_ode]
                    ≤ L · |y(x) − y(x − ih)|         [Lipschitz f]
                    ≤ L · h · i · M_bound            [sub-lemma A with ξ = -i]
                    = i · h · L · M_bound.
```

**Concrete Lean tactic plan** (consultant note §D.4):

```lean
lemma deriv_diff_bound … := by
  rw [hy_ode x, hy_ode (x - (i : ℝ) * h)]
  -- Goal: |f (y x) - f (y (x - i*h))| ≤ i * h * L * M_bound
  have hLip : |f (y x) - f (y (x - (i : ℝ) * h))|
                ≤ L * |y x - y (x - (i : ℝ) * h)| := by
    have := hf_lip.dist_le_mul (y x) (y (x - (i : ℝ) * h))
    simpa [Real.dist_eq, ← NNReal.coe_le_coe, NNReal.coe_mul,
           Real.coe_toNNReal _ hL] using this
  -- Apply sub-lemma A at ξ = -i (note: x + h * -i = x - i*h, abs_sub_comm).
  have hA : |y x - y (x - (i : ℝ) * h)| ≤ h * (i : ℝ) * M_bound := by
    have hA_raw := exact_solution_norm_bound hM hy_diff hy_ode hf_y_bound
                     x h hh (-(i : ℝ)) (neg_nonpos_of_nonneg (Nat.cast_nonneg i))
    have heq1 : x + h * (-(i : ℝ)) = x - (i : ℝ) * h := by ring
    have heq2 : -(-(i : ℝ)) = (i : ℝ) := by ring
    rw [heq1, heq2] at hA_raw
    rw [abs_sub_comm]
    exact hA_raw
  calc |f (y x) - f (y (x - (i : ℝ) * h))|
      ≤ L * |y x - y (x - (i : ℝ) * h)| := hLip
    _ ≤ L * (h * (i : ℝ) * M_bound) := by
        apply mul_le_mul_of_nonneg_left hA hL
    _ = (i : ℝ) * h * L * M_bound := by ring
```

If `simpa` on the Lipschitz bridge stalls, the alternative pattern
is to extract `dist_le_mul` and rewrite `Real.dist_eq` and
`NNReal.coe_mul` separately, then close with `linarith`.

### Step 2 — Manually prove sub-lemma A `exact_solution_norm_bound` (line 525)

**Hypothesis-strengthening required.** As detailed in
`consultant_advice_cycle_040.md` §D.1, the textbook proof needs
`f∘y = deriv y` to be **continuous**, not merely defined pointwise.
`Differentiable ℝ y` alone does not give a continuous derivative —
`y` could be differentiable with a discontinuous `deriv y`.

**Action**: strengthen the hypothesis on `y` from
`(hy_diff : Differentiable ℝ y)` to `(hy_C1 : ContDiff ℝ 1 y)`.
Update the signature at line 519 (sub-lemma A), and propagate the
same change to sub-lemmas B (line 536), C (line 552), D (line 571),
and the main theorem at line 684. Replace
`Differentiable ℝ y` with `ContDiff ℝ 1 y` throughout, and adjust
internal uses (e.g. `hy_diff.differentiableAt` becomes
`hy_C1.differentiable le_rfl |>.differentiableAt` if needed; but
sub-lemma D as written above only uses `hy_ode`, so it needs no
change beyond the parameter spelling).

**Faithfulness justification** (mandatory; record in cycle_041.md):
Butcher §406's "exact solution to the standard initial value
problem `y' = f∘y` with `f` Lipschitz" implicitly assumes `y ∈ C¹`,
because the Picard–Lindelöf theorem (Butcher §110, our `thm:110C`)
produces a `C¹` solution from Lipschitz `f`. Surfacing this as an
explicit hypothesis is **not a strengthening relative to the
textbook** — it is making explicit what was implicit. Document this
in the docstring of sub-lemma A and in the cycle 041 task results
faithfulness check.

**Mathematical argument** (consultant note §D.1):

```
y(x + hξ) − y(x) = ∫_x^{x+hξ} y'(t) dt = ∫_x^{x+hξ} f(y(t)) dt    [FTC]
|integral|       ≤ M_bound · |hξ - 0| = M_bound · h · (-ξ)         [norm bound]
```

**Concrete Lean tactic plan** (consultant note §D.1):

```lean
lemma exact_solution_norm_bound
    {f : ℝ → ℝ} {M_bound : ℝ} (hM : 0 ≤ M_bound)
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ M_bound)
    (x h : ℝ) (hh : 0 ≤ h)
    (ξ : ℝ) (hξ : ξ ≤ 0) :
    |y (x + h * ξ) - y x| ≤ h * (-ξ) * M_bound := by
  -- Step 1: f∘y is continuous (= deriv y, which is continuous from C¹ y).
  have hfy_cont : Continuous (fun t => f (y t)) := by
    have heq : (fun t => f (y t)) = deriv y := by
      funext t; exact (hy_ode t).symm
    rw [heq]
    exact (hy_C1.continuous_deriv le_rfl)
  -- Step 2: HasDerivAt at every point.
  have hderiv : ∀ t, HasDerivAt y (f (y t)) t := by
    intro t
    have ht := (hy_C1.differentiable le_rfl).differentiableAt.hasDerivAt
    rw [hy_ode] at ht
    exact ht
  -- Step 3: integrability.
  have hint : IntervalIntegrable (fun t => f (y t)) MeasureTheory.volume
                x (x + h * ξ) := hfy_cont.intervalIntegrable _ _
  -- Step 4: FTC.
  have hFTC : ∫ t in x..(x + h * ξ), f (y t) = y (x + h * ξ) - y x := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt
              (fun t _ => hderiv t) hint
    simpa using this
  -- Step 5: bound the integral by M_bound.
  have hC : ∀ t ∈ Set.uIoc x (x + h * ξ), ‖f (y t)‖ ≤ M_bound := by
    intro t _
    simpa [Real.norm_eq_abs] using hf_y_bound t
  have hbound :
      ‖∫ t in x..(x + h * ξ), f (y t)‖ ≤ M_bound * |h * ξ| := by
    -- Use intervalIntegral.norm_integral_le_of_norm_le_const.
    have := intervalIntegral.norm_integral_le_of_norm_le_const hC
    -- Length is |b - a| = |(x + h*ξ) - x| = |h * ξ|.
    simpa [add_sub_cancel_left] using this
  -- Step 6: simplify |h * ξ| = h * (-ξ).
  have habs : |h * ξ| = h * (-ξ) := by
    rw [abs_mul, abs_of_nonneg hh, abs_of_nonpos hξ]
  rw [← hFTC, Real.norm_eq_abs] at hbound
  calc |y (x + h * ξ) - y x|
      ≤ M_bound * |h * ξ| := by linarith [hbound]
    _ = M_bound * (h * (-ξ)) := by rw [habs]
    _ = h * (-ξ) * M_bound := by ring
```

The exact spelling of `intervalIntegral.norm_integral_le_of_norm_le_const`
arguments and `ContDiff.continuous_deriv` may differ slightly —
verify each with `lean_hover_info` first. Common variants:
`intervalIntegral.norm_integral_le_of_norm_le_const_ae` (a.e.
version), `ContDiff.continuous_iteratedDeriv` (general-order
version, specialise to k=1).

### Step 3 — verify and commit

Run, in this order:

```bash
# 1. Compile cleanly.
lake env lean OpenMath/Chapter4/Section404.lean
# Expected: warnings on remaining sorrys at lines 541, 559, 692 only.
# (Lines 525 and 577 should disappear from the warning list.)

# 2. Axiom check on the two newly-proved lemmas.
echo '#print axioms OpenMath.Chapter4.Section404.deriv_diff_bound' | …
echo '#print axioms OpenMath.Chapter4.Section404.exact_solution_norm_bound' | …
# Expected: [propext, Classical.choice, Quot.sound] only.

# 3. Verify the rest of the project still builds.
lake build
```

Update `.prover-state/task_results/cycle_041.md` with the
faithfulness check (especially the `Differentiable → ContDiff`
hypothesis upgrade — flag it explicitly), the proof outcomes, the
Aristotle status, and any dead ends.

Update `extraction/formalization_data/lean_status.json` only if a
*whole entity* moves from `partial` to `formalized` — in this cycle
that does not happen; `lem:406B` itself stays `partial` until the
main theorem proof closes. Leave the status row unchanged.

### Step 4 — commit and push

```
git add OpenMath/Chapter4/Section404.lean \
        .prover-state/task_results/cycle_041.md \
        .prover-state/heartbeat.json \
        .prover-state/history.jsonl
git commit -m "Cycle 041 — close sub-lemmas A and D of lem:406B"
git push origin Main/Experiments
```

If only D closed (A turns out sticky on the `ContDiff` upgrade),
commit D alone and adjust the message accordingly. **Always commit
non-empty progress** — a single sub-lemma closed is a valid cycle
deliverable per CLAUDE.md.

## Fallback plan

If sub-lemma A's `intervalIntegral` plumbing burns more than 90 min
of cycle time:

1. Keep the `ContDiff ℝ 1 y` upgrade in ALL sub-lemma signatures
   (A, B, C, D, main). The cost of consistent signatures is zero
   even if A is still `sorry`.
2. Leave sub-lemma A as `sorry`.
3. File a follow-up issue
   `.prover-state/issues/exact_solution_norm_bound_FTC_plumbing.md`
   documenting the specific Mathlib-lemma signature problem
   encountered.
4. Commit D + the signature upgrade only. Cycle deliverable is
   "structure + 2 sub-lemmas closed (D, E) + ContDiff signature
   upgrade". Aristotle continues to work on A/B/C in the background.

## What NOT to do

* Do **NOT** treat the `cycle 40 score=-2 REVERTED` verdict as real.
  See §A above; the commit IS on `origin/Main/Experiments`. If you
  start "fixing" cycle-040 work, you will overwrite valid
  deliverables.
* Do **NOT** re-prove sub-lemma E. It is fully closed at lines
  588–666 with `[propext, Classical.choice, Quot.sound]` axioms.
* Do **NOT** revert the corrected `β_i` decomposition in favour of
  Butcher's stated `(iα_i − β_i)` form. The textbook has a typo;
  see `.prover-state/issues/lem_406B_textbook_check.md` and
  `consultant_advice_cycle_040.md` §B for two independent
  derivations confirming the typo.
* Do **NOT** poll Aristotle more than once. If the project is still
  `IN_PROGRESS` at the start of the cycle, treat it as "no
  contribution this cycle" and move on. CLAUDE.md is explicit; the
  consultant note §C reaffirms it.
* Do **NOT** raise `maxHeartbeats` above 200000. If a `ring_nf` or
  `simp` blows up, decompose into named `have`s.
* Do **NOT** introduce `axiom` or `constant` to bypass the
  `Continuous (deriv y)` gap. The right move is the
  `ContDiff ℝ 1 y` upgrade described in Step 2; that is faithful to
  the textbook.
* Do **NOT** generalise `localTruncationError` from `ℝ → ℝ` to
  vector-valued `ℝ → ℝ^N`. The current scalar formulation matches
  Butcher's §406 narrative and the proof plans above all require it.
* Do **NOT** edit `scripts/autonomous_loop.py`. The phantom-verdict
  bug is loop-maintainer territory; see
  `.prover-state/issues/tautology_scanner_false_positives.md`.
* Do **NOT** attempt sub-lemmas B (FTC + change-of-variables) or C
  (chain of A+B+Lipschitz) this cycle. B is the most plumbing-heavy
  of the four and is the natural cycle-042 target *after* A's FTC
  pattern is established and the Aristotle results land.
* Do **NOT** cherry-pick easier work elsewhere. `lem:406B` is the
  current `[~]` entity and is the gate for `thm:406C`,
  `thm:406D`, `thm:422C`, and the cross-chapter `thm:243A`. Stay on
  this target.

## Pre-commit faithfulness checklist (mandatory before commit)

For each newly-closed lemma in this cycle:

* `deriv_diff_bound`: not a textbook entity (helper for `lem:406B`).
  Statement matches Butcher's implicit step
  `|y'(x) − y'(x − ih)| ≤ ihLM`. ✓ tautology-free, ✓ no extra
  hypotheses beyond what Butcher's §406 proof uses.
* `exact_solution_norm_bound`: not a textbook entity (helper for
  `lem:406B`). The `ContDiff ℝ 1 y` strengthening relative to
  `Differentiable ℝ y`: **document explicitly** in the docstring
  AND in the task_results faithfulness section, with the
  Picard–Lindelöf-implies-C¹ justification. This is the single
  most important faithfulness flag for this cycle.

## Cross-references

* `.prover-state/issues/consultant_advice_cycle_040.md` §C, §D.1,
  §D.4, §E — Aristotle polling rule, sub-lemma A and D proof plans,
  cycle-041 strategy recommendation.
* `.prover-state/issues/lem_406B_textbook_check.md` — textbook typo
  documentation.
* `.prover-state/task_results/cycle_040.md` — cycle 040 deliverables
  and current sorry list.
* `OpenMath/Chapter4/Section404.lean:516–692` — the sorry-first
  scaffold under development.
* MEMORY.md `feedback_satisfieseq404b_cast.md` — the cast-bridging
  pattern used in sub-lemma E (already applied; documented for
  posterity).
