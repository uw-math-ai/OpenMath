# Cycle 065 Strategy — §406B helpers 3/4/5 nonauto lift via joint Lipschitz

## Aristotle status

**No pending Aristotle results**, no in-flight project. We submit a
batch at the END of this cycle (after the manual proofs land), per
the cycle 064 task-results follow-up plan.

## Target

Land the **non-autonomous lifts** of the three remaining §406B
helpers, plus the two summation helpers, plus the main theorem.
This is the second half of cluster 1 in the cycle 064–068 refactor
(see `.prover-state/issues/non_autonomous_lift_plan.md`).

| # | Autonomous source | New nonauto lemma name |
|---|---|---|
| 3 | `residual_bound` (`Section404.lean:691`) | `residual_bound_nonauto` |
| 4 | `deriv_diff_bound` (`Section404.lean:789`) | `deriv_diff_bound_nonauto` |
| α | `localTruncationError_α_sum_bound` (`Section404.lean:921`) | `localTruncationError_α_sum_bound_nonauto` |
| β | `localTruncationError_β_sum_bound` (`Section404.lean:964`) | `localTruncationError_β_sum_bound_nonauto` |
| 5 | `LinearMultistepMethod.localTruncationError_bound` (`Section404.lean:1005`) | `LinearMultistepMethod.localTruncationError_bound_nonauto` |

**Total estimate: ~200 lines.** Upper end of the §406B cluster
budget; matches the cycle 064 task-results projection. If you run
over (≥ 250 lines), use the fallback in §"Order of work" below.

**Insertion point.** Place the new lemmas **immediately after**
`residual_integral_form_nonauto` (which currently ends around
`Section404.lean:4087`) and **immediately before** the cycle 062
autonomous theorem at line 4090. This keeps the cycle 064 + cycle
065 non-autonomous helpers contiguous, with the autonomous helpers
preserved in their original block at lines 567–1033.

**Do NOT delete or rename the autonomous helpers.** Cycle 062's
`stable_consistent_isConvergent_autonomous` (line 3863) still
consumes them; they remain the cleaner proof for the autonomous
case and stay as committed deliverables.

**Do NOT attempt to close the line-4258 sorry this cycle.** That is
the cycle 068 target (slipped from 067 by cycle 064's deferral).

---

## Approach: single-constant joint Lipschitz on `Function.uncurry f`

### The hypothesis form

Replace `(hf_lip : LipschitzWith L.toNNReal f)` (autonomous,
`f : ℝ → ℝ`) with the joint Lipschitz form on `Function.uncurry f`
(non-autonomous, `f : ℝ → ℝ → ℝ`):

```lean
{f : ℝ → ℝ → ℝ} {L_joint M_bound : ℝ}
(hL_joint : 0 ≤ L_joint) (hM : 0 ≤ M_bound)
(hf_lip_joint : LipschitzWith L_joint.toNNReal (Function.uncurry f))
{y : ℝ → ℝ}
(hy_C1 : ContDiff ℝ 1 y)
(hy_ode : ∀ t, deriv y t = f t (y t))
(hf_y_bound : ∀ t, |f t (y t)| ≤ M_bound)
```

The **single-constant** form is recommended over a separate
`(L_t, L_y)` pair — algebraic bookkeeping stays simple, and the
extra constant factor `(1 + M_bound)` (see §"Bound shape" below) is
absorbed into the leading constant `D` of `lem:406B` cleanly.

### Insert this private helper FIRST (~25 lines)

Place at the head of the cycle 065 block, BEFORE
`residual_bound_nonauto`. Both helpers C and D will call it.

```lean
/-- **Joint-Lipschitz product-distance bound (cycle 065 helper).**
For a jointly Lipschitz `f : ℝ → ℝ → ℝ`, bound `|f t₁ y₁ − f t₂ y₂|`
by `L_joint · (|t₁ − t₂| + |y₁ − y₂|)`. -/
private lemma joint_lipschitz_pair_bound
    {f : ℝ → ℝ → ℝ} {L_joint : ℝ}
    (hL_joint : 0 ≤ L_joint)
    (hf_lip_joint : LipschitzWith L_joint.toNNReal (Function.uncurry f))
    (t₁ y₁ t₂ y₂ : ℝ) :
    |f t₁ y₁ - f t₂ y₂| ≤ L_joint * (|t₁ - t₂| + |y₁ - y₂|) := by
  have hd := hf_lip_joint.dist_le_mul (t₁, y₁) (t₂, y₂)
  -- `Function.uncurry f (a, b) = f a b`
  simp only [Function.uncurry_apply_pair] at hd
  rw [Real.dist_eq] at hd
  rw [show ((Real.toNNReal L_joint : ℝ≥0) : ℝ) = L_joint from
        Real.coe_toNNReal L_joint hL_joint] at hd
  -- The product distance on ℝ × ℝ is the sup norm; bound by sum.
  have hprod : dist ((t₁, y₁) : ℝ × ℝ) (t₂, y₂)
                ≤ |t₁ - t₂| + |y₁ - y₂| := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _))
                 (le_add_of_nonneg_left (abs_nonneg _))
  exact hd.trans (mul_le_mul_of_nonneg_left hprod hL_joint)
```

If any of `Function.uncurry_apply_pair` or `Prod.dist_eq` has
shifted name, verify with `lean_local_search` first.
`mcp__lean-lsp__lean_multi_attempt` on the simp call is the
fastest way to recover the correct unfolding lemma.

### Bound shape (sanity check before writing the proofs)

For helper C (`residual_bound_nonauto`), with `t₁ = x+hξ, t₂ = x`:

```
|f (x+hξ) (y(x+hξ)) - f x (y x)|
  ≤ L_joint * (|h*ξ| + |y(x+hξ) - y x|)              [joint Lip]
  ≤ L_joint * (h*(-ξ) + h*(-ξ)*M_bound)              [sub-lemma A]
  = L_joint * h * (-ξ) * (1 + M_bound)
```

Integrating against `∫_{-i}^0 (-ξ) dξ = i²/2`:

```
|residual|
  ≤ h * ∫_{-i}^0 L_joint * h * (-ξ) * (1 + M_bound) dξ
  = (1/2) * i² * h² * L_joint * (1 + M_bound)
```

For helper D (`deriv_diff_bound_nonauto`), with `t₁ = x, t₂ = x-i*h`:

```
|f x (y x) - f (x-i*h) (y(x-i*h))|
  ≤ L_joint * (|i*h| + |y x - y(x-i*h)|)
  ≤ L_joint * (i*h + h*i*M_bound)
  = i * h * L_joint * (1 + M_bound)
```

For the main theorem `localTruncationError_bound_nonauto`, the
α/β-sum helpers carry through unchanged in shape, with `L * M_bound`
replaced by `L_joint * (1 + M_bound)`:

```
|L(y, x, h)| ≤ ((1/2) * Σ (i+1)² |α_{i+1}|
                + Σ (i+1) |β_{i+1}|)
              * L_joint * (1 + M_bound) * h²
```

### Step-by-step lift recipe (apply per helper)

1. **Copy** the autonomous proof from the cited line.
2. **Replace** every `f (y t)` with `f t (y t)` (and likewise
   `f (y (x+h*ξ))` → `f (x+h*ξ) (y (x+h*ξ))`, etc.).
3. **Replace** the `hLip_pw` step (where `hf_lip.dist_le_mul` is
   invoked) with a call to `joint_lipschitz_pair_bound`.
4. **Adjust** the integrand bound: instead of
   `L * |y (x+h*ξ) - y x|`, use
   `L_joint * (|h*ξ| + |y (x+h*ξ) - y x|)`. The `|h*ξ|` term
   integrates separately via `intervalIntegral.integral_const_mul`
   + `integral_id`; the `|y (x+h*ξ) - y x|` term integrates via
   sub-lemma A as before.
5. **Adjust** the final closed-form integral computation. With
   `|h*ξ| = h*(-ξ)` for `ξ ≤ 0, h ≥ 0`, the `(1 + M_bound)` factor
   factors out cleanly:
   `∫_{-i}^0 L_joint * (h*(-ξ) + h*(-ξ)*M_bound) dξ
     = L_joint * h * (1 + M_bound) * (i²/2)`.
6. **Adjust** the final `ring` step to handle the new factor.

### Tactical notes

- **Reuse cycle 063 imports**: the adapter
  `lipschitzInSecond_univ_toLipschitzWith` (around line 3760)
  already brings in `Function.uncurry` and the joint-Lipschitz
  pattern. No new imports needed.
- **`abs_mul` + `abs_of_nonneg hh` + `abs_of_nonpos hξ`** still
  handles `|h*ξ| = h*(-ξ)` exactly as in the autonomous helper A.
- **`max_le`** + `le_add_of_nonneg_right` / `le_add_of_nonneg_left`
  are the canonical bridge for `max a b ≤ a + b` when `a, b ≥ 0`.
  An alternative is `max_le_add_of_nonneg`; check with
  `lean_local_search` if the first form fails.
- **Integration boilerplate**: lines 722–734 of the autonomous
  `residual_bound` set up integrability obligations; the
  non-autonomous version needs analogous obligations for the new
  `|h*ξ|` integrand. Use `(continuous_const.mul continuous_id).abs`
  + `Continuous.intervalIntegrable` for the `|h*ξ|` strand.

---

## Order of work (target ~200 lines, ~90 minutes)

1. **(20 min)** Insert `joint_lipschitz_pair_bound` (~25 lines).
   Verify with `lake env lean OpenMath/Chapter4/Section404.lean`.
2. **(30 min)** Port `residual_bound_nonauto` (~85 lines, mirror
   lines 691–782).
3. **(15 min)** Port `deriv_diff_bound_nonauto` (~30 lines, mirror
   lines 789–822).
4. **(15 min)** Port `localTruncationError_α_sum_bound_nonauto` and
   `localTruncationError_β_sum_bound_nonauto` (~30+30 lines, mirror
   lines 921–993). These are pure summation wrappers; the work is
   replacing `L * M_bound` with `L_joint * (1 + M_bound)` in the
   bound shape.
5. **(15 min)** Port `LinearMultistepMethod.localTruncationError_bound_nonauto`
   (~25 lines, mirror lines 1005–1033). Note: the `localTruncationError`
   field of `LinearMultistepMethod` is non-autonomous — verify this
   by reading the def around line 305 if needed; the cycle 062
   autonomous theorem rewires it via `(fun _ y => f y)` which we
   no longer need.
6. **(10 min)** Verify the build:
   * `lake env lean OpenMath/Chapter4/Section404.lean` clean exit.
   * Only sorry remains at line 4258
     (`stable_consistent_isConvergent`).
   * Axiom check on each of the five new lemmas returns
     `[propext, Classical.choice, Quot.sound]`.
7. **(5 min)** Update
   `.prover-state/issues/non_autonomous_lift_plan.md`: move cycle
   064 deferral note to "RESOLVED in cycle 065"; renumber cycle 066
   as the §406D recurrence cluster (~200 lines), cycle 067 as
   squeeze helpers (~100 lines), cycle 068 as the closure of
   `stable_consistent_isConvergent` (~80 lines). The schedule slips
   by one cycle relative to the original cycle 063 plan.

### Fallback (if cycle 065 runs over budget)

If steps 1–3 land cleanly but steps 4–6 don't fit:
- Commit cycle 065 with helpers C, D + the joint-Lipschitz helper
  only (~115 lines, 3 helpers). 
- Defer the α/β sum wrappers and the main theorem to cycle 066.
- Update `non_autonomous_lift_plan.md` to extend the schedule by a
  further cycle (final closure becomes cycle 069).

This still meets the cycle's "minimum: decompose a sorry or write
an issue" bar from CLAUDE.md, and stays well under the cycle 060
red-flag threshold (~430 lines / negative score).

---

## What NOT to try (failed approaches and known traps)

1. **Do NOT use `LipschitzInSecond Set.univ L f`** as the
   hypothesis. Cycle 063 introduced it for the autonomous-only
   adapter chain, but it bounds Lipschitz only in the **spatial**
   argument `y` for fixed `t`. It does NOT bound
   `|f t₁ y₁ - f t₂ y₂|` when `t₁ ≠ t₂`. Both helpers C and D
   have time-shifted arguments (`x+hξ` vs `x`; `x` vs `x-i*h`), so
   `LipschitzInSecond` is fundamentally insufficient. Cycle 064
   traced this; the `non_autonomous_lift_plan.md` issue captures
   the diagnosis.

2. **Do NOT introduce a separate `(L_t, L_y)` pair.** Cycle 060's
   regression (~430 lines, score −1) was caused by complexity
   outpacing verification. A two-constant form forces every
   downstream wrapper to track two invariants and an extra
   `max(L_t, L_y)` reduction step. Single-constant joint Lipschitz
   is simpler and faithful (Mathlib's `Function.uncurry`-Lipschitz
   class is a well-trodden path).

3. **Do NOT delete or modify the autonomous helpers** at lines
   567, 624, 691, 789, 833, 921, 964, 1005. Cycle 062's
   `stable_consistent_isConvergent_autonomous` consumes them; they
   are the cleaner proof for the autonomous case.

4. **Do NOT inline the joint-Lipschitz argument** (skip
   `joint_lipschitz_pair_bound`). Helpers C and D both invoke the
   same algebra; pulling it out as a private helper saves ~40
   lines and one source of `simp only` divergence.

5. **Do NOT raise `maxHeartbeats`** above 200000 if a proof is
   slow. Per CLAUDE.md, decompose instead. The autonomous proofs
   close within budget; the non-autonomous lifts add only one
   extra `mul_le_mul_of_nonneg_left` composition per Lipschitz
   step. If the main theorem's `ring` tactic balks on the new
   `(1 + M_bound)` factor, decompose into a `have h_factor : … = …`
   + `ring` rewrite.

6. **Do NOT submit Aristotle until the manual proofs are in
   place.** Submitting Aristotle on a hypothesis form that may
   need adjustment is wasted compute. Only after the cycle 065
   manual proofs land cleanly should we submit a batch (see
   §"Aristotle batch" below).

7. **Do NOT introduce `axiom` or `constant`** to bypass any gap.
   If a `LipschitzWith.dist_le_mul`/`Function.uncurry`/`Prod.dist_eq`
   identity proves uncooperative, that is a `lean_multi_attempt` /
   `lean_hover_info` problem, not an axiom problem. Per CLAUDE.md.

8. **Do NOT touch `scripts/autonomous_loop.py`.** Per CLAUDE.md and
   the standing
   `.prover-state/issues/tautology_scanner_false_positives.md`
   issue, the scanner is loop-maintainer territory.

---

## Faithfulness check (run before commit, per CLAUDE.md)

For each new lemma, the textbook content matches the autonomous
helper exactly except `f y` → `f t y`. Specifically:

- **`residual_bound_nonauto`**: bound shape changes from
  `(1/2) i² h² L M_bound` to `(1/2) i² h² L_joint (1+M_bound)`.
  **Justification**: the joint-Lipschitz form picks up the
  time-shift `|h*ξ|` contribution; `(1+M_bound)` is the natural
  absorption (see §"Bound shape" derivation). This is faithful to
  the textbook: Butcher §406 silently assumes `f` Lipschitz in `y`
  uniformly in `t`, plus continuous in `t`; on a compact `[a, b]`
  this combination is equivalent to joint Lipschitz on `[a, b] × ℝ`.
  The constant shift `L M ↦ L_joint (1+M)` is a faithful
  re-parameterisation. **Document in the lemma's docstring.**

- **`deriv_diff_bound_nonauto`**: same justification.

- **`localTruncationError_α_sum_bound_nonauto`**,
  **`localTruncationError_β_sum_bound_nonauto`**: same; the bound
  scales linearly through the sum.

- **`LinearMultistepMethod.localTruncationError_bound_nonauto`**:
  matches `lem:406B` (corrected form, see
  `.prover-state/issues/lem_406B_textbook_check.md`) with the same
  `L M ↦ L_joint (1+M)` reparametrisation. **Document in the
  docstring.**

**Tautology check**: each new lemma's conclusion is a quantitative
bound, not a hypothesis. No identity proofs (no `exact h`, no
`:= h`).

**Hypothesis strength check**: the only new hypothesis relative to
the autonomous version is the joint-Lipschitz form, which is
strictly weaker than the conjunction "Lipschitz in `y` uniformly in
`t`" + "continuous in `t` on a compact" that the textbook
implicitly assumes. Document this in each docstring.

**Identity check**: each proof is a substantive algebraic
combination (FTC + change of variables + Lipschitz + integration),
not a single `exact` of a hypothesis.

**Absent theorem check**: the docstrings should NOT promise
content that is absent from the file. If you write
"will be lifted in cycle 066", the cycle 066 strategy must follow
through.

---

## Aristotle batch (END of cycle, NOT now)

After the manual proofs are committed and pushed, submit a single
Aristotle project with **alternative proofs** for the three main
helpers:

- `residual_bound_nonauto`
- `deriv_diff_bound_nonauto`
- `LinearMultistepMethod.localTruncationError_bound_nonauto`

Do NOT submit:
- `joint_lipschitz_pair_bound` (~25 lines, too short to warrant
  compute)
- The α/β-sum wrappers (mechanical, low Aristotle leverage)

The submission is a "second opinion" — if Aristotle returns proofs
that close in fewer steps or use cleaner Mathlib lemmas, examine
them but keep the manual proofs unless the Aristotle versions are
obviously cleaner. Per CLAUDE.md, sleep 30 min after submission,
check ONCE in cycle 066, then move on. Do not poll repeatedly.

Submission command pattern (single-file project):
1. Write `.prover-state/aristotle_submissions/cycle_065/lift_helpers.lean`
   with the three theorem statements and `:= by sorry` placeholders
   (plus ALL their dependencies — autonomous helpers, cycle 064
   nonauto helpers, the joint-Lipschitz helper).
2. Submit via `mcp__aristotle__submit_file` or
   `mcp__aristotle__submit_directory`.
3. Record the project ID in
   `.prover-state/task_results/cycle_065.md`.

---

## References

- Cycle 064 task results
  (`.prover-state/task_results/cycle_064.md`) — original cycle 065
  plan and decision protocol.
- `.prover-state/issues/non_autonomous_lift_plan.md` — cluster
  schedule (currently cycles 064–068; will become 064–069 if the
  cycle 065 fallback fires).
- Cycle 040 consultant note
  `.prover-state/issues/consultant_advice_cycle_040.md` §D —
  original Mathlib lemma table for §406B helpers; still applicable
  (FTC, `norm_integral_le_of_norm_le_const`, `integral_id`, etc.).
- Autonomous helpers at `Section404.lean:567–1033`.
- Cycle 064 nonauto helpers 1, 2 at `Section404.lean:3968–4087`.
- Single sorry at `Section404.lean:4258`
  (`stable_consistent_isConvergent`, cycle 068 target post-slip).

## Build verification before commit

```bash
lake env lean OpenMath/Chapter4/Section404.lean    # clean exit
```

Plus axiom checks on each new lemma. Suggested commit message
style:
`Cycle 065 — §406B helpers 3/4/5 nonauto lift via joint Lipschitz`.
