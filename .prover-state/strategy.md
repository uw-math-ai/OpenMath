# Cycle 115 Strategy — Phase 1 of Solution A: localize `M_bound` in `localStepError_bound` family

## Context

Cycle 114 landed `aux_515D_construct_ell_U_phi_A` (M-matrix `ell_U`/`phi_A`
constructor) and fixed the lake-wrapper recursion bug that hung cycle 113.
The remaining sorry — `aux_515D_output_tendsto` body composition at
`OpenMath/Chapter5/Section515.lean:1793` — cannot be cleanly closed until
the §514 cascade conflict (documented in
`.prover-state/issues/cycle_113_isconvergent_strengthening_514_blocker.md`)
is resolved.

The favored resolution path is **Solution A**: localize the `M_bound`
hypothesis from "global" (`∀ t, |yex t| ≤ M_bound`) to "compact-interval"
(`∀ t ∈ Set.Icc x₀ x, |yex t| ≤ M_bound`). This makes a future
`IsConvergent` strengthening compatible with §514's `yex = id` consumer
(`Section514.lean:496`) because `id` IS bounded on `[0, 1]`.

Solution A is a multi-cycle refactor. **Cycle 115 owns Phase 1 only**:
refactor the helper chain that consumes `hy_M` / `hy'_LM` / `hf_y_bound`
to take compact-interval bounds. This is one cohesive change inside
`OpenMath/Chapter5/Section515.lean` with NO impact on §513 / §514 (since
those files don't touch these private/protected helpers).

Cycles 116 and 117 will then handle (respectively) the `IsConvergent`
strengthening + §513/§514 verification, and the
`aux_515D_output_tendsto` body composition.

## Aristotle results

None pending. Cycle 115 should NOT submit Aristotle this cycle —
the refactors are mechanical signature replacements where Aristotle
gives little leverage. Save Aristotle compute for cycle 117 body
composition.

## Phase 1 deliverable (cycle 115 target)

Refactor the following helpers in `OpenMath/Chapter5/Section515.lean`
to consume *compact-interval* bounds. The dependency chain is:

```
aux_y_diff_norm_bound  (line 129)
   ↓ used by
aux_T3_bound  (line 289)         aux_T4_bound  (line 378)
   ↓ both used by
localStageError_bound_a  (574)   localStageError_bound_b  (703)
   ↓ both used by
GeneralLinearMethod.localStepError_bound  (1302)
```

### Step 1 — refactor `aux_y_diff_norm_bound` (highest priority)

Current signature at `Section515.lean:129–137`:
```lean
lemma aux_y_diff_norm_bound
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (_hL : 0 ≤ L) (_hM : 0 ≤ M_bound)
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ L * M_bound)   -- GLOBAL
    (x h : ℝ) (hh : 0 ≤ h) (ξ : ℝ) :
    |y (x + h * ξ) - y x| ≤ h * |ξ| * (L * M_bound)
```

The proof body (line 158–161) only uses `hf_y_bound t` for
`t ∈ Set.uIoc x (x + h*ξ)`. Refactor `hf_y_bound` to:
```lean
    (hf_y_bound : ∀ t ∈ Set.uIoc x (x + h * ξ), |f (y t)| ≤ L * M_bound)
```
and update the `hC` block at line 158 to consume the membership directly:
```lean
have hC : ∀ t ∈ Set.uIoc x (x + h * ξ), ‖f (y t)‖ ≤ L * M_bound := by
  intro t ht
  rw [Real.norm_eq_abs]
  exact hf_y_bound t ht
```

You will need to reorder parameters so `(x h ξ)` are introduced
BEFORE `hf_y_bound` (since the bound depends on them). Move `(ξ : ℝ)`
up next to `(x h : ℝ)`.

### Step 2 — refactor `aux_T3_bound` and `aux_T4_bound`

Both currently take `(hf_y_bound : ∀ t, |f (y t)| ≤ L * M_bound)`
(at lines 296 and 385). Both pass it to `aux_y_diff_norm_bound`.

For `aux_T3_bound`: the integration variable is `ξ ∈ [0, c_i]`, so
the relevant evaluation interval is `Set.uIcc x (x + h * c_i)` (the
union of all `Set.uIcc x (x + h * ξ)` for `ξ ∈ [0, c_i]`). Refactor:
```lean
(hf_y_bound : ∀ t ∈ Set.uIcc x (x + h * c_i), |f (y t)| ≤ L * M_bound)
```
At line 320 where `aux_y_diff_norm_bound` is invoked, supply the
restriction-to-sub-interval slice via `Set.uIoc_subset_uIcc` (or
manual interval inclusion). Helpful Mathlib lemmas:
* `Set.uIoc_subset_uIcc`
* `Set.uIcc_of_le`, `Set.uIcc_of_ge`
* `Set.mem_uIcc`

For `aux_T4_bound`: the function is sampled at `y(x + h * c_j)` for
each `j : Fin s`. Refactor to:
```lean
(hf_y_bound : ∀ j : Fin s, ∀ t ∈ Set.uIcc x (x + h * c j),
    |f (y t)| ≤ L * M_bound)
```
At line 415 where `aux_y_diff_norm_bound` is invoked, pass
`hf_y_bound j` (specialized to the loop index `j`).

### Step 3 — refactor `localStageError_bound_a` and `localStageError_bound_b`

Both currently take:
```lean
(_hy_M : ∀ t, |yex t| ≤ M_bound)             -- GLOBAL
(_hy'_LM : ∀ t, |deriv yex t| ≤ L * M_bound) -- GLOBAL
```
at lines 582–583 and 711–712. Both then derive `hf_yex_bound` at
lines 599–600 / 729 via:
```lean
have hf_yex_bound : ∀ t, |f (yex t)| ≤ L * M_bound := by
  intro t; rw [← _hy_ode t]; exact _hy'_LM t
```
and pass that GLOBAL `hf_yex_bound` to `aux_T3_bound`/`aux_T4_bound`.

After Step 2, refactor as:
```lean
(_hy'_LM_local : ∀ j : Fin s, ∀ t ∈ Set.uIcc xn1 (xn1 + h * c j),
    |deriv yex t| ≤ L * M_bound)
```

(Note: `_hy_M` itself is unused in the proof body of
`localStageError_bound_a` — it has a leading underscore — but it's
needed for the consistent contract surface. Keep its name and just
swap to a per-`j` compact-interval form for parallelism. Same for
the `localStageError_bound_b` version, which uses indices in `Fin s`
for `c j`.)

Then update the `hf_yex_bound` derivation per-`j`:
```lean
have hf_yex_bound : ∀ j : Fin s, ∀ t ∈ Set.uIcc xn1 (xn1 + h * c j),
    |f (yex t)| ≤ L * M_bound := by
  intro j t ht; rw [← _hy_ode t]; exact _hy'_LM_local j t ht
```
and pass `hf_yex_bound i` (for the relevant index) to `aux_T3_bound`,
and `hf_yex_bound` (the full per-`j` version) to `aux_T4_bound`.

### Step 4 — refactor `GeneralLinearMethod.localStepError_bound`

The capstone helper at `Section515.lean:1302–1347`. Currently takes:
```lean
(_hy_M : ∀ t, |yex t| ≤ M_bound)               -- GLOBAL
(_hy'_LM : ∀ t, |deriv yex t| ≤ L * M_bound)   -- GLOBAL
```
at lines 1311–1312, and passes them through to
`localStageError_bound_a`/`_b` at lines 1358 and 1365.

Refactor to take the per-`j` compact-interval form matching Step 3:
```lean
(_hy'_LM_local : ∀ j : Fin s, ∀ t ∈ Set.uIcc xn1 (xn1 + h * c j),
    |deriv yex t| ≤ L * M_bound)
```
The `_hy_M` hypothesis can either (a) be dropped entirely since it's
unused in the body, OR (b) be kept as a per-`j` parallel for the
contract surface. Recommendation: drop it if unused; keep if it makes
the consumer side cleaner. Verify by `rg "_hy_M[^_]" OpenMath/Chapter5/Section515.lean`
to confirm it's not consumed downstream.

Then propagate the new `_hy'_LM_local` to the call sites at
lines 1358 and 1365 (just pass through).

If Step 4 turns out to be heavier than the budget allows, **defer it
to cycle 116** and ship Steps 1–3 only. Cycle 116 would then close
Step 4 plus the `IsConvergent` strengthening together.

## Development workflow (mandatory)

Per cycle 114's lessons:

1. **Scratch-file first**: open `test_phase1_step1.lean` in the project
   root, write the new `aux_y_diff_norm_bound` signature + body, and
   verify it compiles via `lake env lean test_phase1_step1.lean` BEFORE
   transplanting into `Section515.lean`. The scratch file should
   `import Mathlib` plus any Section515 prerequisites.

2. **Once each Step compiles in scratch**, transplant into
   `Section515.lean` and verify the FULL file builds via
   `lake env lean OpenMath/Chapter5/Section515.lean`.

3. **Do this Step-by-Step**, not all at once. Each Step touches a
   different lemma; transplant + verify per Step to localize any
   compile failures.

4. **Verify §513 and §514 still compile** after Steps 1–4:
   ```bash
   lake env lean OpenMath/Chapter5/Section513.lean
   lake env lean OpenMath/Chapter5/Section514.lean
   ```
   They should — Phase 1 doesn't touch their public interfaces, only
   the helpers' signatures (which §513/§514 don't directly invoke).

5. **Axiom-check the refactored helpers** via a scratch file:
   ```lean
   import OpenMath.Chapter5.Section515
   #print axioms GeneralLinearMethod.localStepError_bound
   #print axioms GeneralLinearMethod.localStageError_bound_a
   #print axioms GeneralLinearMethod.localStageError_bound_b
   #print axioms aux_T3_bound
   #print axioms aux_T4_bound
   #print axioms aux_y_diff_norm_bound
   ```
   Expect `[propext, Classical.choice, Quot.sound]` only.

## What NOT to do this cycle

- **Do NOT strengthen `GeneralLinearMethod.IsConvergent`** at
  `OpenMath/Chapter5/Section512.lean:138`. That's cycle 116 work; it
  depends on Phase 1 landing first.
- **Do NOT modify `OpenMath/Chapter5/Section513.lean` or
  `OpenMath/Chapter5/Section514.lean`** beyond confirming they still
  build. The §514 cascade conflict is real, but Phase 1 doesn't
  trigger it (the helpers' callers in §513/§514 are NONE — only
  `IsConvergent` consumers cascade).
- **Do NOT attempt to compose the body of `aux_515D_output_tendsto`**
  this cycle. That's cycle 117+ once the cascade is resolved.
- **Do NOT pursue Solutions B / C / D** from
  `cycle_113_isconvergent_strengthening_514_blocker.md`. The audit
  identified Solution A as cheapest and most faithful.
- **Do NOT inline the `aux_515D_construct_ell_U_phi_A` helper**
  anywhere — it's already landed in cycle 114 and ready for cycle 117
  to consume.
- **Do NOT use `Set.Ico` or `Set.Ioc` for the bound restriction** —
  the helpers integrate over closed intervals, and `Set.uIcc` /
  `Set.uIoc` are the right primitives because they handle both
  orientations of the interval. The proof inside
  `aux_y_diff_norm_bound` already uses `Set.uIoc`; align with it.
- **Do NOT raise `maxHeartbeats`** above 200000.
- **Do NOT introduce `axiom`/`constant`** to bypass any obligation.
- **Do NOT submit anything to Aristotle this cycle**. The refactors
  are mechanical; Aristotle's premise selection adds no leverage
  on signature replacements. Save the compute for cycle 117 body
  composition.
- **Do NOT recreate the lake-wrapper recursion bug** — cycle 114's
  fix is in place at `/tmp/lean4-toolchain/bin/lake-real` with a
  one-line `exec` wrapper at `/tmp/lean4-toolchain/bin/lake`. If
  `lake env lean` hangs past 5 min on a small file, check the
  wrapper before assuming Lean is the problem.
- **Do NOT pursue the Path B mean ergodic theorem work** for
  `cesaro_inverse_I_minus_V.md` this cycle. That's an orthogonal
  §514 blocker not on the §515D critical path.
- **Do NOT delete or modify `aux_515D_construct_ell_U_phi_A`,
  `aux_515D_per_step_recurrence`, `aux_515D_gronwall_bound`,
  `aux_515D_squeeze`, or `aux_515D_stage_eventually_bounded`**.
  These cycle 110–114 deliverables are what cycle 117's body
  composition will consume.

## Failed approaches not to repeat

- **Cycle 110 inlining of M-matrix arguments inside
  `aux_515D_stage_tendsto`**: rejected by the strategy at the time;
  the M-matrix work was correctly factored into a separate file
  (`MMatrix.lean`, cycles 105–106) and the cycle-114 helper. Don't
  re-inline.
- **Cycle 113 attempt to land `aux_515D_construct_ell_U_phi_A`
  without scratch-file verification**: hit the lake wrapper bug
  and burned the cycle to score 0. Cycle 114's pattern of
  scratch-file-first development is the canonical workflow. Apply
  it here too.
- **Cycle 113 Aristotle outputs that "compiled in isolation but
  hadn't been verified in Section515.lean"**: cycle 114 had to
  repair `aux_515D_per_step_recurrence` and
  `aux_515D_discrete_gronwall_raw` for missing
  `import Mathlib.Tactic.Cases` and a missing
  `simp only [Finset.mul_sum, mul_add, mul_left_comm]` before `ring`.
  Lesson: if you do submit anything to Aristotle, any returned
  proof MUST be re-verified inside the full Section515.lean import
  context, not just on the standalone submission.
- **Cycle 098 / 097 attempts to bypass the §514 cascade by tweaking
  the `IsConvergent` signature without first establishing the
  helper-chain compatibility**: don't repeat. Helper signatures must
  be settled BEFORE the public predicate signature changes — that's
  the whole point of doing Phase 1 (cycle 115) before Phase 2
  (cycle 116).

## Backup plan if Step 4 (`localStepError_bound`) blows the budget

If Steps 1–3 take longer than expected (target: complete by
~75 minutes wall-clock), ship Steps 1–3 only and **defer Step 4 to
cycle 116**. The intermediate state (helpers refactored to compact-
interval, capstone still on global) is still a clean compile because
the capstone simply derives the per-`j` compact bounds inline from
its own global hypothesis at the call sites:

```lean
-- inside localStepError_bound, before invoking the refactored helpers:
have _hy'_LM_local : ∀ j : Fin s, ∀ t ∈ Set.uIcc xn1 (xn1 + h * c j),
    |deriv yex t| ≤ L * M_bound :=
  fun j t _ => _hy'_LM t
```

Document the deferral in `.prover-state/task_results/cycle_115.md` as
"Step 4 deferred to cycle 116; signature change ready, just need to
rewire the call sites at Section515.lean:1358 and 1365."

## Faithfulness flag for cycle 115's pre-commit check

The Phase 1 refactor introduces a *strict weakening* of the helper
hypotheses (compact-interval bound is implied by global bound, so
all existing call sites can supply the new form by trivial
restriction). No faithfulness divergence is created at this layer.
The faithfulness divergence at the `IsConvergent` layer (the
`M_bound` strengthening overall) is documented in
`is_convergent_strengthened.md` (LMM precedent) and will be
extended in cycle 116.

For the cycle 115 pre-commit check:

* **No new `def` or `theorem`** is introduced — only signature
  refactors of existing helpers. Skip the entity-ID / textbook-quote
  step.
* **Tautology check**: N/A (no new theorems).
* **Hypothesis strength check**: PASSES (each refactored helper now
  takes a *weaker* hypothesis than before).
* **Absent theorem check**: confirm no proof comment promises content
  that was lost in the refactor.

## Suggested cycle 115 task results template

Document under "Worked on": `Section515.lean` Phase 1 helper-chain
refactor for Solution A.

Document under "Approach": list which Steps (1–4) landed and the
exact lines/signatures changed.

Document under "Result": SUCCESS/PARTIAL/FAILED with which Steps
shipped.

Document under "Faithfulness check": confirm that the refactor is a
strict *weakening* of helper hypotheses (not strengthening), so
existing consumers in §513/§514 still compile by trivial supply of
the weaker bound from their stronger ones.

Document under "Suggested next approach": cycle 116 should pursue
Phase 2 — strengthen `GeneralLinearMethod.IsConvergent` in
Section512.lean to require the localized hypotheses, then verify
§513 / §514 still build by supplying `M_bound := 0` (for `yex = 0`)
and `M_bound := |x|` on `Set.Icc 0 x` (for `yex = id`).
