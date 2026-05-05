# Cycle 117 Strategy — Compose body of `aux_515D_output_tendsto` (last sorry in §515)

## TL;DR

**Compose the body of `aux_515D_output_tendsto`**
(`OpenMath/Chapter5/Section515.lean:1865`) — the SOLE remaining
sorry in `Section515.lean` and the gating step for
`thm:515D` (`stable_consistent_isConvergent`).

All the load-bearing infrastructure landed in cycles 110–116:
- `aux_515D_construct_ell_U_phi_A` (cycle 114) — M-matrix
  constructor for `ell_U`, `phi_A`
- `localStepError_bound` (cycle 116, strengthened) — per-step
  error bound consuming the four cycle-116 localized hypotheses
- `aux_515D_per_step_recurrence` (cycle 113) — recurrence chain
- `aux_515D_gronwall_bound` (cycle 113) — closed-form bound
- `aux_515D_squeeze` (cycle 112) — squeeze argument
- `aux_515D_stage_tendsto` (cycle 110) + `aux_515D_stage_eventually_bounded`
  (cycle 111) — stage-side limit
- `IsConvergent` strengthening (cycle 116) — supplies the four
  localized hypotheses + Frobenius bound to the helper

Cycle 117 **only fills in a body**; no new `def`/`structure`/
`theorem` is introduced (modulo the optional decomposition
fallback below).

---

## Priority 0 — Aristotle Job 1 check (5 minutes, ONCE only)

**Project ID**: `9ef8f033-59d5-4557-b040-cf327e6a7063`
**Submitted**: 2026-05-05 00:01 UTC (cycle 116)
**Submission file**: `.prover-state/aristotle_submissions/cycle_116/output_tendsto_body.lean`

### Step 0a — Single status check

```python
mcp__aristotle__get_status(project_id="9ef8f033-59d5-4557-b040-cf327e6a7063")
```

**Decision tree**:

* **COMPLETE / proof returned**: jump to Step 0b (incorporation).
* **IN_PROGRESS / FAILED / TIMEOUT / any other state**: jump to
  Priority 1 (manual composition). Per CLAUDE.md, do NOT poll
  again this cycle.

### Step 0b — Incorporation (only if proof returned)

The Aristotle submission used **abstract axioms** for the GLM
structure (`AbstractGLM`, `IsStable`, `IsGLMSolution`) so the
returned proof needs adaptation to the real
`GeneralLinearMethod`-based file:

1. Download with `mcp__aristotle__download_result` and
   `mcp__aristotle__extract_result` — DO NOT manually re-derive.
2. Replace `AbstractGLM` field accesses with the real
   `GeneralLinearMethod` accesses (same field names: `A`, `U`, `B`, `V`).
3. Replace the abstract `IsStable`, `IsGLMSolution` with the real
   `GeneralLinearMethod.IsStable`, `GeneralLinearMethod.IsGLMSolution`.
4. Replace the `localStepError_bound_strengthened` axiom call with
   the real `GeneralLinearMethod.localStepError_bound`
   (`Section515.lean:1355`).
5. Build with `lake build OpenMath.Chapter5.Section515` to verify.
6. **Axiom-check** with `#print axioms aux_515D_output_tendsto` —
   must return `[propext, Classical.choice, Quot.sound]` (no
   `sorryAx`).
7. **Axiom-check `stable_consistent_isConvergent`** — should also
   become axiom-clean (the cycle 116 §513/§514 cascade was already
   axiom-clean modulo `aux_515D_output_tendsto`'s `sorryAx`).

If incorporation succeeds → `thm:515D` closed. Skip to "Wrap-up".

If incorporation breaks (compile errors, axiom mismatch, etc.) →
record the failure mode in `task_results/cycle_117.md` and proceed
to Priority 1.

---

## Priority 1 — Manual composition (if Aristotle not usable)

### Target

Body of `aux_515D_output_tendsto` (`Section515.lean:1865`).
Conclude:

```
Filter.Tendsto (fun n : ℕ => Y n n) Filter.atTop
    (nhds (fun i => u i * yex x))
```

### Tendsto-of-vector strategy

Use `tendsto_pi_nhds` to reduce vector-Tendsto to per-component
Tendsto. Then for each `i : Fin r`, prove `(Y n n) i → u i * yex x`
via the standard δ-decomposition: `(Y n n) i = u i · yex x +
v i · h_n · deriv yex x + δ i n`, where `δ i n → 0`.

Concretely, define for each `n` the *deviation vector*

```
δ n m i := Y n m i − (u i · yex(x_{n,m}) + v i · h_n · deriv yex(x_{n,m}))
```

with `h_n := (x − x₀)/n` and `x_{n,m} := x₀ + m · h_n`. The
target follows from `δ n n → 0` (use a max-abs reduction over
`Fin r` to convert to a scalar squeeze).

### Step-by-step body composition

**Step 1** — Set up constants and abbreviations:

```lean
set Δx : ℝ := x - x₀ with hΔx
have hΔx_pos : 0 < Δx := sub_pos.mpr _hxx
have hΔx_nn : 0 ≤ Δx := hΔx_pos.le
set Lr : ℝ := (L : ℝ)
have hLr_nn : 0 ≤ Lr := L.coe_nonneg
```

**Step 2** — Construct `ell_U`, `phi_A` once (independent of `n`):

```lean
-- Apply aux_515D_construct_ell_U_phi_A at h₀ := Δx, L := Lr.
-- The Frobenius hypothesis _h_norm is exactly what we need.
obtain ⟨ell_U, phi_A, hell_U_nn, hphi_A_nn, hell_U_eq, hphi_A_eq⟩ :=
  aux_515D_construct_ell_U_phi_A M.A M.U hΔx_pos hLr_nn
    (M.glmAbscissae v) (...nonneg proof...) _h_norm
```

(Verify the exact name `M.glmAbscissae`'s nonnegativity lemma — if
absent, supply an inline `intro i; ...` discharge. Inspect
`Section515.lean` near `def GeneralLinearMethod.glmAbscissae` at
line ~98 for what's available.)

**Step 3** — Define abbreviations
`α := Lr · max_i (∑ j, |M.B i j| · ell_U j)`,
`β := Lr² · max_i ((1/2) |u i| + |v i| + ∑ |B i j · c j| + ...)`.
These are constants determined by `M`, `Lr`, `M_bound`, `ell_U`,
`phi_A` — pull them out as `let` bindings or derive them from
`Finset.sup'` over `Fin r`.

**Step 4** — For each `n > 0`, set `h_n := Δx / n`. Iterate
`localStepError_bound` across `m = 0, …, n-1` to obtain the
per-step recurrence.

The cleanest packaging: define a *helper sub-claim* INSIDE the
proof body via `have`:

```lean
have per_step :
    ∀ n m : ℕ, 0 < n → m + 1 ≤ n →
    ∃ K : Fin r → ℝ,
      (∀ i, Y n (m+1) i - (u i * yex (x₀ + (m+1) * (Δx / n))
              + v i * (Δx / n) * deriv yex (x₀ + (m+1) * (Δx / n)))
            = (∑ j, M.V i j * (Y n m j - (u j * yex (x₀ + m * (Δx / n))
                  + v j * (Δx / n) * deriv yex (x₀ + m * (Δx / n)))))
              + K i)
      ∧ (∀ i, |K i| ≤ α * (Δx / n) * δ_max + β * (Δx / n)^2) := by
  intro n m hn hm
  -- Apply localStepError_bound with:
  --   h := Δx/n, h₀ := Δx, xn1 := x₀ + m·(Δx/n)
  --   ell_U, phi_A from Step 2
  -- Discharge the localized hypotheses by transferring from
  -- the global Set.Icc x₀ x bound:
  --   Set.uIcc xn1 (xn1 + h * c j) ⊆ Set.Icc x₀ x
  --   Set.uIcc xn1 (xn1 + h)       ⊆ Set.Icc x₀ x
  -- via Set.uIcc_subset_Icc + arithmetic on m, n.
  apply M.localStepError_bound (h := Δx / n) (h₀ := Δx) ...
  ...
```

**Critical subtlety**: each iteration of `localStepError_bound`
references `Y n m` (the current step) and produces a bound on
`Y n (m+1)`. The hypothesis `_hY_props n hn` provides
`M.IsGLMSolution h_n f (Y n)` which unfolds to per-step recurrences
we can use. Cross-reference how `Section512.lean::IsGLMSolution`
is defined at line ~89 to extract the right per-step stage data.

**Locality transfer** (use heavily):
- `Set.Icc x₀ x ⊇ Set.uIcc xn1 (xn1 + h * c j)` whenever
  `x₀ ≤ xn1 ≤ xn1 + h * c j ≤ x`. Since `c j ∈ [0, 1]`
  (typical for GLM abscissae) and `xn1 + h ≤ x` for `m + 1 ≤ n`,
  this is provable by `nlinarith` plus `Set.uIcc_subset_Icc`.
- Use `_hyex_M`, `_hyex'_LM` (which are on `Set.Icc x₀ x`) restricted
  via subset.

**Step 5** — Define `δ : ℕ → ℕ → ℝ` as the max-abs deviation:

```lean
let δ : ℕ → ℕ → ℝ := fun n m =>
  Finset.univ.sup' Finset.univ_nonempty
    (fun i : Fin r => |Y n m i - (u i * yex (x₀ + m * (Δx / n))
                        + v i * (Δx / n) * deriv yex (x₀ + m * (Δx / n)))|)
```

(or use `iSup` / `Finset.image.max'` — pick the variant your
sub-lemmas already speak.) From `per_step` plus
`Finset.abs_sum_le_sum_abs` and a `‖V‖_∞`-style monotone bound,
derive

```
δ n (m+1) ≤ V_norm · δ n m + α · h_n · δ n m + β · h_n^2
```

For `_hStab : M.IsStable`, you'll need a uniform bound on `‖V^k‖`;
see how cycle 110 used the stability hypothesis. (Do NOT re-prove
stability — extract via the existing `M.IsStable` API.) If
`‖V‖_∞ ≤ 1` is available directly from `M.IsStable`, use it.
Otherwise pull out `V_norm` abstractly and prove it nonneg via
`Matrix.opNorm_nonneg`.

**Step 6** — Apply `aux_515D_per_step_recurrence` (cycle 113) with
`V_norm`, `α`, `β`, `h := h_n`, `δ := δ n` to get a closed-form
bound:

```
δ n m ≤ (V_norm + α · h_n)^m · δ n 0
        + β · h_n^2 · ∑_{k<m} (V_norm + α · h_n)^k
```

**Step 7** — Convert the closed-form bound to Grönwall form using
`aux_515D_gronwall_bound` (cycle 113). Concretely, the converted
form at `m := n` is

```
δ n n ≤ exp(α · n · h_n) · a_n + (exp(α · n · h_n) − 1) · (β · h_n / α)
       = exp(α · Δx) · a_n + (exp(α · Δx) − 1) · (β · h_n / α)
```

where `a_n := δ n 0 = max_i |Y n 0 i − u i · y₀|` (since
`yex x₀ = y₀` and the `v · h · deriv yex` term vanishes at `m = 0`
because `x₀ + 0 · h_n = x₀`, so the bracket `u i · yex x₀ + v i ·
h_n · deriv yex x₀ = u i · y₀ + v i · h_n · f y₀` and the
`v i · h_n · f y₀` part is `O(h_n) → 0`).

**Step 8** — Define `δ0_seq : ℕ → ℝ := fun n => a_n` and show
`δ0_seq → 0` using `_hφ`:

```lean
have hφ_to_a : Filter.Tendsto δ0_seq Filter.atTop (nhds 0) := by
  -- Use _hφ : ∀ i, Tendsto (fun h => φ h i) (nhds 0) (nhds (u i * y₀))
  -- and _hY_props : Y n 0 = φ ((x - x₀) / n)
  -- For δ0_seq n := max_i |Y n 0 i - u i · y₀|, this is the
  -- composition of (fun n => (x-x₀)/n) → 0 with `_hφ`.
  ...
```

The `(fun n : ℕ => Δx / n)` tends to `0` via
`tendsto_const_div_atTop_nhds_zero_nat` or
`Filter.Tendsto.div_atTop` after `(n : ℝ) → ∞`. Reduce vector-max
to per-component via `Finset.sup'` continuity at zero.

**Step 9** — Apply `aux_515D_squeeze` (cycle 112) with the bound
from Step 7 and `δ0_seq → 0` from Step 8:

```lean
have hδ_to_0 : Filter.Tendsto (fun n => δ n n) Filter.atTop (nhds 0) :=
  aux_515D_squeeze ... hα_pos hβ_nn Δx hΔx_pos (fun n => δ n n)
    δ0_seq (fun n => Finset.sup'_nonneg ...) hφ_to_a step7_bound
```

**Step 10** — Convert `δ n n → 0` (max-abs of deviation) to
`Y n n → fun i => u i * yex x` via `tendsto_pi_nhds`:

```lean
rw [tendsto_pi_nhds]
intro i
-- δ n n bounds |Y n n i - (u i · yex(x₀ + n · h_n)
--                + v i · h_n · deriv yex(x₀ + n · h_n))|
-- Note: x₀ + n · h_n = x₀ + n · (Δx/n) = x₀ + Δx = x.
-- So the bracket = u i · yex x + v i · h_n · deriv yex x.
-- The v · h_n · deriv yex x term tends to 0 (h_n → 0).
-- Squeeze: |Y n n i - u i * yex x|
--   ≤ δ n n + |v i| · h_n · |deriv yex x|.
...
```

This is the only step that genuinely "uses" the `v` from
`_hCons_eq`; the v-term vanishes in the `n → ∞` limit because
`h_n = (x - x₀)/n → 0`.

### Decomposition fallback (mid-cycle, ALLOWED)

If the body composition exceeds 400 LOC by Step 5 or stalls on a
specific obstruction, **DO NOT FORCE ALL TEN STEPS THIS CYCLE**.
Instead, decompose into smaller private helpers:

1. Define `aux_515D_per_step_bound` as a NEW private theorem with
   sorry body, encapsulating Steps 4–5 (the per-step recurrence
   derivation).
2. Define `aux_515D_closed_form_bound` as a NEW private theorem
   with sorry body, encapsulating Steps 6–7.
3. Define `aux_515D_a_n_tendsto_zero` as a NEW private theorem
   with sorry body, encapsulating Step 8.
4. Compose `aux_515D_output_tendsto` from these three new helpers
   plus `aux_515D_squeeze` (cycle 112) and the `tendsto_pi_nhds`
   conversion (Step 10). This composition target is ≤ 80 LOC.

Net result: cycle 117 closes the original sorry but opens 3 smaller
sorries. Cycle 118 closes those.

This is **strictly preferable** to leaving `aux_515D_output_tendsto`
as a single ~600-LOC sorry. The decomposition makes verifiable
forward progress AND records the structure for the next cycle.

If the body composition is going *much worse* than expected (e.g.
a fundamental locality-transfer obstruction surfaces), submit the
decomposed sub-lemmas to **Aristotle Job 2** (cycle 117 mid-cycle):

- One project per sub-lemma (Steps 4–5, Steps 6–7, Step 8, Step 10),
  with the abstract-axioms pattern from cycle 116's submission.
- Submit at minute ~30 of cycle 117 if Aristotle Job 1 was a miss
  AND manual composition stalls.
- Cycle 118 polls those after 30 minutes per CLAUDE.md.

---

## What NOT to try

1. **Do NOT poll Aristotle Job 1 more than once.** CLAUDE.md is
   explicit. If the first check is IN_PROGRESS, treat it as a miss
   and proceed to Priority 1.
2. **Do NOT strengthen `IsConvergent` further.** The cycle 116
   strengthening (localized `M_bound` + Frobenius `< 1`) is the
   final, committed Solution-A form. The §514 option-(b) fallback
   (`h_norm_obligation`) is in place; do not pursue option-(a)
   restructuring this cycle.
3. **Do NOT touch the §513 / §514 cascade.** Cycle 116 verified
   `convergent_isStable`, `convergence_witness_satisfies_U`,
   `convergent_isPreconsistent`, `convergent_preconsistent_isConsistent`
   are all axiom-clean. Any edit there is wasted churn.
4. **Do NOT lift `M_bound` to a global bound.** This is the exact
   blocker `cycle_113_isconvergent_strengthening_514_blocker.md`
   documents. Solution-A localization to `Set.Icc x₀ x` is the
   correct path; transfer via `Set.uIcc_subset_Icc` and
   `Set.Icc_subset_Icc`.
5. **Do NOT inline-prove the M-matrix machinery.** Use
   `aux_515D_construct_ell_U_phi_A` (cycle 114) as a black box.
   The cycle-110 inline-attempt failure is documented in
   `aux_515D_stage_eventually_bounded_deferred.md` (rejected by
   the cycle 110 strategy explicitly).
6. **Do NOT modify `scripts/autonomous_loop.py`** or any loop
   infrastructure. Worker scope is `OpenMath/`, `extraction/`,
   `.prover-state/` only.
7. **Do NOT raise `maxHeartbeats`** above 200000. If a single
   composed `have` is too slow, decompose it into the fallback
   sub-lemmas above.
8. **Do NOT rebuild `Section512.lean`** as part of this cycle.
   Cycle 116's strengthening is final. Only `Section515.lean`
   should change.
9. **Do NOT introduce `axiom` or `constant` declarations.** The
   composition is *fully provable* given the cycle 110–116
   sub-lemmas; if you find yourself wanting to axiomatize, you
   are routing around an existing helper.
10. **Do NOT redo Aristotle Job 1's abstract-axiom adaptation
    manually if the proof returns.** Use
    `mcp__aristotle__extract_result` to download the file, then
    mechanically substitute the abstract names → real names.
    Do NOT "re-derive" the proof from the returned text.
11. **Do NOT introduce new `def` of named mathematical concepts**
    in this cycle. The decomposition fallback adds private helper
    *theorems* only — these are intermediate proof sub-claims, not
    new mathematical objects. The faithfulness checklist therefore
    has no new definitions to audit.
12. **Do NOT cherry-pick a different Chapter 5 entity** to work on
    instead. The cycle 116 work is structurally incomplete until
    `aux_515D_output_tendsto` closes; the §515 capstone is the
    project's current critical-path bottleneck. Pivoting to a
    different §520+ leaf would leave a sorry in the most heavily
    invested module.

---

## Pre-commit checks (mandatory)

After the body lands (whether via Aristotle incorporation or
manual composition):

1. **Build verification**:
   ```
   lake build OpenMath.Chapter5.Section515
   ```
   Must succeed. Note: olean rebuild ≠ `lake env lean <file>` —
   use `lake build` for proper dependency tracking.

2. **Sorry count check**:
   ```
   grep -c '^[[:space:]]*sorry\|[^a-zA-Z]sorry[^a-zA-Z]' OpenMath/Chapter5/Section515.lean
   ```
   Must be `0` (full success) or `≤ 3` (decomposition fallback).

3. **Axiom check** (use a scratch test file, then DELETE it before
   commit — never commit ad-hoc test files):
   ```lean
   -- file: cycle_117_axiom_check.lean (DELETE BEFORE COMMIT)
   import OpenMath.Chapter5.Section515
   #print axioms OpenMath.Chapter5.Section510.GeneralLinearMethod.stable_consistent_isConvergent
   ```
   If full success (no sorries), must return
   `[propext, Classical.choice, Quot.sound]`. If decomposition
   fallback was used, expect `sorryAx` from the new sub-lemma
   sorries (acceptable — document in cycle results).

4. **Faithfulness checklist** (from CLAUDE.md):
   - [ ] No new `def` / `structure` introduced this cycle (the
     decomposition fallback adds *theorems*, not definitions).
   - [ ] No tautological proof: the body genuinely consumes the
     cycle 110–116 sub-lemmas, not just `exact`-renames a
     hypothesis.
   - [ ] No identity proof: the body is not a single `exact h_*`.
   - [ ] If decomposition fallback used: each new private helper
     has a clear textbook role in the proof outline (Steps 4–10
     above).
   - [ ] Hypothesis strength: no new hypothesis added to
     `aux_515D_output_tendsto`'s signature (it was finalized in
     cycle 116).
   - [ ] Absent theorem: any new `have` claim referenced from
     elsewhere actually has a body or `sorry` in this cycle —
     not just a comment.

5. **`lean_status.json` update**: `thm:515D` was already at
   `partial` (per cycle 116 results). Update to `formalized`
   ONLY if `aux_515D_output_tendsto` is fully closed (no
   sorries, axiom-clean). If decomposition fallback used, leave
   at `partial` and append a note about which sub-lemmas remain.

6. **`plan.md` update**: bump the §515 row's status note to
   reflect the cycle 117 closure (full or partial).

---

## Wrap-up

If `aux_515D_output_tendsto` closes fully:
- `Section515.lean` becomes sorry-free.
- `thm:515D` (the last open §515 theorem) is fully formalized.
- The §513/§514/§515 trifecta is a clean unit; Chapter 5 §510
  block is functionally complete (35 entities, with `def:520*`,
  `def:521*` separately-tracked).
- Cycle 118 starts on a new Chapter 5 entity per `plan.md`
  (most likely candidates: `thm:520B`, `thm:520D`, or the §550
  doubly-companion infrastructure).

If decomposition fallback used:
- 1–3 sub-lemmas remain with `sorry`. Cycle 118 closes them via
  Aristotle Job 2 results (if submitted) or manually.

Either way, write `task_results/cycle_117.md` per CLAUDE.md
template, including:
- Aristotle Job 1 status at single-poll (state + percentage).
- Whether incorporation succeeded.
- If manual composition: which steps landed, which deferred,
  estimated cycle 118 cost.
- Faithfulness check.
- Updated `lean_status.json` row for `thm:515D`.

---

## File-level checklist

Files expected to change this cycle:
- `OpenMath/Chapter5/Section515.lean` — body of
  `aux_515D_output_tendsto` filled. Possibly 1–3 new private
  decomposition helpers (with their own bodies, ideally closed
  this cycle, allowable as sorries if the fallback is taken).
- `extraction/formalization_data/lean_status.json` —
  `thm:515D` row.
- `plan.md` — §515 status line.
- `.prover-state/issues/aux_515D_output_tendsto_hypotheses.md`
  — add cycle 117 closure section (mark CLOSED if full success;
  otherwise update with the decomposition sub-lemma list).
- `.prover-state/task_results/cycle_117.md` — new.

Files that should NOT change:
- `OpenMath/Chapter5/Section510.lean`, `Section512.lean`,
  `Section513.lean`, `Section514.lean` — already verified
  axiom-clean by cycle 116.
- `OpenMath/Chapter5/MMatrix.lean` — M-matrix infrastructure
  is final.
- `scripts/`, `extraction/raw_text/`, `extraction/formalization_data/entities/`
  — never edited by worker.
