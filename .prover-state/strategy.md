# Cycle 110 Strategy

## Status snapshot

* Cycle 109 closed the `s = 0` inline sorry (3 → 2). Sorry count in
  `OpenMath/` is now **2**, both in `OpenMath/Chapter5/Section515.lean`:
  - line **1504**: `aux_515D_output_tendsto` (HARD — discrete Grönwall + squeeze)
  - line **1544**: `aux_515D_stage_tendsto` (EASIER — linear-algebra limit)
* The surrounding theorem `GeneralLinearMethod.stable_consistent_isConvergent`
  (line 1573) already dispatches to these two helpers in its proof body.
* Cycle 108 Aristotle batch `40554853-18b3-424c-81e4-2a2fae9e57c4`
  was at 6% in cycle 109. Likely complete by now.

---

## Priority 0 — Aristotle poll (5 min cap, single check)

Run **once** at start of cycle:

```
mcp__aristotle__get_status project_id="40554853-18b3-424c-81e4-2a2fae9e57c4"
```

* If `COMPLETED` and proofs returned for `aux_515D_output_tendsto` or
  `aux_515D_stage_tendsto`: extract via
  `mcp__aristotle__extract_result`, evaluate fit, and salvage what
  type-checks. **Aristotle has historically been weak on
  discrete-Grönwall + squeeze (cycles 094/096), so do not block
  Priority 1 on Aristotle even if proofs are returned.**
* If still `IN_PROGRESS` and < 50%: cancel via
  `mcp__aristotle__cancel_project` to free queue. The shape of the
  cycle 110 work below diverges from the cycle 108 submission
  signature (we are *refactoring* `aux_515D_stage_tendsto`'s
  hypotheses), so leftover work won't fit the new signature anyway.
* **Do NOT poll a second time.** CLAUDE.md is explicit: one check,
  then proceed.

---

## Priority 1 (REQUIRED) — Refactor + close `aux_515D_stage_tendsto`

Follow cycle 109's "Suggested next approach" steps 1 + 2 verbatim.
Net sorry count: 2 → 2 (one closed, one new helper sorry'd), but the
hard residue is now a clean boundedness fact instead of a vague limit
argument.

### Step 1a — Refactor `aux_515D_stage_tendsto` signature

In `OpenMath/Chapter5/Section515.lean:1522-1544`, **add** the explicit
hypothesis

```lean
(h_output : Filter.Tendsto (fun n : ℕ => Y n n) Filter.atTop
              (nhds (fun i => u i * yex x)))
```

immediately after the `Y, Y_int, _hY_props` block. This is a
**zero-cost** signature change because the only call site
(`stable_consistent_isConvergent` at lines 1591-1592) can supply it via
the *output* sub-lemma:

```lean
let h_output := aux_515D_output_tendsto M hStab hf_lip hyex_x₀ hyex_ode
                  hVu hUu hCons_eq hφ hxx Y Y_int hY_props
exact aux_515D_stage_tendsto M hStab hf_lip hyex_x₀ hyex_ode
        hVu hUu hCons_eq hφ hxx Y Y_int hY_props h_output
```

(or pass `aux_515D_output_tendsto … hY_props` inline as the last
argument). Verify this update in the call site at lines 1591-1592.

### Step 1b — Open new helper `aux_515D_stage_eventually_bounded`

Insert a new private theorem **before** `aux_515D_stage_tendsto` (so
it is in scope when the latter is proved). Signature:

```lean
private theorem aux_515D_stage_eventually_bounded {s r : ℕ}
    (M : GeneralLinearMethod s r)
    (_hStab : M.IsStable)
    {f : ℝ → ℝ} {L : NNReal} (_hf_lip : LipschitzWith L f)
    {x₀ y₀ : ℝ} {yex : ℝ → ℝ}
    (_hyex_x₀ : yex x₀ = y₀)
    {u : Fin r → ℝ}
    {x : ℝ} (_hxx : x₀ < x)
    (Y : ℕ → ℕ → Fin r → ℝ) (Y_int : ℕ → Fin s → ℝ)
    (_hY_int_eq : ∀ n : ℕ, 0 < n → ∀ i,
      Y_int n i =
        (∑ j, M.A i j * (((x - x₀) / (n : ℝ)) * f (Y_int n j)))
        + (∑ j, M.U i j * Y n n j))
    (_h_output : Filter.Tendsto (fun n : ℕ => Y n n) Filter.atTop
                   (nhds (fun i => u i * yex x))) :
    ∃ Bf : ℝ, 0 ≤ Bf ∧
      ∀ᶠ n in Filter.atTop, ∀ j : Fin s, |f (Y_int n j)| ≤ Bf := by
  sorry  -- DEFERRED to cycle 111 (see issue + suggested next approach)
```

Then **add an issue file**
`.prover-state/issues/aux_515D_stage_eventually_bounded_deferred.md`
following the template in `lem_515B_eta_contraction_deferred.md`,
explaining:
* The bound follows from the M-matrix comparison principle
  (`OpenMath/Chapter5/MMatrix.lean::Matrix.EntrywiseNonneg.nonneg_of_one_sub_mulVec_nonneg`,
  cycle 107) applied to the stage equation rearranged as
  `(I - h_n L |A|) · |Y_int n| ≤ h_n · |A| · 𝟙 · |f 0| + |U · Y n n|`.
* Output convergence `Y n n → u · yex(x)` makes the RHS eventually
  bounded.
* For sufficiently small `h_n` (i.e. large enough `n`), the M-matrix
  hypothesis `‖h_n · L · |A|‖ < 1` holds (analogous to cycle 107's
  `‖h₀ · L · |A|‖ < 1` Frobenius hypothesis on `lem:515B`).
* This is **infrastructure work** not pure proof work, hence the
  deferral.

### Step 2 — Close `aux_515D_stage_tendsto` end-to-end

Replace the body's lone `sorry` (line 1544) with a complete proof.
Reference patterns are in `OpenMath/Chapter5/Section514.lean:595-680`
(cycle 099's `convergence_witness_satisfies_U` proof). The structure:

```
intro / unfold
Goal: Tendsto Y_int atTop (nhds (fun _ => yex x))
Use tendsto_pi_nhds.mpr — reduce to componentwise:
  ∀ i : Fin s, Tendsto (fun n => Y_int n i) atTop (nhds (yex x))

For each i:
  Stage equation gives:
    Y_int n i = h_n · ∑_j A_ij · f(Y_int n j) + (M.U *ᵥ Y n n) i
  where h_n := (x - x₀) / n.

  T1_n := h_n · ∑_j A_ij · f(Y_int n j)
  T2_n := (M.U *ᵥ Y n n) i

  T1 → 0:
    h_n → 0 by `tendsto_one_div_atTop_nhds_zero_nat` style
      (specifically: (x - x₀) * (1/n) → (x - x₀) * 0 = 0).
    `f(Y_int n j)` eventually bounded by `aux_515D_stage_eventually_bounded`.
    Product of (→ 0) × (eventually bounded) → 0
    via `Filter.Tendsto.smul_zero_of_bounded_eventually` /
    `NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded`
    (see `Section514.lean:585-594` for the exact pattern;
    `Filter.IsBoundedUnder.smul_tendsto_zero` is the canonical name).
    Sum-over-j is closed by `Finset.tendsto_sum`.

  T2 → yex(x):
    Continuous (Matrix.mulVec M.U) by
      `Continuous.matrix_mulVec continuous_const continuous_id`
      (see Section514.lean:625-626).
    Hence (M.U *ᵥ Y n n) → M.U *ᵥ (fun i => u i * yex x).
    Use `tendsto_pi_nhds.mp` at index i, then evaluate:
      (M.U *ᵥ (fun i => u i * yex x)) i
        = ∑ j, M.U i j * (u j * yex x)
        = yex x * (∑ j, M.U i j * u j)
        = yex x * (M.U *ᵥ u) i
        = yex x * 1                       [by hUu, evaluated at i]
        = yex x.

  Combine T1 + T2 → 0 + yex(x) = yex(x). Done.

  Edge case n = 0: the stage equation is conditional on `0 < n`.
  Handle via `Filter.Tendsto.congr'` with `Filter.eventually_atTop_iff`
  to ignore the n = 0 value (Tendsto only cares about cofinite tails).
```

Mathlib lemmas to use (verify each name with `lean_local_search`
before writing):

| Goal | Lemma |
|---|---|
| `(1/n : ℝ) → 0` | `tendsto_one_div_atTop_nhds_zero_nat` |
| `c * (1/n) → 0` | `Filter.Tendsto.const_mul` |
| Bounded × tendsto-zero | `Filter.Tendsto.zero_smul_isBoundedUnder` (loogle the exact name) or `NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded` (Section514:591) |
| Continuous of `Matrix.mulVec M` | `Continuous.matrix_mulVec continuous_const continuous_id` |
| Componentwise → fn-valued | `tendsto_pi_nhds.mpr` |
| Fn-valued → componentwise | `tendsto_pi_nhds.mp` |
| Sum of tendsto | `Finset.tendsto_sum` (or per-summand `Tendsto.add` + induction) |
| Congr on cofinite tail | `Filter.Tendsto.congr'` + `Filter.eventually_atTop` |

If any of these names is wrong, **search via `lean_local_search` or
`lean_loogle` before falling back**. Do NOT manually unfold
`Filter.Tendsto` — Mathlib has a clean lemma for everything in this
list.

---

## What NOT to do

* **Do NOT attempt `aux_515D_output_tendsto`** (line 1504). That is a
  full discrete-Grönwall + squeeze argument mirroring the LMM
  `Section404.lean:1300+` chain — comfortably 2-3 cycles of focused
  work. Cycle 110's deliverable is the *stage-side* sub-lemma only.
  Per cycle 109 task results: cycle 112+ is the right time to open
  `aux_515D_output_tendsto`.

* **Do NOT inline-prove the M-matrix boundedness inside
  `aux_515D_stage_tendsto`.** Open the helper `aux_515D_stage_eventually_bounded`
  as `sorry`, file the issue, and defer. The boundedness proof needs
  the cycle 105–107 M-matrix infrastructure plus a non-trivial
  rearrangement of the implicit stage equation; that's a dedicated
  cycle 111 deliverable. If you try to do both this cycle, you will
  likely produce nothing committable.

* **Do NOT poll Aristotle a second time.** CLAUDE.md, cycle 109 task
  results, and standing project rules all forbid this.

* **Do NOT raise `maxHeartbeats` above 200000.** If the
  `aux_515D_stage_tendsto` body becomes slow, decompose into named
  intermediate `have` blocks.

* **Do NOT introduce `axiom` or `constant`.** The deferred boundedness
  goes in a sorry'd helper backed by an issue file, not an axiom.

* **Do NOT touch `scripts/autonomous_loop.py`.** Per
  `tautology_scanner_false_positives.md`.

* **Do NOT replace `aux_515D_stage_tendsto`'s textbook-style
  signature with a vacuous predicate.** The cycle 108 worker cleanly
  set up the right hypotheses; the cycle 110 work is to ADD
  `h_output` (zero-cost since the call site supplies it) and PROVE
  the body, not to weaken any hypothesis.

---

## What previously failed (do NOT repeat)

* Cycle 108: opened both sub-lemma sorries + s=0 inline sorry (3
  total). REVERTED with score −2 because sorry count regressed 0→3
  in one cycle. **Lesson: a refactor that opens new sorries must be
  *paired* with closing at least the same number in the same cycle.**
  Cycle 110's plan respects this: opens `aux_515D_stage_eventually_bounded`
  but closes `aux_515D_stage_tendsto`'s body (net 2 → 2).

* Cycles 094/096: Aristotle was poor on discrete-Grönwall + squeeze.
  Do not over-rely on it for `aux_515D_output_tendsto` either —
  those proofs need to be hand-written.

* Cycle 071/035/008: "commits not reaching repo" verdicts that were
  false alarms (consultant cycles 009/014/015/040 confirmed phantoms).
  After committing, **verify with `git rev-parse HEAD` and
  `git rev-parse origin/Main/Experiments` matching**, then proceed.

---

## Pre-commit faithfulness checklist (cycle 110)

For `aux_515D_stage_tendsto` (refactored signature, body filled):

- [ ] **Refactor signature** adds only `h_output` parameter; preserves
      all other hypotheses.
- [ ] **Body is sorry-free** modulo the single named helper call
      `aux_515D_stage_eventually_bounded`.
- [ ] Tautology check: conclusion `Tendsto Y_int atTop (nhds …)` is
      not equal to any hypothesis.
- [ ] Identity check: proof actually does work (computes via stage
      equation + matrix-mulVec continuity); not `exact h_output`.

For `aux_515D_stage_eventually_bounded` (new helper):

- [ ] Marked `private` (not exported).
- [ ] Body is `sorry`. Issue file
      `.prover-state/issues/aux_515D_stage_eventually_bounded_deferred.md`
      created and references the M-matrix infrastructure path.
- [ ] Statement is a non-trivial *boundedness* claim (not a tautology
      or `True`).
- [ ] Hypotheses are minimal: only what the closure proof actually
      needs.

For `stable_consistent_isConvergent` (call site update):

- [ ] Body still type-checks after passing `h_output` to the stage
      sub-lemma.
- [ ] No new sorries introduced at the call site.
- [ ] `lake env lean OpenMath/Chapter5/Section515.lean` builds with
      exactly 2 warnings about `sorry` (matching the line numbers of
      `aux_515D_output_tendsto` and the new
      `aux_515D_stage_eventually_bounded`).

For housekeeping:

- [ ] Update `extraction/formalization_data/lean_status.json` row for
      `thm:515D` to reflect new sorry distribution
      ("scaffold + 2 sorries (cycle 110; aux_515D_stage_tendsto closed
      modulo eventual-stage-boundedness helper)").
- [ ] No edits to entities other than `thm:515D`'s row.
- [ ] Cycle 110 task result file
      `.prover-state/task_results/cycle_110.md` documents:
      Aristotle poll outcome, the refactor, the body proof, and the
      new helper + issue file.

---

## After cycle 110: forward-looking trajectory

For the planner's reference (do not act on this in cycle 110):

* **Cycle 111** — Close `aux_515D_stage_eventually_bounded` via
  M-matrix comparison + stage-equation rearrangement. Net 2 → 1.
  Likely needs an additional `‖h₀ · L · |A|‖ < 1` Frobenius-norm
  hypothesis on the helper; surface it up to `IsConvergent`'s
  cycle 098 strengthening or carry it on the helper signature
  (latter is cleaner).
* **Cycle 112** — Open `aux_515D_output_tendsto` decomposition:
  introduce per-step error vector `δ_n m i := |Y n m i − (u_i · yex(x_{n,m})
  + v_i · h_n · y'(x_{n,m}))|`, set up the discrete-Grönwall recurrence
  via `localStepError_bound` (cycle 107), and write a sorry-first
  scaffold mirroring `Section404.lean:1300+`. Net 1 → 1+k for some
  small k of sub-lemma sorries.
* **Cycle 113-115** — Close the discrete-Grönwall recurrence,
  Squeeze + φ-limit, and capstone. Final 1 → 0.

This trajectory completes `thm:515D` in roughly 5 more cycles
(110-115), comparable to the LMM `thm:406D` path that took
cycles 040-068.

---

## Working order

1. **Aristotle poll** (5 min) — Priority 0.
2. **Refactor signature** (10 min) — Step 1a above.
3. **Open helper sorry + issue file** (15 min) — Step 1b above.
4. **Prove `aux_515D_stage_tendsto`** (60-90 min) — Step 2 above.
5. **Verify build clean** (5 min) — `lake env lean
   OpenMath/Chapter5/Section515.lean`, exact-2-sorry expectation.
6. **Update `lean_status.json`** (5 min).
7. **Write cycle 110 task results** (15 min).
8. **Commit + push** (5 min). Verify HEAD matches origin
   per the cycle 071/035/008 lesson.

Total target: ~2.5-3 hours of focused work.
