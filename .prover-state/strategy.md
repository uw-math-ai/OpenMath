# Cycle 111 Strategy

## State entering cycle 111

* Branch tip: `c318fdd Cycle 110 — close aux_515D_stage_tendsto modulo M-matrix boundedness helper`.
* `OpenMath/` sorry count: **2**, both in `OpenMath/Chapter5/Section515.lean`:
  * Line **1481** — `aux_515D_output_tendsto` (capstone of §515D's discrete-Grönwall + squeeze; not touched yet).
  * Line **1522** — `aux_515D_stage_eventually_bounded` (NEW cycle 110 helper; the M-matrix-based eventual boundedness step).
* No pending Aristotle results.
* Capstone `GeneralLinearMethod.stable_consistent_isConvergent` and the `aux_515D_stage_tendsto` body already compile clean modulo these two helpers.

## Goal

**Net 2 → 1.** Close `aux_515D_stage_eventually_bounded` (line 1522) using the M-matrix comparison principle from cycle 106. Do **NOT** open new helper sorries. Do **NOT** touch `aux_515D_output_tendsto` this cycle.

The full proof outline is in `.prover-state/issues/aux_515D_stage_eventually_bounded_deferred.md` ("Approach 1: Direct M-matrix application"). Follow it. The cycle 110 task results' "Suggested next approach" (Steps 1–6) is the canonical recipe; this strategy file expands it.

---

## Priority 0 — Aristotle batch (sorry-first)

Submit a parallel attempt to Aristotle BEFORE you start hand-proving. This is free compute that can land while you work.

1. Compose a `.prover-state/aristotle_submissions/cycle_111/` directory with a self-contained Lean file containing:
   * The exact statement of `aux_515D_stage_eventually_bounded` from `Section515.lean:1522`, **with the new hypothesis** `(h_norm : ‖((x - x₀) * (L : ℝ)) • M.A.map (|·|)‖ < 1)` added (see Priority 1 step 1 below — Aristotle should see the strengthened signature).
   * The relevant imports, including `OpenMath.Chapter5.MMatrix` for the comparison-principle and inverse-positivity lemmas.
   * The cycle 105–107 M-matrix lemma names visible to the prompt: `Matrix.EntrywiseNonneg.nonneg_of_one_sub_mulVec_nonneg`, `Matrix.EntrywiseNonneg.inv_one_sub_of_norm_lt_one`.
2. Submit via `mcp__aristotle__submit_directory` (or `submit_file` if a single .lean is preferred). Note the project ID in the submission directory.
3. **Continue immediately to Priority 1.** Do not wait for Aristotle. Per CLAUDE.md, poll **once** ~30 min later (or at end of cycle, whichever is later). Do not re-poll.
4. If Aristotle returns a clean proof later: incorporate it (verify axioms come back to `[propext, Classical.choice, Quot.sound]`) and skip Priority 1 hand-proof.

Past Aristotle performance on M-matrix / discrete-Grönwall arguments has been weak (cycles 094/096/103). Set expectations accordingly: Aristotle is a backup, not the primary plan.

---

## Priority 1 — Hand-prove `aux_515D_stage_eventually_bounded`

Estimated 60–90 minutes of focused work. Concrete steps; follow in order.

### Step 1 — Surface the M-matrix Frobenius hypothesis

Add a new hypothesis to `aux_515D_stage_eventually_bounded` of the form

```lean
(h_norm : ‖((x - x₀) * (L : ℝ)) • M.A.map (|·|)‖ < 1)
```

(use the `Matrix.frobeniusNorm` / default `‖·‖` on `Matrix _ _ ℝ` — verify the exact spelling by reading cycle 107's `lem:515B` callsite around `Section515.lean:931+` for the prevailing convention). This is a **faithfulness divergence** analogous to cycle 107's `‖h₀ L |A|‖ < 1` hypothesis on `lem:515B`. Document it in the helper's docstring with a one-line comment "textbook tacitly assumes h₀ small enough; we surface the precise condition" plus a pointer to `aux_515D_stage_eventually_bounded_deferred.md`.

The natural propagation path is:

* `aux_515D_stage_eventually_bounded` → takes `h_norm`.
* `aux_515D_stage_tendsto` (line 1469) → also takes `h_norm`, forwards to the helper.
* `stable_consistent_isConvergent` (capstone) → adds `h_norm` to its hypothesis list (analogous to how cycle 107 added the `lem:515B` Frobenius hypothesis to `localStepError_bound`).

This is acceptable per cycle 098/107 precedent (both already strengthened the capstone signature).

### Step 2 — Choose a tail `N` such that `‖h_n L |A|‖ < 1` for `n ≥ N`

Use `tendsto_one_div_atTop_nhds_zero_nat` (or the derived `(x - x₀) / n → 0` form already used in `aux_515D_stage_tendsto`) plus `Filter.Eventually.mono` to argue:

```
∀ᶠ n in atTop, ‖((x - x₀) / (n : ℝ) * L) • M.A.map (|·|)‖ < 1
```

For `n ≥ N` with `N ≥ ⌈(x - x₀) / threshold⌉`, the scaled Frobenius norm shrinks below 1. The arithmetic is mechanical; do not over-engineer. The `h_norm` hypothesis at `(x - x₀)` itself is the worst-case bound, and the running `h_n` only shrinks the LHS further (entrywise non-neg + monotone scaling).

### Step 3 — Rearrange the stage equation

For `n ≥ N`, take `|·|` of `_hY_int_eq` and apply triangle inequality + Lipschitz `f`:

```
|Y_int n i|
  ≤ |∑ j, M.A i j · (h_n · f (Y_int n j))| + |∑ j, M.U i j · Y n n j|
  ≤ ∑ j, |M.A i j| · h_n · (L · |Y_int n j| + |f 0|)
    + |(M.U *ᵥ Y n n) i|
  = h_n L · (∑ j, |M.A i j| · |Y_int n j|)
    + h_n · (∑ j, |M.A i j|) · |f 0|
    + |(M.U *ᵥ Y n n) i|
```

i.e. entrywise

```
(I - h_n L |A|) · |Y_int n| ≤ h_n · |A| · 𝟙 · |f 0| + |M.U *ᵥ Y n n|.
```

Use `LipschitzWith.dist_le_mul` for the Lipschitz step; bridge `dist`-form to `|·|` via `Real.dist_eq` and `NNReal.coe_le_coe`. Cycle 107's `lem:515B` closure used the same bridge — read it.

### Step 4 — Apply M-matrix inverse-positivity to extract a bound

Cycle 106 `Matrix.EntrywiseNonneg.inv_one_sub_of_norm_lt_one` (file `OpenMath/Chapter5/MMatrix.lean:199`) gives `(I - h_n L |A|)^{-1}` entrywise non-negative. Combined with the comparison principle `nonneg_of_one_sub_mulVec_nonneg` (`MMatrix.lean:219`), conclude

```
|Y_int n| ≤ (I - h_n L |A|)^{-1} · (h_n · |A| · 𝟙 · |f 0| + |M.U *ᵥ Y n n|)
```

entrywise. Cycle 107's `lem:515B` closure went through this exact pattern at `Section515.lean` around the `localStepError_bound` proof — mirror its structure.

### Step 5 — Bound the RHS uniformly using output convergence

* `|M.U *ᵥ Y n n|` converges to `|M.U *ᵥ (fun i => u i · yex x)|` (continuous image of convergent sequence; use `Continuous.matrix_mulVec` + `tendsto_pi_nhds` — see cycle 110 task results' Step 3 recipe). A convergent sequence is bounded, so there exists `B_U` with `|(M.U *ᵥ Y n n) i| ≤ B_U` eventually.
* `h_n · (∑ j, |M.A i j|) · |f 0| → 0` since `h_n → 0`. Eventually `≤ |f 0|` (or any positive constant).
* `(I - h_n L |A|)^{-1}` entries are bounded uniformly for `n ≥ N` by `(I - h_N L |A|)^{-1}` (monotonicity of inverse on the comparison cone; if this lift is nontrivial, just use the explicit `n = N` bound at all `n ≥ N` since the inverse is continuous in the entrywise-non-negative cone).

So eventually `|Y_int n| ≤ Bd_const` componentwise for some explicit `Bd_const ≥ 0` (function of `M`, `L`, `|f 0|`, `‖u · yex x‖`, `(x - x₀)`).

### Step 6 — Lift to `f` via Lipschitz

```
|f (Y_int n j)| = |f (Y_int n j) - f 0 + f 0|
                ≤ L · |Y_int n j - 0| + |f 0|
                ≤ L · Bd_const + |f 0| =: Bf
```

Conclude with `⟨Bf, by positivity, …⟩`.

---

## Priority 2 — Update call sites and capstone

After Step 1 surfaces `h_norm` on `aux_515D_stage_eventually_bounded`:

* `aux_515D_stage_tendsto` (line 1469) — receives and forwards `h_norm`. One-line signature change, one-line forwarding.
* `stable_consistent_isConvergent` (capstone) — supplies `h_norm`. Add it as a new explicit hypothesis on the theorem signature; document the divergence in the docstring with the same boilerplate cycle 109 used for the `(hs : 0 < s)` divergence. Verify the only call site (none in `OpenMath/`) does not break.

After updates, build with `lake env lean OpenMath/Chapter5/Section515.lean`. Expect exactly **1** sorry warning at line 1481 (`aux_515D_output_tendsto`).

---

## Priority 3 — Pre-commit hygiene

* `lake env lean OpenMath/Chapter5/Section515.lean` clean (1 sorry warning at `aux_515D_output_tendsto`).
* `mcp__lean-lsp__lean_verify` on `aux_515D_stage_eventually_bounded` → axioms `[propext, Classical.choice, Quot.sound]` (NO `sorryAx`).
* `mcp__lean-lsp__lean_verify` on `stable_consistent_isConvergent` → axioms `[propext, Classical.choice, Quot.sound, sorryAx]` (sorryAx still inherited from `aux_515D_output_tendsto`).
* Update `.prover-state/issues/aux_515D_stage_eventually_bounded_deferred.md` to **RESOLVED** with a one-paragraph cycle-111 closure note pointing to the lemma name in `Section515.lean`.
* Faithfulness check on the new `h_norm` hypothesis: write the cycle docstring, mention the divergence in `cycle_111.md` task results.
* `.prover-state/task_results/cycle_111.md` per CLAUDE.md template.
* Commit with message starting `Cycle 111 — close aux_515D_stage_eventually_bounded via M-matrix comparison principle`.

---

## DO NOT DO this cycle

Explicit blacklist of approaches that have failed or are out of scope:

1. **Do NOT inline the M-matrix proof inside `aux_515D_stage_tendsto`.** The cycle 110 task results explicitly rejected this — keep the helper structure clean.
2. **Do NOT touch `aux_515D_output_tendsto` (line 1481).** That is a separate 2–3 cycle effort (discrete Grönwall + squeeze, parallel to LMM `Section404.lean:1300+`). Cycle 112+ work.
3. **Do NOT raise `maxHeartbeats`** above 200000. If a step is slow, decompose further.
4. **Do NOT introduce `axiom` / `constant`** for the M-matrix infrastructure or any of `h_norm`. The infrastructure exists at `MMatrix.lean:199, 219`; use it.
5. **Do NOT poll Aristotle more than once.** Submit once, work in parallel, check at end of cycle. CLAUDE.md is explicit.
6. **Do NOT pursue option 2 from the issue file** ("strengthen `IsConvergent` again"). The cycle 098 strengthening is enough; surface `h_norm` directly on the helper / capstone instead.
7. **Do NOT submit an Aristotle batch with the wrong signature.** If Step 1 of Priority 1 changes the signature, the Aristotle submission must include the strengthened form. (Cycle 110 cancelled an in-progress Aristotle project for this exact reason.)
8. **Do NOT try `Finset.induction_on` over `Fin s`** as a substitute for the M-matrix argument. The M-matrix machinery exists for exactly this proof; use it.
9. **Do NOT delete or alter the `_hStab`/`_hf_lip`/etc. underscore-prefixed parameters** unless your proof actually uses them. Cycle 110 left them prefixed because the body did not consume them. Step 1's added `h_norm` is the only signature change cycle 111 should make.
10. **Do NOT modify `scripts/autonomous_loop.py`.** The scanner / prompt-builder bugs documented in `tautology_scanner_false_positives.md` remain loop-maintainer territory.

---

## Backup plan if Priority 1 stalls past 90 minutes

If by ~90 minutes you have Steps 1–3 working but Step 4's comparison-principle invocation refuses to type-check, **stop and decompose**:

* Open a **new private helper** `aux_515D_stage_pointwise_bound` capturing the entrywise inequality `(I - h_n L |A|) · |Y_int n| ≤ rhs` for fixed `n` (no `∀ᶠ`).
* Close that helper this cycle (it does not need M-matrix machinery — just rearrangement).
* Leave `aux_515D_stage_eventually_bounded` as-is (still `sorry`) and update the issue file to note the partial decomposition.
* Net sorry count: 2 → 2 (same), but with the rearrangement step factored out so cycle 112 only needs to invoke the M-matrix comparison.

This is graceful degradation — **avoid it if you can**, but it is acceptable if Step 4 reveals a Mathlib API gap that needs investigation. Do NOT use this fallback as a first resort.

---

## Quick reference — Mathlib / OpenMath lemmas you will need

| Goal | Lemma | File |
|---|---|---|
| Entrywise non-negativity of matrix | `Matrix.EntrywiseNonneg` | `OpenMath/Chapter5/MMatrix.lean:52` |
| `M ≥ 0`, `‖M‖ < 1` ⇒ `(I - M)^{-1} ≥ 0` | `Matrix.EntrywiseNonneg.inv_one_sub_of_norm_lt_one` | `MMatrix.lean:199` |
| Comparison principle | `Matrix.EntrywiseNonneg.nonneg_of_one_sub_mulVec_nonneg` | `MMatrix.lean:219` |
| Lipschitz `f`: `\|f a - f b\| ≤ L · \|a - b\|` | `LipschitzWith.dist_le_mul` | `Mathlib/Topology/MetricSpace/Lipschitz.lean` |
| `1/n → 0` | `tendsto_one_div_atTop_nhds_zero_nat` | std |
| Eventually-AND of two `∀ᶠ` | `Filter.Eventually.and` / `Filter.eventually_atTop` | std |
| Convergent sequence is bounded | `Filter.Tendsto.bddAbove_range` (or extract via `bounded_of_convergent`) | std |
| Continuous matrix-mulVec | `Continuous.matrix_mulVec` | (used cycle 110) |
| Componentwise tendsto | `tendsto_pi_nhds` | std |
| Frobenius norm form `‖h_n • L • A.map(|·|)‖ < 1` | mirror cycle 107's `lem:515B` callsite spelling | `Section515.lean:931+` |

Cycle 107's `lem:515B` closure (`Section515.lean` ~ line 931+) is the closest template — read it before writing cycle 111's proof.

---

## Definition of done

* `OpenMath/` sorry count drops from 2 to 1 (only `aux_515D_output_tendsto` at line 1481 remaining).
* `lake env lean OpenMath/Chapter5/Section515.lean` exits clean with one sorry warning.
* `aux_515D_stage_eventually_bounded` axiom check: `[propext, Classical.choice, Quot.sound]`.
* `.prover-state/issues/aux_515D_stage_eventually_bounded_deferred.md` marked RESOLVED.
* `.prover-state/task_results/cycle_111.md` written per template.
* Faithfulness divergence on `h_norm` documented in the helper's docstring AND in the cycle results faithfulness check.
* All changes committed and pushed in one commit.
