# Cycle 118 Strategy — Close `aux_515D_componentwise_deviation_tendsto_zero` (final §515D sorry)

## TL;DR

Close the **single remaining sorry** in `OpenMath/Chapter5/Section515.lean`:
`aux_515D_componentwise_deviation_tendsto_zero` at line 1873. Closing
this closes `aux_515D_output_tendsto` (cycle 117's clean ~30-LOC
composition already wraps it), which closes
`stable_consistent_isConvergent` (the §515D capstone), which closes
`thm:515D` — the final §515 theorem.

After this cycle, `thm:515D` flips from `partial` → `formalized` in
`lean_status.json` and `plan.md`.

## Priority 0 — Submit Aristotle Job 2 IMMEDIATELY (5 min)

Per CLAUDE.md "Aristotle-first (MANDATORY)" + cycle 117 task results
("viable Aristotle Job 2 target"). The helper's signature is fixed and
the proof structure is fully outlined (Steps 1–10 below) — exactly
the kind of compute-bound batch Aristotle excels at.

**Submission template** (use cycle 116's abstract-axioms substitution
pattern):

1. Create `.prover-state/aristotle_submissions/cycle_118/`.
2. Copy the helper signature + the `sorry` body of
   `aux_515D_componentwise_deviation_tendsto_zero` (Section515.lean
   ~line 1820–1873) into a standalone `.lean` file.
3. Replace cycle 110–116 helper invocations
   (`aux_515D_construct_ell_U_phi_A`, `localStepError_bound`,
   `aux_515D_per_step_recurrence`, `aux_515D_gronwall_bound`,
   `aux_515D_squeeze`, `aux_515D_stage_eventually_bounded`,
   `aux_515D_stage_tendsto`) with `axiom` declarations exposing
   their signatures only — Aristotle does not need their bodies.
4. Submit via `mcp__aristotle__submit_file` (single-file is faster
   than `submit_directory`). One project.
5. Sleep 30 minutes per CLAUDE.md.
6. **Single poll only** after the 30-min sleep. Do NOT re-poll
   within the cycle.

## Priority 1 — Manual composition in parallel (~3 hours)

Do NOT idle while Aristotle runs. Attempt manual composition
following the **10-step outline** below (transcribed from
`.prover-state/issues/aux_515D_output_tendsto_hypotheses.md` cycle 117
update §"What's needed for cycle 118"). If any single step stalls
> 30 min, introduce ONE sub-`have` with `sorry` and proceed
(decomposition fallback acceptable; see Backup plan below).

### Step 1 — Constants

```lean
intro i
set Δx : ℝ := x - x₀ with hΔx_def
have hΔx_pos : 0 < Δx := sub_pos.mpr hxx
set Lr : ℝ := (L : ℝ) with hLr_def
have hLr_nn : 0 ≤ Lr := L.coe_nonneg
```

### Step 2 — M-matrix `ell_U / phi_A` constructor (cycle 114)

```lean
obtain ⟨ell_U, phi_A, hellU_nn, hphiA_nn, hellU_eq, hphiA_eq⟩ :=
  aux_515D_construct_ell_U_phi_A (h₀ := Δx) hΔx_pos.le hLr_nn
    M.A M.U <hnorm_from_IsConvergent>
```
Use the strengthened `IsConvergent` Frobenius hypothesis
`‖((x - x₀) * L) • A.map abs‖_F < 1` (cycle 116 clause 5,
`Section512.lean:171`).

### Step 3 — Pick scalar constants α, β

Read off from cycle 107's `aux_515B_eta_contraction` /
`localStepError_bound` output bound shape
`ell_U · δ_max + h² L² M_bound · phi_A`:
- α := `Lr · Σ_{i,j} |M.A i j|` (Frobenius L¹-norm of A used in cycle 111).
- β := `M_bound · max_i phi_A i` (or similar — read precisely from
  `localStepError_bound`'s capstone signature at line 1355).

### Step 4 — Max-abs deviation `δ : ℕ → ℕ → ℝ`

```lean
set δ : ℕ → ℕ → ℝ :=
  fun n m => Finset.univ.sup' Finset.univ_nonempty
    (fun i : Fin r =>
      |Y n m i - (u i * yex (x₀ + (m : ℝ) * (Δx / n))
                  + v i * (Δx / n) * deriv yex (x₀ + (m : ℝ) * (Δx / n)))|)
```

### Step 5 — Per-step recurrence via `localStepError_bound`

For each `n > 0` and `m ∈ {0, ..., n-1}`, apply
`localStepError_bound` (cycle 116 strengthened, `Section515.lean:1355`)
at `xn1 := x₀ + m · h_n`, `h := h_n := Δx / n`. Locality transfer:
`Set.uIcc xn1 (xn1 + h_n) ⊆ Set.Icc x₀ x` follows from `0 ≤ m` and
`m+1 ≤ n` — use `Set.uIcc_subset_Icc` if it exists, else unfold to
`Set.Icc` and apply `linarith` / `nlinarith` with `m + 1 ≤ n`.

Take `Finset.sup'` over `i : Fin r` and apply triangle inequality →
`δ n (m+1) ≤ V_norm · δ n m + α · h_n · δ n m + β · h_n²`.

### Step 6 — Closed form via `aux_515D_per_step_recurrence` (cycle 113)

```lean
have hclosed := aux_515D_per_step_recurrence …
-- δ n m ≤ (V_norm + α·h_n)^m · δ n 0 + β·h_n² · Σ_{k<m} (V_norm + α·h_n)^k
```

### Step 7 — Exponential bound via `aux_515D_gronwall_bound` (cycle 113)

```lean
have hexp := aux_515D_gronwall_bound …
-- δ n n ≤ exp(α·Δx) · δ n 0 + β·h_n/α · (exp(α·Δx) - 1)   (specialized m = n)
```
Second term is `O(h_n)`, vanishes as `n → ∞`.

### Step 8 — Initial deviation `δ n 0 → 0`

`δ n 0 = max_i |Y n 0 i - (u_i · yex x₀ + v_i · h_n · deriv yex x₀)|`.
By `_hφ` (the φ-tendsto-zero clause of `IsConvergent`),
`Y n 0 i = φ(h_n) i → u_i · y₀ = u_i · yex x₀` (second equality from
`_hyex_x₀`). Linear correction `v_i · h_n · deriv yex x₀ → 0` since
`h_n → 0`. Use `Finset.sup'_le_iff` + `Tendsto.sub` per-component,
then lift via `Finset.sup'`-tendsto.

### Step 9 — Squeeze via `aux_515D_squeeze` (cycle 112)

```lean
have hδ_tendsto_zero : Tendsto (fun n => δ n n) atTop (nhds 0) := by
  apply aux_515D_squeeze …
  · exact <hexp specialized to m = n>
  · exact <step 8: δ n 0 → 0>
  · exact tendsto_one_div_atTop_nhds_zero_nat.const_mul Δx -- h_n → 0
```

### Step 10 — Convert max-abs → per-component

```lean
-- Goal (after `intro i` in Step 1):
--   Tendsto (fun n => Y n n i - (u i · yex x + v i · h_n · deriv yex x)) atTop (nhds 0)
-- Note: m = n means x₀ + n·(Δx/n) = x₀ + Δx = x, so deviation collapses to target.
have h_le : ∀ n, |Y n n i - (u i * yex x + v i * (Δx / n) * deriv yex x)|
              ≤ δ n n := fun n =>
  Finset.le_sup' _ (Finset.mem_univ i)
exact squeeze_zero_norm h_le hδ_tendsto_zero
```
(Adapt lemma name: `squeeze_zero_norm`, `Filter.Tendsto.of_norm_le`,
or unfold via `tendsto_zero_iff_norm_tendsto_zero` + `squeeze_zero`
— verify with `lean_local_search`.)

## Priority 2 — Aristotle integration (after sleep, ~30 min)

After the 30-min sleep:
1. Single `mcp__aristotle__get_status` poll on Job 2.
2. If COMPLETE: extract proof, compare with manual progress, choose
   the cleaner one. Replace `axiom` stand-ins with the real cycle
   110–116 helpers; verify
   `lake build OpenMath.Chapter5.Section515` succeeds.
3. If IN_PROGRESS or FAILED: keep manual progress, document Aristotle
   miss in cycle 118 task results.

## Priority 3 — Final integration & faithfulness check

After `aux_515D_componentwise_deviation_tendsto_zero` closes:

1. `lake build OpenMath.Chapter5.Section515` — must succeed clean.
2. `#print axioms OpenMath.Chapter5.Section510.GeneralLinearMethod.stable_consistent_isConvergent`
   must return `[propext, Classical.choice, Quot.sound]` — **no
   `sorryAx`**.
3. Update `extraction/formalization_data/lean_status.json`: `thm:515D`
   `partial` → `formalized`, cycle 118.
4. Update `plan.md` §515 row for `thm:515D`: `[~]` → `[x]`, replace
   cycle-117 detail block with one-line cycle 118 closure note.
5. Faithfulness check for `aux_515D_componentwise_deviation_tendsto_zero`:
   - Quote textbook fragment (Butcher 2008 §515D, p. 417 — the
     "deviation analysis" step within the proof).
   - Confirm Lean statement captures the same content (per-component
     deviation tendsto zero under cycle 116's localized hypotheses).
   - Document any divergence (cycle 116's localized `M_bound` and
     Frobenius bound are already documented in
     `cycle_113_isconvergent_strengthening_514_blocker.md` and
     `glm_isconvergent_strengthened.md` — this cycle introduces no
     new divergence).

## What NOT to try

- **Do NOT re-poll Aristotle** within the cycle after the single
  post-sleep check. CLAUDE.md is explicit. (Cycle 117 followed this
  correctly with Job 1.)
- **Do NOT attempt a global-yex `M_bound` retrofit.** Cycle 113's
  audit established that `Set.Icc x₀ x` localization is the correct
  path; cycle 116 landed it. Reverting would break §514's `yex = id`
  consumer (see
  `cycle_113_isconvergent_strengthening_514_blocker.md`).
- **Do NOT try to derive `U·u' = 𝟙` inside this proof.** That bridge
  closed in cycle 099 via cycle 098's stage-limit strengthening; the
  convergence witness `u'` already satisfies `U·u' = 𝟙` and
  `V·u' = u'` by hypothesis chain. The strategy here is purely
  analytical (discrete Grönwall + squeeze), not algebraic.
- **Do NOT inline-prove the M-matrix infrastructure.** Reuse
  `aux_515D_construct_ell_U_phi_A` (cycle 114) directly — it is
  load-bearing and already axiom-clean.
- **Do NOT bypass `localStepError_bound`** by reproving its content
  inline. The cycle 116 strengthening is exactly designed to be
  invoked per-step here; use it.
- **Do NOT split into more than 1 new sub-helper.** Cycle 117's
  lesson: single-helper decomposition is cleaner than multi-helper.
  If manual stalls at Step 5/6/8, introduce ONE additional sorry-
  bodied helper (e.g. `aux_515D_per_step_inequality` capturing only
  the per-step bound) and proceed.
- **Do NOT modify `scripts/autonomous_loop.py`.** Worker rule per
  CLAUDE.md.
- **Do NOT raise `maxHeartbeats`.** If `ring_nf` or `simp` blows up,
  decompose with intermediate `have` bindings.
- **Do NOT introduce `axiom` or `constant` declarations** in
  `OpenMath/`. (The Aristotle submission file in
  `.prover-state/aristotle_submissions/cycle_118/` is a sandbox and
  may use `axiom` for cycle 110–116 helper signatures.)
- **Do NOT cherry-pick a different easier theorem.** All other plan
  blockers (`AN_stability_deferred`, `cesaro_inverse_I_minus_V`,
  `convolution_vertex_vs_multiset`, etc.) need infrastructure
  cycles; closing `thm:515D` finishes Chapter 5's flagship
  convergence theorem and is the highest-value single deliverable.

## Backup plan (decomposition fallback)

If by ~3 hours of cycle work the manual proof has not closed AND
Aristotle has not returned a usable proof:

1. Identify the **specific stalled step** (most likely Step 5
   per-step iteration, Step 6 closed-form chaining, or Step 8
   initial deviation).
2. Introduce ONE new sub-helper with `sorry` capturing only that
   step. Compose the rest of the body around it.
3. Document the stall in `.prover-state/issues/` with the exact
   Lean state at the stalled goal.
4. Net delta: sorry count moved from
   `aux_515D_componentwise_deviation_tendsto_zero` to a narrower
   sub-helper. Cycle 119 closes the narrower one.

This is acceptable per CLAUDE.md "A cycle with zero changes is
unacceptable" — narrowing a sorry counts as forward progress.

## Pre-commit checklist

1. `lake build OpenMath.Chapter5.Section515` succeeds.
2. `#print axioms` of `stable_consistent_isConvergent` is clean (NO
   `sorryAx`) — IF closure complete.
3. `lean_status.json` and `plan.md` updated.
4. `cycle_118.md` task results written: worked-on, approach, result
   (SUCCESS/PARTIAL/FAILED), faithfulness check (the new helper or
   absence thereof), dead ends, discoveries, next-cycle suggestion.
5. Standard CLAUDE.md faithfulness checklist for any new
   declarations.
6. Commit message format:
   - Full closure: `Cycle 118 — close §515D capstone via aux_515D_componentwise_deviation_tendsto_zero`
   - Backup case: `Cycle 118 — narrow §515D sorry via <sub-helper> + close N steps`

## Reference files

- `OpenMath/Chapter5/Section515.lean` — the file to edit.
- `OpenMath/Chapter5/MMatrix.lean` — M-matrix infrastructure
  (cycle 105–107).
- `.prover-state/issues/aux_515D_output_tendsto_hypotheses.md`
  — full cycle 117 update with Steps 1–10 outline (this strategy
  expands it into actionable Lean form).
- `.prover-state/issues/glm_isconvergent_strengthened.md` — the
  cycle 098/116 IsConvergent strengthening documentation.
- `extraction/formalization_data/entities/thm_515D.json` — textbook
  reference.
- Butcher 2008, Numerical Methods for ODEs (3rd ed.), §515,
  pp. 414–420 — primary source.
