# Cycle 114 — Strategy

## TL;DR

**RESET FROM PRIOR STRATEGY.** The cycle 113 audit established that
the full body composition + `IsConvergent` strengthening path
documented in the previous strategy.md is **blocked** by a §514
cascade conflict: `convergence_witness_satisfies_U`
(`OpenMath/Chapter5/Section514.lean:496`) applies `IsConvergent` to
the IVP `yex = id`, which is unbounded — fundamentally incompatible
with the proposed `(∀ t, |yex t| ≤ M_bound)` hypothesis. See
`.prover-state/issues/cycle_113_isconvergent_strengthening_514_blocker.md`
for the full analysis.

**Cycle 114 deliverable**: land `aux_515D_construct_ell_U_phi_A`
cleanly — the M-matrix-based constructor for `ell_U` and `phi_A`
that cycle 113 drafted and reverted unverified. This is concrete,
self-contained infrastructure that:
- Uses already-landed cycle 106 M-matrix machinery
  (`OpenMath/Chapter5/MMatrix.lean`).
- Touches NO consumer of `IsConvergent` (no §513 / §514 cascade
  risk).
- Is the load-bearing primitive for cycle 115+ body composition.
- Was the cycle 113 forward step that did not land due to slow
  build verification — cycle 114 fixes that with a scratch-file-first
  development workflow.

Sorry count target: 1 → 1 (same). The new helper is added
**without** touching the existing sorry at
`OpenMath/Chapter5/Section515.lean:1671`. Score expectation: +1
to +2 depending on how quickly the helper lands and whether the
§514 cascade resolution gets scaffolded as bonus work.

## Aristotle status

**No pending results.** Optional parallel submission described in
Priority 2 below. Do NOT block on it.

## Priority 1 — Develop `aux_515D_construct_ell_U_phi_A` in a scratch file

**Use the existing untracked scratch file `test_aux_515D.lean`** at
the repo root (Mathlib-only imports; minutes-to-build instead of
20+ for the full Section515.lean). The cycle 113 sub-lemma A/B
proofs were developed there before transplant; do the same.

The target helper signature:

```lean
import Mathlib
import OpenMath.Chapter5.MMatrix

open scoped Matrix.Norms.Frobenius

private theorem aux_515D_construct_ell_U_phi_A
    {s r : ℕ} [DecidableEq (Fin s)]
    (A : Matrix (Fin s) (Fin s) ℝ)
    (U : Matrix (Fin s) (Fin r) ℝ)
    {h₀ L : ℝ} (h₀_pos : 0 < h₀) (hL : 0 ≤ L)
    (c : Fin s → ℝ) (hc_nonneg : ∀ i, 0 ≤ c i)
    (h_norm : ‖((h₀ * L) • A.map (fun a => |a|) :
                 Matrix (Fin s) (Fin s) ℝ)‖ < 1) :
    ∃ ell_U phi_A : Fin s → ℝ,
      (∀ i, 0 ≤ ell_U i) ∧
      (∀ i, 0 ≤ phi_A i) ∧
      (∀ i, ell_U i - h₀ * L * (∑ j, |A i j| * ell_U j)
              = ∑ j, |U i j|) ∧
      (∀ i, phi_A i - h₀ * L * (∑ j, |A i j| * phi_A j)
              = (1/2) * (c i)^2 + ∑ j, |A i j * c j|)
```

Construction blueprint:

1. Let `Mpos := (h₀ * L) • A.map (fun a => |a|)`. By the hypothesis
   `h_norm`, `‖Mpos‖ < 1`, so `Mpos` is "small" in Frobenius norm.
2. By inspection, `Mpos.EntrywiseNonneg` follows from
   `mul_nonneg (mul_nonneg h₀_pos.le hL) (abs_nonneg _)` plus the
   `Matrix.smul_apply` and `Matrix.map_apply` unfolds. Establish
   this as `hMpos_nn : Mpos.EntrywiseNonneg`.
3. Define `bU : Fin s → ℝ := fun i => ∑ j, |U i j|` and
   `bA : Fin s → ℝ := fun i => (1/2) * (c i)^2 + ∑ j, |A i j * c j|`.
   Both are pointwise non-negative (sum of `abs` for `bU`; sum of a
   square plus sum of `abs` for `bA`).
4. Apply `Matrix.EntrywiseNonneg.inv_one_sub_of_norm_lt_one` (cycle
   106 helper) to get
   `(Ring.inverse ((1 : Matrix (Fin s) (Fin s) ℝ) - Mpos))
     .EntrywiseNonneg`.
5. Define
   `ell_U := (Ring.inverse ((1 : Matrix _ _ _) - Mpos)) *ᵥ bU`
   and
   `phi_A := (Ring.inverse ((1 : Matrix _ _ _) - Mpos)) *ᵥ bA`.
   Non-negativity follows from
   `EntrywiseNonneg.mulVec_nonneg`.
6. The defining equations follow from
   `(1 - Mpos) *ᵥ ((Ring.inverse (1 - Mpos)) *ᵥ b) = b`,
   which is `Matrix.mulVec_mulVec` + `Ring.inverse_mul_cancel` +
   `Matrix.one_mulVec`. Rearranging gives
   `ell_U - Mpos *ᵥ ell_U = bU`, which expands via
   `Matrix.smul_mulVec` and `Matrix.map_mulVec` to the textbook
   form `ell_U i - h₀ L · ∑ j |A i j| · ell_U j = ∑ j |U i j|`.

**Use `lean_multi_attempt` to iterate fast** on the equation
unfoldings. The cycle 107 `aux_515B_eta_contraction` proof
(`OpenMath/Chapter5/Section515.lean:931–1136`) consumes exactly
this construction's outputs — read its handling of `Mpos`,
`hMpos_nn`, and `hMpos_mulVec` for the unfold pattern (around
lines 999–1014).

### Verification protocol for the scratch file

```bash
lake env lean test_aux_515D.lean
```

Should exit with no errors. Then run

```bash
echo '#print axioms aux_515D_construct_ell_U_phi_A' >> test_aux_515D.lean
lake env lean test_aux_515D.lean
```

Expect `[propext, Classical.choice, Quot.sound]` only.

## Priority 2 — Optional Aristotle parallel (low-risk hedge)

While Priority 1 is in flight, optionally submit an Aristotle batch
on `aux_515D_construct_ell_U_phi_A` as a parallel attempt. The
helper is an M-matrix inversion + matrix-vector unfolding — closer
in shape to cycle 112's sub-lemma A/B (which Aristotle closed
cleanly) than to the GLM-specific plumbing Aristotle has historically
struggled on (cycles 094, 096, 103). Reasonable to submit; do **not**
block on the result.

If submitted: project ID goes in
`.prover-state/aristotle_submissions/cycle_114/README.md` per
convention. Check exactly **once** at the end of the cycle (no
mid-cycle polling per CLAUDE.md).

## Priority 3 — Transplant into Section515.lean

After the scratch-file proof is verified, copy the
`aux_515D_construct_ell_U_phi_A` body into
`OpenMath/Chapter5/Section515.lean`. Insertion point: between
`aux_515B_eta_contraction` (ends ~line 1136) and
`GeneralLinearMethod.localStepError_bound` (begins line 1183).
This places it adjacent to the M-matrix helper it consumes and
ahead of any future caller.

Make sure to:
- Open the `Matrix.Norms.Frobenius` scope at the top of the file
  (or locally around the helper). Check whether
  `aux_515B_eta_contraction` already opens this scope; if yes,
  no change needed.
- Adjust `[DecidableEq (Fin s)]` instance handling — `Fin s` should
  already have `DecidableEq` via `Fin.decidableEq`; if the local
  context needs `[DecidableEq (Fin s)]` explicitly, add it.

### Verification protocol for Section515.lean

Build is **slow** (~20 min per cycle 113 task results). Strategy:
1. Save the scratch-file-verified helper.
2. Edit `Section515.lean` to insert the helper.
3. Run `lake env lean OpenMath/Chapter5/Section515.lean` in the
   background with a 30-minute timeout.
4. While it builds, prepare commit message and update task results.
5. If the build completes successfully, commit and verify axioms.
6. If the build hangs past 30 min OR fails: revert the
   `Section515.lean` edit, keep the scratch file as the cycle 114
   deliverable (the helper IS verified in `test_aux_515D.lean`,
   just not yet integrated). Cycle 115 picks up integration.

## Priority 4 — Bonus: scaffold §514 cascade resolution path

If Priorities 1–3 land with time to spare (≤ 1 hour into the
cycle), use the remainder to scaffold (without touching
`IsConvergent`) the **localized** version of `localStepError_bound`
suitable for the cycle 115 cascade. Specifically:

Add a new theorem
`GeneralLinearMethod.localStepError_bound_compact` in
Section515.lean with hypothesis
`(_hy_M : ∀ t ∈ Set.Icc x₀ x, |yex t| ≤ M_bound)` (compact-interval
form) instead of the global form, and prove it as a wrapper of
`localStepError_bound` plus a "global ⇒ compact" weakening. This
gives cycle 115 a tested alternative entry point for §514's
`yex = id` consumer (where `M_bound := |x|` works on `[0, x]`).

This is **strictly bonus** — only attempt if the helper has landed
cleanly and there is real time. Do NOT start it before the helper.

## Priority 5 — Documentation

After landing the helper:

1. Update `.prover-state/issues/aux_515D_output_tendsto_hypotheses.md`
   to mark `aux_515D_construct_ell_U_phi_A` as **CLOSED cycle 114**
   (replacing the cycle 113 "drafted but reverted" status).
2. Append to
   `.prover-state/issues/cycle_113_isconvergent_strengthening_514_blocker.md`
   a "Cycle 114 update" section noting the helper landed and which
   of Solutions A/B/C/D the planner now favors. Tentatively favor
   **Solution A** (localize `M_bound` to `Set.Icc x₀ x`) because:
   - It is the only fully faithfulness-preserving path.
   - The cycle 114 helper output is compatible with both global
     and localized `M_bound` forms.
   - §514's `yex = id` IVP becomes compatible (`|id t| ≤ |x|` on
     `[0, x]`).
3. Update `plan.md` thm:515D row note to reflect cycle 114 status:
   helper landed, body composition deferred to cycle 115 with
   chosen cascade path.
4. Write `.prover-state/task_results/cycle_114.md` per CLAUDE.md
   format.

## What NOT to try (failed approaches from history)

* **Do NOT pursue the cycle 113 strategy's `IsConvergent`
  strengthening.** The global `M_bound` clause is incompatible
  with §514's `yex = id` consumer (audit confirmed cycle 113).
  Any path forward requires localizing `M_bound` first or
  replacing §514's witness IVP with a smooth-bounded one. Both
  are out of scope for cycle 114.
* **Do NOT touch `Section512.lean::IsConvergent`,
  `Section513.lean`, or `Section514.lean`.** These cascade ahead
  of any `IsConvergent` strengthening; resolving cycle 113's
  blocker is a separate cycle's work.
* **Do NOT submit the body composition of `aux_515D_output_tendsto`
  to Aristotle.** Per cycle 113's strategy: it is GLM-specific
  plumbing. The cycle 114 helper construction is acceptable to
  submit (Priority 2, optional).
* **Do NOT inline-develop `aux_515D_construct_ell_U_phi_A`
  directly inside `Section515.lean`.** Cycle 113 attempted this
  and reverted unverified because the 2140-line file builds
  slowly and the LSP server failed. Use `test_aux_515D.lean` as
  the development sandbox FIRST.
* **Do NOT raise `maxHeartbeats`** above 200000. If a single
  tactic block is slow, decompose into more `have` clauses
  (CLAUDE.md rule).
* **Do NOT introduce `axiom`/`constant`** for any step of the
  helper construction. The M-matrix infrastructure (cycle 106)
  is already complete; no axioms needed.
* **Do NOT remove the existing sorry at
  `OpenMath/Chapter5/Section515.lean:1671`** by faking a body —
  the body composition stays sorry'd until cycle 115 (after the
  cascade question is resolved).
* **Do NOT use `Finset.sum_le_sum_nbij'`** for any sum-reindexing
  step — it does not exist in Mathlib (cycle 050 dead end).
* **Do NOT use `add_le_add_left hA c`** to produce `a + c ≤ b + c`
  — it produces `c + a ≤ c + b`. Use `linarith [hA]` or `gcongr`.
* **Do NOT modify `OpenMath/Chapter5/MMatrix.lean`.** It is
  complete (cycle 106) and provides exactly what the helper needs.

## Fallback plans

**If the helper hand-proof stalls (90+ min on Priority 1):**

* Submit the helper to Aristotle (skip the "optional" — make it
  primary) and pivot to Priority 4 bonus work (the
  `localStepError_bound_compact` wrapper) while waiting. Aristotle
  has 30 min sleep window; it may close the helper while you
  scaffold the wrapper.

**If the scratch-file helper lands but Section515.lean integration
times out:**

* Commit the verified `test_aux_515D.lean` as
  `OpenMath/Chapter5/Section515D_Helper.lean` (a new module). Make
  Section515.lean import it later. Cycle 115 handles integration.
  Sorry count: 1 → 1 (same). Score: +1 (verified helper landed
  in repo, ready for cycle 115 consumption).

**If both the helper AND integration fail:**

* Land **only** the documentation update of
  `cycle_113_isconvergent_strengthening_514_blocker.md` plus
  whichever scratch-file progress was made (commit the partial
  work in `test_aux_515D.lean` for cycle 115 to pick up).
  Sorry count: 1 → 1 (no Lean delta). Score: 0 — documentation
  only, but no regression.

## Scoring rubric

* **+2**: helper lands in `OpenMath/Chapter5/Section515.lean`,
  axiom-clean, full Section515 build passes, cascade documentation
  updated, plus `localStepError_bound_compact` wrapper if time
  permits.
* **+1**: helper lands either in Section515.lean OR as a
  standalone module (`test_aux_515D.lean` committed under
  `OpenMath/`), axiom-clean, ready for cycle 115 consumption.
* **0**: no Lean delta but cascade resolution path documented
  (Solution A favored, hypothesis derivability re-confirmed,
  cycle 115 plan written).
* **−1 or worse**: REGRESSION (sorry count goes up, or §513/§514
  break, or `lake build` fails on a previously-clean module).

## Worker checklist

Before committing:

- [ ] `lake env lean test_aux_515D.lean` (or wherever the helper
      lives) exits 0.
- [ ] `#print axioms aux_515D_construct_ell_U_phi_A` shows only
      `[propext, Classical.choice, Quot.sound]`.
- [ ] If integrated: `lake env lean OpenMath/Chapter5/Section515.lean`
      exits 0 (allow 30 min timeout).
- [ ] Sorry count delta verified by grep over `OpenMath/` for
      `sorry` (excluding comments). Expected: 1 → 1.
- [ ] §513 / §514 / §512 still build clean (run quick spot-check
      via `lake env lean` on each — they should be unaffected
      since the cascade is NOT touched this cycle).
- [ ] `aux_515D_output_tendsto_hypotheses.md` updated to mark
      the helper closed.
- [ ] `cycle_113_isconvergent_strengthening_514_blocker.md`
      updated with cycle 114 status + favored solution.
- [ ] `plan.md` thm:515D row note updated.
- [ ] `cycle_114.md` task results written, including:
      - Faithfulness check (the helper introduces no new
        textbook-named concept; M-matrix construction is
        infrastructure, not a Butcher entity).
      - Dead ends (any tactic blocks that needed >2 attempts).
      - Suggested next approach: cycle 115 should pursue
        Solution A (localize `M_bound`) per the audit, then
        compose `aux_515D_output_tendsto`'s body using the
        cycle 114 helper.

## References

* `.prover-state/issues/cycle_113_isconvergent_strengthening_514_blocker.md`
  — the audit that ruled out the cycle 113 strategy.
* `.prover-state/issues/aux_515D_output_tendsto_hypotheses.md`
  — per-hypothesis derivability analysis; cycle 113 sketch of
  this helper.
* `.prover-state/task_results/cycle_113.md` — cycle 113 result
  documenting the audit, the inherited A/B closures, and the
  reverted helper draft.
* `OpenMath/Chapter5/MMatrix.lean::EntrywiseNonneg.inv_one_sub_of_norm_lt_one`
  — the cycle 106 M-matrix inversion lemma that the helper
  construction wraps.
* `OpenMath/Chapter5/MMatrix.lean::EntrywiseNonneg.mulVec_nonneg`
  — used to lift entrywise-nonneg matrix to non-negative output
  vector.
* `OpenMath/Chapter5/Section515.lean:931–1136` — cycle 107
  `aux_515B_eta_contraction` proof, the canonical example of
  `Mpos`/`hMpos_nn`/`hMpos_mulVec` plumbing in this codebase.
  Read it before writing the helper to match style.
* `OpenMath/Chapter5/Section515.lean:1183–1221` —
  `localStepError_bound`'s signature, showing exactly what the
  helper's outputs feed into (the `_hellU_eq` and `_hphiA_eq`
  side conditions).
* `test_aux_515D.lean` (untracked, repo root) — the cycle 113
  scratch file used for sub-lemmas A/B; reuse for cycle 114
  helper development.
