# Cycle 183 Strategy

## Status going in

* HEAD: `457f68c Cycle 182 — §441 lem:441A Phase C.2 proof draft (compile blocked by GPFS slowness)`.
* `OpenMath/Chapter4/Section441.lean`: 1227 LOC, 0 sorries, axiom-clean (cycle 181 state). Phase B closed (cycle 179, `a₁ > 0`). Phase C.1 closed (cycle 181, Möbius bridge).
* **Phase C.2 proof draft preserved at `.prover-state/cycle_182_draft_section441.lean` (1568 LOC, +341 LOC over HEAD).** Cycle 182 wrote three substantive theorems closing the textbook "Re ζ ≤ 0" claim but **could not verify the compile** because GPFS olean loading was running 30+ minutes per attempt. See `.prover-state/issues/cycle_182_gpfs_slowness.md`.
* No pending Aristotle results.

## Top priority — verify and ship cycle 182's Phase C.2 draft

The cycle 182 draft is mathematically sound (uses only Phase B-validated Mathlib idioms; the per-step decomposition Step 1 → Step 2 → Step 3 mirrors the textbook exactly). The blocker was infrastructure (cluster I/O), not proofs. **Cycle 183 should re-attempt the verification.**

### Step 1 — GPFS speed smoke test (5 min budget)

Before touching `OpenMath/Chapter4/Section441.lean`, run a cheap smoke test to gauge today's filesystem performance:

```bash
time lake env lean OpenMath/Chapter4/Section441.lean
```

This is the HEAD (cycle 181) version — known to compile clean. Expected: ≤ 5 min. If it takes > 10 min, today's GPFS is still slow → **abort to Step 4 fallback**.

### Step 2 — Apply the draft

If smoke test passes:

```bash
cp .prover-state/cycle_182_draft_section441.lean OpenMath/Chapter4/Section441.lean
```

The draft adds these theorems (line numbers in the draft):
- L817: `complexPow_re_isHomogeneousSolution_of_ρPoly_isRoot` (private helper)
- L854: `complexPow_im_isHomogeneousSolution_of_ρPoly_isRoot` (private helper)
- L899: `LinearMultistepMethod.ρPoly_complex_root_norm_le_one_of_stable` (Step 1 main)
- L1376: `ρPoly_aeval_inv_eq_zero_of_αPoly_aeval_complex_eq_zero` (private helper)
- L1419: `LinearMultistepMethod.αPoly_complex_root_norm_ge_one_of_stable` (Step 2 main)
- L1457: `aPoly_aeval_one_complex_eq_two_pow` (private helper)
- L1487: `LinearMultistepMethod.aPoly_complex_root_re_nonpos_of_stable` (Step 3 main = textbook "Re ζ ≤ 0")

### Step 3 — Verify and fix

```bash
lake env lean OpenMath/Chapter4/Section441.lean
```

**Outcome A (clean compile)**: Verify axiom-cleanliness on the three public theorems via `lean_verify` (one for each):
- `OpenMath.Chapter4.Section404.LinearMultistepMethod.ρPoly_complex_root_norm_le_one_of_stable`
- `OpenMath.Chapter4.Section404.LinearMultistepMethod.αPoly_complex_root_norm_ge_one_of_stable`
- `OpenMath.Chapter4.Section404.LinearMultistepMethod.aPoly_complex_root_re_nonpos_of_stable`

Each should return `[propext, Classical.choice, Quot.sound]` only.

Then proceed to Step 5 (commit + bookkeeping).

**Outcome B (specific tactic errors)**: Most likely 1–3 errors due to simp-set ordering or naming. Standard fixes:
- `simp only [..., aeval_*, ...]` arg order — try permuting; use `simp?` at the failing point.
- `Complex.coe_algebraMap` may need different spelling (try `Polynomial.aeval_C` directly + `RingHom.coe_*` lemmas).
- `pow_mul_pow_sub` may need `le_of_lt (Fin.isLt _)` rather than `Nat.le_of_lt_succ`.
- For `aeval_one_complex = 2^k`: if `(1 - 1)^(i+1) = 0` doesn't close via simp, use `Polynomial.aeval_one` + explicit `Finset.sum_eq_zero` with per-term `(1-1) = 0`.

Fix the specific errors using `lean_diagnostic_messages` to identify them, then re-compile. Budget: 60 min for fixing typical errors. If errors are structural (e.g. a Mathlib lemma we cited doesn't exist), see Step 4.

**Outcome C (GPFS slow again, or compile hangs > 30 min)**: Revert to HEAD via `git checkout HEAD -- OpenMath/Chapter4/Section441.lean` and proceed to Step 4 fallback.

### Step 4 — Fallback if GPFS is still slow OR compile reveals structural gap

**Option 4a (preferred): Submit Phase C.2 to Aristotle**

The three theorems are independent enough to submit as one job. Inject `sorry` at the three main theorems' bodies of the draft (in a copy, not the live file), then submit via `mcp__aristotle__submit_file`. After submission, sleep 30 min, poll once. If complete, incorporate. If not, leave running and pivot per Option 4b.

**Option 4b: Pivot to a fresh deliverable that doesn't touch Section441.lean**

Avoid Section441.lean entirely if today's GPFS makes it un-compilable. Candidates from `plan.md`:

1. **`def:451A` G-stable** (chapter 4 §451) — definition-only deliverable. Per `lean_status.json`, status currently `formalized` cycle 169 — verify; if not yet shipped, single-cycle definition + non-vacuity witness via `bdf2LMM`.
2. **`def:422B` underlying one-step method** — chapter 4 §422 entry point. Definition-only.
3. **`def:442A` principal sheet** — chapter 4 §442 entry point. Definition-only.
4. **`thm:535A` underlying one-step method (GLM)** — chapter 5 §535 entry point.

Recommend **#3 `def:442A`** as the pivot target: it opens §442 (the principal sheet of order arrows), the next §441-cluster section, and a definition-only ship is low-risk. Read `extraction/formalization_data/entities/def_442A.json` first to confirm scope.

### Step 5 — Bookkeeping (only if Step 3 Outcome A or B succeeds)

Once Phase C.2 verifies axiom-clean:

1. Update `extraction/formalization_data/lean_status.json`:
   - `lem:441A`: still `partial` (Phase C.3 + C.4 remain — `aᵢ ≥ 0` for `i ≥ 2` via real factorisation), but bump cycle to 183 with note "Phase C.2 closed: `Re ζ ≤ 0` for complex roots of `aPoly`."

2. Update `.prover-state/issues/lem_441A_phase_C_scoping.md`:
   - Add Cycle 183 update marking Phase C.2 closed.
   - Confirm Phase C.3 (real factorisation) is the next phase.

3. Update `plan.md` Chapter 4 row for `lem:441A`: keep `[~]` (still partial), update progress note to mention Phase C.2 closed.

4. Delete `.prover-state/cycle_182_draft_section441.lean` (no longer needed — content is in the live file).

5. Write `.prover-state/task_results/cycle_183.md`.

6. Commit and push.

## What NOT to try

* **Do NOT re-attempt `bdf2LMM_aPoly_eq` via `Polynomial.ext` or `simp + ring`.** Cycles 172/173 stalled on this; cycle 180 closed it via `Polynomial.funext + ring + match-reduction` and that is the canonical recipe. The cycle 180 closed form is at line ~1096 of the draft and should compile as-is.
* **Do NOT modify `scripts/autonomous_loop.py`.** Per CLAUDE.md, this is loop-maintainer territory. The cycle 182 GPFS issue is documented in `cycle_182_gpfs_slowness.md`.
* **Do NOT raise `maxHeartbeats` above 200000.** Cycle 150 hit 200000 on a similar n=7 stepping-stone for §550; the fix was decomposition, not bumping. If a tactic in the cycle 182 draft hits the heartbeat limit, decompose the offending step into a private helper rather than bumping the limit.
* **Do NOT try `linear_combination` or `nlinarith` for the residue identities.** Cycle 182 specifically replaced these with `eq_of_sub_eq_zero` + explicit `ring` for performance reasons. Keep that discipline.
* **Do NOT introduce `axiom` or `constant` for any Phase C step.** Phase C.2 closes via standard Mathlib polynomial + complex-analysis hooks — no axiom needed.
* **Do NOT poll Aristotle more than once per cycle.** If you submit in Option 4a, sleep 30 min, poll once, then move on regardless of result.
* **Do NOT take phantom-commit-verdict warnings at face value.** Cycles 176–180 produced six false positives diagnosed in `phantom_commit_verdict_pattern.md`. The cycle 182 commit DOES land (`457f68c`, includes the +1568-line draft as an untracked-then-committed file). Ignore any "Section441.lean was never staged" verdict from the supervisor — verify with `git show --stat HEAD` if needed.
* **Do NOT spend more than 60 min on a single tactic-error fix.** If a fix isn't producing within an hour, decompose the offending theorem into smaller helpers OR pivot to Option 4b.
* **Do NOT poll the Aristotle general-`n` jobs from §550.** Per `thm_550A_general_n.md` cycle 151 update, both long-running attempts were cancelled and no further submissions are recommended.

## Cycle scope summary

| Outcome | Cycle 183 deliverable | Phase C status |
|---|---|---|
| 3A (clean compile) | Ship Phase C.2: 3 public + 3 private theorems, axiom-clean | C.2 closed; C.3 next |
| 3B (fixable errors) | Same as 3A after error fixes | Same |
| 3C/4a (Aristotle path) | Sorry-first scaffold submitted; await result | C.2 in flight |
| 3C/4b (pivot) | `def:442A` or another definition-only ship | C.2 deferred |

The substantive goal is **Outcome 3A**. Treat 4a/4b as safety nets only if today's GPFS performance makes 3A infeasible.

## Next-cycle preview

If cycle 183 lands Phase C.2 (Outcome 3A or 3B), cycle 184 should begin **Phase C.3** (real factorisation of `aPoly` into linear/quadratic factors with `ξ ≤ 0`). This is the highest-risk Phase C step per `lem_441A_phase_C_scoping.md`, estimated at 250–400 LOC over 1–2 cycles. Mathlib hooks needed: `Polynomial.aeval_conj`, `Polynomial.IsRoot.map_conj`, conjugate-root pairing.

If cycle 183 falls back to 4a/4b, cycle 184 will resume Phase C.2 (depending on Aristotle / GPFS state).
