# Cycle 184 Strategy — ship Phase C.2 of `lem:441A` via Aristotle verification path

## Context

- Cycle 182 wrote a complete proof draft for **Phase C.2 of `lem:441A`**
  (3 substantive theorems + 4 private helpers, +341 LOC over HEAD,
  preserved at `.prover-state/cycle_182_draft_section441.lean`).
- Cycles 182 and 183 were blocked by **GPFS olean-loading slowness**
  (>10 min compile time vs the cycle 181 baseline of ~3 min).
- Cycle 183 killed a stuck `find /` zombie process (PID 77987, in `D`
  state for 2+ hours from a prior session) and submitted the draft to
  Aristotle for parallel verification: project
  **`7c4d0ffb-e6c1-4ef4-b8f5-688d256bac44`** at 12:31 PDT 2026-05-07.
  Status at end of cycle 183: IN_PROGRESS at 3 %.
- HEAD `OpenMath/Chapter4/Section441.lean` is at cycle 181
  (1227 LOC, 0 sorries, axiom-clean). The cycle 182 draft has 0
  sorries — the Aristotle submission asks Aristotle to confirm the
  compile or surface specific tactic errors that can be fixed in
  cycle 184.

## Top priority

**Get Phase C.2 verified and committed**, by whichever path is open.
Do NOT freelance into Phase C.3 or new entities until Phase C.2 is
shipped — the 3 drafted theorems form a complete textbook unit
(Butcher §441 p. 376 stability ⇒ `Re ζ ≤ 0`) and deferring further
would compound the C.2 stall.

## Step 0 — Process janitor (≤2 min, MANDATORY before any compile)

The cycle 183 root-cause investigation found a 2-hour-stuck `find /`
zombie was holding GPFS disk locks. Cleanup is cheap and may save
10+ minutes per failed compile attempt:

```bash
ps -eo pid,user,stat,etime,cmd | grep -E "find / -name" | grep -v grep
ps -eo pid,user,stat,etime,cmd | grep -E "lake|lean" | grep -v grep | head
```

Kill any `find /` processes you own that are in `D` (disk-wait)
state and >30 min old. Do NOT kill processes owned by other users.
If you launched a `lake build` in a previous cycle and forgot, kill
that too.

## Step 1 — Poll Aristotle ONCE (≤2 min)

Use `mcp__aristotle__get_status` with project_id
`7c4d0ffb-e6c1-4ef4-b8f5-688d256bac44`. Branch on the response.

### Branch 1A — COMPLETE with successful verification

This is the happy path. Aristotle confirms the cycle 182 draft
compiles cleanly.

1. Overwrite locally:
   ```bash
   cp .prover-state/cycle_182_draft_section441.lean \
      OpenMath/Chapter4/Section441.lean
   ```
2. Verify locally with a generous timeout (Aristotle confirmed it
   compiles, but local GPFS may still be slow):
   ```bash
   time lake env lean OpenMath/Chapter4/Section441.lean
   ```
   Allow up to 20 min. If it completes cleanly, proceed.
3. Run `lean_verify` (axiom check) on the three new public theorems:
   - `OpenMath.Chapter4.Section404.LinearMultistepMethod.ρPoly_complex_root_norm_le_one_of_stable`
   - `OpenMath.Chapter4.Section404.LinearMultistepMethod.αPoly_complex_root_norm_ge_one_of_stable`
   - `OpenMath.Chapter4.Section404.LinearMultistepMethod.aPoly_complex_root_re_nonpos_of_stable`

   Expected: `[propext, Classical.choice, Quot.sound]` only.
4. Bookkeeping (mandatory four files): see "Bookkeeping checklist"
   at the bottom of this strategy.
5. Commit and push (file-by-file `git add`, NOT `git add -A`).

### Branch 1B — COMPLETE with errors

Aristotle found compile errors. Apply fixes:

1. Read every error message Aristotle returned. Likely culprits:
   - **simp-set ordering** — a `simp only [..., aeval_*, ...]` may
     need a different lemma order or a missing
     `Polynomial.eval_X` / `Polynomial.eval_pow` rewrite.
   - **`Complex.normSq_apply` vs `Complex.normSq_def`** — Mathlib
     may have only one of these spellings; use whichever Aristotle
     references.
   - **`pow_mul_pow_sub` argument order** — needs `i ≤ k`; the
     draft expects this from `Fin.isLt` but the rewrite direction
     may need swapping.
   - **`mul_inv_cancel₀`** — guard hypothesis `a ≠ 0` may need an
     explicit `Complex.ofReal_ne_zero.mpr` or a `field_simp` setup.
2. Apply fixes to `OpenMath/Chapter4/Section441.lean` (NOT the
   preserved draft — keep that as the cycle 182 record).
3. Re-verify locally. If the second compile attempt also stalls
   (>20 min wall, <5 % CPU), submit a *minimal* Aristotle job
   containing only the fixed theorem(s); do not block the cycle on
   it. Continue with bookkeeping.
4. Bookkeeping + commit as in Branch 1A.

### Branch 1C — still IN_PROGRESS

Do **NOT** poll again this cycle. Per CLAUDE.md, one poll per
cycle. Proceed to Step 2 (local fallback) with strict time budget.

## Step 2 — Local fallback (Branch 1C only) (≤25 min total)

### Step 2a — GPFS health check

Quick smoke test on HEAD's `Section441.lean`:

```bash
time lake env lean OpenMath/Chapter4/Section441.lean
```

Hard timeout: **8 min**. If it completes cleanly in <8 min, GPFS is
healthy enough to proceed. If not, kill the lean process and skip to
Step 2c.

### Step 2b — Ship draft (GPFS-healthy path)

```bash
cp .prover-state/cycle_182_draft_section441.lean \
   OpenMath/Chapter4/Section441.lean
time lake env lean OpenMath/Chapter4/Section441.lean
```

Allow up to 20 min for the draft compile. The draft is +341 LOC of
new complex-arithmetic content — expect ~2× HEAD's compile time
even on a healthy filesystem. If it completes cleanly, follow
Branch 1A's Steps 3–5.

If the draft compile fails with errors (rather than stalling),
analyze them. Likely fixes follow Branch 1B's playbook. Apply,
retry, ship.

### Step 2c — GPFS still degraded (skip to bookkeeping + pivot)

If Step 2a stalled (>8 min on a clean HEAD compile), GPFS is still
degraded. Do **not** attempt the draft locally — it would consume
the rest of the cycle without progress.

Instead:

1. Update `.prover-state/issues/cycle_182_gpfs_slowness.md` with the
   cycle 184 GPFS state and the still-in-flight Aristotle project ID.
2. Pivot to Step 3 for the rest of the cycle.

## Step 3 — Pivot (Branch 1C + Step 2c only)

If Phase C.2 cannot ship this cycle, the rest of the cycle should
produce something committable. **Do not attempt Phase C.3** (real
factorisation, 250–400 LOC, highest risk per scoping doc).

The following are bounded single-cycle deliverables compatible with
GPFS-degraded conditions (each touches ≤200 LOC and adds no new
heavy imports, so olean loading is tolerable):

### Option 3A (PREFERRED) — `def:381F` (P-equivalent)

Definition-only deliverable. `def:381B` (Φ-equivalent) and
`def:381D` (P-reducible) are already formalised in
`OpenMath/Chapter3/Section381.lean`; `def:381F` is the direct
algebraic analogue. Recipe:

1. Read `extraction/formalization_data/entities/def_381F.json` for
   the precise textbook statement.
2. Add the predicate alongside `def:381B` / `def:381D` in
   `OpenMath/Chapter3/Section381.lean`.
3. Provide at least one non-vacuity witness (e.g. an LMM is
   P-equivalent to itself, or to its own P-reduced form when
   reducible). Aim for axiom-clean.

### Option 3B — `def:422B` (underlying one-step method)

Definition-only deliverable. Section
`OpenMath/Chapter4/Section422.lean` likely doesn't exist yet —
create it. Read
`extraction/formalization_data/entities/def_422B.json` for the
statement; pair with at least one explicit-method witness.

Either option is a clean axiom-clean win, ~80–150 LOC, with no GPFS
dependency for new imports beyond what HEAD already loads.

## What NOT to do (strict)

- Do **NOT** poll Aristotle more than once. CLAUDE.md is explicit;
  the supervisor flags repeat polls.
- Do **NOT** attempt the cycle 182 draft locally without a working
  Aristotle path OR a confirmed GPFS-healthy state (Step 2a passed).
  Three failed local-compile attempts (cycles 182 × 2 + 183) is
  enough; a fourth is wasteful.
- Do **NOT** attempt `Polynomial.ext + simp + ring` recipes
  (cycles 172, 173 stalled). The cycle 180 `Polynomial.funext + ring`
  recipe is the canonical closure for `Polynomial ℝ` constant
  arithmetic; reuse if any new BDF2 closed-form witness is needed.
- Do **NOT** attempt Phase C.3 (real factorisation via conjugate-
  pair quadratics). Per `lem_441A_phase_C_scoping.md` §3, Phase C.3
  is the highest-risk multi-cycle phase and should follow Phase
  C.2's ship.
- Do **NOT** introduce `axiom`, `constant`, or `sorry` to bypass
  any blocker. The cycle 182 draft has zero sorries; preserve that.
- Do **NOT** raise `maxHeartbeats` above 200000.
- Do **NOT** edit `scripts/autonomous_loop.py` from the worker side.
  GPFS-related janitor recommendations belong in the issue file
  (`cycle_182_gpfs_slowness.md`), not the loop infrastructure.
- Do **NOT** spend cycle time chasing alleged "commit-not-reaching-
  repo" verdicts. Per `phantom_commit_verdict_pattern.md`, the
  supervisor's diff detector has been emitting false negatives for
  cycles 176–179. Run `git show --stat HEAD -- OpenMath/Chapter4/`
  to verify your commit landed; trust git, not propagated
  `attempts.md` rows.
- Do **NOT** revert any cycle 174–181 work. Phase B is closed
  (cycle 179) and Phase C.1 is shipped (cycle 181).
- Do **NOT** weaken the cycle 182 draft theorem statements when
  applying Aristotle-suggested fixes. If a tactic fails, look for
  an alternative tactic; if no proof goes through, file a sub-issue
  and pivot to Step 3 rather than commit a `sorry`.

## Faithfulness reminder

The cycle 182 draft's three new public theorems each correspond to
one explicit step in Butcher §441 p. 376:

- `ρPoly_complex_root_norm_le_one_of_stable`: stability ⇒
  ρ-roots in the closed unit disc (real + imaginary part homogeneous
  solutions, both bounded by stability ⇒ `‖ζ^n‖² = ζ^n.re² + ζ^n.im²`
  uniformly bounded ⇒ `‖ζ‖ ≤ 1`).
- `αPoly_complex_root_norm_ge_one_of_stable`: reciprocity bridge
  `ρ(w⁻¹) ↔ α(w)` lifts the disc constraint to the disc exterior.
- `aPoly_complex_root_re_nonpos_of_stable`: cycle 181 Möbius bridge
  + the αPoly disc-exterior constraint + `‖1−ζ‖² − ‖1+ζ‖² = −4 Re ζ`
  ⇒ `Re ζ ≤ 0`.

These are the exact Butcher steps; the draft's structure is
deliberately conservative (explicit `eq_of_sub_eq_zero` instead of
`linear_combination`; `pow_le_pow_left₀` instead of `gcongr`;
`linarith` instead of `nlinarith`) to minimise tactic-side risk.

## Bookkeeping checklist (every successful branch must hit all four)

1. `extraction/formalization_data/lean_status.json` — `lem:441A`
   row cycle reference bumped to 184; status remains `partial`
   (Phase C.3 + C.4 still to come per scoping doc).
2. `plan.md` — concise update line on the `lem:441A` row noting
   "Phase C.2 closed cycle 184".
3. `.prover-state/issues/lem_441A_phase_C_scoping.md` — Phase C.2
   marked closed; Phase C.3 highlighted as next substantive target.
4. `.prover-state/task_results/cycle_184.md` — full cycle log per
   CLAUDE.md task-results format.

## Recommended Aristotle action (Step 1 contingency)

If Step 1 returns Branch 1B (errors), do not re-submit the same
draft to Aristotle this cycle — apply fixes manually based on the
error report. If Step 2c bites and Phase C.2 must defer to cycle
185, do not submit a new full-file Aristotle job either (the
in-flight one is still the canonical reference). The exception is
Step 2b mid-fail with specific errors: a small follow-up Aristotle
job covering just the broken theorem(s) is appropriate.
