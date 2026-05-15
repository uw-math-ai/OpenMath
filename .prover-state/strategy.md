# Cycle 289 strategy

## Context

Cycle 288 shipped axiom-clean `butcherShiftedLegendre_eleven` and
`butcherShiftedLegendre_recurrence_eleven` (the `n = 11` rung of the
(342f) ladder). The empirical evidence base for the general (342f)
recurrence now spans `n ∈ {2, 3, 4, 5, 6, 7, 8, 9, 10, 11}`. Aristotle
project `efe4940e-0931-4fb2-8549-7eafab20d7f7` (general (342f)
resubmission from cycle 285) was IN_PROGRESS at **20%** for two
consecutive cycle observations (cycle 287 saw 20% at 18:35 UTC, cycle
288 saw 20% at 18:51 UTC — flat for ~16 min). This is observation
**#2 of 3** in the cycle 285 three-stall protocol.

§342 status (axiom-clean, `partial`): (342a) orthogonality + (342b)
eval-one + (342c) eval-one-sub + (342d) general norm-square + (342e)
Rodrigues + (342f) at `n = 2..11` shipped. Open: general (342f)
recurrence, (342g) `n` distinct real zeros.

Repo sorry count = 0. Section441.lean still GPFS-blocked (43+
consecutive timeouts since cycle 182) — do NOT attempt.

## Priority 0 (mandatory, ~30s): single-poll Aristotle `efe4940e`

Run `mcp__aristotle__get_status` **once** on
`efe4940e-0931-4fb2-8549-7eafab20d7f7`. Record `status`,
`percent_complete`, and `last_updated_at` in the cycle's task results.
Do NOT re-poll later — single-poll discipline per CLAUDE.md.

Compare `percent_complete` against cycle 288's observation (20% at
18:51 UTC) to decide branching below.

## Branching decision tree

### Branch A: `efe4940e` COMPLETE or COMPLETE_WITH_ERRORS

This is the headline outcome. Skip all other branches; ship the
integration:

1. Download the proof with `mcp__aristotle__download_result project_id=efe4940e-0931-4fb2-8549-7eafab20d7f7`,
   extract via `mcp__aristotle__extract_result`. Read
   `ARISTOTLE_SUMMARY.md` carefully.
2. Read the actual Lean proof file. Cross-check it proves the target
   statement (Butcher's general (342f) three-term recurrence:
   `(n : ℝ) • butcherShiftedLegendre n
     = C (2*n - 1) * (C 2 * X - C 1) * butcherShiftedLegendre (n - 1)
       - C (n - 1) * butcherShiftedLegendre (n - 2)`
   for `n ≥ 2`, or whatever exact form Aristotle delivers).
3. If Aristotle introduces non-trivial helper lemmas, follow cycle
   281's pattern for `butcherShiftedLegendre_norm_sq`: factor them
   into a new dedicated file
   `OpenMath/Chapter3/Section342RecurrenceHelpers.lean` in namespace
   `OpenMath.Chapter3.Section342Helpers`. Mirror cycle 281's
   `Section342NormSqHelpers.lean` (~210 LOC reusable polynomial /
   integral lemmas), keeping `Section342.lean` itself focused on
   `butcherShiftedLegendre`-specific theorems.
4. If COMPLETE_WITH_ERRORS: identify the specific edits needed
   (likely namespace fixes per cycle 277's integration pattern, simp-
   set reordering, or import additions). Apply them locally. Do NOT
   blindly trust Aristotle's stub replacements for our codebase's
   existing definitions — only adopt the genuinely new content.
5. Verify the integrated headline theorem axiom-clean via
   `mcp__lean-lsp__lean_verify` (expect
   `[propext, Classical.choice, Quot.sound]`). Add specialization
   cross-checks: confirm cycles 282–288's `_recurrence_two..._eleven`
   ladder rungs follow as numerical witnesses of the general theorem
   via `rw [← <general theorem>] at` or as standalone re-proofs.
6. Update `lean_status.json` `lem:342A` row with cycle 289 trace;
   keep `status: partial` (since (342g) still open); update
   `lean_symbol` to point at the general theorem.
7. Update `plan.md` `lem:342A` bullet with cycle 289 ship line.
8. **P3 stretch (if time permits, ~10 min)**: fire-and-forget
   Aristotle on (342g) per `.prover-state/issues/lem_342A_g_zeros_scoping.md`.
   Submit project with cycles 271–289 as cited prerequisites
   (`butcherShiftedLegendre_orthogonal`, `_norm_sq`,
   `_recurrence`, `_natDegree`, `_eval_one`, `_eval_zero`,
   `_rodrigues`, the explicit `_zero..._eleven` forms). Cycle 290
   polls.

### Branch B: `efe4940e` IN_PROGRESS at ≥30%

Aristotle made real progress beyond the cycle 287/288 plateau. Skip
ladder extension; let Aristotle finish. Ship 1–2 axiom-clean cross-
check theorems extending cycle 287's pattern to fill an odd-`n`
parity-coverage gap:

- **`butcherShiftedLegendre_nine_explicit_eval_zero`** —
  `(butcherShiftedLegendre 9).eval 0 = -1`. Cross-validates (342c) at
  odd `n = 9`. Recipe (mirrors cycle 287's `_ten_explicit_eval_zero`,
  ~3 lines):
  ```lean
  theorem butcherShiftedLegendre_nine_explicit_eval_zero :
      (butcherShiftedLegendre 9).eval 0 = -1 := by
    rw [butcherShiftedLegendre_nine]
    simp [Polynomial.eval_add, Polynomial.eval_sub,
          Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
  ```

- **`butcherShiftedLegendre_eleven_explicit_eval_one`** —
  `(butcherShiftedLegendre 11).eval 1 = 1`. Cross-validates (342b) at
  `n = 11`. Recipe mirrors cycle 287's `_ten_explicit_eval_one`:
  ```lean
  theorem butcherShiftedLegendre_eleven_explicit_eval_one :
      (butcherShiftedLegendre 11).eval 1 = 1 := by
    rw [butcherShiftedLegendre_eleven]
    simp [Polynomial.eval_add, Polynomial.eval_sub,
          Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
    norm_num
  ```

- **`butcherShiftedLegendre_eleven_explicit_eval_zero`** —
  `(butcherShiftedLegendre 11).eval 0 = -1`. Cross-validates (342c) at
  odd `n = 11`. ~3 lines, same recipe as `_nine_explicit_eval_zero`.

These exercise odd-`n` parity at `n ∈ {9, 11}` (cycle 287 covered only
even `n = 10`). Place after cycle 287's cross-check theorems.

### Branch C: `efe4940e` IN_PROGRESS at 21%–29%

Some advance from cycle 288's 20%, but slow. Treat as Branch B (ship
cross-checks); reset stall count for cycle 290. Do NOT cancel.

### Branch D: `efe4940e` IN_PROGRESS at exactly 20% (or below), or FAILED, or CANCELLED

Three-stall threshold met (per cycle 285 protocol: cycle 287 = 20%,
cycle 288 = 20%, cycle 289 = 20% would be observation #3). Time for
manual closure.

1. **Cancel** `efe4940e` via `mcp__aristotle__cancel_project`.
2. **Open issue file** `.prover-state/issues/lem_342A_342f_manual_closure_plan.md`
   mirroring the cycle 285 `lem_441A_phase_C_scoping.md` precedent
   (full §1 textbook statement, §2 distilled mathematical content,
   §3 project-hook inventory, §4 gap inventory, §5 phase decomposition,
   §6 risk assessment, §7 cycle-290 entry point). Recommended path:

   **Path A — Polynomial-degree closure**. Define
   ```
   Q n := (n : ℝ) • butcherShiftedLegendre n
        − C (2*n − 1) · (C 2 · X − C 1) · butcherShiftedLegendre (n−1)
        + C (n − 1) · butcherShiftedLegendre (n−2)
   ```
   (the LHS − RHS of the target recurrence). Three-phase plan:
   - **Phase A.1** (cycle 290): show `Q.natDegree < n`. Both sides
     have degree ≤ `n` (LHS is `n • P_n^*` with degree `n`; RHS top
     block is `(2n−1) · (2X − 1) · P_{n−1}^*` with degree `1 + (n−1)
     = n`); the leading coefficients cancel via the binomial identity
     `n · C(2n, n) = 2 · (2n − 1) · C(2n − 2, n − 1)` (paper-checked:
     both reduce to `(2n)! / ((n − 1)! · n!)`). Use cycle 281's
     `butcherShiftedLegendre_leadingCoeff` + `Polynomial.natDegree`
     arithmetic. Estimated 80–120 LOC.
   - **Phase A.2** (cycle 291): show `∫₀¹ Q · butcherShiftedLegendre k
     = 0` for all `k ∈ {0, 1, ..., n−2}`. The `n • P_n^*` and `C(n−1)
     · P_{n−2}^*` summands vanish by cycle 277's
     `butcherShiftedLegendre_orthogonal` (since `deg P_k^* = k < n`);
     the cross-term `(2X − 1) · P_{n−1}^* · P_k^*` requires the
     observation that `2X − 1 = -P_1^*` (paper-check via cycle 273's
     `butcherShiftedLegendre_one : P_1^* = C 2 * X - C 1`), so the
     cross-term reduces to `-∫₀¹ P_1^* · P_{n−1}^* · P_k^*` which
     vanishes for `k ≤ n − 2` by orthogonality applied to the product
     `P_{n−1}^* · P_k^*` (which has degree ≤ `n − 2`). Estimated
     100–150 LOC.
   - **Phase A.3** (cycle 292): conclude `Q = 0` from Phase A.1 + A.2.
     The basis `{P_0^*, ..., P_{n−1}^*}` spans the polynomial space
     `Polynomial.degreeLT ℝ n`; any `Q ∈ degreeLT n` orthogonal to
     all basis elements is zero. Use `Polynomial.degreeLT` +
     `LinearMap.span` + a Gram-Schmidt-style argument. Estimated
     60–100 LOC.

   Total: 3 cycles (290–292), all axiom-clean targets, no new Mathlib
   gaps.

3. **Ship the Phase A.1 first deliverable in cycle 289 itself**
   (after the issue file). Two sub-steps:

   a. **Helper lemma** — the binomial identity:
      ```lean
      private lemma n_mul_choose_two_n_n_eq (n : ℕ) (hn : 1 ≤ n) :
          (n : ℝ) * (Nat.choose (2 * n) n : ℝ)
            = 2 * ((2 * n - 1 : ℕ) : ℝ) * (Nat.choose (2 * n - 2) (n - 1) : ℝ)
      ```
      Proof: cast all `Nat.choose` via `Nat.choose_eq_factorial_div_factorial`
      + `field_simp` + `Nat.factorial_succ` × 2 + `ring`. Or close
      directly via `decide`-helpers if the values can be computed
      arithmetically (probably not for general `n`). Estimated ~30–50 LOC.

   b. **Main residual-degree theorem**:
      ```lean
      theorem recurrence_residual_natDegree_lt (n : ℕ) (hn : 2 ≤ n) :
          ((n : ℝ) • butcherShiftedLegendre n
            - Polynomial.C ((2 * n - 1 : ℕ) : ℝ)
              * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
              * butcherShiftedLegendre (n - 1)
            + Polynomial.C ((n - 1 : ℕ) : ℝ)
              * butcherShiftedLegendre (n - 2)).natDegree < n
      ```
      Proof: bound the natDegree of each summand, then show the leading-
      coefficient cancellation via `Polynomial.natDegree_sub_lt_of_leadingCoeff_eq`
      (or similar; verify exact name with `lean_local_search "natDegree_sub_lt"`).
      Use cycle 281's `butcherShiftedLegendre_natDegree` and
      `butcherShiftedLegendre_leadingCoeff`. Estimated 80–120 LOC.

   If the LOC budget for (a)+(b) exceeds 150, ship only (a) in cycle
   289 + the issue file + cancellation, and defer (b) to cycle 290.
   Phase A.1 must be axiom-clean — no sorries.

## What NOT to do

- **Do NOT re-poll Aristotle** (single-poll per CLAUDE.md).
- **Do NOT ship `n = 12` or higher ladder rung**. Per cycle 285's
  protocol and cycle 288's observation, the empirical base at `n ∈
  {2..11}` is sufficient. Further ladder extension provides no new
  information; pivot to manual closure (Branch D) or cross-checks
  (Branch B).
- **Do NOT start (342g) manual work** unless Branch A succeeds.
  (342g) has its own scoping doc (`lem_342A_g_zeros_scoping.md`);
  fire-and-forget Aristotle on (342g) is fine post-(342f) (Branch A
  P3), but manual work on (342g) is out of scope until (342f) lands.
- **Do NOT attempt `Section441.lean`** — 43+ consecutive GPFS
  timeouts since cycle 182. Skip per
  `.prover-state/issues/cycle_182_gpfs_slowness.md`.
- **Do NOT raise `maxHeartbeats`** above 200000 (CLAUDE.md). If a
  proof stalls, decompose.
- **Do NOT introduce `axiom`/`constant`** declarations.
- **Do NOT introduce sorries**. Cycles 149/200/201 all rolled back
  sorry-first scaffolds; cycle 289's deliverables must be axiom-clean
  or skipped entirely.
- **Do NOT modify `scripts/autonomous_loop.py`** — loop-maintainer
  territory per `tautology_scanner_false_positives.md`.
- **Do NOT pursue a definitionally-different Möbius-style or Pascal-
  identity manual closure for (342f)**. Cycle 273's task results
  documented those paths as too complex without (342a) infrastructure;
  with (342a) + (342d) + Rodrigues now in hand, Path A above (degree-
  bound + orthogonality basis) is the clean route.
- **Do NOT trust supervisor "commit-not-reaching-repo" verdicts
  without git verification**. The phantom verdict pattern persists
  (cycles 008, 035, 073, 170, 176–179, 196 — see
  `.prover-state/issues/phantom_commit_verdict_pattern.md`). Always
  run `git show --stat <sha>` before reacting to such a verdict.

## Pre-flight verification commands

Before declaring the cycle done, run:

```bash
lake env lean OpenMath/Chapter3/Section342.lean
lake env lean OpenMath/Chapter3.lean
grep -c "sorry" OpenMath/Chapter3/Section342.lean   # expect 0
```

If Branch A produced a new helper file:

```bash
lake env lean OpenMath/Chapter3/Section342RecurrenceHelpers.lean
```

For each new public theorem, run `mcp__lean-lsp__lean_verify
OpenMath.Chapter3.Section342.<symbol>` and confirm axioms are
`[propext, Classical.choice, Quot.sound]` only.

## Bookkeeping checklist

- [ ] `.prover-state/task_results/cycle_289.md` written (Worked on /
      Approach / Result / Faithfulness check / Dead ends / Discovery /
      Suggested next approach sections).
- [ ] `extraction/formalization_data/lean_status.json` `lem:342A` row
      updated with cycle 289 trace.
- [ ] `plan.md` `lem:342A` bullet appended with cycle 289 line.
- [ ] If Branch D: new issue file
      `.prover-state/issues/lem_342A_342f_manual_closure_plan.md`
      opened; Aristotle `efe4940e` cancelled; Phase A.1 helper +
      main theorem shipped (or just helper + deferral note if the
      main theorem exceeds budget).
- [ ] `git add` + `git commit` + `git push` (only if there are
      changes).
