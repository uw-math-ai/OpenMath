# Cycle 288 Strategy

## Context summary

- **Repo state**: HEAD `419d4a3` — cycle 287 polled Aristotle (20% IN_PROGRESS,
  +9pp from cycle 286's 11%), shipped two axiom-clean non-vacuity cross-check
  theorems anchoring cycle 286's `butcherShiftedLegendre_ten` to (342b)/(342c).
  Sorry count: **0**.
- **Current target**: `lem:342A` clause (342f) — general three-term recurrence
  `(n : ℝ) • P_n^* = C(2n-1) · (2X - 1) · P_{n-1}^* − C(n-1) · P_{n-2}^*` for `n ≥ 2`.
- **Aristotle project**: `efe4940e-0931-4fb2-8549-7eafab20d7f7` (strengthened
  resubmission from cycle 285).
- **Last observed status** (cycle 287 poll, 2026-05-15 18:35 UTC, ~32 min after submission):
  `IN_PROGRESS / 20%` — up +9pp from cycle 286's 11% observation at 18:19 UTC.
  Pace ~+9pp / 16 min; linear extrapolation puts completion at ~21:00 UTC, which
  cycle 288 may catch.
- **Empirical ladder**: explicit recurrence witnesses shipped for `n ∈ {2,...,10}`
  (cycles 282–286) plus cycle 287's two cross-check theorems anchoring the
  `n = 10` form to (342b)/(342c). Sorry count: 0.
- **§441 GPFS pathology**: 43+ consecutive timeouts since cycle 182.
  **Do NOT** attempt to compile or modify `OpenMath/Chapter4/Section441.lean`
  this cycle. See `.prover-state/issues/cycle_182_gpfs_slowness.md`.

## Priority 0 (mandatory, ~30 seconds): single Aristotle poll

Run `mcp__aristotle__get_status` **once** on project
`efe4940e-0931-4fb2-8549-7eafab20d7f7`. Record `status`, `percent_complete`,
and `last_updated_at`. **Do NOT re-poll later in the cycle** — CLAUDE.md is
explicit on single-poll-per-cycle discipline.

Based on the result, branch as follows.

## Priority 1: branch on poll result

### Branch A — `COMPLETE` or `COMPLETE_WITH_ERRORS`

The general (342f) recurrence proof is back. Integrate it as the cycle 288
headline deliverable.

1. Download the proof with `mcp__aristotle__download_result project_id=efe4940e-0931-4fb2-8549-7eafab20d7f7`.
2. Extract the file with `mcp__aristotle__extract_result`.
3. **Read the proof carefully** before integrating. Check:
   - Does it use any helper lemmas not already in `Section342.lean` /
     `Section342NormSqHelpers.lean`? If so, prepare to land them in a new file
     `OpenMath/Chapter3/Section342RecurrenceHelpers.lean` (mirror cycle 281's
     `Section342NormSqHelpers.lean` pattern — namespace
     `OpenMath.Chapter3.Section342Helpers`, axiom-clean, ~150–250 LOC).
   - Are there any Aristotle-substituted stubs / axioms for cycles 271–281
     results? Replace them with citations to the genuine theorems already
     in our codebase (`butcherShiftedLegendre_eval_one`, `_eval_one_sub`,
     `_eval_zero`, `_natDegree`, `_rodrigues`, `_orthogonal`, `_norm_sq`,
     and the explicit `_zero` through `_ten` forms).
   - Does it apply at the right type signature? The target is morally:
     ```
     theorem butcherShiftedLegendre_recurrence {n : ℕ} (hn : 2 ≤ n) :
         (n : ℝ) • butcherShiftedLegendre n
           = Polynomial.C ((2 * n : ℝ) - 1) * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
               * butcherShiftedLegendre (n - 1)
             - Polynomial.C ((n : ℝ) - 1) * butcherShiftedLegendre (n - 2)
     ```
     Verify against Aristotle's exact statement; adjust if Aristotle used
     different parenthesization or expressed the `(n-1) / (n-2)` indices as
     `Nat.pred` etc.
4. **Ship in `OpenMath/Chapter3/Section342.lean`** after the cycle 286 `_ten`
   rung. Add helper imports as needed.
5. **Verify axiom-clean**: run `mcp__lean-lsp__lean_verify` on the new
   `butcherShiftedLegendre_recurrence` theorem. Required:
   `[propext, Classical.choice, Quot.sound]` only.
6. **Cross-check via specialization**: add 1–2 `example` blocks confirming
   the general theorem specializes to cycles 282–286's ladder rungs. If
   `rfl` bridging fails (likely due to `(n : ℝ) - 1` not reducing
   definitionally for fixed `n`), accept the redundancy — the ladder rungs
   stand on their own as named theorems.
7. **Do NOT delete** cycles 282–286's `_recurrence_two..._ten` ladder rung
   theorems. They are valuable as cross-validation witnesses.
8. Update `extraction/formalization_data/lean_status.json`:
   `lem:342A` cycle bumped to 288, `lean_symbol` switched to
   `butcherShiftedLegendre_recurrence`. Status stays `partial` until (342g)
   `n` distinct real zeros also lands.
9. Update `plan.md` `lem:342A` row with the cycle 288 closure note.
10. Run `lake env lean OpenMath/Chapter3.lean` to confirm no aggregator
    regression.

### Branch B — `IN_PROGRESS` with `percent_complete ≥ 30%`

Aristotle continues to make progress (≥10pp advance from cycle 287's 20%).
Adopt the cycle 287 pattern: ship a **small non-vacuity / cross-check theorem**
as the cycle deliverable, without competing computational work.

**Preferred deliverable**: extend cycle 287's two cross-check theorems to
cover the `n = 9` and `n = 8` cases (downward along the ladder). Recipe is
the cycle 287 idiom — 3–5 line proofs each:

```lean
theorem butcherShiftedLegendre_nine_explicit_eval_zero :
    (butcherShiftedLegendre 9).eval 0 = -1 := by
  rw [butcherShiftedLegendre_nine]
  simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_one]
  norm_num
```

(Odd `n = 9` gives `(-1)^9 = -1` at `x = 0` per (342c) parity.)

```lean
theorem butcherShiftedLegendre_eight_explicit_eval_one :
    (butcherShiftedLegendre 8).eval 1 = 1 := by
  rw [butcherShiftedLegendre_eight]
  simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_one]
  norm_num
```

(Even `n = 8` gives `+1` at `x = 1` per (342b).)

Place them after cycle 287's `butcherShiftedLegendre_ten_explicit_eval_zero`
in `OpenMath/Chapter3/Section342.lean`. Both must verify axiom-clean.

Do **NOT** ship a new `n = 11` ladder rung in Branch B. The progress signal
is healthy; let Aristotle finish without competing computational work.

### Branch C — `IN_PROGRESS` at `<30%` (regressed or stalled near 20%)

This is observation #2 of 3 in the cycle 285 three-stall protocol (a flat
or weakly-advancing observation since cycle 287's 20%). **Do NOT cancel yet.**
Ship the `n = 11` ladder rung as the empirical backstop.

Recipe — mechanical port of cycle 286's `n = 10`:

1. **Compute coefficients via Python before writing Lean code.** Pattern:
   ```python
   from math import comb
   n = 11
   # (butcherShiftedLegendre n).coeff k = (-1)^k * C(n, k) * C(n+k, k)
   coeffs = [(-1)**k * comb(n, k) * comb(n + k, k) for k in range(n + 1)]
   print(coeffs)
   # Cross-check (342b): coeffs sum to 1 (since P_n^*(1) = 1)
   assert sum(coeffs) == 1
   # Cross-check (342c) at x = 0: coeff[0] = (-1)^n
   assert coeffs[0] == (-1)**n
   ```
   Expected leading at `k = 11`: `(-1)^11 · C(11,11) · C(22,11) =
   -1 · 1 · 705432 = -705432`.

2. **Write `butcherShiftedLegendre_eleven`** following cycle 285's
   `_nine` template (odd `n`):
   - `ext k`, `match k with | 0 => ... | 1 => ... | ... | 11 => ... | k + 12 => Polynomial.coeff_eq_zero_of_natDegree_lt`.
   - Each `0..11` arm closes by `simp [coeff_C_mul, coeff_map,
     coeff_shiftedLegendre]; norm_num` with appropriate `Nat.choose`
     `decide`-helpers (e.g. `Nat.choose 13 11`, `Nat.choose 22 11`).

3. **Write `butcherShiftedLegendre_recurrence_eleven`** following
   cycle 285's `_recurrence_nine` template:
   ```lean
   theorem butcherShiftedLegendre_recurrence_eleven :
       (11 : ℝ) • butcherShiftedLegendre 11
         = Polynomial.C 21 * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
             * butcherShiftedLegendre 10
           - Polynomial.C 10 * butcherShiftedLegendre 9 := by
     apply Polynomial.funext
     intro x
     rw [butcherShiftedLegendre_eleven, butcherShiftedLegendre_ten,
         butcherShiftedLegendre_nine]
     simp [Polynomial.eval_smul, Polynomial.eval_add, Polynomial.eval_sub,
           Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
           Polynomial.eval_X, Polynomial.eval_one, smul_eq_mul]
     ring
   ```
   Coefficient check: `(2n - 1, n - 1) = (21, 10)` at `n = 11`.

4. **Verify axiom-clean** via `mcp__lean-lsp__lean_verify` on both.
5. Update `lean_status.json` cycle stamp to 288, status `partial`. Note in
   `plan.md` that this is observation #2 of 3 stalls.

### Branch D — `FAILED`, `CANCELLED`, or status confused

The Aristotle attempt is dead. Execute the cycle 285 three-stall protocol:

1. **Cancel** the project (if not already terminal) with
   `mcp__aristotle__cancel_project project_id=efe4940e-0931-4fb2-8549-7eafab20d7f7`.
2. **Open** `.prover-state/issues/lem_342A_342f_manual_closure_plan.md`
   documenting the multi-cycle manual closure plan. Structure:
   - **§1**: Textbook statement of (342f) verbatim from
     `extraction/formalization_data/entities/lem_342A.json`.
   - **§2**: Distilled mathematical content. Note that the recurrence is
     equivalent to a polynomial identity `LHS − RHS = 0` where both sides
     have `natDegree ≤ n`.
   - **§3**: Three closure paths:
     - **Path A — `Q := LHS − RHS`, prove `Q = 0` via orthogonality basis**.
       Show `Q.natDegree < n` and `∫₀¹ Q · P_k^* = 0` for all `k ≤ n−1`
       using cycle 277's `butcherShiftedLegendre_orthogonal`. Then `Q = 0`
       follows from the basis property (any degree-< n polynomial orthogonal
       to all `P_k^*` with `k < n` is zero by dimension counting). Estimated
       2–3 cycles.
     - **Path B — Coefficient-by-coefficient comparison via `Polynomial.ext`**.
       Match each coefficient of LHS and RHS using `Nat.choose` identities
       (Pascal-style). High LOC, mechanical but tedious. Estimated 3–4 cycles.
     - **Path C — Continue ladder to `n = 12, 13, ...` and avoid the general
       claim**. Each ladder rung is ~70 LOC, axiom-clean. Pragmatic but does
       not close (342f) generally.
   - **§4**: Recommended path (A), with cycle-by-cycle decomposition.
   - **§5**: Cycle 289 entry point.
3. **Ship `n = 11` ladder rung** (using the Branch C recipe above) as the
   first step in Path C while planning Path A. This gives the cycle a
   concrete deliverable.

## Priorities NOT to pursue

- **Do NOT** attempt to compile `OpenMath/Chapter4/Section441.lean`
  (43+ consecutive GPFS timeouts since cycle 182).
- **Do NOT** re-poll Aristotle (single-poll discipline per CLAUDE.md).
- **Do NOT** ship `n = 12` or higher in Branch C/D — `n = 11` is sufficient
  to mark observation/backstop. Higher rungs are diminishing returns.
- **Do NOT** modify `scripts/autonomous_loop.py` (loop-maintainer territory;
  see `.prover-state/issues/phantom_commit_verdict_pattern.md`).
- **Do NOT** introduce sorries, axioms, or `maxHeartbeats` bumps.
- **Do NOT** attempt (342g) `n` distinct real zeros this cycle. Per
  `.prover-state/issues/lem_342A_g_zeros_scoping.md`, it should follow
  (342f) closure (Branch A), not precede it.
- **Do NOT** rewrite cycle 287's two cross-check theorems
  (`butcherShiftedLegendre_ten_explicit_eval_one` and `_eval_zero`).
- **Do NOT** start `lem:310B` Phase A.3 or other multi-cycle work. The
  cycle 288 focus is on (342f) closure / continued progress on Aristotle.
- **Do NOT** attempt to compose Aristotle's general recurrence with the
  ladder rungs to reduce LOC. Keep both forms — the ladder rungs are
  empirical regression witnesses, the general theorem is the abstract content.
- **Do NOT** ship a Branch B deliverable AND a Branch C ladder rung in
  the same cycle. Pick one branch based on the poll result.

## Verification checklist (run before commit)

- `lake env lean OpenMath/Chapter3/Section342.lean` exit 0.
- `lake env lean OpenMath/Chapter3.lean` (aggregator) exit 0.
- `grep -c "sorry" OpenMath/Chapter3/Section342.lean` = 0.
- `mcp__lean-lsp__lean_verify` on **every** new theorem returns
  `[propext, Classical.choice, Quot.sound]` only.
- Tautology-scanner clean (no `exact h_<name>` or `:= h_<name>` patterns
  in proofs that aren't doing real work).
- Faithfulness check per CLAUDE.md for any new `def`/`theorem`.

## Cycle 289+ outlook

- **Branch A landed**: pivot cycle 289 to (342g) `n` distinct real zeros
  per `.prover-state/issues/lem_342A_g_zeros_scoping.md` §5. Estimated
  1–2 cycles; can be fire-and-forget to Aristotle since all of
  (342a)/(342b)/(342c)/(342d)/(342e)/(342f) are now available as citable
  prerequisites.
- **Branch B (continued progress)**: cycle 289 polls again, expects
  ~40%+ at that point. Continue with more cross-check theorems or
  small witnesses until Aristotle completes.
- **Branch C (stalled, observation #2)**: cycle 289 is observation #3
  of 3. If status has still not advanced, cancel and pivot to manual
  closure per Branch D's plan.
- **Branch D (failed)**: cycle 289 executes Path A from the manual
  closure plan (define `Q := LHS − RHS`, show `Q.natDegree < n`, prove
  `∫₀¹ Q · P_k^* = 0` for `k < n`, conclude `Q = 0`).

## Suggested commit message

```
Cycle 288 — §342 (342f) [Aristotle <status>] + <deliverable>.
```

Replace `<status>` with the observed Aristotle status (e.g.
`COMPLETE`, `20% IN_PROGRESS`, `30% IN_PROGRESS`, `CANCELLED`) and
`<deliverable>` with the cycle's main contribution (e.g. "general
recurrence integrated", "`n=9,8` explicit cross-checks", "`n=11`
ladder rung", "manual closure plan opened").
