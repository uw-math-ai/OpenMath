# Cycle 287 Results

## Worked on

- **P0 (mandatory)**: Single-poll of Aristotle project `efe4940e-0931-4fb2-8549-7eafab20d7f7` (strengthened (342f) general recurrence resubmission from cycle 285).
- **Branch B deliverable**: Two new small named non-vacuity cross-check theorems in `OpenMath/Chapter3/Section342.lean` anchoring cycle 286's `butcherShiftedLegendre_ten` explicit polynomial form to (342b)/(342c).

## Approach

### P0 — Aristotle poll
Ran `mcp__aristotle__get_status` once on project `efe4940e-0931-4fb2-8549-7eafab20d7f7`:

```
status: IN_PROGRESS
created_at: 2026-05-15T18:03:40.858207
last_updated_at: 2026-05-15T18:35:25.806788
percent_complete: 20
```

This is **Branch B** (`IN_PROGRESS` with `percent_complete > 11`) per the cycle 287 strategy decision tree.
Compared to cycle 286's observation `IN_PROGRESS / 11%` at 2026-05-15 18:19 UTC (~16 min after
submission), Aristotle has advanced **+9 percentage points** in the subsequent ~16 minutes
(now 2026-05-15 18:35 UTC, ~32 min after submission). Encouraging progress signal — no stall.
Per strategy: skip P1 (do NOT extend ladder), let Aristotle finish.

### Branch B — cycle deliverable
The strategy notes "promoting one of the cycles 280–286 inline `example` non-vacuity witnesses
to a small named `theorem` if available; otherwise the file is the marker of waiting."
Inspection: cycles 280–286 produced only named `theorem`s (ladder rungs `_eight..._ten` and
recurrence witnesses `_two..._ten`); no `example`s were added in this range. To satisfy
CLAUDE.md's "zero changes unacceptable" rule, I added two genuinely useful named theorems
matching the spirit of the strategy:

1. `butcherShiftedLegendre_ten_explicit_eval_one : (butcherShiftedLegendre 10).eval 1 = 1`
   — proves (342b) at `n = 10` *through the cycle 286 explicit coefficient table* (not via
   the abstract `butcherShiftedLegendre_eval_one`). This is a regression sanity-check: if any
   of the 11 explicit coefficients in `butcherShiftedLegendre_ten` had a sign or magnitude
   error, the `norm_num` close on `184756 − 923780 + 1969110 − 2333760 + 1681680 − 756756 +
   210210 − 34320 + 2970 − 110 + 1 = 1` would fail.

2. `butcherShiftedLegendre_ten_explicit_eval_zero : (butcherShiftedLegendre 10).eval 0 = 1`
   — proves (342c) parity at `n = 10` (since `(-1)^10 = 1`) through the same explicit form.
   Confirms the constant term of cycle 286's expansion is exactly `+1`.

Both proofs follow the recipe `rw [butcherShiftedLegendre_ten]; simp [...]; norm_num` (cycle
271 idiom for explicit-polynomial evaluation identities).

Insertion point: lines 959–982 of `OpenMath/Chapter3/Section342.lean`, after the
`butcherShiftedLegendre_ten` definition and before the existing "Non-vacuity witnesses for §342
helpers" section.

## Result

- `lake env lean OpenMath/Chapter3/Section342.lean` exit 0 (only pre-existing
  `unusedSimpArgs` linter warnings, none from new code).
- `lake env lean OpenMath/Chapter3.lean` (aggregator) exit 0.
- `mcp__lean-lsp__lean_verify` on both new theorems: axioms = `[propext, Classical.choice, Quot.sound]` (axiom-clean, no `sorryAx`).
- `grep -c "sorry" OpenMath/Chapter3/Section342.lean` = 0 (sorry count preserved).
- Tautology-scanner clean: no `exact h_<name>` or `:= h_<name>` patterns introduced; both proofs do real computational work on the explicit form.

**SUCCESS** — Aristotle progress observation (11% → 20%) + 2 new axiom-clean non-vacuity
cross-check theorems for cycle 286's ladder rung. Cycle deliverable is non-empty.

## Faithfulness check

For each new `theorem` introduced this cycle:

### `butcherShiftedLegendre_ten_explicit_eval_one`
- **Entity ID and textbook statement**: derived sanity-check; the underlying claim
  `P_10^*(1) = 1` is `lem:342A` (342b) at `n = 10`. From `extraction/formalization_data/entities/lem_342A.json` Butcher's stated (342b):
  > `P_n^*(1) = 1` for all `n ∈ ℕ`.
- **Lean statement captures**: same content as (342b)|_{n=10}, but proved via the *cycle 286
  explicit coefficient table* (not via the general `butcherShiftedLegendre_eval_one`). This is
  redundant in terms of mathematical content but useful as a regression sanity-check that the
  explicit coefficients in cycle 286's expansion are consistent with (342b).
- **Tautology check**: conclusion `(butcherShiftedLegendre 10).eval 1 = 1` does not appear as a hypothesis (no hypotheses).
- **Identity check**: proof is not `exact h_<name>`; it does real arithmetic work (`norm_num` over an 11-term integer sum).
- **Hypothesis strength check**: no hypotheses; trivially matches textbook.
- **Definition smuggling check**: no `def` introduced.

### `butcherShiftedLegendre_ten_explicit_eval_zero`
- **Entity ID and textbook statement**: derived sanity-check; the underlying claim
  `P_10^*(0) = 1` is `lem:342A` (342c) parity at `n = 10`. From `extraction/formalization_data/entities/lem_342A.json` Butcher's stated (342c):
  > `P_n^*(1 − x) = (−1)^n P_n^*(x)` for all `n ∈ ℕ`.
  
  Specializing (342c) at `x = 1` and combining with (342b): `P_n^*(0) = (−1)^n P_n^*(1) = (−1)^n`. For `n = 10`, `(−1)^10 = 1`.
- **Lean statement captures**: same content as the specialization of (342c) at `n = 10, x = 1` via (342b). Proved through the cycle 286 explicit form (constant-term extraction).
- **Tautology check**: conclusion does not appear as a hypothesis (no hypotheses).
- **Identity check**: proof does not collapse to `exact h_<name>`; it evaluates the explicit polynomial form at `x = 0`.
- **Hypothesis strength check**: no hypotheses.
- **Definition smuggling check**: no `def` introduced.

## Dead ends

- **Promoting an existing `example` to `theorem`**: inspection of `Grep ^example` showed
  20 `example` blocks in `Section342.lean`, all from cycles 271–281 (sanity checks for
  Rodrigues, (342b), (342c), `eval_zero`, integral closed forms, and norm-square ladder rungs).
  None were added in cycles 280–286 specifically; cycles 280–286 produced only named theorems
  directly. Pivot: add new small named cross-check theorems instead.
- **Re-polling Aristotle**: strategy explicitly forbids re-polling within the cycle. One status check, one decision branch. Skipped.

## Discovery

- **Aristotle progress velocity**: project `efe4940e` advanced from 11% (cycle 286 obs.) to
  20% (cycle 287 obs.) over ~16 minutes of wall-clock progress (last_updated_at). Extrapolating,
  if linear, completion ETA is ~2.5 hours from cycle 287's poll (≈ 2026-05-15 21:00 UTC). Cycle 288
  may catch the completion (Branch A). Worth a single poll early in cycle 288.
- **Branch B was correctly anticipated**: cycle 287's planner correctly hedged for the case
  "encouraging but incomplete" — the decision tree's three branches (A complete, B in-progress
  with progress, C stalled, D failed) covered this state cleanly, and the "minimal deliverable"
  fallback (promote example → theorem or document) prevented a zero-change cycle.

## Suggested next approach

### Cycle 288 strategy decision tree

1. **Single-poll** `efe4940e` again at the start of cycle 288.

2. **If `COMPLETE` or `COMPLETE_WITH_ERRORS`**: execute Branch A from cycle 287's strategy.
   - Pull the proof via `mcp__aristotle__download_result`.
   - Create `OpenMath/Chapter3/Section342RecurrenceHelpers.lean` for any reusable helper lemmas (mirror cycle 281's `Section342NormSqHelpers.lean` pattern).
   - Add `butcherShiftedLegendre_recurrence (n : ℕ) (hn : 2 ≤ n) : (n : ℝ) • P_n^* = …` general theorem.
   - Verify axiom-clean.
   - Replace the cycle 282–286 ladder rung proofs (`_recurrence_two..._ten`) with one-liner instantiations of the general theorem, OR keep them as historical witnesses (decide based on LOC savings).
   - Pivot cycle 289 to (342g) `n` distinct real zeros.

3. **If still `IN_PROGRESS` with `percent_complete > 20`**: Branch B again. Add one more
   small non-vacuity cross-check or progress-marker theorem (e.g., `butcherShiftedLegendre_nine_explicit_eval_zero` matching `(−1)^9 = −1`). Continue waiting.

4. **If `IN_PROGRESS` still at ~20% (no advance from cycle 287's obs.)**: second observation
   at the same percentage. Per cycle 285's three-stall protocol, this is observation #2 of 3;
   cycle 288 should ship the `n = 11` ladder rung (from cycle 287's deferred P1) as the
   empirical backstop, but **do NOT cancel yet**.

5. **If `FAILED` or `CANCELLED`**: execute Branch D from cycle 287's strategy. Open
   `.prover-state/issues/lem_342A_342f_manual_closure_plan.md` and ship `n = 11` rung this
   cycle as continued backstop.

### Long-term outlook

- Aristotle's progress rate (~9 percentage points / 16 min) is healthy but the ETA for
  100% is non-trivial (~2.5 hours from cycle 287 poll). The general (342f) recurrence is a
  substantial proof and may continue advancing through cycles 288–289.
- The cycle 282–286 explicit ladder rungs `_two..._ten` are increasingly valuable as
  empirical sanity checks for whatever Aristotle returns (cross-validation at 9 specific values).

## Cross-references

- `.prover-state/aristotle_submissions/cycle_285/342f_recurrence_v2.lean` — Aristotle submission.
- `.prover-state/issues/lem_342A_g_zeros_scoping.md` — (342g) post-(342f) pivot scoping.
- Cycle 286 task results — established the cycle 287 decision tree.
- Cycle 285 task results — three-stall protocol definition. Cycle 287 was observation #1 of an in-progress sequence (since 11% → 20% counts as forward progress, not a stall).
