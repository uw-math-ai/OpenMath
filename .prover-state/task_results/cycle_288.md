# Cycle 288 Results

## Worked on

- **P0 (mandatory)**: Single-poll of Aristotle project `efe4940e-0931-4fb2-8549-7eafab20d7f7` (strengthened (342f) general recurrence resubmission from cycle 285).
- **Branch C deliverable**: `n = 11` ladder rung pair for Butcher's (342f) three-term recurrence — `butcherShiftedLegendre_eleven` (explicit closed-form expansion) and `butcherShiftedLegendre_recurrence_eleven` (the (342f) instance at `n = 11`).

## Approach

### P0 — Aristotle poll

Ran `mcp__aristotle__get_status` once on `efe4940e-0931-4fb2-8549-7eafab20d7f7`:

```
status: IN_PROGRESS
created_at: 2026-05-15T18:03:40.858207
last_updated_at: 2026-05-15T18:51:45.963076
percent_complete: 20
```

Compared to cycle 287's observation `IN_PROGRESS / 20%` at 2026-05-15 18:35 UTC (~32 min after submission), the project is **flat** at 20% — no advance over the subsequent ~16 minutes (now at 2026-05-15 18:51 UTC, ~48 min after submission). This is observation #2 of 3 in the cycle 285 three-stall protocol per cycle 288 strategy Branch C (`IN_PROGRESS` at `<30%`, stalled near 20%).

Per strategy: **do NOT cancel** at observation #2; ship the `n = 11` ladder rung as the empirical backstop. Single-poll discipline observed — no re-polling later in cycle.

### Branch C — `n = 11` ladder rung

#### Step 1 — Compute coefficients

Python integer arithmetic:

```
butcherShiftedLegendre 11 has coefficients (ascending degree, k = 0..11):
  [-1, 132, -4290, 60060, -450450, 2018016, -5717712, 10501920, -12471030,
   9237800, -3879876, 705432]
```

Sanity checks:
- Sum = 1 ✓ (matches (342b) `P_n^*(1) = 1`)
- Coeff at `k = 0` = `−1` ✓ (matches (342c) `P_n^*(0) = (-1)^n` at `n = 11` odd)
- Leading coeff at `k = 11` = `+C(22, 11) = 705432` ✓ (matches `lead(P_n^*) = C(2n, n)` from cycle 281's `butcherShiftedLegendre_leadingCoeff`)

#### Step 2 — Ship `butcherShiftedLegendre_eleven`

Inserted at line ~985 of `OpenMath/Chapter3/Section342.lean` (immediately after cycle 287's `_ten_explicit_eval_zero` cross-check). Following cycle 285's `_nine` template (odd-`n` cycle 280's odd-template peel-off pattern):

```lean
theorem butcherShiftedLegendre_eleven :
    butcherShiftedLegendre 11 =
      Polynomial.C 705432 * Polynomial.X ^ 11
        - Polynomial.C 3879876 * Polynomial.X ^ 10
        + Polynomial.C 9237800 * Polynomial.X ^ 9
        - Polynomial.C 12471030 * Polynomial.X ^ 8
        + Polynomial.C 10501920 * Polynomial.X ^ 7
        - Polynomial.C 5717712 * Polynomial.X ^ 6
        + Polynomial.C 2018016 * Polynomial.X ^ 5
        - Polynomial.C 450450 * Polynomial.X ^ 4
        + Polynomial.C 60060 * Polynomial.X ^ 3
        - Polynomial.C 4290 * Polynomial.X ^ 2
        + Polynomial.C 132 * Polynomial.X
        - Polynomial.C 1 := by
  unfold butcherShiftedLegendre
  ext k
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map,
             Polynomial.coeff_shiftedLegendre]
  match k with
  | 0 => simp [...]; norm_num
  | 1 => simp [...]; norm_num
  | 2 =>
      have hch1 : Nat.choose 13 11 = 78 := by decide
      have hch2 : Nat.choose 11 2 = 55 := by decide
      simp [..., hch1, hch2]; norm_num
  ...
  | 11 =>
      have hch : Nat.choose 22 11 = 705432 := by decide
      simp [..., hch]; norm_num
  | (k + 12) =>
      have hk : (11 : ℕ).choose (k + 12) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [..., hk]
```

All `decide`-helpers required:
- `Nat.choose 13 11 = 78`, `Nat.choose 11 2 = 55`
- `Nat.choose 14 11 = 364`, `Nat.choose 11 3 = 165`
- `Nat.choose 15 11 = 1365`, `Nat.choose 11 4 = 330`
- `Nat.choose 16 11 = 4368`, `Nat.choose 11 5 = 462`
- `Nat.choose 17 11 = 12376`, `Nat.choose 11 6 = 462`
- `Nat.choose 18 11 = 31824`, `Nat.choose 11 7 = 330`
- `Nat.choose 19 11 = 75582`, `Nat.choose 11 8 = 165`
- `Nat.choose 20 11 = 167960`, `Nat.choose 11 9 = 55`
- `Nat.choose 21 11 = 352716`, `Nat.choose 11 10 = 11`
- `Nat.choose 22 11 = 705432` (leading)

Outer Butcher sign `(-1)^11 = −1` flips every coefficient, producing the closed form above with leading `+705432`.

#### Step 3 — Ship `butcherShiftedLegendre_recurrence_eleven`

Inserted at the end of `OpenMath/Chapter3/Section342.lean` (after `butcherShiftedLegendre_recurrence_ten`):

```lean
theorem butcherShiftedLegendre_recurrence_eleven :
    (11 : ℝ) • butcherShiftedLegendre 11 =
      Polynomial.C 21 * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre 10
      - Polynomial.C 10 * butcherShiftedLegendre 9 := by
  apply Polynomial.funext
  intro x
  rw [butcherShiftedLegendre_eleven, butcherShiftedLegendre_ten,
      butcherShiftedLegendre_nine]
  simp [Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_one, smul_eq_mul]
  ring
```

Coefficient check `(2n − 1, n − 1) = (21, 10)` at `n = 11` confirmed. Python integer-arithmetic cross-check: LHS and RHS both produce
```
[-11, 1452, -47190, 660660, -4954950, 22198176, -62894832, 115521120,
 -137181330, 101615800, -42678636, 7759752]
```
(ascending coeffs). LHS == RHS = True.

#### Step 4 — Verify

- `lake env lean OpenMath/Chapter3/Section342.lean`: exit 0 (only linter warnings about unused `hch2` simp args carried over from the `_nine`/`_ten` templates — pre-existing pattern).
- `lake env lean OpenMath/Chapter3.lean` (aggregator): exit 0.
- `grep -c "sorry" OpenMath/Chapter3/Section342.lean`: 0.
- `mcp__lean-lsp__lean_verify` on `butcherShiftedLegendre_eleven`: axioms = `[propext, Classical.choice, Quot.sound]` ✓
- `mcp__lean-lsp__lean_verify` on `butcherShiftedLegendre_recurrence_eleven`: axioms = `[propext, Classical.choice, Quot.sound]` ✓

#### Step 5 — Bookkeeping

- `extraction/formalization_data/lean_status.json`: appended cycle 287 and cycle 288 trace entries to the `lem:342A` row; `status` stays `partial` (general (342f) still open), `lean_symbol` unchanged.
- `plan.md`: appended cycle 287 and cycle 288 inline notes to the `lem:342A` bullet.

## Result

**SUCCESS** — All planned deliverables shipped:
1. Aristotle single-poll executed (Branch C identified — flat at 20%).
2. `butcherShiftedLegendre_eleven` (explicit closed form, axiom-clean).
3. `butcherShiftedLegendre_recurrence_eleven` (the (342f) instance at `n = 11`, axiom-clean).
4. `lean_status.json` + `plan.md` updated.
5. Section342.lean compiles, aggregator compiles, sorry count = 0.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `butcherShiftedLegendre_eleven`

- **Entity ID**: helper supporting `lem:342A` (Butcher §342, properties (342a)-(342g)).
- **Textbook statement (from `extraction/formalization_data/entities/lem_342A.json`, property (342b)/(342c) underlying the explicit form)**:
  > The shifted Legendre polynomial on `[0, 1]` satisfies `P_n^*(1) = 1` and `P_n^*(0) = (-1)^n`. Its coefficient at `x^k` is `(-1)^{n-k} · C(n,k) · C(n+k,k)`.
- **Lean statement captures**: same content (a specialization, at `n = 11`, of the coefficient formula `butcherShiftedLegendre n = C ((-1)^n) * (shiftedLegendre n).map ι` to the explicit polynomial `Σ_k coeff_k · X^k`). The closed form follows mechanically from `Polynomial.coeff_shiftedLegendre`.
- **No divergence** — this is a numerical specialization, paper-verified against Python integer arithmetic for the constant term, leading coefficient, and `x = 1` summation.

### `butcherShiftedLegendre_recurrence_eleven`

- **Entity ID**: `lem:342A`, property (342f).
- **Textbook statement (from `extraction/formalization_data/entities/lem_342A.json`)**:
  > `(342f)` For `n ≥ 2`, the polynomial `P_n^*(x)` satisfies the three-term recurrence `n · P_n^*(x) = (2n − 1) · (2x − 1) · P_{n−1}^*(x) − (n − 1) · P_{n−2}^*(x)`.
- **Lean statement captures**: same content at `n = 11` (substituting `(2 · 11 − 1, 11 − 1) = (21, 10)`). The `(2X − 1)` factor is encoded as `(Polynomial.C 2 * Polynomial.X - Polynomial.C 1)`; the `n ·` LHS is encoded as `(11 : ℝ) • butcherShiftedLegendre 11`. Both encodings match `_recurrence_two..._ten` ladder rungs verbatim (cycle 282–286 pattern).
- **No divergence** — direct port of cycle 286 `_recurrence_ten` template with `n` bumped to `11` and the prior-rung indices shifted accordingly.

## Dead ends

None this cycle — the `n = 11` ladder rung was a mechanical port of cycle 285's `_nine` template (odd-`n` peel-off pattern). All `decide`-helper `Nat.choose` values verified against Python `math.comb` before write. Python integer-arithmetic cross-check of `LHS == RHS` for the recurrence passed on the first try, so no `ring` failures or coefficient typos to debug.

## Discovery

- **Aristotle pace observation**: `efe4940e` advanced from 11% → 20% over cycles 286 → 287 (16 min), then stalled at 20% for cycle 288 (16 min). The +9pp burst in cycle 287 may have been Aristotle finishing planning + opening a search front; the 20% plateau in cycle 288 suggests it has entered a deeper proof-search phase where wall-clock progress reporting may lag actual progress. **Implication for cycle 289**: a single more flat observation (#3 of 3) at ~20% should trigger Branch D cancellation per the cycle 285 three-stall protocol; an advance to ≥30% would revert to Branch B (no ladder extension).
- **Odd-`n` template stability**: cycles 285 (`_nine`) and 288 (`_eleven`) both ship via the same template — the only edits are the leading-coefficient `Nat.choose (2n) n`, the `Nat.choose (n+k) n` and `Nat.choose n k` values per arm, and the tail `Nat.choose n (k + n+1) = 0` proof. Total LOC for `_eleven` is ~115 (vs `_nine` at ~88 and `_ten` at ~96). The template scales linearly in `n` and can mechanically support `_twelve`, `_thirteen`, ... if needed for future Branch C cycles — but per the strategy "Do NOT ship `n = 12` or higher in Branch C/D — `n = 11` is sufficient to mark observation/backstop", we should not.

## Suggested next approach

- **Cycle 289 P0 (mandatory)**: single-poll `efe4940e` once more. Branching:
  - **If COMPLETE / COMPLETE_WITH_ERRORS**: integrate as Branch A headline deliverable per cycle 288 strategy. Download, extract, read carefully, ship in Section342.lean with helper imports as needed, verify axiom-clean, add specialization cross-checks against cycles 282–288's ladder rungs.
  - **If IN_PROGRESS ≥ 30%**: Branch B continues. No new ladder rung. Either ship 1–2 cross-check theorems extending cycle 287's pattern (e.g. `_nine_explicit_eval_zero` for `P_9^*(0) = -1` per (342c) at odd `n`, or `_eight_explicit_eval_one` for `P_8^*(1) = 1` per (342b) at even `n`), or accept a no-new-theorem cycle and let Aristotle finish.
  - **If IN_PROGRESS at 20% (#3 of 3 stalls)**: cancel `efe4940e`, open `.prover-state/issues/lem_342A_342f_manual_closure_plan.md` per cycle 288 strategy Branch D §3, and ship the first manual step. Recommended Path A from the strategy: define `Q := LHS − RHS`, show `Q.natDegree < n` (using cycle 281's `butcherShiftedLegendre_leadingCoeff = C(2n,n)` + the leading-coefficient identity `n · C(2n,n) = 2(2n−1) · C(2n−2, n−1)`), then show `∫₀¹ Q · P_k^* = 0` for `k ≤ n−2` (using cycle 277's `butcherShiftedLegendre_orthogonal` + `integral_poly_mul_iterDeriv_vanish`), then conclude `Q = 0` from the basis property. Estimated 2–3 cycles.
  - **If FAILED / CANCELLED / status confused**: Branch D as above.

- **Do NOT** in cycle 289: re-poll (single-poll discipline); ship `n = 12+` ladder rung (cycle 285's "`n = 11` is sufficient" rule); start (342g); attempt to compile `Section441.lean` (43+ consecutive GPFS timeouts); modify `scripts/autonomous_loop.py`.

- **Cycle 290+ outlook**: if Branch D launched in cycle 289, expect 2–3 more cycles for Path A closure. After (342f) lands, fire-and-forget Aristotle on (342g) `n` distinct real zeros (sign-change argument, scoping doc already at `.prover-state/issues/lem_342A_g_zeros_scoping.md`). After (342g), `lem:342A` flips to `done`; pivot to `lem:342B` (Gaussian quadrature exactness degree, can now consume (342a) + (342d) + (342f) + (342g) as prerequisites).
