# Strategy — Cycle 285

## Context

**Current state at HEAD (`8eb3d0b`)**:
- `OpenMath/Chapter3/Section342.lean` ~2123 LOC, **0 sorries**, axiom-clean.
- §342 (342f) ladder closed at n=2..8 (cycles 282/283/284).
- General §342 (342f) submitted to Aristotle (project `c8b8f138-f875-4263-94ec-74533b5120d7`) cycle 282; **IN_PROGRESS at 12% for two consecutive polls** (cycles 283 and 284 — stalled).
- §342 (342a) orthogonality, (342b) eval_one, (342c) eval_one_sub, (342d) general norm_sq, (342e) Rodrigues all **closed general** (cycles 271/272/273/277/281).
- Repo sorry count: 0.

**Remaining §342 open work**:
- (342f) general three-term recurrence — Aristotle stalled.
- (342g) `n` distinct real zeros — scoping doc at `.prover-state/issues/lem_342A_g_zeros_scoping.md`.

## Priority order

### P0 (mandatory) — Single-poll Aristotle `c8b8f138`

Run **exactly one** `mcp__aristotle__get_status` on project `c8b8f138-f875-4263-94ec-74533b5120d7`. Do NOT re-poll (CLAUDE.md rule).

**Branch decision**:
- **Branch A (Aristotle COMPLETE)**: Skip P1/P2, integrate analogously to cycle 281's `d4ce527b` integration:
  - Extract Aristotle's helpers into `OpenMath/Chapter3/Section342RecurrenceHelpers.lean` (new file, mirror cycle 281's `Section342NormSqHelpers.lean` pattern). Place under namespace `OpenMath.Chapter3.Section342Helpers`.
  - Add the main theorem `butcherShiftedLegendre_recurrence (n : ℕ) (hn : 2 ≤ n) : (n : ℝ) • P_n^* = C(2n-1) · (2X − 1) · P_{n-1}^* − C(n-1) · P_{n-2}^*` to `Section342.lean`.
  - Verify cycles 282–284's seven concrete witnesses (n=2..8) still compile (they should remain independent direct computations).
  - Update `extraction/formalization_data/lean_status.json` `lem:342A` cycle reference to 285.
  - Stretch (P3 below): fire Aristotle on (342g) per `.prover-state/issues/lem_342A_g_zeros_scoping.md`.

- **Branch B (Aristotle IN_PROGRESS at any %)**:
  - **If still at 12% (third consecutive stall)**: cancel `c8b8f138` and execute P1 (resubmit with stronger prompt) AND P2 (ship n=9 manual ladder rung).
  - **If percentage has advanced** (e.g. 12% → 17%+): leave it running, skip P1, ship P2 (n=9 manual rung) only.

- **Branch C (Aristotle COMPLETE_WITH_ERRORS or FAILED)**: Apply suggested fixes if minor (1–2 line patches like the cycle 277 namespace fix); otherwise cancel and execute P1.

### P1 (conditional — only if P0 Branch B "third stall" or Branch C "FAILED") — Cancel + Resubmit Aristotle

Cancel `c8b8f138`. Resubmit a strengthened (342f) prompt to a fresh project. Submission target file: `.prover-state/aristotle_submissions/cycle_285/342f_recurrence_v2.lean`. Include the following enrichments over the cycle 282 submission:

1. **Add cycle 277 helper as axiom**: `integral_poly_mul_iterDeriv_vanish` (the iterated-IBP × n orthogonality machinery from cycle 277's (342a) closure). This gives Aristotle the orthogonality lemma without redoing cycle 277's work.

2. **Add cycle 281 helper as axiom**: `butcherShiftedLegendre_leadingCoeff` (the `C(2n,n)` leading-coefficient identity, used in cycle 281's general (342d) proof). Gives Aristotle the leading-coefficient bookkeeping.

3. **Add textbook proof sketch verbatim**: Quote from `formalization_data/entities/lem_342A.json` the proof sketch for (342f) (induction on `n`; show `Q := n P_n^* − (2n − 1)(2x − 1) P_{n-1}^* + (n − 1) P_{n-2}^*` has degree < n via leading-coefficient cancellation; then `Q ⊥ {P_0^*, …, P_{n-1}^*}` via (342a); conclude `Q = 0` by basis dimension).

4. **Cite all already-closed pieces** as in-context axioms: `butcherShiftedLegendre_orthogonal`, `_eval_one`, `_eval_one_sub`, `_norm_sq`, `_rodrigues`, `_natDegree`, plus `_zero` through `_eight` explicit forms.

Record the new project ID in `task_results/cycle_285.md` for cycle 286's first-poll.

### P2 (conditional — only if P0 lands in Branch B) — Ship n=9 ladder rung manually

Add two public theorems to `OpenMath/Chapter3/Section342.lean`:

#### Theorem 1: `butcherShiftedLegendre_nine`

Statement: `butcherShiftedLegendre 9 = 48620 X^9 − 218790 X^8 + 411840 X^7 − 420420 X^6 + 252252 X^5 − 90090 X^4 + 18480 X^3 − 1980 X^2 + 90 X − 1` (encoded as a sum of `C(c) * X^k` terms in Lean).

**Coefficient derivation** (paper-verified BEFORE writing Lean):
- Mathlib's `Polynomial.coeff_shiftedLegendre n k = (-1)^k · C(n,k) · C(n+k,n)` for `k ≤ n`.
- At `n = 9`, `k ∈ {0..9}`:
  - `k=0`: `+1 · 1 · 1 = 1`
  - `k=1`: `−1 · 9 · 10 = −90`
  - `k=2`: `+1 · 36 · 55 = 1980`
  - `k=3`: `−1 · 84 · 220 = −18480`
  - `k=4`: `+1 · 126 · 715 = 90090`
  - `k=5`: `−1 · 126 · 2002 = −252252`
  - `k=6`: `+1 · 84 · 5005 = 420420`
  - `k=7`: `−1 · 36 · 11440 = −411840`
  - `k=8`: `+1 · 9 · 24310 = 218790`
  - `k=9`: `−1 · 1 · 48620 = −48620`
- Outer Butcher sign `(-1)^9 = -1` flips every coefficient → final signs in the statement above.

**Sanity check (compute BEFORE writing Lean)**:
- `P_9^*(0) = -1 = (-1)^9` ✓ (matches `butcherShiftedLegendre_eval_zero`).
- `P_9^*(1) = -1 + 90 − 1980 + 18480 − 90090 + 252252 − 420420 + 411840 − 218790 + 48620`. Must equal `1` (matches `butcherShiftedLegendre_eval_one`). Run this sum via Python `sum([-1, 90, -1980, 18480, -90090, 252252, -420420, 411840, -218790, 48620])` and confirm `= 1` before committing to the coefficient list. **If the sum is not 1, the coefficient table above has an error — re-derive before writing any Lean.**

**Recipe** (cycle 280's odd-n template):
```lean
theorem butcherShiftedLegendre_nine :
    butcherShiftedLegendre 9 = … := by
  unfold butcherShiftedLegendre
  ext k
  simp only [coeff_C_mul, coeff_map, coeff_shiftedLegendre]
  match k with
  | 0 => simp; norm_num
  | 1 => simp; norm_num
  | 2 => simp [show Nat.choose 9 2 = 36 from by decide,
                show Nat.choose 11 9 = 55 from by decide]; norm_num
  | 3 => simp [show Nat.choose 9 3 = 84 from by decide,
                show Nat.choose 12 9 = 220 from by decide]; norm_num
  | 4 => simp [show Nat.choose 9 4 = 126 from by decide,
                show Nat.choose 13 9 = 715 from by decide]; norm_num
  | 5 => simp [show Nat.choose 14 9 = 2002 from by decide]; norm_num
  | 6 => simp [show Nat.choose 9 6 = 84 from by decide,
                show Nat.choose 15 9 = 5005 from by decide]; norm_num
  | 7 => simp [show Nat.choose 9 7 = 36 from by decide,
                show Nat.choose 16 9 = 11440 from by decide]; norm_num
  | 8 => simp [show Nat.choose 9 8 = 9 from by decide,
                show Nat.choose 17 9 = 24310 from by decide]; norm_num
  | 9 => simp [show Nat.choose 18 9 = 48620 from by decide]; norm_num
  | k + 10 =>
    rw [Nat.choose_eq_zero_of_lt (by omega : 9 < k + 10)]
    simp
```

#### Theorem 2: `butcherShiftedLegendre_recurrence_nine`

Statement: `(9 : ℝ) • P_9^* = C 17 · (C 2 · X − C 1) · P_8^* − C 8 · P_7^*` (Butcher (342f) at n=9: `(2n − 1, n − 1) = (17, 8)`).

**Algebraic cross-check** (Python integer arithmetic, BEFORE Lean):
- LHS coefficients in descending-degree order: `9 · [48620, −218790, 411840, −420420, 252252, −90090, 18480, −1980, 90, −1]`
  `= [437580, −1969110, 3706560, −3783780, 2270268, −810810, 166320, −17820, 810, −9]`.
- RHS: compute `(2X − 1) · P_8^*` first by convolving `[2, −1]` with `P_8^* = [12870, −51480, 84084, −72072, 34650, −9240, 1260, −72, 1]` (descending degree), then multiply by 17, then subtract `8 · P_7^* = 8 · [3432, −12012, 16632, −11550, 4200, −756, 56, −1]` aligned at the trailing end (degrees 0..7).
- Verify the two 10-vectors match exactly. **If they don't match, the recurrence coefficients `(17, 8)` are wrong — recheck Butcher (342f) before writing Lean.**

**Recipe** (cycle 282+ template):
```lean
theorem butcherShiftedLegendre_recurrence_nine :
    (9 : ℝ) • butcherShiftedLegendre 9 =
      C 17 * (C 2 * X − C 1) * butcherShiftedLegendre 8
        − C 8 * butcherShiftedLegendre 7 := by
  apply Polynomial.funext
  intro x
  rw [butcherShiftedLegendre_nine, butcherShiftedLegendre_eight,
      butcherShiftedLegendre_seven]
  simp only [Polynomial.eval_smul, eval_mul, eval_add, eval_sub,
             eval_pow, eval_C, eval_X, eval_one, smul_eq_mul]
  ring
```

**LOC budget**: ~120 LOC total (explicit form ~80 LOC, recurrence witness ~10 LOC, plus ~10 LOC of `--` comments documenting the paper-verified coefficients).

### P3 (stretch — only if P0 Branch A and time remains) — Fire Aristotle on (342g)

Per `.prover-state/issues/lem_342A_g_zeros_scoping.md`:
- Target: `butcherShiftedLegendre_n_distinct_zeros (n : ℕ) (hn : 0 < n) : ∃ S : Finset ℝ, S.card = n ∧ ∀ x ∈ S, 0 < x ∧ x < 1 ∧ (butcherShiftedLegendre n).IsRoot x`.
- Strategy: sign-change contradiction via product polynomial `Q := ∏ᵢ (X − xᵢ)` with `∫₀¹ P_n^* · Q = 0` by (342a) yet `≠ 0` by sign-constancy.
- Cite all of (342a)–(342f) plus `_zero, _one, ..., _eight` (and `_nine` if P2 ships) as in-context axioms.
- Provide Mathlib hooks in submission: `Polynomial.roots`, `Polynomial.card_roots_le_degree`, `intermediate_value_Ioo`, `Polynomial.continuous`, `Polynomial.IsRoot`.
- Record new project ID; do NOT poll until cycle 286+.

This is **fire-and-forget** — do NOT manually attempt (342g) in cycle 285.

## What NOT to try

1. **Do NOT attempt (342f) general manually**. Cycle 273's manual attempt stalled because `Polynomial.ext` and `Polynomial.funext` both required Pascal-style binomial identities `ring` couldn't close, and Mathlib has no standard Bonnet-recurrence hook for shifted Legendre polynomials. The proof needs either Aristotle's machinery (via P1's strengthened prompt) or a multi-cycle Mathlib build-out — not a single-cycle ship.

2. **Do NOT poll Aristotle more than once per cycle** (CLAUDE.md rule).

3. **Do NOT modify cycles 271–284's existing theorems** — any of `butcherShiftedLegendre_{zero, one, two, three, four, five, six, seven, eight, eval_one, eval_one_sub, rodrigues, orthogonal, norm_sq, _natDegree}` or any `_norm_sq_n` / `_recurrence_n` witness for n=2..8. They are all axiom-clean and load-bearing.

4. **Do NOT pivot to `lem:310B` Phase A.3** (`TreeAutomorphism` strengthening). It's multi-cycle work per `lem_310B_plan.md` and not appropriate for a single-cycle pivot. If P0 Branch B and bandwidth remains after P2, prefer P3 (fire Aristotle on 342g) over a §310 pivot.

5. **Do NOT raise `maxHeartbeats`**. If the explicit form at n=9 is slow, decompose. Cycle 280 n=7 took ~80 LOC and stayed within defaults; n=9 should scale linearly.

6. **Do NOT use `Polynomial.ext + ring`** for the recurrence witness. Cycle 273 documented this fails due to `Polynomial.C` constant arithmetic outside `ring`'s normal form. Use the cycle 282+ template `Polynomial.funext → intro x → rw [explicit forms] → simp [eval_*] → ring`.

7. **Do NOT introduce sorries**. Cycle 285's bar is "ship axiom-clean or skip the cycle".

8. **Do NOT write new files** unless P0 lands in Branch A (helper file `Section342RecurrenceHelpers.lean` mirrors cycle 281's pattern). All cycle 285 P2 work lives in the existing `OpenMath/Chapter3/Section342.lean`.

9. **Do NOT modify `scripts/autonomous_loop.py`** — loop-maintainer territory per CLAUDE.md.

## Faithfulness checklist (mandatory before commit)

For each new theorem (`_nine`, `_recurrence_nine`, plus any Branch A integration):

- [ ] Statement matches textbook: explicit form derived from `Polynomial.coeff_shiftedLegendre` at n=9; recurrence matches Butcher (342f) at n=9.
- [ ] No definition smuggling: the textbook (342f) is a polynomial-ring identity, and the Lean version proves the same identity over `ℝ[X]`.
- [ ] No hypothesis strengthening: both new theorems are unconditional at n=9.
- [ ] Numerical coefficients cross-checked via Python integer arithmetic BEFORE writing Lean.
- [ ] `#print axioms` returns `[propext, Classical.choice, Quot.sound]` for both new theorems.

## Verification sequence (end of cycle)

```bash
lake env lean OpenMath/Chapter3/Section342.lean    # exit 0
grep -c sorry OpenMath/Chapter3/Section342.lean    # 0
lake build OpenMath.Chapter3.Section342            # completes
lake env lean OpenMath/Chapter3.lean               # aggregator clean
```

Then run `#print axioms` (via standalone test file or `lean_verify` MCP) on each new theorem.

## Cycle 286+ outlook

- If P0 Branch A: cycle 286 polls (342g) Aristotle (if P3 fired), integrates if COMPLETE; otherwise pivots to `lem:310B` Phase A.3 or continues ladder.
- If P0 Branch B (Aristotle still running): cycle 286 polls again. If three stalled polls AND P1 not yet executed, execute P1. Otherwise continue ladder to n=10.
- If P0 Branch B and P1 executed in cycle 285: cycle 286 polls the new project ID. If still IN_PROGRESS at low %, continue ladder to n=10 manually.
