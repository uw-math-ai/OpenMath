# Cycle 283 Results

## Worked on
- `lem:342A` (342f) three-term recurrence — ladder rungs at `n = 5, 6, 7`
  added to `OpenMath/Chapter3/Section342.lean` (cycles 282's recipe
  extended).
- Aristotle project `c8b8f138-f875-4263-94ec-74533b5120d7` (general
  342f recurrence) single-polled per strategy P0.

## Approach

### P0 — Aristotle single-poll
Called `mcp__aristotle__get_status` once on
`c8b8f138-f875-4263-94ec-74533b5120d7`. Returned **IN_PROGRESS at 12%**
(created `2026-05-15T17:14:45Z`, last update `2026-05-15T17:30:04Z` —
~15 min in). Per strategy Branch B, did not poll again.

### P1 — Branch B ladder extension
Per cycle 282's verified `Polynomial.funext + simp [eval_*] + ring`
recipe, shipped three more recurrence rungs:

1. **`butcherShiftedLegendre_recurrence_five`**:
   `(5 : ℝ) • P_5^* = C 9 · (C 2 · X − C 1) · P_4^* − C 4 · P_3^*`.
   - LHS: `5 · (252x⁵ − 630x⁴ + 560x³ − 210x² + 30x − 1)
     = 1260x⁵ − 3150x⁴ + 2800x³ − 1050x² + 150x − 5`.
   - RHS: `9 · (2x − 1) · (70x⁴ − 140x³ + 90x² − 20x + 1)
     − 4 · (20x³ − 30x² + 12x − 1)`
     = `9 · (140x⁵ − 350x⁴ + 320x³ − 130x² + 22x − 1)
        − (80x³ − 120x² + 48x − 4)`
     = `1260x⁵ − 3150x⁴ + 2880x³ − 1170x² + 198x − 9
        − 80x³ + 120x² − 48x + 4`
     = `1260x⁵ − 3150x⁴ + 2800x³ − 1050x² + 150x − 5`. ✓

2. **`butcherShiftedLegendre_recurrence_six`**:
   `(6 : ℝ) • P_6^* = C 11 · (C 2 · X − C 1) · P_5^* − C 5 · P_4^*`.
   - LHS: `6 · (924x⁶ − 2772x⁵ + 3150x⁴ − 1680x³ + 420x² − 42x + 1)
     = 5544x⁶ − 16632x⁵ + 18900x⁴ − 10080x³ + 2520x² − 252x + 6`.
   - RHS sanity-checked: `(2x − 1) · P_5^*
     = 504x⁶ − 1512x⁵ + 1750x⁴ − 980x³ + 270x² − 32x + 1`;
     × 11 = `5544x⁶ − 16632x⁵ + 19250x⁴ − 10780x³ + 2970x² − 352x + 11`;
     − 5·P_4^* = `5544x⁶ − 16632x⁵ + 18900x⁴ − 10080x³ + 2520x² − 252x + 6`. ✓

3. **`butcherShiftedLegendre_recurrence_seven`**:
   `(7 : ℝ) • P_7^* = C 13 · (C 2 · X − C 1) · P_6^* − C 6 · P_5^*`.
   - LHS: `7 · P_7^* = 24024x⁷ − 84084x⁶ + 116424x⁵ − 80850x⁴
     + 29400x³ − 5292x² + 392x − 7`.
   - RHS sanity-checked: `(2x − 1) · P_6^*
     = 1848x⁷ − 6468x⁶ + 9072x⁵ − 6510x⁴ + 2520x³ − 504x² + 44x − 1`;
     × 13 = `24024x⁷ − 84084x⁶ + 117936x⁵ − 84630x⁴ + 32760x³
             − 6552x² + 572x − 13`;
     − 6·P_5^* = `24024x⁷ − 84084x⁶ + 116424x⁵ − 80850x⁴
                  + 29400x³ − 5292x² + 392x − 7`. ✓

All three proofs use the identical tactic:
```
apply Polynomial.funext
intro x
rw [butcherShiftedLegendre_{n}, butcherShiftedLegendre_{n-1},
    butcherShiftedLegendre_{n-2}]
simp [Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_one, smul_eq_mul]
ring
```

## Result
**SUCCESS** — all three rungs compile axiom-clean
(`[propext, Classical.choice, Quot.sound]` only on each).
`lake env lean OpenMath/Chapter3/Section342.lean` exits 0.
`lake env lean OpenMath/Chapter3.lean` exits 0.
0 sorries in Section342.lean.
Section342.lean grew from 1949 → ~2014 LOC.

## Faithfulness check
For each new theorem introduced this cycle:

- **`butcherShiftedLegendre_recurrence_{five, six, seven}`** (entity
  `lem:342A`, formula (342f) — concrete `n = 5, 6, 7` instances):
  - Textbook statement (from `extraction/formalization_data/entities/lem_342A.json`,
    formula (342f)):
    > `n P_n^*(x) = (2n − 1)(2x − 1) P_{n−1}^*(x) − (n − 1) P_{n−2}^*(x)`.
  - Lean statements capture: **same content**, with `n ∈ {5, 6, 7}`
    specialised, scalar multiplication on the LHS, and `Polynomial.C`
    coercions on the RHS. Coefficients `(2n − 1, n − 1)` substituted
    correctly: `(9, 4)` for n=5, `(11, 5)` for n=6, `(13, 6)` for n=7.
  - Tautology check: no hypothesis equals the conclusion (vacuously,
    these theorems take no hypotheses).
  - Identity check: proof is a multi-step tactic body
    (`apply Polynomial.funext; intro; rw; simp; ring`), not `exact h`.
  - Hypothesis strength check: no hypotheses at all (concrete numerical
    instances). Matches textbook (no constraint on `n` is mentioned in
    the textbook for these specific small `n`).
  - No definition smuggling: these are theorems witnessing the textbook
    recurrence at specific `n`, not redefinitions.

## Dead ends
None. The cycle-282 recipe extended to `n = 5, 6, 7` first-try, as
expected (all explicit forms `_five`, `_six`, `_seven` were already
in the file from cycles 278–280).

## Discovery
The `Polynomial.funext + ring` recipe scales linearly in `n` —
no `ring` slowdown observed at `n = 7` vs. `n = 2`. This suggests
the ladder can in principle continue indefinitely; the practical
ceiling is the absence of `butcherShiftedLegendre_{n}` explicit forms
beyond `n = 7`. Manual extension would cost ~50 LOC per new explicit
form (per the cycle 278–280 pattern).

## Suggested next approach
Cycle 284 should:

1. **P0**: Single-poll Aristotle `c8b8f138`. At the observed pace
   (12% at cycle 283 vs. d4ce527b's ~+5%/cycle), expect COMPLETE
   around cycles 295–296.
2. **Branch A (Aristotle COMPLETE)**: Integrate the general (342f)
   recurrence theorem analogously to cycle 281's `d4ce527b`
   (`Section342NormSqHelpers.lean` extraction precedent). After
   integration, fire Aristotle on (342g) per
   `.prover-state/issues/lem_342A_g_zeros_scoping.md`.
3. **Branch B (Aristotle IN_PROGRESS)**: Extend the ladder to
   `n = 8` (requires shipping `butcherShiftedLegendre_eight` ~50 LOC
   explicit form first, then the rung).
4. **Branch C (FAILED/CANCELLED)**: Cancel `c8b8f138`, ship
   `_recurrence_eight`, then pivot to `lem:342B` (Gaussian quadrature
   exactness) consuming (342a–e) plus the (342f) numerical witnesses.

Alternative: in parallel with polling, consider also shipping
`butcherShiftedLegendre_eight` (and rung) preemptively to keep
the ladder warm in case Aristotle stalls past cycle 290.
