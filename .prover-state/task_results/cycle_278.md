# Cycle 278 Results

## Worked on
- Priority 0: single poll of Aristotle project `d4ce527b-b714-4e51-b0a6-e3d06302d7fa` (general (342d) norm-square).
- Priority 1 (Branch B): shipped `butcherShiftedLegendre_five` and
  `butcherShiftedLegendre_norm_sq_five` in
  `OpenMath/Chapter3/Section342.lean`, plus one non-vacuity witness.

## Approach
1. **Aristotle poll**: `mcp__aristotle__get_status` on
   `d4ce527b-b714-4e51-b0a6-e3d06302d7fa` returned `IN_PROGRESS` at
   `percent_complete: 33`. Up from 31% in cycle 277. **Branch B** taken —
   manual ship of the `n = 5` rung.
2. **`butcherShiftedLegendre_five`** (degree-5 explicit form): used the
   cycle-276 peel-off recipe (`unfold butcherShiftedLegendre; ext k;
   simp only [coeff_C_mul, coeff_map, coeff_shiftedLegendre]; match k`).
   For odd `n` the Butcher sign factor `(-1)^5 = -1` flips every sign,
   giving closed form `252X^5 - 630X^4 + 560X^3 - 210X^2 + 30X - 1`.
   Per-`k` arms `k ∈ {0..5, k+6}`; arms `k=2,3,4,5` needed `decide`
   helpers for the binomials `Nat.choose 7 5 = 21`, `Nat.choose 5 2 = 10`,
   `Nat.choose 8 5 = 56`, `Nat.choose 5 3 = 10`, `Nat.choose 9 5 = 126`,
   `Nat.choose 10 5 = 252`. Each arm closed with `simp [...]; norm_num`.
3. **`butcherShiftedLegendre_norm_sq_five`** (integral `= 1/11`):
   followed the cycle-277 `_four` template. Expanded `(P_5^*(x))^2`
   coefficient-by-coefficient via convolution of `(-1, 30, -210, 560,
   -630, 252)` with itself, giving `c_k` for `k ∈ {0..10}`. Validated
   that `c_0 = 1`, `c_10 = 63504 = 252²`, and the arithmetic sum
   `63504/11 − 31752 + 75460 − 101430 + 84760 − 45584 + 15792 − 3430
   + 440 − 30 + 1 = 1/11` (algebraic check done before committing).
   Lean proof structure: 11 `IntervalIntegrable` witnesses for `x^k`
   (`k ∈ {1..10}`), 10 `integral_pow` `h_k` facts, then a single `rw`
   with 10 nested `intervalIntegral.integral_add`/`integral_sub`
   + 10 `intervalIntegral.integral_const_mul` + 10 `h_k` + `integral_one`,
   closed with `ring`.
4. **Non-vacuity witness**: added an `example` confirming
   `∫₀¹ (butcherShiftedLegendre 5).eval x ^ 2 = 1 / (2 * 5 + 1)`.

## Result
**SUCCESS** —
- `lake env lean OpenMath/Chapter3/Section342.lean` exits 0; no sorry,
  no errors.
- `lake build OpenMath.Chapter3.Section342` exits 0.
- `lake env lean OpenMath/Chapter3.lean` exits 0 (aggregator check).
- `grep -c sorry OpenMath/Chapter3/Section342.lean` = 0.
- `#print axioms` returns `[propext, Classical.choice, Quot.sound]` for
  both `butcherShiftedLegendre_five` and
  `butcherShiftedLegendre_norm_sq_five`.

## Faithfulness check
For each new theorem introduced this cycle:

- **`butcherShiftedLegendre_five`** (entity ID: helper, not textbook):
  - Statement: `butcherShiftedLegendre 5 = C 252 * X^5 - C 630 * X^4
    + C 560 * X^3 - C 210 * X^2 + C 30 * X - C 1`.
  - Helper infrastructure (cycle 273/275/276/277 precedent for
    `_two`/`_three`/`_four`). Captures the **same content** as the
    Mathlib coefficient formula `coeff_shiftedLegendre` instantiated at
    `n = 5` with the outer `(-1)^5 = -1` Butcher sign factor.
  - Tautology check: conclusion is an explicit polynomial identity; not
    a hypothesis re-export.
  - Identity check: proof body does real per-`k` coefficient
    computation; not `exact h`.
  - Hypothesis strength check: no hypotheses; trivially minimal.

- **`butcherShiftedLegendre_norm_sq_five`** (entity ID: `lem:342A`
  (342d), `n = 5` specialization):
  - Textbook statement (`extraction/raw_text/ch03.txt` §342 (342d)):
    > `∫₀¹ P_n^*(x)^2 dx = 1/(2n + 1)`
  - Lean statement at `n = 5`:
    `∫ x in (0 : ℝ)..1, (butcherShiftedLegendre 5).eval x ^ 2 = 1 / 11`
    captures the **same content** at the specific instance
    `n = 5` ⇒ `1/(2·5+1) = 1/11`.
  - Tautology check: integral identity, not a hypothesis re-export.
  - Identity check: proof body does real algebraic computation
    (squaring expansion + 10 integrals + ring close).
  - Hypothesis strength check: no hypotheses; only the Mathlib measure
    structure on `ℝ`. Matches textbook.
  - Definition smuggling check: `butcherShiftedLegendre` was defined
    cycle 271 via Mathlib's `shiftedLegendre n` lifted to ℝ —
    not smuggling. Norm-squares are proved properties, not bakings-in.

## Dead ends
1. **Initial paren-count mistake**: my first draft of the
   `intervalIntegral.integral_add/_sub` rewrite block for
   `_norm_sq_five` had 9 initial opening parens on each line where 10
   were needed (and similarly off-by-one for downstream lines). The
   pattern from cycle-277 `_four` is: line `N` (counting from the
   outermost) starts with `(K - N + 1)` opening parens, where `K =
   number of binary ops in the LHS sub-expression`. For `n = 5` with 9
   binary ops in the outermost LHS, that means 10 opens for the first
   integral_add, 9 for the next integral_sub, ..., down to 1 for the
   innermost integral_sub of `x^10` vs `x^9`. Caught via `cat -A` /
   parenthesis depth trace; fixed by adding one more `(` to each line.
2. No actual Lean tactic dead-ends — the cycle-276 / cycle-277 templates
   transferred cleanly.

## Discovery
1. **Aristotle `d4ce527b` (342d general) growth rate**: 23% (c276) →
   31% (c277) → 33% (c278). Growth has slowed: c277→c278 was only +2pp
   vs c276→c277's +8pp. At ~+2pp/cycle this project may take until cycle
   ~311 to finish; at +8pp it would finish by cycle ~285. Worth a single
   poll per cycle to monitor, but the manual ladder rungs continue to
   provide concrete value while waiting.
2. **Coefficient-convolution sanity check pays off**: hand-computing
   `(P_5^*)²` coefficients by convolution before committing to the
   Lean expansion caught no errors this cycle (lucky), but the
   `c_10 = 252² = 63504` and `c_0 = (-1)² = 1` boundary checks plus
   the final `63504/11 − 31752 + ... + 1 = 1/11` algebraic identity
   verified correctness before any `lake env lean` invocation. The
   intermediate values `c_5 = -273504` and `c_7 = -811440` are not
   round numbers; verifying them costs <2 minutes mentally and saves
   an entire rebuild cycle.
3. **Paren-count formula**: for ladder rung `n` (LHS has `2n` terms =
   `2n − 1` binary ops), the first line of the `rw` block needs
   `2n` opening parens, then each subsequent line one fewer. For
   `n = 5`: 10, 9, 8, 7, 6, 5, 4, 3, 2, 1 across the 10 integral_op
   lines.
4. **Section342.lean size growth**: 623 LOC (c272) → 822 LOC (c275) →
   875 LOC (c276) → 1043 LOC (c277) → 1231 LOC (c278). Each ladder rung
   adds ~50 LOC for the `_norm_sq_n` plus ~70 LOC for the explicit-form
   `_n`. At this rate, `n = 6` would push past 1400 LOC, `n = 7` past
   1600 LOC. The file remains tractable but is approaching a size
   where splitting into `Section342Ladder.lean` may be worth
   considering by `n = 8` or so.

## Suggested next approach
Cycle 279 candidates, in rough priority order:

1. **(Most promising) Poll Aristotle `d4ce527b` again**: at +2pp/cycle
   it would be at 35%; at +8pp it would be at 41%. If COMPLETE,
   integrate the general norm-square and the ladder rungs (`_zero` ...
   `_five`) become non-vacuity witnesses for the universal result.
2. **Ship `n = 6` ladder rung** if `d4ce527b` is still IN_PROGRESS.
   Coefficients (using `(-1)^6 = 1`, leading `C(12, 6) = 924`):
   `P_6^*(x) = 924x^6 - 2772x^5 + 3150x^4 - 1680x^3 + 420x^2 - 42x + 1`.
   Sanity at `x = 1`: `924 − 2772 + 3150 − 1680 + 420 − 42 + 1 = 1` ✓
   (matches `butcherShiftedLegendre_eval_one`). For `_norm_sq_six`,
   integrand is degree-12, 13 terms; 12 nested `integral_op` lines.
   The pattern is mechanical but pushes the file to ~1430 LOC.
3. **Attempt (342f) three-term recurrence** via inner-product
   expansion route (now that (342a) orthogonality is in hand). Cycle
   277's discovery suggests this route is open. Time-box 30 min;
   abort with issue file if stalled.
4. **Consider splitting Section342.lean** into `Section342.lean`
   (definitions + (342a-c, 342e) properties) and `Section342Ladder.lean`
   (the explicit-`n` ladder + `_norm_sq_n` family) before adding more
   rungs.

**Do NOT** attempt (342g) zeros this cycle — multi-cycle, requires
sign-change argument or general Mathlib orthogonal-polynomial root
theorem. Defer.
