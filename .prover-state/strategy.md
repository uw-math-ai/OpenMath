# Cycle 277 Strategy — §342 (342d) ladder at n=4 + Aristotle poll

## Context (1-paragraph recap)

Cycle 276 shipped the §342 (342d) ladder at `n = 3`: two axiom-clean
theorems `butcherShiftedLegendre_three` (`P_3^* = 20X³ − 30X² + 12X − 1`)
and `butcherShiftedLegendre_norm_sq_three` (`∫₀¹ (P_3^*)² = 1/7`).
Section342.lean is now 623 LOC, 0 sorries. Two Aristotle projects
remain IN_PROGRESS (`727396d5` 342a orthogonality @ 32%; `d4ce527b`
342d general @ 23%), both advancing ~10% per cycle. Cycle 277 follows
the cycle 276 recommendation: **continue the ladder to n = 4**.

## Priority 0 — Aristotle single-poll (mandatory, ≤2 min)

Run **exactly one** poll per CLAUDE.md (no second pollings even if the
first call hits a transient error — log and skip):

1. `mcp__aristotle__get_status` on **`727396d5-14f9-4014-9aad-1f38238a1651`**
   (342a orthogonality).
2. `mcp__aristotle__get_status` on **`d4ce527b-b714-4e51-b0a6-e3d06302d7fa`**
   (342d general norm-square).

### Branch on results

* **If either returns `COMPLETE`**: pivot to Branch B (integration)
  immediately. Download via `mcp__aristotle__download_result` ➜ extract
  to `.prover-state/aristotle_results/cycle_277/<project_id>/`. Read
  `ARISTOTLE_SUMMARY.md`; if `success: true` and the inlined Lean proof
  has 0 sorries, integrate into `OpenMath/Chapter3/Section342.lean` as
  `butcherShiftedLegendre_orthogonal` (for 342a) or
  `butcherShiftedLegendre_norm_sq` (for 342d), preserving cycles 271–276
  hypotheses verbatim. Bump `lean_status.json` `lem:342A` cycle to 277
  and update its `lean_symbol` only if the integration verifies
  axiom-clean.
* **If both return `IN_PROGRESS` or `FAILED`**: proceed to Priority 1
  with the n=4 ladder ship. Do NOT cancel either project — they're
  expected to land in cycle 281–283 at the current ~10%/cycle pace.

## Priority 1 — Ship `butcherShiftedLegendre_four` + norm-square (n = 4)

### Why this target (over alternatives)

Cycle 276 task results recommended Option A explicitly. Mirrors the
cycle 273 → 274 → 275 → 276 ladder progression. **Even n = 4 means
`(−1)^4 = 1`, so the cycle 275 `_two` simp recipe applies cleanly
without the odd-n peel-off pattern needed in cycle 276 for `_three`.**
Alternatives B/C from cycle 276 task results either duplicate
Aristotle's general (342a) effort (Option B) or are too narrow for a
full cycle (Option C).

### Coefficient computation (paper-side, pre-Lean)

`P_4^*` coefficients via `Polynomial.coeff_shiftedLegendre`:
`coeff (P_n^*) k = (−1)^n · (−1)^k · (n.choose k) · ((n+k).choose n)`.

For `n = 4` (even, so the `(−1)^n` factor is `+1`):

| k | sign | n.choose k | (n+k).choose n | coeff |
|---|------|------------|----------------|-------|
| 0 | +1   | 1          | 1              | 1     |
| 1 | −1   | 4          | 5              | −20   |
| 2 | +1   | 6          | 15             | 90    |
| 3 | −1   | 4          | 35             | −140  |
| 4 | +1   | 1          | 70             | 70    |

So **`P_4^* = 70X^4 − 140X^3 + 90X^2 − 20X + 1`**.

Eval-1 sanity (matches cycle 271's `butcherShiftedLegendre_eval_one`):
`70 − 140 + 90 − 20 + 1 = 1` ✓.
Eval-0 sanity (matches cycle 273's `butcherShiftedLegendre_eval_zero`
at `(−1)^4 = 1`): coefficient of `X^0` is `1` ✓.

### Deliverable 1.A — `butcherShiftedLegendre_four`

Place immediately after cycle 276's `butcherShiftedLegendre_three`.
Recipe (port cycle 275's `_two` verbatim with index updates):

```lean
theorem butcherShiftedLegendre_four :
    butcherShiftedLegendre 4 = C 70 * X^4 - C 140 * X^3 + C 90 * X^2
                                - C 20 * X + C 1 := by
  unfold butcherShiftedLegendre
  ext k
  match k with
  | 0 => simp [coeff_map, coeff_shiftedLegendre]
  | 1 => simp [coeff_map, coeff_shiftedLegendre]
  | 2 => simp [coeff_map, coeff_shiftedLegendre]
  | 3 => simp [coeff_map, coeff_shiftedLegendre]
  | 4 => simp [coeff_map, coeff_shiftedLegendre]
  | k + 5 =>
    simp [coeff_map, coeff_shiftedLegendre,
          Nat.choose_eq_zero_of_lt (by omega : 4 < k + 5)]
```

**Pre-flight check**: try the recipe verbatim first. If `simp` doesn't
close a per-k arm because `Nat.choose 5 4` or `(4 + k + 5).choose 4`
doesn't auto-evaluate, add explicit hints via
`(show (...).choose (...) = N by decide)`. Cycle 275's `_two` needed
`Nat.choose 4 2 = 6 by decide`; cycle 276's `_three` needed `decide`
for `5.choose 3 = 10` and `6.choose 3 = 20`. Likely candidates here:
`5.choose 4 = 5`, `6.choose 4 = 15`, `7.choose 4 = 35`, `8.choose 4 = 70`.

**If the per-k `simp` arms leave residual goals** (e.g. patterns like
`((-1)^4).coeff k = ...` because the `C ((-1)^4)` factor wasn't
collapsed cleanly): prepend `simp only [Polynomial.coeff_C_mul,
coeff_map, coeff_shiftedLegendre]` to peel off the constant factor
BEFORE the per-k simp (this is the cycle 276 odd-n workaround; even
n = 4 should NOT need it, but it's a cheap fallback).

LOC: ~25.

### Deliverable 1.B — `butcherShiftedLegendre_norm_sq_four`

Place immediately after Deliverable 1.A. Target: `∫₀¹ (P_4^*)^2 dx = 1/9`.

Integrand expansion (`(70x⁴ − 140x³ + 90x² − 20x + 1)²`):

Let `a=70, b=-140, c=90, d=-20, e=1`. Then
`(ax⁴+bx³+cx²+dx+e)² = a²x⁸ + 2ab x⁷ + (2ac+b²) x⁶ + (2ad+2bc) x⁵
                       + (2ae+2bd+c²) x⁴ + (2be+2cd) x³ + (2ce+d²) x²
                       + 2de x + e²`

Numerically:
```
4900x⁸ − 19600x⁷ + 32200x⁶ − 28000x⁵ + 13840x⁴ − 3880x³ + 580x² − 40x + 1
```

Verification of target (common denominator 2520):
`4900/9 − 19600/8 + 32200/7 − 28000/6 + 13840/5 − 3880/4 + 580/3
 − 40/2 + 1 = 1/9` ✓.

Recipe (extend cycle 276's 7-monomial split to 9 monomials):

```lean
theorem butcherShiftedLegendre_norm_sq_four :
    ∫ x in (0:ℝ)..1, (butcherShiftedLegendre 4).eval x ^ 2 = 1 / 9 := by
  rw [show (fun x : ℝ => (butcherShiftedLegendre 4).eval x ^ 2)
        = (fun x : ℝ => 4900 * x^8 - 19600 * x^7 + 32200 * x^6
                         - 28000 * x^5 + 13840 * x^4 - 3880 * x^3
                         + 580 * x^2 - 40 * x + 1) from by
        funext x; rw [butcherShiftedLegendre_four]
        simp [Polynomial.eval_add, Polynomial.eval_sub,
              Polynomial.eval_mul, Polynomial.eval_pow,
              Polynomial.eval_C, Polynomial.eval_X]; ring]
  -- 8 nested add/sub for left-associative integrand
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_add, intervalIntegral.integral_sub]
  -- 8× integral_const_mul (one per monomial except constant)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  -- Evaluate ∫₀¹ xᵏ for k ∈ {2..8} via integral_pow; ∫₀¹ 1 via integral_one;
  -- ∫₀¹ x¹ via pow_one + Nat.cast_one trick (cycle 274/275/276 pattern)
  rw [integral_pow, integral_pow, integral_pow, integral_pow,
      integral_pow, integral_pow, integral_pow]
  · simp [Nat.cast_one]
    rw [show ∫ x in (0:ℝ)..1, x = ∫ x in (0:ℝ)..1, x^1 by simp [pow_one]]
    rw [integral_pow, intervalIntegral.integral_one]
    push_cast
    ring
  all_goals
    first
    | apply Continuous.intervalIntegrable; continuity
    | apply IntervalIntegrable.mul_continuous;
      exact intervalIntegrable_const
      · continuity
```

**Risk**: the 8 nested `integral_add`/`integral_sub` rewrites create
8 integrability side-goals each. Cycle 276's 7-monomial split closed
these all with `Continuous.intervalIntegrable; continuity`. The 9-
monomial extension should follow the same pattern. If `continuity`
times out, replace with explicit chains of
`(Continuous.pow continuous_id _).intervalIntegrable _ _`.

**Time-box**: if Deliverable 1.B's first compile exceeds 90s wall, drop
the explicit `integral_const_mul` chain and try a `simp` with the
appropriate lemma set instead:
```lean
simp [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, integral_pow, integral_one,
      Nat.cast_ofNat, Nat.cast_one]
```
followed by `ring` or `norm_num`. This is a Plan B if the explicit
chain stalls.

LOC: ~110.

### Non-vacuity witness

Add (or extend the existing block) at the end of the (342d) witness
section:

```lean
example : (1 : ℝ) / 9 = 1 / (2 * 4 + 1) := by norm_num
```

(Confirms the `1/9 = 1/(2n+1)` formula at `n = 4`.)

## Priority 2 (stretch, only if Priority 1 closes in <40 min)

Ship one of:
* **`butcherShiftedLegendre_natDegree_three` and `_four`** — extend
  cycle 272's `butcherShiftedLegendre_natDegree` witness to small `n`.
  Each is a one-liner using the cycle 272 general lemma at the
  concrete index. ~5 LOC each.
* **n=2 Rodrigues witness** — `2! · P_2^* = (-1)^2 · derivative^[2]
  (X^2 · (1-X)^2)`. Mirrors cycle 272's general statement at `n = 2`.
  ~10 LOC.

Skip Priority 2 if Priority 1 wall-clock exceeds 40 minutes.

## What NOT to try (explicit blockers from prior cycles)

1. **Do NOT attempt (342f) recurrence manually.** Cycle 273 task
   results documented that `Polynomial.ext` and `Polynomial.funext`
   both require Pascal-style binomial identities that `ring` cannot
   close. Mathlib has no standard Legendre infrastructure to bridge.
   Wait for Aristotle's general (342a) to land first.

2. **Do NOT cancel either Aristotle project.** Both are advancing
   ~10%/cycle and are expected to complete in 4–6 more cycles. The
   slot-pool cost is negligible compared to manual proof attempts.

3. **Do NOT re-poll Aristotle.** Single poll per project per cycle
   per CLAUDE.md.

4. **Do NOT use `Polynomial.ext + ring`** for the polynomial identity
   at `n = 4`. Use the per-coefficient `match k` recipe from cycles
   273/275/276. `ring` cannot fold `Polynomial.C` constants over ℝ.

5. **Do NOT introduce sorries.** Cycle 138/139, 149/150, 171/172,
   200/201 all rolled back sorry-first scaffolds; cycle 277's bar is
   axiom-clean or skip the cycle.

6. **Do NOT raise `maxHeartbeats`.** If a `simp` in Deliverable 1.A
   times out at default heartbeats, decompose into per-k
   `simp only [...]` calls with explicit lemma sets instead.

7. **Do NOT touch `Section441.lean`** (43rd consecutive GPFS timeout
   per `cycle_182_gpfs_slowness.md`; skip per strategy §A).

8. **Do NOT edit `scripts/autonomous_loop.py`.** Loop-maintainer
   territory; phantom verdict patterns documented in
   `phantom_commit_verdict_pattern.md`.

## Faithfulness checklist (pre-commit, MANDATORY)

For Deliverable 1.A (`butcherShiftedLegendre_four`):
* This is **helper infrastructure** for (342d), not a textbook-named
  entity. Cycle 273/275/276 precedent established this naming convention.
* Sanity at `x = 1`: `70 − 140 + 90 − 20 + 1 = 1` ✓
  (matches `butcherShiftedLegendre_eval_one`).
* Sanity at `x = 0`: coefficient is `1`, matching
  `butcherShiftedLegendre_eval_zero` at `(−1)^4 = 1` ✓.
* Identity check: proof does real per-coefficient
  `coeff_shiftedLegendre` arithmetic, not `exact h_anything`.
* Tautology check: `= 70X^4 - 140X^3 + 90X^2 - 20X + 1` is not a
  hypothesis.

For Deliverable 1.B (`butcherShiftedLegendre_norm_sq_four`):
* Entity ID: `lem:342A` clause (342d), at `n = 4`. Butcher (342d):
  `∫₀¹ P_n^*(x)^2 dx = 1/(2n+1)`. At `n = 4`, RHS = `1/9`. Statement
  captures: **same content** at the specific instance.
* `lean_status.json` row for `lem:342A` stays `partial` (general `n`
  still in Aristotle queue).
* Identity check: proof does real `integral_pow` work, not a hypothesis
  re-export.
* Tautology check: `= 1/9` not equal to any hypothesis.
* Hypothesis strength check: no extra hypotheses; `n = 4` inlined.

## Verification

After both deliverables compile:
1. `lake env lean OpenMath/Chapter3/Section342.lean` exits 0.
2. `grep -c sorry OpenMath/Chapter3/Section342.lean` returns 0.
3. `#print axioms OpenMath.Chapter3.Section342.butcherShiftedLegendre_four`
   returns `[propext, Classical.choice, Quot.sound]`.
4. `#print axioms OpenMath.Chapter3.Section342.butcherShiftedLegendre_norm_sq_four`
   returns `[propext, Classical.choice, Quot.sound]`.
5. Bump `lean_status.json` `lem:342A` cycle to 277 (status stays
   `partial`).
6. Update `plan.md` `lem:342A` row's cycle progress note to reflect
   the `n = 4` extension.

## Task results write-up (MANDATORY before commit)

Write `.prover-state/task_results/cycle_277.md` with:
* What was tried (Priority 0 poll outcomes, both projects).
* What worked (Deliverable 1.A and 1.B, with LOC counts).
* Dead ends (if any — e.g. if the odd-n peel-off was needed at n=4
  unexpectedly, or if `continuity` timed out and Plan B was invoked).
* Faithfulness check entries for both new theorems.
* Suggested next approach for cycle 278 (poll Aristotle again,
  decide on n=5 vs Aristotle integration).

## Commit message template

```
Cycle 277 — §342 (342d) n=4 case + butcherShiftedLegendre_four SHIPPED.

* New: `butcherShiftedLegendre_four : P_4^* = 70X^4 - 140X^3 + 90X^2
  - 20X + 1` (axiom-clean, mirrors cycle 275's _two recipe at even n).
* New: `butcherShiftedLegendre_norm_sq_four : ∫₀¹ (P_4^*)^2 = 1/9`
  (axiom-clean, 9-monomial extension of cycle 276's 7-monomial split).
* Section342.lean grows ~623 → ~755 LOC, 0 sorries.
* Aristotle polls: 342a @ X%, 342d @ Y% (single-poll discipline).
```

## Cycle 278+ outlook

* If Aristotle (342a) or (342d) lands in cycle 278, **integrate it
  immediately** as Priority 1; defer ladder extension to n=5.
* If both still IN_PROGRESS, ship n=5 (`butcherShiftedLegendre_five`
  and `_norm_sq_five = 1/11`). At n=5 the `(−1)^5 = −1` odd-n simp
  peel-off pattern recurs; lift cycle 276's
  `simp only [coeff_C_mul, coeff_map, coeff_shiftedLegendre]` into a
  named helper lemma to future-proof odd-n cases.
* By cycle 281 at the current 10%/cycle Aristotle pace, expect (342a)
  to close; plan for integration cycle 281 and pivot to (342f)
  recurrence in cycle 282+.
