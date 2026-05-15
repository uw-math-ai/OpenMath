# Cycle 275 Results

## Worked on

* **P1**: Single-poll of both Aristotle projects (cycle 273's (342a)
  `727396d5-14f9-4014-9aad-1f38238a1651` and cycle 274's (342d)
  `d4ce527b-b714-4e51-b0a6-e3d06302d7fa`).
* **P3**: Manual ship of Butcher §342 (342d) at `n = 2` —
  `∫₀¹ (P_2^*(x))^2 dx = 1/5` plus its prerequisite
  expansion lemma `butcherShiftedLegendre_two : P_2^* = 6X² - 6X + 1`.

## Approach

### P1 — Aristotle single-poll

Per CLAUDE.md "one check after 30 min is enough" and the cycle 275
strategy's "do not re-poll" rule, both projects were polled exactly
once at the start of the cycle.

```
project_id: 727396d5-14f9-4014-9aad-1f38238a1651  (342a orthogonality)
status: IN_PROGRESS  percent_complete: 22  last_updated: 2026-05-15T13:34:55
project_id: d4ce527b-b714-4e51-b0a6-e3d06302d7fa  (342d norm-square)
status: IN_PROGRESS  percent_complete: 11  last_updated: 2026-05-15T13:34:51
```

Per strategy §B.P1 branching: both `IN_PROGRESS` → skip P2 integration,
proceed straight to P3 manual `n = 2` ship.

### P3 — Manual (342d) at `n = 2`

Mirrors the cycle 273 / 274 template one rung higher on the (342d)
ladder.

**Step 3a — `butcherShiftedLegendre_two`** (expansion lemma):

The coefficient formula `Polynomial.coeff_shiftedLegendre`
`(shiftedLegendre n).coeff k = (-1)^k · C(n,k) · C(n+k,n)`
gives, for `n = 2`:

| k | (-1)^k | C(2,k) | C(2+k, 2) | product |
|---|---|---|---|---|
| 0 | 1 | 1 | 1 | 1 |
| 1 | -1 | 2 | 3 | -6 |
| 2 | 1 | 1 | 6 | 6 |
| ≥3 | — | 0 | — | 0 |

So `shiftedLegendre 2 = 6X² - 6X + 1` over ℤ, and
`butcherShiftedLegendre 2 = (-1)^2 · 1 · (shiftedLegendre 2 cast to ℝ)
= 6X² - 6X + 1` over ℝ.

Proof: `Polynomial.ext` + `match` on `k ∈ {0, 1, 2, k+3}`. The `k = 2`
case requires `Nat.choose 4 2 = 6` (closed via `decide`). The `k+3`
tail uses `Nat.choose_eq_zero_of_lt` to kill the choose factor.
~25 LOC.

**Step 3b — `butcherShiftedLegendre_norm_sq_two`**:

`(6x² - 6x + 1)² = 36x⁴ - 72x³ + 48x² - 12x + 1`. Integrating term
by term on `[0, 1]`:

`36 · (1/5) - 72 · (1/4) + 48 · (1/3) - 12 · (1/2) + 1`
`= 36/5 - 18 + 16 - 6 + 1`
`= 7.2 - 7`
`= 0.2 = 1/5` ✓

Proof: rewrite the integrand pointwise via `butcherShiftedLegendre_two`
+ `Polynomial.eval_*` simp + `ring`; split the integral via four
nested `intervalIntegral.integral_add` / `integral_sub` calls and
four `integral_const_mul`; close with `integral_pow` for
`∫₀¹ x^k` at `k ∈ {1, 2, 3, 4}` and `integral_one`. The `∫₀¹ x = 1/2`
piece uses the cycle 274 trick `simp only [pow_one, Nat.cast_one]`
to coax `integral_pow 1` into a usable form. ~40 LOC.

**Step 3c — Non-vacuity witness**:

```lean
example : ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre 2).eval x ^ 2
    = 1 / (2 * (2 : ℕ) + 1) := by
  rw [butcherShiftedLegendre_norm_sq_two]; norm_num
```

Confirms the closed-form match `1/(2n+1)` at `n = 2`.

## Result

**SUCCESS** — Cycle 275 deliverables:

1. **`butcherShiftedLegendre_two`**: `P_2^* = 6X² - 6X + 1` axiom-clean
   ([propext, Classical.choice, Quot.sound]).
2. **`butcherShiftedLegendre_norm_sq_two`**: `∫₀¹ (P_2^*)² = 1/5`
   axiom-clean ([propext, Classical.choice, Quot.sound]).
3. **One new non-vacuity witness** confirming the match to
   `1/(2n+1)` at `n = 2`.
4. **Aristotle projects** both still IN_PROGRESS — `727396d5` at 22%
   (up from cycle 274's 18% — moving slowly but progressing);
   `d4ce527b` at 11% (first poll for this project).

Section342.lean: 491 LOC, 0 sorries, 0 errors, 0 warnings.
Verified via `lean_diagnostic_messages` and per-theorem
`lean_verify`.

## Faithfulness check

### `butcherShiftedLegendre_two`

* **Entity ID**: helper for `lem:342A` (auxiliary expansion at n=2;
  see `feedback_planner_faithfulness_spotcheck.md` for the broader
  faithfulness convention).
* **Textbook statement** (quoted from
  `extraction/raw_text/full_text.txt`, Butcher Table 312(I) p.197 and
  derivable from (342e) Rodrigues at n=2):
  > `P_2^*(x) = 6x² - 6x + 1`
* **Lean statement captures**: **same content** — Lean proves
  `butcherShiftedLegendre 2 = Polynomial.C 6 * Polynomial.X ^ 2
   - Polynomial.C 6 * Polynomial.X + Polynomial.C 1`, the
  polynomial-ring identity over `ℝ[X]` corresponding to the textbook
  formula.
* **Hypotheses**: none beyond the polynomial definition.
* **Identity check**: the proof is **not** `exact h` — it unfolds
  the definition, applies `Polynomial.ext`, and computes per-coefficient
  via `Polynomial.coeff_shiftedLegendre` + `decide` on
  `Nat.choose 4 2 = 6` + `Nat.choose_eq_zero_of_lt` for the tail.
* **Tautology check**: conclusion is a polynomial-ring equality, not
  one of the hypotheses.

### `butcherShiftedLegendre_norm_sq_two`

* **Entity ID**: `lem:342A`, clause (342d), instance at `n = 2`.
* **Textbook statement** (quoted from `lem_342A.json`):
  > `∫_0^1 P_n^*(x)^2 \, dx = \frac{1}{2n + 1}, \quad n = 0, 1, 2, \dots`
* **Lean statement captures**: **same content at `n = 2`** — Lean
  proves `∫ x in (0:ℝ)..1, (butcherShiftedLegendre 2).eval x ^ 2 = 1 / 5`,
  which is the `n = 2` instance of Butcher's (342d) since
  `1 / (2 · 2 + 1) = 1/5`. A separate non-vacuity witness confirms
  the match to the closed form `1 / (2n + 1)`.
* **Hypotheses**: none beyond the polynomial definition.
* **Identity check**: the proof is **not** `exact h` — it rewrites
  `P_2^* = 6X² - 6X + 1` (`butcherShiftedLegendre_two`, cycle 275),
  expands `(6x² - 6x + 1)² = 36x⁴ - 72x³ + 48x² - 12x + 1` via
  `simp` + `ring`, splits the integral via nested
  `intervalIntegral.integral_add` / `integral_sub` /
  `integral_const_mul`, and closes via `integral_pow` (for
  `∫₀¹ x^k` at `k ∈ {2, 3, 4}`) plus explicit derivation of
  `∫₀¹ x = 1/2` from `integral_pow` (with `Nat.cast_one` simp) and
  `integral_one`.
* **Tautology check**: conclusion `= 1/5` is not equal to any
  hypothesis.

## Dead ends

* **None this cycle**. The (342d) `n = 2` ladder rung followed the
  cycle 274 template directly. The only minor friction was the
  `Nat.choose 4 2 = 6` evaluation in the `k = 2` coefficient case;
  `simp` does not unfold `Nat.choose` automatically, so an explicit
  `decide` helper was needed.

## Discovery

* **`Nat.choose 4 2` evaluation**: `simp` does not reduce
  `Nat.choose 4 2` via its defining recursion; `decide` closes the
  goal at the Nat level (and the cast to ℝ then proceeds via simp).
  Recipe for any future `butcherShiftedLegendre_n` expansion lemma:
  precompute the relevant `Nat.choose` values with `decide` and pass
  them as simp arguments.
* **Five-monomial integral split**: the cycle 274 three-monomial
  recipe extends without surprise to five monomials — four nested
  `integral_add` / `integral_sub` calls plus four `integral_const_mul`
  applications. Stable pattern for further `(342d)` rungs.
* **Cycle 274's `Nat.cast_one` trick remains essential**: `integral_pow 1`
  still produces `(b^2 - a^2) / (↑1 + 1)` with the same `Nat.cast`
  artifact noted in cycle 274. Reusable across all polynomial-integral
  proofs in this ladder.

## Suggested next approach

### Cycle 276 P1 (mandatory)

Single-poll both Aristotle projects again:

* `727396d5-14f9-4014-9aad-1f38238a1651` — (342a) orthogonality
  (created 2026-05-15T12:59, currently at 22%).
* `d4ce527b-b714-4e51-b0a6-e3d06302d7fa` — (342d) norm-square
  (created 2026-05-15T13:24, currently at 11%).

Aristotle precedent (cycle 273's (342e) Rodrigues took ~24 h to
COMPLETE); both have been running 25–24 h respectively, so completion
by cycle 276–278 is plausible.

### Cycle 276 P2 (if no Aristotle hits)

The next rung of the (342d) ladder — `n = 3` — would require
`butcherShiftedLegendre_three : P_3^* = 20X³ - 30X² + 12X - 1`.
The norm-square `∫₀¹ (P_3^*(x))^2 dx = 1/7` would then need a
six-monomial integral split (expanding `(20x³ - 30x² + 12x - 1)²` =
`400x⁶ - 1200x⁵ + ...` with 7 terms), substantially heavier than
`n = 2`. Total budget ~120–150 LOC; right at the upper bound of a
cycle. Alternative: ship just the `butcherShiftedLegendre_three`
expansion lemma (~30 LOC) without the integral, deferring the
norm-square to cycle 277.

### Alternative pivots

* **`(342f)` recurrence** remains blocked per cycle 273 attempts
  (Pascal-style binomial identities unreachable by `ring`); do NOT
  retry without `(342a)` orthogonality in hand.
* **§310/§311 Phase A.1** remains a viable pivot if both Aristotle
  jobs stall further (see `lem_310B_plan.md`).
* **`(342g)` real-zeros-in-(0,1)** still requires complex analysis
  machinery not yet built.
