# Cycle 276 Results

## Worked on
- Priority 0: Single-poll of both Aristotle projects (mandatory).
- Priority 1: §342 (342d) ladder at `n = 3`: shipped
  - `butcherShiftedLegendre_three : P_3^* = 20X³ - 30X² + 12X - 1`
  - `butcherShiftedLegendre_norm_sq_three : ∫₀¹ (P_3^*)² = 1/7`

## Approach

### Aristotle poll (Priority 0)
* `727396d5-14f9-4014-9aad-1f38238a1651` (342a orthogonality): IN_PROGRESS, 32%.
* `d4ce527b-b714-4e51-b0a6-e3d06302d7fa` (342d general norm-square): IN_PROGRESS, 23%.

Both projects advanced from last cycle (22% → 32% and 11% → 23%). No
download/integration triggered. Proceeded to Branch C (Priority 1).

### Priority 1 — `butcherShiftedLegendre_three`
Mirrored cycle 275's `_two` recipe with one structural change: at
`n = 3`, the Butcher sign factor `(-1)^3 = -1` survives the `C` push,
so the polynomial `C ((-1)^3) * map(...) (shiftedLegendre 3)` does NOT
collapse to `map(...) (shiftedLegendre 3)` the way `(-1)^2 = 1` did at
`n = 2`. With the cycle 275 simp recipe applied verbatim, `simp`
normalized `C ((-1)^3)` to the polynomial `-1` via `C_pow + C_neg + C_1`,
which destroyed the `C a * p` pattern needed by `coeff_C_mul`, leaving
unsolved goals like `((-1)^3).coeff 0 = -1`.

**Fix**: prepended `simp only [Polynomial.coeff_C_mul, coeff_map,
coeff_shiftedLegendre]` to peel off the constant factor BEFORE the
broader simp could collapse it. After this, each `match k` arm reduces
to concrete arithmetic on `(-1)^3 * (Int.cast (...))`, which `simp +
norm_num` closes. `Nat.choose 5 3 = 10` and `Nat.choose 6 3 = 20` are
supplied via `decide`; `Nat.choose 4 3 = 4` simp evaluates on its own.

### Priority 1 — `butcherShiftedLegendre_norm_sq_three`
Extended cycle 275's 5-monomial split to 7 monomials. Integrand:
`(20x³ - 30x² + 12x - 1)² = 400x⁶ - 1200x⁵ + 1380x⁴ - 760x³ + 204x² - 24x + 1`.

The proof uses 6 nested `intervalIntegral.integral_add` /
`integral_sub` rewrites for the left-associative integrand
`((((((400x⁶ − 1200x⁵) + 1380x⁴) − 760x³) + 204x²) − 24x) + 1)`,
then `integral_const_mul` ×6, `integral_pow` for k ∈ {2..6},
the `pow_one + Nat.cast_one` trick from cycle 274/275 for `∫₀¹ x`,
and `integral_one` for the constant. Final `ring` closes
`400/7 - 200 + 276 - 190 + 68 - 12 + 1 = 1/7`.

## Result
SUCCESS — both lemmas compile, 0 errors, 0 warnings, axiom-clean
(`[propext, Classical.choice, Quot.sound]`). Section342.lean grew from
491 LOC to 623 LOC, 0 sorries. The n=3 non-vacuity witness
`= 1 / (2 * 3 + 1)` was added to the existing (342d) witness block.

## Faithfulness check

### `butcherShiftedLegendre_three`
* This is **helper infrastructure** for (342d), not an entity-level
  textbook-named theorem. The cycle 273/275 precedent for `_one` and
  `_two` established the convention.
* Sign sanity: at `x = 1`, evaluates to `20 - 30 + 12 - 1 = 1` ✓
  (matches `butcherShiftedLegendre_eval_one`); at `x = 0`, evaluates
  to `-1` ✓ (matches `butcherShiftedLegendre_eval_zero` since
  `(-1)^3 = -1`).
* Identity check: the proof is NOT `exact h_anything`; it does real
  per-coefficient `Polynomial.ext` work via `coeff_shiftedLegendre`
  and concrete arithmetic.
* Tautology check: `= 20X³ - 30X² + 12X - 1` is not a hypothesis.

### `butcherShiftedLegendre_norm_sq_three`
* Entity ID: `lem:342A` clause (342d), at the specific case `n = 3`.
  Butcher (342d) reads:
  > `∫₀¹ P_n^*(x)^2 dx = 1/(2n + 1)`
  At `n = 3`, RHS = `1/7`. Lean statement matches verbatim. **Captures:
  same content** at the specific instance.
* Identity check: the proof does real integration work via
  `integral_pow` + intervalIntegral_add/sub bookkeeping, not a
  hypothesis re-export.
* Tautology check: `= 1/7` not equal to any hypothesis.
* Hypothesis strength check: no extra hypotheses; just `n = 3`
  inlined.
* `lean_status.json` row for `lem:342A` stays `partial` (per strategy):
  general `n` case still in Aristotle queue.

## Dead ends

### Cycle 275's `_two` simp recipe applied verbatim fails at `n = 3`
At `n = 3`, `C ((-1)^3)` gets simplified by simp's `C_pow + C_neg`
chain to the polynomial `(-1) : ℝ[X]`, which is structurally NOT in
the `C a * p` form required by `coeff_C_mul`. The result was 5
unsolved goals after the per-k simp, with patterns like:
* `((-1) ^ 3).coeff 0 = -1`
* `((-1) ^ 3 * map (Int.castRingHom ℝ) (shiftedLegendre 3)).coeff 1 = 12`

This pattern did NOT manifest at `n = 2` because `(-1)^2 = 1` and
`C 1 = 1` are both simp lemmas that collapse the constant cleanly.

**Resolution**: prepend `simp only [coeff_C_mul, coeff_map,
coeff_shiftedLegendre]` to peel off the C factor BEFORE the general
simp normalizes it. This pattern will recur at every odd `n` in the
ladder if we continue (n = 5, 7, ...).

## Discovery

1. **Odd-n simp pitfall**: the cycle 275 recipe for `_two` is NOT a
   universal template for the ladder. Odd `n` requires the explicit
   `simp only [coeff_C_mul, ...]` peel-off step before the broader
   simp. Cycle 277 should embed this fact in `_one` retroactively to
   future-proof the pattern (cycle 273's `_one` happens to work because
   `(-1)^1 = -1` triggers the `C_neg + C_one_neg = -1` simp chain that
   leaves the `C ... * p` form intact when the inner constant is small;
   for `_three` the `(-1)^3` factor interacts differently).

2. **`Nat.choose` evaluation by simp**: simp evaluates `Nat.choose 4 3`
   without help (the `hch` hint was reported unused at k=1), but
   `Nat.choose 5 3` and `Nat.choose 6 3` require explicit `decide`.
   Threshold appears to be around the second binomial argument crossing
   3.

3. **7-monomial integral split is straightforward**: extending cycle
   275's 5-monomial recipe to 7 monomials added ~30 LOC of nested
   `intervalIntegral.integral_add/sub` arguments but no new conceptual
   difficulty. The pattern scales linearly with degree. Time-box rule
   from strategy (60s wall) was respected — first compile succeeded.

4. **Aristotle progress is steady but slow**: both projects advanced
   ~10% in one cycle (~28 hours of compute since cycle 275 submission).
   At this rate, (342a) and (342d) general cases will land around
   cycle 281-283.

## Suggested next approach

### For cycle 277 (one of these):

**Option A — extend the ladder to `n = 4`**: ship
`butcherShiftedLegendre_four : P_4^* = 70X⁴ - 140X³ + 90X² - 20X + 1`
and `butcherShiftedLegendre_norm_sq_four = 1/9`. Even `n = 4` means
the cycle 275 simp recipe applies cleanly (no odd-n peel-off needed).
Adds ~100 LOC, axiom-clean, leverages all existing infrastructure.

**Option B — orthogonality at small cases**: prove
`butcherShiftedLegendre_orthogonal_zero_one : ∫₀¹ P_0^* · P_1^* = 0`
and similar for `(0, 2)`, `(0, 3)`, `(1, 2)`, `(1, 3)`, `(2, 3)`.
These are direct polynomial integrations of degree ≤ 6, no Rodrigues
machinery needed. ~80 LOC for the 6 small cases. Useful as
witnesses if Aristotle's general (342a) lands.

**Option C — non-vacuity witnesses for `_rodrigues` at `n = 3`**:
verify that `3! · P_3^* = -1 · derivative^[3] (X^3 · (1-X)^3)`
expands to the closed form. Small cycle, ~10 LOC.

**Recommendation**: Option A. Continues the ladder steadily and
mirrors the cycle 273 → 274 → 275 → 276 progression. Option B is
attractive but a stepping-stone toward the general (342a) that
Aristotle is already working on; if Aristotle lands, Option B
becomes redundant. Option C is too narrow for a full cycle.

### Watch
* If either Aristotle project crosses 50% by cycle 277's poll, plan
  for integration in cycle 278.
* The `simp only [coeff_C_mul, coeff_map, coeff_shiftedLegendre]`
  peel-off pattern should be lifted into a helper lemma if we add
  more odd-n cases (n = 5, 7).
