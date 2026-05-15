# Cycle 277 Results

## Worked on
* **Priority 0 (Aristotle poll)**: Single poll of `727396d5` (342a) and
  `d4ce527b` (342d). 342a returned **COMPLETE** (100%, ran 2026-05-15
  12:59 → 14:01). 342d still **IN_PROGRESS** at 31%.
* **Priority 1 pivot to Branch B (342a integration)**: integrated
  Aristotle's proof of `butcherShiftedLegendre_orthogonal` (with 4
  helper lemmas) into `OpenMath/Chapter3/Section342.lean`.
* **Priority 1 supplementary (n=4 ladder)**: shipped
  `butcherShiftedLegendre_four` and `butcherShiftedLegendre_norm_sq_four`
  per the original Priority 1 plan, since the cycle still had budget
  after the integration.

## Approach

### A. Aristotle (342a) integration
1. `mcp__aristotle__extract_result` to
   `.prover-state/aristotle_results/cycle_277/727396d5/`.
2. Read `ARISTOTLE_SUMMARY.md` — confirmed `success: true`, 0 sorries.
3. Aristotle's proof has 4 helper lemmas + main theorem:
   - `iterDeriv_XnOneSubXn_eval_zero` (k-th derivative of `X^n(1-X)^n`
     vanishes at `x=0` for `k<n`; uses `Polynomial.iterate_derivative_mul`
     + induction on `m` for `derivative^[m] (X^n) = C (descFactorial n m)
     · X^(n-m)` + `simp_all +decide`).
   - `iterDeriv_XnOneSubXn_eval_one` (similar, at `x=1`; uses `(1-X)^n`
     derivative expansion).
   - `poly_ibp` (integration by parts on `[0,1]` for polynomial evals).
   - `integral_poly_mul_iterDeriv_vanish` (general iterated IBP × n by
     induction).
   - `integral_poly_mul_iterDeriv_XnOneSubXn_eq_zero` (specialization).
   - `butcherShiftedLegendre_orthogonal` (main: WLOG m<n via `wlog`,
     substitute Rodrigues, apply IBP lemma using
     `butcherShiftedLegendre_natDegree`).
4. **Required imports added**: `Mathlib.Analysis.Calculus.Deriv.Polynomial`
   (for `Polynomial.differentiableAt`, `Polynomial.hasDerivAt`),
   `Mathlib.Topology.Algebra.Polynomial` (for `Polynomial.continuous`),
   `Mathlib.Tactic.Cases` (for the `induction'` tactic used in two of
   the helpers).
5. **Cleanup**: Rewrote Aristotle's `poly_ibp` from a manual
   `intervalIntegral.integral_deriv_eq_sub'` chain (which had Lean parser
   issues with the nested `(by exact ...)` blocks across newlines) into
   a clean specialization of Mathlib's
   `intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt` using
   `f.hasDerivAt` and `(Polynomial.continuous f).continuousOn`.
6. Three non-vacuity witnesses: orthogonality at
   `(m,n) ∈ {(0,1), (1,2), (0,2)}` (all closed by direct application of
   the main theorem with `by decide` for the `m ≠ n` hypothesis).

### B. Cycle 277 Priority 1 ladder ship (n = 4)
* `butcherShiftedLegendre_four`: tried the cycle-275 `_two` even-n
  recipe first (no peel-off). **Failed** — left residual goals
  `((-1)^4 * map ...).coeff k = ...` at every k. Fell back to cycle
  276's `_three` peel-off pattern + per-arm `norm_num`. Plus needed
  `Nat.choose 4 2 = 6` decide-helper at k=2 in addition to the obvious
  `Nat.choose (n+k) n` helpers.
* `butcherShiftedLegendre_norm_sq_four`: direct extension of cycle 276's
  `_three` recipe to 9 monomials. The integrand
  `(P_4^*(x))^2 = 4900x⁸ - 19600x⁷ + 32200x⁶ - 28000x⁵ + 13840x⁴ -
   3880x³ + 580x² - 40x + 1` (coefficients hand-computed and verified
  by `∫₀¹` summing to `1/9`). 8 nested `integral_add`/`integral_sub` +
  `integral_const_mul` × 8 + `integral_pow` × 7 + `integral_one`. The
  cycle-276 `Continuous.intervalIntegrable` pattern worked without
  modification.

## Result
**SUCCESS** — three new axiom-clean theorems shipped:
* `butcherShiftedLegendre_orthogonal` (342a)
* `butcherShiftedLegendre_four` (helper)
* `butcherShiftedLegendre_norm_sq_four` (342d at n=4)

All three verified `#print axioms` returns
`[propext, Classical.choice, Quot.sound]`. `Section342.lean` grew
from 623 → ~1043 LOC, 0 sorries. Build succeeds.

## Faithfulness check

### `butcherShiftedLegendre_orthogonal`
- Entity ID: `lem:342A` clause (342a). Butcher textbook statement:
  > `∫₀¹ P_m^*(x) P_n^*(x) dx = 0`, `m ≠ n`.
- Lean statement: `∀ {m n : ℕ} (hmn : m ≠ n), ∫ x in (0:ℝ)..1,
  (butcherShiftedLegendre m).eval x * (butcherShiftedLegendre n).eval x
  = 0`. **Same content** verbatim.
- Identity check: proof does real `wlog` + Rodrigues substitution + IBP
  × n + `natDegree`-driven degree bound, not `exact h`.
- Tautology check: conclusion `= 0` is not a hypothesis.
- Hypothesis strength check: the only hypothesis `m ≠ n` is exactly the
  textbook's `m ≠ n`. No extra strength.
- Definition smuggling check: orthogonality is genuinely proved (not
  baked into the definition of `butcherShiftedLegendre`, which is the
  Mathlib `shiftedLegendre n` scaled by `(-1)^n`).

### `butcherShiftedLegendre_four`
- This is **helper infrastructure**, not a textbook-named entity (cycle
  273/275/276 precedent: `_one`, `_two`, `_three`).
- Sanity at `x = 1`: `70 − 140 + 90 − 20 + 1 = 1` ✓ (matches
  `butcherShiftedLegendre_eval_one`).
- Sanity at `x = 0`: coefficient of `X^0` is `1`, matching
  `butcherShiftedLegendre_eval_zero` at `(−1)^4 = 1` ✓.
- Identity check: per-coefficient `coeff_shiftedLegendre` arithmetic at
  k ∈ {0,1,2,3,4,k+5}, not `exact h`.
- Tautology check: `= 70X^4 - 140X^3 + 90X^2 - 20X + 1` is not a
  hypothesis.

### `butcherShiftedLegendre_norm_sq_four`
- Entity ID: `lem:342A` clause (342d), at `n = 4`. Butcher (342d):
  > `∫₀¹ P_n^*(x)^2 dx = 1/(2n + 1)`.
  At `n = 4`, RHS = `1/9`. Statement captures: **same content** at the
  specific instance.
- `lean_status.json` row for `lem:342A` stays `partial` (general `n`
  still in Aristotle queue `d4ce527b`; (342f), (342g) untouched).
- Identity check: proof does real `integral_pow` work at k ∈ {1..8}, not
  a hypothesis re-export.
- Tautology check: `= 1/9` not equal to any hypothesis.
- Hypothesis strength check: no extra hypotheses; `n = 4` inlined.

## Dead ends
* **Cycle 275 even-n recipe failed at n=4**. The strategy predicted
  that even `n` would let us use the cycle-275 `_two` recipe (no
  peel-off). Empirically at n=4 the bare `simp` left residual goals of
  the form `((-1)^4 * map ...).coeff k = ...` because `simp` collapsed
  `C ((-1)^4)` to the polynomial `1` before `coeff_C_mul` could fire.
  The cycle-276 `_three` peel-off pattern (`simp only [coeff_C_mul,
  coeff_map, coeff_shiftedLegendre]` prepended to `ext k`) closed it.
  **Conclusion**: the peel-off pattern is needed at every n ≥ 3, not
  just odd `n` as the strategy speculated. Future ladder rungs should
  default to the peel-off recipe.
* **`Polynomial.differentiableAt` and `Polynomial.continuous` not
  transitively imported**. The cycle 271–276 work didn't need these, so
  the file's imports omitted them. Adding `Mathlib.Analysis.Calculus.Deriv.Polynomial`
  and `Mathlib.Topology.Algebra.Polynomial` was the fix.
* **`induction'` tactic not in the default tactic set imported by
  `Mathlib.RingTheory.Polynomial.ShiftedLegendre`** — needed explicit
  `import Mathlib.Tactic.Cases`.
* **Aristotle's `poly_ibp` proof relied on a manual `intervalIntegral.integral_deriv_eq_sub'`
  chain that parsed cleanly under Aristotle's `import Mathlib` but not
  under our scoped imports**: the nested `(by exact Continuous.add
  (Continuous.mul ...))` block confused the parser at the `(`-after-newline
  boundary. Rewrote using `intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt`
  directly — fewer lines, no parser issue, axiom-equivalent.

## Discovery
1. **Mathlib's `integral_mul_deriv_eq_deriv_mul_of_hasDerivAt` is the
   right IBP lemma** for polynomial inputs on `[0,1]`. It has the
   structure `∫ u·v' = uv|_a^b - ∫ u'·v` which matches `poly_ibp`'s
   goal exactly when `u := f.eval`, `v := g.eval`,
   `u' := (derivative f).eval`, `v' := (derivative g).eval`. Each
   `IntervalIntegrable` side-goal closes by `(Polynomial.continuous _).intervalIntegrable _ _`.
2. **The cycle-276 peel-off pattern generalizes to all `n ≥ 3`**, not
   just odd `n`. The `(−1)^n` constant factor, even when it's `+1`,
   confuses `simp` enough that pre-`simp only [coeff_C_mul, coeff_map,
   coeff_shiftedLegendre]` is necessary for the per-k arms to close.
3. **`Nat.choose 4 2 = 6` needs explicit `decide` hint at n=4, k=2**
   even though `Nat.choose 5 4 = 5`, `Nat.choose 7 4 = 35`,
   `Nat.choose 8 4 = 70` all auto-evaluate. Reason unclear — likely a
   simp-rewriter quirk with the specific argument structure.
4. **Aristotle's proof depends on `Polynomial.iterate_derivative_mul`**
   (in `Mathlib.Algebra.Polynomial.Derivative`, transitively imported
   via `ShiftedLegendre`) — confirmed during integration.
5. **The `wlog` tactic** is the right idiom for `m ≠ n` symmetry
   in inner-product orthogonality proofs. Aristotle used
   `wlog hmn' : m < n generalizing m n; · convert this hmn.symm
   (lt_of_le_of_ne (le_of_not_gt hmn') hmn.symm) using 1; ac_rfl`
   which is clean and reusable.

## Suggested next approach (cycle 278)
1. **Re-poll Aristotle**: single check on `d4ce527b` (342d general,
   31% at last poll). If COMPLETE → integrate immediately as
   `butcherShiftedLegendre_norm_sq`. If still IN_PROGRESS, proceed
   below.
2. **Continue the ladder to `n = 5`** as fallback: ship
   `butcherShiftedLegendre_five : P_5^* = …` (the peel-off pattern
   now confirmed at all `n ≥ 3`) and `butcherShiftedLegendre_norm_sq_five
   : ∫₀¹ (P_5^*(x))^2 dx = 1/11`. Coefficients for n=5 (odd) per the
   `coeff_shiftedLegendre` formula:
   - `P_5^* = -252·x⁵ + 630·x⁴ - 560·x³ + 210·x² - 30·x + 1`
   (verifiable: eval at `x=1` gives `1`; `(−1)^5 = −1` flips every
   sign).
3. **Alternative (more ambitious)**: with orthogonality now in hand,
   attempt **(342f) three-term recurrence**:
   `n P_n^*(x) = (2x-1)(2n-1) P_{n-1}^*(x) - (n-1) P_{n-2}^*(x)`.
   The recurrence is derivable from orthogonality via inner-product
   expansion of `xP_n^*` against `{P_k^*}_{k=0..n+1}`. This was blocked
   in cycles 273+ because the manual Pascal-binomial proof had no
   Mathlib infrastructure; with orthogonality the path is open.
4. **Alternative (long-shot)**: with orthogonality + natDegree, the
   (342g) `n` distinct real zeros result follows from a standard
   "orthogonal polynomial roots" argument. Mathlib might already have a
   general lemma — worth a `lean_leansearch` / `lean_loogle` query
   before manual attempt.
5. **Do NOT cancel `d4ce527b`** (342d general) — at ~10%/cycle pace,
   expected to land ~cycle 281.
