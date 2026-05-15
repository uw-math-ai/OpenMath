# Cycle 280 Results

## Worked on

§342 (342d) ladder rung at `n = 7`:
- `butcherShiftedLegendre_seven` — closed-form expansion
  `P_7^* = 3432X^7 - 12012X^6 + 16632X^5 - 11550X^4 + 4200X^3 - 756X^2 + 56X - 1`
- `butcherShiftedLegendre_norm_sq_seven` — `∫₀¹ (P_7^*(x))^2 dx = 1/15`
- Non-vacuity witness `1/(2·7+1) = 1/15`

Also polled Aristotle project `d4ce527b-b714-4e51-b0a6-e3d06302d7fa`
(general (342d) proof) — status **IN_PROGRESS at 58%** (up from 52% in
cycle 279). Single poll only per CLAUDE.md. Branch B (manual n=7 rung).

## Approach

**Priority 0 (Aristotle poll)**: Called `mcp__aristotle__get_status` once.
Result: `IN_PROGRESS, 58%`. Did not re-poll. Did not cancel the job.

**Priority 1 (n=7 ladder rung)**:

1.1 `butcherShiftedLegendre_seven`:
- Ported cycle 278 `_five` odd-`n` template (with constant term `-1`)
  to `n = 7`. The outer Butcher sign factor `(-1)^7 = -1` flips every
  shifted-Legendre coefficient, giving the closed form above.
- Recipe: `unfold butcherShiftedLegendre; ext k; simp only [coeff_C_mul,
  coeff_map, coeff_shiftedLegendre]; match k with ...`.
- For `k ∈ {2,3,4,5,6}`, pre-extracted both `Nat.choose 7 k` and
  `Nat.choose (7+k) 7` via `decide`-helpers. For `k = 7`, only
  `Nat.choose 14 7 = 3432` is needed.
- The `k + 8` catch-all closes via `Nat.choose_eq_zero_of_lt`.

1.2 `butcherShiftedLegendre_norm_sq_seven`:
- Pre-computed the 15-coefficient convolution `(P_7^*)^2` by Python:
  `c_0..c_14 = (1, -112, 4648, -93072, 1065036, -7677264, 36990408,
  -123519792, 291657828, -490289184, 582929424, -478846368, 258450192,
  -82450368, 11778624)`. Cross-checked `c_0 = 1`, `c_14 = 3432^2 =
  11778624`, and verified `Σ c_k/(k+1) = 1/15` via `fractions.Fraction`.
- Rewrote the integrand via `butcherShiftedLegendre_seven` + `simp` +
  `ring` to the explicit degree-14 polynomial in `x`.
- 13 `IntervalIntegrable` witnesses (`hi_x14, hi_x13, …, hi_x`) via
  `(continuous_pow k).intervalIntegrable 0 1`.
- 14 `integral_pow` evaluations `h14, h13, …, h1`.
- 14-deep cascade of `intervalIntegral.integral_add` /
  `integral_sub` rewrites, with leading-paren counts
  `14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1` mirroring cycle 279
  `_norm_sq_six` pattern scaled by +2 ops.
- 14 `integral_const_mul` rewrites factor out the leading constants.
- Final `ring` collapses the 15-fraction sum to `1/15`.

## Result

**SUCCESS** — both theorems compile axiom-clean. Verification:

```
$ lake env lean OpenMath/Chapter3/Section342.lean   # exit 0
$ lake build OpenMath.Chapter3.Section342           # exit 0
$ lake env lean OpenMath/Chapter3.lean              # exit 0
$ grep -c sorry OpenMath/Chapter3/Section342.lean   # 0
$ #print axioms butcherShiftedLegendre_seven
  → [propext, Classical.choice, Quot.sound]
$ #print axioms butcherShiftedLegendre_norm_sq_seven
  → [propext, Classical.choice, Quot.sound]
```

Section342.lean grew from 1466 → 1740 LOC (+274 LOC). The 8 pre-existing
"unused simp arg" linter warnings remain (cycles 271–279 carry-over; not
errors). One new identical warning at the `_seven` `k = 6` arm
(`hch2 : Nat.choose 7 6 = 7` is technically redundant since `simp` /
`decide` can solve C(7,6) = 7 inline, but is kept for stylistic
consistency with `_six`).

## Faithfulness check

### `butcherShiftedLegendre_seven`

- Entity ID: §342 helper for (342d). Not a standalone entity in
  `formalization_data/entities/`; supports `lem:342A` (342d clauses).
- Textbook context (from §342, Butcher 3rd ed.): the shifted Legendre
  polynomial `P_n^*` has the explicit form
  `P_n^*(x) = Σ_{k=0}^n (-1)^{n-k} C(n,k) C(n+k,n) x^k`. At `n = 7`,
  this gives `-1 + 56x - 756x^2 + 4200x^3 - 11550x^4 + 16632x^5
  - 12012x^6 + 3432x^7`.
- Lean statement captures: **same content** (rearranged to descending
  degree). Validated against
  - (342b) `P_n^*(1) = 1`: `3432 - 12012 + 16632 - 11550 + 4200 - 756
    + 56 - 1 = 1` ✓
  - `butcherShiftedLegendre_eval_zero`: `P_7^*(0) = (-1)^7 = -1` ✓
    (constant term is `-1`).

### `butcherShiftedLegendre_norm_sq_seven`

- Entity ID: §342 (342d) at `n = 7`. From `entities/lem_342A.json`,
  (342d) states:
  > $$ \int_0^1 [P_n^*(x)]^2 \, dx = \frac{1}{2n+1}. $$
- Lean statement captures: **same content** at the concrete instance
  `n = 7` (so `1/(2·7+1) = 1/15`). The non-vacuity witness
  `1/(2 * (7 : ℕ) + 1) = 1/15` confirms the closed-form match.
- Hypothesis strength: no extra hypotheses; matches the textbook's
  unconditional claim at this `n`.

### Tautology / identity / definition-smuggling checks

- No theorem conclusion appears verbatim as a hypothesis.
- Neither proof reduces to `exact h` or `id`.
- No new `def`, `structure`, or `class` introduced — both new
  declarations are `theorem`s with explicit computational content.

## Dead ends

None this cycle. The c_k convolution Python pre-check caught nothing
since the arithmetic was correct on the first pass (cross-check
`Σ c_k/(k+1) = 1/15` via `Fraction` confirmed before any Lean code was
written, per Priority 1.2 risk-mitigation R2 and the cycle 259 Bell-
coefficient precedent).

## Discovery

1. **Paren-count formula confirmed for n=7**: leading parens on the
   outermost integrability witness `intervalIntegral.integral_add LHS
   intervalIntegrable_const` equals `n + 7` (where the integrand has
   `2n + 1` terms and `2n` binary ops, the outermost split takes off
   the `+1` and the LHS has `2n` terms with `2n - 1` binary ops,
   needing `2n` leading parens). Wait — for n=6, the formula predicts
   `12` leading parens, matching cycle 279. For n=7, it predicts `14`,
   matching this cycle. **Closed form: leading parens at outermost
   level = 2n. Each subsequent rewrite step decrements by 1.** This
   was empirically validated and is now a robust template for n=8+.

2. **n=7 add/sub alternation**: at odd `n`, the outermost binary op
   in the `(P_n^*)^2` integrand is always `+ 1` (since `c_0 = a_0^2
   = ((-1)^n)^2 = 1`). The 14 binary ops alternate `+, -, +, -, …`
   starting from `+ 1` on the right. The innermost (last) op is
   `x^{2n} - x^{2n-1}` (sign of `c_{2n-1} = 2 · a_n · a_{n-1}`, which
   is negative because `a_n = -3432 < 0` and `a_{n-1} = 12012 > 0`).
   For even `n`, the analogous innermost op would be `+`. This
   pattern stays consistent regardless of n.

3. **`hch2` redundancy at the second-to-top arm**: at `k = 6` of
   `_seven` (and `k = 5` of `_six`, `k = 4` of `_five`), the inner
   `Nat.choose n (n-1) = n` factor is small enough that `simp` /
   `decide` closes it without the explicit `have`. The linter flags
   this as "unused simp arg". Future cycles can drop the redundant
   `hch2` at the second-to-top arm.

4. **File size growth**: Section342.lean is now 1740 LOC. Cycle 279's
   discovery #4 set the split threshold at "after general (342d) lands
   OR after n=8". We are right at this boundary. The next ladder rung
   (n=8) would push to ~1990 LOC, justifying a split. Suggested split:
   `Section342Basic.lean` (defn + 342b/c/e/orthogonality), and
   `Section342NormSquare.lean` (ladder rungs + general (342d) when
   Aristotle returns).

## Suggested next approach

The planner should:

1. **Poll Aristotle `d4ce527b` once more in cycle 281**. With 58% in
   one cycle from 33%→52%→58% trajectory (cycles 278→279→280), the
   project is plausibly nearing completion. Branch A integration
   instructions in cycle 280 strategy still apply.

2. **If Aristotle remains IN_PROGRESS in cycle 281**: pivot to either
   - **n=8 ladder rung** (mechanical extension; same recipe, +2 binary
     ops in the integral cascade; 17 leading parens at outermost level)
     — file would grow to ~1990 LOC.
   - **File split**: factor `_zero..._seven` ladder + `_norm_sq_*`
     witnesses into a new `Section342NormSquare.lean`. The basic
     definition, (342b), (342c), (342e), and the orthogonality theorem
     (342a) stay in `Section342.lean`.
   - **Fresh entity**: pivot to `thm:344A` or `lem:342B` (currently
     unaddressed in `lean_status.json`).

3. **Do NOT** attempt (342f) three-term recurrence (cycle 273 blocker
   stands) or (342g) `n` distinct real zeros (deferred; requires
   Sturm-type arguments).

4. **Recommended priority order if Aristotle remains stuck**:
   file split (lowest risk, mechanical, organizational benefit) >
   n=8 rung (diminishing returns but reliable closure) > fresh entity
   (higher risk, broader scope).
