# Cycle 281 Results

## Worked on

Branch A — integration of Aristotle project `d4ce527b-b714-4e51-b0a6-e3d06302d7fa`
which returned **COMPLETE** on the §342 (342d) general norm-square theorem
`butcherShiftedLegendre_norm_sq (n : ℕ) : ∫₀¹ (P_n^*(x))² dx = 1/(2n+1)`.

## Approach

1. **Aristotle poll (Priority 0)**: single `mcp__aristotle__get_status` on
   `d4ce527b` returned `{"status": "COMPLETE", "percent_complete": 100}`,
   trajectory 33% (cycle 278) → 52% (cycle 279) → 58% (cycle 280) → 100%
   (cycle 281), total compute time ~2 hours 9 minutes from submission.
2. **Download + inspect**: pulled `342d_norm_square_d4ce527b.tar.gz`,
   extracted, read `ARISTOTLE_SUMMARY.md` + `342d_norm_square.lean` +
   `NormSqHelpers.lean`. Aristotle's proof follows the textbook outline:
   Rodrigues substitution → iterated IBP × n → constant `D^n P_n^*` →
   Beta integral → arithmetic identity.
3. **Helper extraction**: created a new dedicated file
   `OpenMath/Chapter3/Section342NormSqHelpers.lean` (~210 LOC) containing
   the four reusable polynomial/integral helpers under namespace
   `OpenMath.Chapter3.Section342Helpers`:
   - `iterate_derivative_natDegree_eq` — `n`-th derivative of a degree-`n`
     polynomial is `C (leadingCoeff · n!)`.
   - `iterated_ibp_XnOneSubXn` — iterated IBP × `n` transferring all
     derivatives from `X^n · (1-X)^n` onto an arbitrary polynomial `p`,
     with sign `(-1)^n`. Boundary terms vanish via Aristotle's
     `deriv_iter_XnOneMinusXn_eval_zero/_eval_one`. (Note: cycle 277's
     `iterDeriv_XnOneSubXn_eval_zero/_eval_one` in `Section342.lean`
     prove the same statement; the helper-file copies kept the IBP
     induction proof self-contained rather than introducing a cross-file
     dependency on cycle 277's helpers.)
   - `integral_pow_mul_one_sub_pow` — Beta integral
     `∫₀¹ x^n (1-x)^n dx = (n!)²/(2n+1)!`. Derived from Mathlib's
     `Complex.betaIntegral_eval_nat_add_one_right` via cast through
     `((·:ℝ):ℂ)` plus the product identity
     `∏_{j=0}^n (n+1+j) = (2n+1)!/n!` factored through
     `Nat.factorial_mul_ascFactorial`.
   - `choose_mul_factorial_sq_div` — arithmetic identity
     `C(2n,n) · (n!)²/(2n+1)! = 1/(2n+1)` via
     `Nat.choose_mul_factorial_mul_factorial` + `field_simp` + `ring`.
4. **Bridging helpers in `Section342.lean`**: two new private lemmas
   - `butcherShiftedLegendre_leadingCoeff (n : ℕ) :
     (butcherShiftedLegendre n).leadingCoeff = (Nat.choose (2*n) n : ℝ)` —
     derived from cycle-271's `coeff_shiftedLegendre` formula:
     `(shiftedLegendre n).coeff n = (-1)^n · C(n,n) · C(2n,n)`, and the
     outer Butcher sign `(-1)^n` cancels giving `C(2n,n)`.
   - `iterate_derivative_butcherShiftedLegendre_eval (n : ℕ) (x : ℝ) :
     (D^[n] P_n^*).eval x = C(2n,n) · n!` — instant consequence of
     `iterate_derivative_natDegree_eq` + `butcherShiftedLegendre_leadingCoeff`.
5. **Main theorem**: 8-step proof following Aristotle's outline:
   1. `simp_rw [sq]` to rewrite `_^2` as `_ * _`.
   2. Substitute one `P_n^*` factor via Rodrigues
      (`butcherShiftedLegendre_rodrigues` from cycle 272), pulling out
      `(-1)^n / n!`.
   3. Apply `iterated_ibp_XnOneSubXn` to transfer all `n` derivatives.
   4. Substitute `(D^n P_n^*).eval = C(2n,n) · n!`.
   5. Pull the constant out of the integral.
   6. Apply `integral_pow_mul_one_sub_pow` to evaluate the Beta integral.
   7. Collapse `(-1)^n / n! · (-1)^n · …` to `C(2n,n) · (n!)²/(2n+1)!`
      using `(-1)^n · (-1)^n = 1`.
   8. Apply `choose_mul_factorial_sq_div` to close to `1/(2n+1)`.
6. **Aggregator update**: added `import OpenMath.Chapter3.Section342NormSqHelpers`
   to both `OpenMath/Chapter3.lean` and `OpenMath/Chapter3/Section342.lean`.

## Result

SUCCESS — the general (342d) `butcherShiftedLegendre_norm_sq` ships
axiom-clean. Verified via `#print axioms`:
`['propext, Classical.choice, Quot.sound]` only.

All seven prior concrete `_norm_sq_{0..7}` cases (cycles 274–280)
remain valid as numerical witnesses (none reference the new general
theorem; they remain independent direct computations).

LOC delta:
- `Section342.lean`: 1740 → 1873 (+133 LOC).
- `Section342NormSqHelpers.lean`: new file, 262 LOC.
- `Chapter3.lean`: +1 import line.
- `lean_status.json`: `lem:342A`'s `lean_symbol` upgraded from
  `butcherShiftedLegendre_orthogonal` to `butcherShiftedLegendre_norm_sq`;
  `cycle_trace` extended.
- `plan.md`: cycle 281 entry appended to the `lem:342A` line.

Build verification:
- `lake build OpenMath.Chapter3.Section342NormSqHelpers` — succeeded
  (only unused-simp-arg warnings from the verbatim Aristotle helper,
  no errors).
- `lake build OpenMath.Chapter3.Section342` — succeeded (only
  unused-simp-arg warnings from cycles 277–280's existing IBP/coeff
  helpers, no errors).
- `#print axioms OpenMath.Chapter3.Section342.butcherShiftedLegendre_norm_sq` —
  returns `[propext, Classical.choice, Quot.sound]` only.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `OpenMath.Chapter3.Section342Helpers.iterate_derivative_natDegree_eq`

- Not a textbook entity; a generic auxiliary lemma about polynomials.
- Statement: `p.natDegree = n → derivative^[n] p = C (leadingCoeff p · n!)`.
- Lean statement captures: standard polynomial-calculus fact, no textbook
  divergence to flag.

### `OpenMath.Chapter3.Section342Helpers.poly_ibp_vanishing`

- Not a textbook entity; specialization of integration-by-parts.
- Statement: `q(0) = 0 ∧ q(1) = 0 →
  ∫₀¹ p · D q = -∫₀¹ D p · q`.
- Lean statement captures: standard IBP, no textbook divergence.

### `OpenMath.Chapter3.Section342Helpers.deriv_iter_XnOneMinusXn_eval_zero/_eval_one`

- Not textbook entities; classical boundary-vanishing lemmas for
  `D^k(x^n(1-x)^n)`. (Same content as cycle 277's
  `iterDeriv_XnOneSubXn_eval_zero/_eval_one`.)
- Lean statement captures: same as the cycle-277 helpers.

### `OpenMath.Chapter3.Section342Helpers.iterated_ibp_XnOneSubXn`

- Not a textbook entity; the iterated-IBP × n machinery underlying both
  (342a) (orthogonality, cycle 277) and (342d) (norm-square, cycle 281).
- Statement: transfers `n` derivatives from `X^n(1-X)^n` to `p` with sign
  `(-1)^n`.
- Lean statement captures: same content as the textbook outline; this is
  the standard tool used implicitly in Butcher's "repeated integration by
  parts" remark for the lemma 342A proof.

### `OpenMath.Chapter3.Section342Helpers.integral_pow_mul_one_sub_pow`

- Not a textbook entity per se; the Euler/Beta integral
  `∫₀¹ x^n (1-x)^n dx = (n!)²/(2n+1)!`.
- Lean statement captures: textbook-equivalent of the Euler Beta function
  evaluated at `(n+1, n+1)`.

### `OpenMath.Chapter3.Section342Helpers.choose_mul_factorial_sq_div`

- Not a textbook entity; pure arithmetic identity.

### `OpenMath.Chapter3.Section342.butcherShiftedLegendre_leadingCoeff`

- Not a textbook entity; structural lemma.
- Statement: `(butcherShiftedLegendre n).leadingCoeff = (Nat.choose (2*n) n : ℝ)`.
- Lean statement captures: direct consequence of `coeff_shiftedLegendre`.

### `OpenMath.Chapter3.Section342.iterate_derivative_butcherShiftedLegendre_eval`

- Not a textbook entity; structural consequence of degree.

### `OpenMath.Chapter3.Section342.butcherShiftedLegendre_norm_sq` ⭐ MAIN

- Entity: `lem:342A` clause (342d).
- Textbook statement (quoted from `extraction/formalization_data/entities/lem_342A.json`):
  > `∫₀¹ (P_n^*(x))² dx = 1/(2n+1)`, n = 0, 1, 2, ….
- Lean statement: `theorem butcherShiftedLegendre_norm_sq (n : ℕ) :
  ∫ x in (0 : ℝ)..1, (butcherShiftedLegendre n).eval x ^ 2 =
  1 / (2 * (n : ℝ) + 1)`.
- Lean statement captures: **same content**. The integrand `(P_n^*(x))^2`
  is `(butcherShiftedLegendre n).eval x ^ 2`, the integral is over
  `[0, 1]` via `intervalIntegral`, and the right-hand side `1/(2n+1)` is
  `1 / (2 * (n : ℝ) + 1)`. All variables/quantifiers match.
- No divergence.

## Dead ends

None blocking, but several small fixes were needed during integration:

1. **Aristotle's `exact?` placeholders**: lines 142–151 of Aristotle's
   `342d_norm_square.lean` Beta-integral conversion step had `exact?`
   tactics that would not have elaborated reliably in our project.
   Rewrote that step from scratch using
   `intervalIntegral.integral_ofReal` + `intervalIntegral.integral_congr`,
   and lifted the product identity to `Nat.factorial_mul_ascFactorial`
   (stronger Mathlib lemma than the manual induction Aristotle used).
2. **`Polynomial.continuous` import**: Aristotle's helpers used
   `(Polynomial.continuous _).intervalIntegrable` for IBP setup, but
   the implicit name resolves only with
   `Mathlib.Topology.Algebra.Polynomial` imported. Added that import
   to the new helper file.
3. **`positivity` on `Complex.re` of natCast**: `(↑(n+1)).re` doesn't
   simplify by `positivity` directly. Rewrote via
   `Complex.natCast_re` + `exact_mod_cast Nat.succ_pos n` (exposing the
   fact that `re` of a natural-number complex equals the natural cast
   to ℝ, which is positive for `n + 1`).
4. **`field_simp` "no goals" residue**: `field_simp` followed by `ring`
   in `choose_mul_factorial_sq_div` triggered a "No goals to be solved"
   error — `field_simp` had already closed the goal. Removed the
   trailing `ring`.
5. **`Int.castRingHom ℝ` not unfolded by `push_cast`**: the leading
   coefficient computation needed `simp only [Int.coe_castRingHom, ...,
   mul_one]` to pierce through the `Int.castRingHom ℝ` wrapper and
   reduce `Nat.choose n n = 1` casts to `(1 : ℝ)`. `push_cast` alone
   left a `↑1` term unreduced (`((1 : ℕ) : ℝ)` instead of `(1 : ℝ)`).
6. **`rw` closes the goal after `choose_mul_factorial_sq_div`**:
   the helper's RHS `1 / (2 * n + 1)` (with `n : ℕ` auto-cast) is
   syntactically equal to my main theorem's `1 / (2 * (n : ℝ) + 1)`,
   so `rw` closes the goal directly. The trailing `push_cast; ring`
   was unnecessary and triggered "No goals to be solved" — removed both.

## Discovery

1. **Aristotle's helper file pattern**: when Aristotle returns a multi-file
   submission (here `NormSqHelpers.lean` + `342d_norm_square.lean`), the
   cleanest integration is to map the helpers to a sibling Lean file in
   the same chapter directory rather than inline them. This keeps
   `Section342.lean` from ballooning past 2000 LOC and gives the helpers
   a clear namespace (`OpenMath.Chapter3.Section342Helpers`) reusable for
   future §342 work.
2. **Aristotle `exact?` brittleness**: Aristotle proofs occasionally
   contain `exact?` placeholders that resolved in their build environment
   but may not in ours. Rule: scan downloaded `.lean` files for `exact?`
   / `apply?` and rewrite those steps explicitly before integration.
3. **Cast trail for complex Beta → real integral**: the conversion
   `((∫ x : ℝ, x^n*(1-x)^n : ℝ) : ℂ) = Complex.betaIntegral (n+1) (n+1)`
   is cleanest via `← intervalIntegral.integral_ofReal` +
   `intervalIntegral.integral_congr`, with the integrand congruence
   producing the term `(x : ℂ) ^ ((n+1 : ℂ) - 1) = (x : ℂ) ^ (n : ℕ)`
   bridged by `← Complex.cpow_natCast`.
4. **`Nat.factorial_mul_ascFactorial` over manual induction**: the
   product `∏_{j=0}^n (n+1+j) = (2n+1)!/n!` is one rewrite away from
   Mathlib's `factorial_mul_ascFactorial : n! * (n+1).ascFactorial k = (n+k)!`
   composed with `Nat.ascFactorial_eq_prod_range`; far cleaner than
   Aristotle's per-cycle manual induction.

## Suggested next approach

Cycle 282 candidates (in priority order):

1. **(342f) three-term recurrence**
   `n P_n^*(x) = (2x-1)(2n-1) P_{n-1}^*(x) - (n-1) P_{n-2}^*(x)`. Cycle
   273 noted this needs Pascal-style binomial identities or substantial
   Legendre infrastructure. With orthogonality (cycle 277) + norm-square
   (cycle 281) now in hand, the Bonnet recurrence could potentially be
   derived from inner-product expansion of `xP_n^*` against
   `{P_k^*}_{k=0..n+1}`. This would close another (342) clause.
2. **`lem:342B` — Gaussian quadrature exactness degree** (§342 dependency).
   Now that orthogonality and norm-square are proven, `lem:342B` becomes
   the natural next step (textbook follow-up that uses (342a) + (342d) as
   inputs).
3. **(342g) `n` distinct real zeros** of `P_n^*` in `(0, 1)` — Sturm
   sequence or oscillation argument. Single-cycle if a Mathlib oscillation
   lemma applies; multi-cycle otherwise.
4. **Section342 file split** (deferred from cycle 281 strategy P1) — the
   file is now ~1880 LOC. Splitting `_norm_sq_{0..7}` ladder into
   `Section342NormSquare.lean` would bring `Section342.lean` back under
   1000 LOC. Lower priority than mathematical progress.
5. **Pivot to a fresh entity** in §343 (next §) or §35x: `lem:351A`
   A-stability criteria, `thm:355F` RK stability conditions, etc.

If cycle 282 worker prefers the safest path, recommend (4) file split or
(2) `lem:342B`. If aiming for textbook progress, recommend (1) recurrence
or (2) `lem:342B`.

Aristotle's compute is now free for cycle 282+ — no jobs running.
Consider firing a fresh Aristotle submission for (342f) or `lem:342B`
this cycle and polling cycle 282+.
