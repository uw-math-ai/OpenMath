import OpenMath.Chapter4.Section404

/-!
# Butcher §410 — Criteria for order

This file opens Butcher's §410 cluster (`thm:410A`, `thm:410B`,
`thm:410C`, `thm:410D`) for the *order* of a linear multistep
method. It introduces the generating polynomials α(z), β(z) of an
LMM (per Butcher's §410 sign convention) and the Taylor-expansion
constants `C j` of equation (410b).

## Textbook context (raw_text/ch04.txt §410)

For an LMM `[α, β]` (def:404B convention), the Taylor expansion of
the residual

```
L(y, x_n, h) := y(x_n) - Σ_{i=1}^k α_i y(x_{n-i})
                       - h Σ_{i=0}^k β_i y'(x_{n-i})    (410a)
```

applied to a smooth function `y` has the form

```
L(y, x_n, h) = C_0 y(x_n) + C_1 h y'(x_n) + C_2 h² y''(x_n) + ⋯    (410b)
```

**Theorem 410A** identifies `C_j` as the j-th coefficient in the
formal power-series expansion of

```
α(exp(-z)) - z β(exp(-z)) = C_0 + C_1 z + C_2 z² + ⋯    (410c).
```

Butcher's proof of 410A (raw_text/ch04.txt L650–666) shows that
this generating-function form follows directly by Taylor-expanding
each `y(x_{n-i})` and `y'(x_{n-i})` and matching coefficients of
`h^j y^{(j)}(x_n)` term by term.

## Sign convention

The §404 LMM structure uses the textbook normalisation
`α 0 = -1` (Section404 header). Butcher's §410 polynomial α(z) is
defined so that (410c) holds; matching the proof's Taylor
expansion, the corresponding Lean polynomial has

```
α(z) = 1 - Σ_{i=1}^k M.α_i · z^i,
β(z) = Σ_{i=0}^k M.β_i · z^i.
```

Constant term: `α(1) = 1 - Σ_{i=1}^k M.α_i`. By (404a),
preconsistency is exactly `1 = Σ M.α_i`, i.e. `α(1) = 0`, i.e.
`C M 0 = 0` (see `C_zero_eq_zero_iff_isPreconsistent` below). This
matches Butcher's claim in the 410A proof that "the coefficient of
`y(x_n)` is `1 - Σ_{i=1}^k α_i`".

## §410 cluster status

`thm:410A` is closed (cycle 074), via the per-monomial reduction
`coeff_aeval_C_X_pow` (Aristotle, cycle 073) plus `map_sub`/`map_sum`
push-throughs of `Polynomial.aeval expNegPS` and
`PowerSeries.coeff (j+1)`. The j=0 case reduces to
`thm_410A_zero`; the j ≥ 1 case unfolds `αPoly`/`βPoly`, applies
`coeff_aeval_C_X_pow` per monomial, and matches the closed-form
`C M (j+1)` definitionally (`rfl`). Manually closed sanity sub-lemmas:

* `αPoly_explicitEuler`, `βPoly_explicitEuler` — non-vacuity
  witnesses (`α(z) = 1 - z`, `β(z) = z` for explicit Euler).
* `C_zero` — definitional unfold of the j=0 case.
* `C_zero_eq_zero_iff_isPreconsistent` — bridges §410 ↔ §404
  preconsistency (def:404A).
* `αPoly_eval_one`, `αPoly_eval_one_eq_C_zero` — α(1) = C M 0.
* `C_zero_explicitEuler` — explicit Euler is preconsistent.
-/

open Polynomial

namespace OpenMath.Chapter4.Section410

open OpenMath.Chapter4.Section404

/-- **Butcher §410 α-polynomial of an LMM.**

With our `α 0 = -1` normalisation (Section404), Butcher's §410
polynomial α(z) has constant term `1` and degree-i coefficient
`-M.α i` for `i = 1, …, k`. We encode this as

```
α(z) = 1 - Σ_{i : Fin k} M.α (i.succ) · z^(i+1).
```

The sign convention is dictated by (410c): under this choice,
`α(1) = 1 - Σ M.α i.succ = C M 0`. -/
noncomputable def αPoly {k : ℕ} (M : LinearMultistepMethod k) :
    Polynomial ℝ :=
  1 - ∑ i : Fin k, Polynomial.C (M.α i.succ) * Polynomial.X ^ (i.val + 1)

/-- **Butcher §410 β-polynomial of an LMM.**

`β(z) = Σ_{i=0}^k M.β_i · z^i`. β indexing starts at 0 so the sum
runs over `Fin (k+1)`. -/
noncomputable def βPoly {k : ℕ} (M : LinearMultistepMethod k) :
    Polynomial ℝ :=
  ∑ i : Fin (k + 1), Polynomial.C (M.β i) * Polynomial.X ^ i.val

/-- **Butcher (410b) Taylor coefficient `C_j`.**

Defined directly from the LMM coefficients per Butcher's proof of
(410A) (raw_text/ch04.txt L650–666):

```
C_0 = 1 - Σ_{i=1}^k α_i,
C_j = -Σ_{i=1}^k α_i (-i)^j / j! - Σ_{i=0}^k β_i (-i)^{j-1} / (j-1)!  (j ≥ 1).
```

The β-sum's `i = 0` term contributes `-β_0` at `j = 1` (since
`(-0 : ℝ)^0 = 1`) and contributes `0` for `j ≥ 2` (since
`(0 : ℝ)^k = 0` for `k ≥ 1`).

This is the **faithful** definition: `C_j` is computed *directly*
from the LMM coefficients. Theorem 410A is then a substantive
identity, NOT a tautology — it asserts that this closed form
equals the Taylor coefficients of the generating function. -/
noncomputable def C {k : ℕ} (M : LinearMultistepMethod k) : ℕ → ℝ
  | 0 => 1 - ∑ i : Fin k, M.α i.succ
  | j + 1 =>
      -∑ i : Fin k,
          M.α i.succ *
            (-((i.val + 1 : ℕ) : ℝ)) ^ (j + 1) / (Nat.factorial (j + 1) : ℝ)
      - ∑ i : Fin (k + 1),
          M.β i * (-((i.val : ℕ) : ℝ)) ^ j / (Nat.factorial j : ℝ)

/-- **The formal power series `exp(-z) = Σ_n (-1)^n z^n / n!`.**

Defined directly via `PowerSeries.mk` to avoid threading the
`Algebra ℚ ℝ` instance required by `PowerSeries.exp ℝ` through
the §410A statement. -/
noncomputable def expNegPS : PowerSeries ℝ :=
  PowerSeries.mk fun n => (-1 : ℝ) ^ n / (Nat.factorial n : ℝ)

/-! ### Sub-lemmas — degree bounds, coefficient lemmas, sanity checks -/

/-- **C_0 closed form.** The `j = 0` branch of `C` is definitionally
`1 - Σ M.α i.succ`. -/
@[simp] theorem C_zero {k : ℕ} (M : LinearMultistepMethod k) :
    C M 0 = 1 - ∑ i : Fin k, M.α i.succ := rfl

/-- **C_0 ↔ preconsistency.**

A linear multistep method is preconsistent (def:404A —
Section404.LinearMultistepMethod.IsPreconsistent) if and only if
its zeroth Taylor coefficient `C 0` vanishes. This connects the
§410 generating-function infrastructure to the §404 condition
and matches Butcher's claim in the 410A proof: "the coefficient
of `y(x_n)` is `1 - Σ α_i`" — which equals 0 iff the method is
preconsistent. -/
theorem C_zero_eq_zero_iff_isPreconsistent {k : ℕ}
    (M : LinearMultistepMethod k) :
    C M 0 = 0 ↔ M.IsPreconsistent := by
  unfold LinearMultistepMethod.IsPreconsistent
  rw [C_zero]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **Non-vacuity witness — explicit Euler's α-polynomial is `1 - X`.**

For explicit Euler `(α₀ = -1, α₁ = 1, β₀ = 0, β₁ = 1)`, we have
`αPoly explicitEulerLMM = 1 - X` per the §410 sign convention. -/
theorem αPoly_explicitEuler : αPoly explicitEulerLMM = 1 - X := by
  unfold αPoly
  simp [explicitEulerLMM]

/-- **Non-vacuity witness — explicit Euler's β-polynomial is `X`.**

For explicit Euler `(β₀ = 0, β₁ = 1)`, we have
`βPoly explicitEulerLMM = X`. -/
theorem βPoly_explicitEuler : βPoly explicitEulerLMM = X := by
  unfold βPoly
  simp [explicitEulerLMM, Fin.sum_univ_succ]

/-- **Sanity helper.** Evaluating `αPoly M` at `1 ∈ ℝ` gives
`1 - Σ M.α i.succ`. This is the residue of the generating function
at `z = 0` (since `exp(0) = 1`) and equals `C M 0`. -/
theorem αPoly_eval_one {k : ℕ} (M : LinearMultistepMethod k) :
    (αPoly M).eval 1 = 1 - ∑ i : Fin k, M.α i.succ := by
  unfold αPoly
  simp [eval_finset_sum]

/-- **Sanity helper.** `(αPoly M).eval 1 = C M 0`. Bridges the
polynomial-evaluation form and the closed-form Taylor coefficient. -/
theorem αPoly_eval_one_eq_C_zero {k : ℕ} (M : LinearMultistepMethod k) :
    (αPoly M).eval 1 = C M 0 := by
  rw [αPoly_eval_one, C_zero]

/-- **C_0 for explicit Euler vanishes.** Explicit Euler is
preconsistent (def:404A — already proved as
`explicitEulerLMM_isPreconsistent`), hence `C explicitEulerLMM 0 = 0`. -/
theorem C_zero_explicitEuler : C explicitEulerLMM 0 = 0 :=
  (C_zero_eq_zero_iff_isPreconsistent _).mpr
    explicitEulerLMM_isPreconsistent

/-! ### Polynomial degree bounds -/

/-- **§410 α-polynomial degree bound.** `(αPoly M).natDegree ≤ k`.
Useful for §410B/C/D order-condition theorems. (Aristotle, cycle 073.) -/
theorem αPoly_natDegree_le {k : ℕ} (M : LinearMultistepMethod k) :
    (αPoly M).natDegree ≤ k := by
  refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
  norm_num
  refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
  refine Finset.sup_le fun i _ => ?_
  exact le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _)
    (by linarith [Fin.is_lt i])

/-- **§410 β-polynomial degree bound.** `(βPoly M).natDegree ≤ k`.
Useful for §410B/C/D order-condition theorems. (Aristotle, cycle 073.) -/
theorem βPoly_natDegree_le {k : ℕ} (M : LinearMultistepMethod k) :
    (βPoly M).natDegree ≤ k := by
  refine le_trans (Polynomial.natDegree_sum_le _ _) (Finset.sup_le ?_)
  exact fun i _ => le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _)
    (Nat.le_trans (Fin.is_le _) (Nat.le_refl _))

/-! ### PowerSeries coefficient lemmas -/

/-- **Explicit form of `expNegPS` coefficients.** The j-th
coefficient of `exp(-z) = Σ_n (-1)^n z^n / n!` is `(-1)^j / j!`.
Definitionally true once we unfold `expNegPS = PowerSeries.mk fun n => (-1)^n / n!`.
(Aristotle, cycle 073.) -/
theorem expNegPS_coeff (n : ℕ) :
    (PowerSeries.coeff (R := ℝ) n) expNegPS
      = (-1 : ℝ) ^ n / (Nat.factorial n : ℝ) := by
  simp [expNegPS]

/-- **The key per-monomial coefficient lemma.** For `c : ℝ` and
`m : ℕ`, the j-th formal power-series coefficient of
`(Polynomial.C c * X^m)` substituted at `expNegPS` is
`c * (-m)^j / j!`.

This is the heart of `thm_410A`: it identifies the substitution
`X ↦ exp(-z)` of a single monomial `c · X^m` with its Taylor
coefficients. Reduced via the closed form
`expNegPS^m = PowerSeries.mk fun n ↦ (-m)^n / n!`, proved by
induction on `m` using the binomial theorem (`add_pow`,
`Nat.cast_choose`, and Cauchy product identification).
(Aristotle, cycle 073.) -/
theorem coeff_aeval_C_X_pow (c : ℝ) (m j : ℕ) :
    (PowerSeries.coeff (R := ℝ) j)
        ((Polynomial.aeval expNegPS) (Polynomial.C c * Polynomial.X ^ m))
      = c * (-(m : ℝ)) ^ j / (Nat.factorial j : ℝ) := by
  have h_exp_pow : (expNegPS ^ m) =
      PowerSeries.mk (fun n => (-m : ℝ) ^ n / (Nat.factorial n : ℝ)) := by
    induction' m with m ih
    · ext (_ | n) <;> simp +decide
    · rw [pow_succ', ih]
      ext n
      simp +decide [expNegPS, PowerSeries.coeff_mul]
      rw [add_pow]
      rw [Finset.sum_div _ _ _]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          fun i j => (-1 : ℝ) ^ i / (i.factorial : ℝ) *
            ((-m : ℝ) ^ j / (j.factorial : ℝ))]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Nat.cast_choose]
      ring
      · norm_num [Nat.factorial_ne_zero]
      · linarith [Finset.mem_range.mp hi]
  simp +decide [h_exp_pow, mul_div_assoc]

/-! ### Theorem 410A — generating-function identity -/

/-- **Theorem 410A at `j = 0`** — the constant term of
`α(exp(-z)) - z β(exp(-z))` is `1 - Σ M.α i.succ = C M 0`.

The `X * (...)` term contributes 0 at coefficient 0 (X has order 1),
so this reduces to evaluating `α` at the constant term of
`expNegPS`, which is 1. (Aristotle, cycle 073.) -/
theorem thm_410A_zero {k : ℕ} (M : LinearMultistepMethod k) :
    (PowerSeries.coeff (R := ℝ) 0)
        ((Polynomial.aeval expNegPS) (αPoly M)
          - PowerSeries.X * (Polynomial.aeval expNegPS) (βPoly M))
      = C M 0 := by
  simp +decide [C, αPoly]
  unfold expNegPS
  aesop

/-- **Butcher §410 Theorem 410A** — the generating-function form
of the Taylor coefficients `C_j`.

Equation (410c): `α(exp(-z)) - z β(exp(-z)) = C_0 + C_1 z + ⋯`.

The Lean statement asserts: for every `j`, the j-th formal
power-series coefficient of `α(exp(-z)) - z β(exp(-z))` (with
α, β substituted at the power series `expNegPS` via
`Polynomial.aeval`) equals `C M j`.

Proof: case split on `j`. The j=0 case is `thm_410A_zero`. For
j = j' + 1, push `aeval` and `coeff` through the `αPoly`/`βPoly`
sums via `map_sub`/`map_one`/`map_sum` and reduce each monomial
via `coeff_aeval_C_X_pow`. The β side first peels off the leading
`X` via `PowerSeries.coeff_succ_X_mul`. The resulting closed-form
sums match the `j' + 1` branch of `C M` definitionally. -/
theorem thm_410A {k : ℕ} (M : LinearMultistepMethod k) (j : ℕ) :
    (PowerSeries.coeff (R := ℝ) j)
        ((Polynomial.aeval expNegPS) (αPoly M)
          - PowerSeries.X * (Polynomial.aeval expNegPS) (βPoly M))
      = C M j := by
  cases j with
  | zero => exact thm_410A_zero M
  | succ j' =>
    rw [map_sub]
    have hα : (PowerSeries.coeff (R := ℝ) (j' + 1))
                ((Polynomial.aeval expNegPS) (αPoly M))
              = -∑ i : Fin k, M.α i.succ *
                  (-((i.val + 1 : ℕ) : ℝ))^(j' + 1) /
                  (Nat.factorial (j' + 1) : ℝ) := by
      unfold αPoly
      rw [map_sub, map_one, map_sub, map_sum, map_sum]
      simp only [PowerSeries.coeff_one, Nat.succ_ne_zero, if_false]
      rw [zero_sub]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [coeff_aeval_C_X_pow (M.α i.succ) (i.val + 1) (j' + 1)]
    have hβ : (PowerSeries.coeff (R := ℝ) (j' + 1))
                (PowerSeries.X * (Polynomial.aeval expNegPS) (βPoly M))
              = ∑ i : Fin (k + 1), M.β i *
                  (-((i.val : ℕ) : ℝ))^j' /
                  (Nat.factorial j' : ℝ) := by
      rw [PowerSeries.coeff_succ_X_mul]
      unfold βPoly
      rw [map_sum, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [coeff_aeval_C_X_pow (M.β i) i.val j']
    rw [hα, hβ]
    rfl

end OpenMath.Chapter4.Section410
