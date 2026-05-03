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

/-- **Generating function of an LMM (per Butcher §410, eq. 410c).**

In our backward-sign convention,
`genFn M = α(exp(-z)) - z·β(exp(-z))`. By `thm_410A`, the j-th
formal power-series coefficient of `genFn M` equals `C M j`, so
`genFn M` is exactly the Taylor-series generating function of the
order constants.

Sign convention: Butcher's textbook (§410, p. 331) writes the
generating function as `α(exp(z)) + z β(exp(z))` (forward sign).
Our backward-sign encoding matches def:406A, §404, §405, §406, and
all of cycle 074's §410 work; the two formulations are equivalent
under `z ↦ -z`. -/
noncomputable def genFn {k : ℕ} (M : LinearMultistepMethod k) :
    PowerSeries ℝ :=
  (Polynomial.aeval expNegPS) (αPoly M)
    - PowerSeries.X * (Polynomial.aeval expNegPS) (βPoly M)

/-- **Theorem 410A at `j = 0`** — the constant term of
`α(exp(-z)) - z β(exp(-z))` is `1 - Σ M.α i.succ = C M 0`.

The `X * (...)` term contributes 0 at coefficient 0 (X has order 1),
so this reduces to evaluating `α` at the constant term of
`expNegPS`, which is 1. (Aristotle, cycle 073.) -/
theorem thm_410A_zero {k : ℕ} (M : LinearMultistepMethod k) :
    (PowerSeries.coeff (R := ℝ) 0) (genFn M) = C M 0 := by
  unfold genFn
  simp +decide [C, αPoly]
  unfold expNegPS
  aesop

/-- **Butcher §410 Theorem 410A** — the generating-function form
of the Taylor coefficients `C_j`.

Equation (410c): `α(exp(-z)) - z β(exp(-z)) = C_0 + C_1 z + ⋯`.

The Lean statement asserts: for every `j`, the j-th formal
power-series coefficient of `genFn M = α(exp(-z)) - z β(exp(-z))`
(with α, β substituted at the power series `expNegPS` via
`Polynomial.aeval`) equals `C M j`.

Proof: case split on `j`. The j=0 case is `thm_410A_zero`. For
j = j' + 1, push `aeval` and `coeff` through the `αPoly`/`βPoly`
sums via `map_sub`/`map_one`/`map_sum` and reduce each monomial
via `coeff_aeval_C_X_pow`. The β side first peels off the leading
`X` via `PowerSeries.coeff_succ_X_mul`. The resulting closed-form
sums match the `j' + 1` branch of `C M` definitionally. -/
theorem thm_410A {k : ℕ} (M : LinearMultistepMethod k) (j : ℕ) :
    (PowerSeries.coeff (R := ℝ) j) (genFn M) = C M j := by
  cases j with
  | zero => exact thm_410A_zero M
  | succ j' =>
    unfold genFn
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

/-! ### Theorem 410B — order condition -/

/-- **§410↔§404 bridge.** The first Taylor coefficient `C M 1`
vanishes if and only if the method satisfies the consistency
equation (404b).

Computation: at `j = 0` (so the `j+1` branch with `j = 0`),
`(-x)^(0+1)/(0+1)! = -x` and `(-x)^0/0! = 1`. So
`C M 1 = -Σᵢ M.α(i.succ) · (-(i+1)) - Σᵢ M.β i
       = Σᵢ (i+1) · M.α(i.succ) - Σᵢ M.β i`,
which equals 0 iff `M.SatisfiesEq404b`. -/
theorem C_one_eq_zero_iff_isConsistent_aux {k : ℕ}
    (M : LinearMultistepMethod k) :
    C M 1 = 0 ↔ M.SatisfiesEq404b := by
  simp [C, LinearMultistepMethod.SatisfiesEq404b]
  constructor <;> intro h <;>
    norm_num [Finset.sum_add_distrib, add_mul, mul_add, mul_assoc,
      mul_comm, mul_left_comm] at * <;>
    linarith

/-- **§410↔§404 consistency bridge.** The first Taylor coefficient
`C M 1` vanishes if and only if the method is consistent
(def:404B), assuming preconsistency (def:404A).

`C 0 = 0` ↔ preconsistency was already proved as
`C_zero_eq_zero_iff_isPreconsistent`; this lemma packages the
`C 1 = 0` ↔ (404b) algebra and combines with preconsistency to
give the full equivalence with `IsConsistent`. -/
theorem C_one_eq_zero_iff_isConsistent {k : ℕ}
    (M : LinearMultistepMethod k) (hpre : M.IsPreconsistent) :
    C M 1 = 0 ↔ M.IsConsistent := by
  rw [LinearMultistepMethod.IsConsistent, and_iff_right hpre]
  exact C_one_eq_zero_iff_isConsistent_aux M

end OpenMath.Chapter4.Section410

namespace OpenMath.Chapter4.Section404

/-- **Butcher §410B order predicate.**

A linear multistep method has order at least `p` if its first
`p+1` Taylor coefficients vanish: `C M j = 0` for all `j ≤ p`.

This matches Butcher's definitional statement (§410, p. 330):
"order p will mean that `C₀ = C₁ = ⋯ = Cp = 0`".

The asymptotic interpretation `L(y, x, h) = O(h^{p+1})` is captured
implicitly via Butcher's Taylor expansion (410b); for `p = 1` it is
captured quantitatively by `lem:406B` (`localTruncationError_bound`,
Section404.lean). Equivalence to the generating-function form
`α(exp(-z)) - z β(exp(-z)) = O(z^{p+1})` is the content of
`thm_410B` below. -/
def LinearMultistepMethod.HasOrderAtLeast {k : ℕ}
    (M : LinearMultistepMethod k) (p : ℕ) : Prop :=
  ∀ j ≤ p, OpenMath.Chapter4.Section410.C M j = 0

end OpenMath.Chapter4.Section404

namespace OpenMath.Chapter4.Section410

open OpenMath.Chapter4.Section404

/-- **Butcher §410 Theorem 410B (order condition).**

A linear multistep method has order at least `p` if and only if
the first `p+1` formal power-series coefficients of its generating
function `α(exp(-z)) - z β(exp(-z))` vanish.

Sign convention: Butcher's textbook statement uses
`α(exp(z)) + z β(exp(z))` with the forward sign convention. Our
encoding uses backward sign matching def:406A and `thm_410A`; the
two formulations are equivalent under `z ↦ -z`.

Proof: by `thm_410A`, `coeff j (genFn M) = C M j` for every `j`,
so the predicate `∀ j ≤ p, coeff j (genFn M) = 0` is equivalent to
`∀ j ≤ p, C M j = 0`, which is `M.HasOrderAtLeast p`. -/
theorem thm_410B {k : ℕ} (M : LinearMultistepMethod k) (p : ℕ) :
    M.HasOrderAtLeast p
      ↔ ∀ j ≤ p, (PowerSeries.coeff (R := ℝ) j) (genFn M) = 0 := by
  unfold LinearMultistepMethod.HasOrderAtLeast
  refine ⟨fun h j hj => ?_, fun h j hj => ?_⟩
  · rw [thm_410A]; exact h j hj
  · rw [← thm_410A]; exact h j hj

/-! ### §410B witnesses -/

/-- **Non-vacuity witness — explicit Euler has order ≥ 0.**
Order ≥ 0 is exactly preconsistency (`C 0 = 0`). -/
theorem explicitEulerLMM_hasOrderAtLeast_zero :
    explicitEulerLMM.HasOrderAtLeast 0 := by
  intro j hj
  interval_cases j
  exact C_zero_explicitEuler

/-- **Non-vacuity witness — explicit Euler has order ≥ 1.**
By `C_one_eq_zero_iff_isConsistent` and
`explicitEulerLMM_isConsistent`. -/
theorem explicitEulerLMM_hasOrderAtLeast_one :
    explicitEulerLMM.HasOrderAtLeast 1 := by
  intro j hj
  interval_cases j
  · exact C_zero_explicitEuler
  · exact (C_one_eq_zero_iff_isConsistent explicitEulerLMM
            explicitEulerLMM_isPreconsistent).mpr
            explicitEulerLMM_isConsistent

/-- **Restrictiveness check — explicit Euler does NOT have order 2.**
This proves `HasOrderAtLeast` is genuinely restrictive (not
vacuous) and matches the textbook's classification of explicit
Euler as a first-order method. -/
theorem explicitEulerLMM_C_two_ne_zero :
    C explicitEulerLMM 2 ≠ 0 := by
  unfold C explicitEulerLMM
  simp [Fin.sum_univ_succ]
  norm_num

/-! ### §410C — (ρ, σ)-form generating-function order condition

Butcher §410C states the order condition in the traditional
`(ρ, σ)` notation: `ρ(exp(z)) − z σ(exp(z)) = O(z^{p+1})`, where
`ρ(z) = z^k · α(1/z)` and `σ(z) = z^k · β(1/z)` are the reverse
polynomials of α, β. The load-bearing identity is

  ρ(exp(z)) - z σ(exp(z)) = exp(kz) · genFn M.

Multiplication by the unit `exp(kz)` (constant term 1) preserves
the property "first p+1 coefficients vanish", so §410C reduces
to §410B. -/

/-- **The forward exponential power series `exp(z) = Σ_n z^n / n!`.**

Defined directly via `PowerSeries.mk` to avoid the `Algebra ℚ ℝ`
requirements of `PowerSeries.exp`. -/
noncomputable def expPS : PowerSeries ℝ :=
  PowerSeries.mk fun n => 1 / (Nat.factorial n : ℝ)

/-- **The unit power series `exp(k z) = Σ_n k^n z^n / n!`.**

Defined directly via `PowerSeries.mk`. Constant term is `1` (a unit
in `PowerSeries ℝ`), so multiplying by `expKzPS k` preserves the
"first p+1 coefficients vanish" property used in §410C. -/
noncomputable def expKzPS (k : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk fun n => (k : ℝ) ^ n / (Nat.factorial n : ℝ)

/-- **Coefficients of `expPS`.** The j-th coefficient of
`exp(z) = Σ_n z^n / n!` is `1 / j!`. -/
theorem expPS_coeff (n : ℕ) :
    (PowerSeries.coeff (R := ℝ) n) expPS
      = 1 / (Nat.factorial n : ℝ) := by
  simp [expPS]

/-- **Coefficients of `expKzPS`.** The j-th coefficient of
`exp(k z) = Σ_n k^n z^n / n!` is `k^j / j!`. -/
theorem expKzPS_coeff (k n : ℕ) :
    (PowerSeries.coeff (R := ℝ) n) (expKzPS k)
      = (k : ℝ) ^ n / (Nat.factorial n : ℝ) := by
  simp [expKzPS]

/-- **`expKzPS k` has constant term 1.** Used to show `expKzPS k`
is a unit in `PowerSeries ℝ`. -/
theorem expKzPS_constantCoeff (k : ℕ) :
    (PowerSeries.constantCoeff (R := ℝ)) (expKzPS k) = 1 := by
  simp [expKzPS]

/-- **Bridge: `expPS = PowerSeries.exp ℝ`.**

Both sides have constant-coefficient `1/n!` at degree `n` (with the
Mathlib `algebraMap ℚ ℝ` collapsing to the cast). Lets us reuse
Mathlib's `PowerSeries.exp_mul_exp_neg_eq_one` and
`PowerSeries.exp_pow_eq_rescale_exp`. -/
theorem expPS_eq_exp : expPS = PowerSeries.exp ℝ := by
  ext n
  rw [expPS_coeff, PowerSeries.coeff_exp]
  rw [show algebraMap ℚ ℝ (1 / (n.factorial : ℚ)) = 1 / (n.factorial : ℝ) from by
    rw [map_div₀, map_one, map_natCast]]

/-- **Bridge: `expNegPS = evalNegHom (PowerSeries.exp ℝ)`.**

`expNegPS = mk fun n => (-1)^n / n!`, and `evalNegHom = rescale (-1)`,
which gives `coeff n (rescale (-1) (exp ℝ)) = (-1)^n * coeff n (exp ℝ)
= (-1)^n / n!`. -/
theorem expNegPS_eq_evalNegHom_exp :
    expNegPS = PowerSeries.evalNegHom (PowerSeries.exp ℝ) := by
  rw [PowerSeries.evalNegHom, ← expPS_eq_exp]
  ext n
  rw [PowerSeries.coeff_rescale, expPS_coeff, expNegPS_coeff]
  ring

/-- **Bridge: `expKzPS k = rescale (k : ℝ) (PowerSeries.exp ℝ)`.** -/
theorem expKzPS_eq_rescale_exp (k : ℕ) :
    expKzPS k = PowerSeries.rescale (k : ℝ) (PowerSeries.exp ℝ) := by
  rw [← expPS_eq_exp]
  ext n
  rw [PowerSeries.coeff_rescale, expPS_coeff, expKzPS_coeff]
  ring

/-- **`expPS · expNegPS = 1`.**

Direct corollary of Mathlib's `exp_mul_exp_neg_eq_one`. -/
theorem expPS_mul_expNegPS_eq_one : expPS * expNegPS = 1 := by
  rw [expPS_eq_exp, expNegPS_eq_evalNegHom_exp]
  exact PowerSeries.exp_mul_exp_neg_eq_one

/-- **`expPS^a = expKzPS a`.**

Direct corollary of Mathlib's `exp_pow_eq_rescale_exp`. -/
theorem expPS_pow_eq_expKzPS (a : ℕ) : expPS ^ a = expKzPS a := by
  rw [expPS_eq_exp, expKzPS_eq_rescale_exp]
  exact PowerSeries.exp_pow_eq_rescale_exp a

/-- **Bridge lemma.** For `m ≤ k`, `expPS^(k - m) = expKzPS k * expNegPS^m`.

Proof: multiply both sides by `expPS^m` and use `expPS · expNegPS = 1`
plus `expPS^k = expKzPS k`. -/
theorem expPS_pow_sub_eq_expKzPS_mul_expNegPS_pow {k m : ℕ} (hm : m ≤ k) :
    expPS ^ (k - m) = expKzPS k * expNegPS ^ m := by
  have h1 : expPS ^ k = expKzPS k := expPS_pow_eq_expKzPS k
  have h2 : (expPS * expNegPS) ^ m = 1 := by
    rw [expPS_mul_expNegPS_eq_one, one_pow]
  calc expPS ^ (k - m)
      = expPS ^ (k - m) * 1 := (mul_one _).symm
    _ = expPS ^ (k - m) * (expPS * expNegPS) ^ m := by rw [h2]
    _ = expPS ^ (k - m) * (expPS ^ m * expNegPS ^ m) := by rw [mul_pow]
    _ = (expPS ^ (k - m) * expPS ^ m) * expNegPS ^ m := by ring
    _ = expPS ^ k * expNegPS ^ m := by rw [← pow_add, Nat.sub_add_cancel hm]
    _ = expKzPS k * expNegPS ^ m := by rw [h1]

/-- **Butcher §410 ρ-polynomial of an LMM.**

In the `(ρ, σ)` notation, `ρ(z) = z^k · α(1/z)` is the reverse
polynomial of α(z). With our `α(z) = 1 - Σ_{i=1}^k M.α i.succ · z^i`,
this gives

```
ρ(z) = z^k - Σ_{i=1}^k M.α i.succ · z^{k-i}.
```

Butcher writes this as `ρ(z) = z^k - α₁ z^{k-1} - ⋯ - α_k`. -/
noncomputable def ρPoly {k : ℕ} (M : LinearMultistepMethod k) :
    Polynomial ℝ :=
  Polynomial.X ^ k -
    ∑ i : Fin k,
      Polynomial.C (M.α i.succ) * Polynomial.X ^ (k - (i.val + 1))

/-- **Butcher §410 σ-polynomial of an LMM.**

In the `(ρ, σ)` notation, `σ(z) = z^k · β(1/z) = Σ_{i=0}^k β_i z^{k-i}`. -/
noncomputable def σPoly {k : ℕ} (M : LinearMultistepMethod k) :
    Polynomial ℝ :=
  ∑ i : Fin (k + 1), Polynomial.C (M.β i) * Polynomial.X ^ (k - i.val)

/-- **Non-vacuity witness — explicit Euler's ρ-polynomial is `X - 1`.**

For explicit Euler `(α₁ = 1, k = 1)`, we have
`ρPoly explicitEulerLMM = X - 1`. -/
theorem ρPoly_explicitEuler : ρPoly explicitEulerLMM = X - 1 := by
  unfold ρPoly
  simp [explicitEulerLMM]

/-- **Non-vacuity witness — explicit Euler's σ-polynomial is `1`.**

For explicit Euler `(β₀ = 0, β₁ = 1, k = 1)`, we have
`σPoly explicitEulerLMM = 1`. -/
theorem σPoly_explicitEuler : σPoly explicitEulerLMM = 1 := by
  unfold σPoly
  simp [explicitEulerLMM]

/-- **(ρ, σ)-form generating function (forward sign).**

`genFnForward M = ρ(exp(z)) - z σ(exp(z))`. By §410C, the
condition `M.HasOrderAtLeast p` is equivalent to the first p+1
coefficients of `genFnForward M` vanishing. -/
noncomputable def genFnForward {k : ℕ} (M : LinearMultistepMethod k) :
    PowerSeries ℝ :=
  (Polynomial.aeval expPS) (ρPoly M)
    - PowerSeries.X * (Polynomial.aeval expPS) (σPoly M)

/-- **ρ-side substitution identity.**

`aeval expPS (ρPoly M) = expKzPS k · aeval expNegPS (αPoly M)`.

Per-monomial: `expPS^(k-(i+1)) = expKzPS k · expNegPS^(i+1)` by
the bridge `expPS_pow_sub_eq_expKzPS_mul_expNegPS_pow`. -/
theorem aeval_expPS_ρPoly_eq {k : ℕ} (M : LinearMultistepMethod k) :
    (Polynomial.aeval expPS) (ρPoly M) =
      expKzPS k * (Polynomial.aeval expNegPS) (αPoly M) := by
  unfold ρPoly αPoly
  rw [map_sub, map_sub, map_pow, Polynomial.aeval_X,
      expPS_pow_eq_expKzPS k, map_one, map_sum, map_sum,
      mul_sub, mul_one]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi_succ_le : i.val + 1 ≤ k := i.isLt
  rw [map_mul, map_mul, Polynomial.aeval_C, Polynomial.aeval_C,
      map_pow, map_pow, Polynomial.aeval_X, Polynomial.aeval_X,
      expPS_pow_sub_eq_expKzPS_mul_expNegPS_pow hi_succ_le]
  ring

/-- **σ-side substitution identity.**

`aeval expPS (σPoly M) = expKzPS k · aeval expNegPS (βPoly M)`.

Per-monomial: `expPS^(k-i) = expKzPS k · expNegPS^i` by the
bridge `expPS_pow_sub_eq_expKzPS_mul_expNegPS_pow`. -/
theorem aeval_expPS_σPoly_eq {k : ℕ} (M : LinearMultistepMethod k) :
    (Polynomial.aeval expPS) (σPoly M) =
      expKzPS k * (Polynomial.aeval expNegPS) (βPoly M) := by
  unfold σPoly βPoly
  rw [map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi_le : i.val ≤ k := Nat.lt_succ_iff.mp i.isLt
  rw [map_mul, map_mul, Polynomial.aeval_C, Polynomial.aeval_C,
      map_pow, map_pow, Polynomial.aeval_X, Polynomial.aeval_X,
      expPS_pow_sub_eq_expKzPS_mul_expNegPS_pow hi_le]
  ring

/-- **§410C unit equivalence.**

`ρ(exp(z)) - z σ(exp(z)) = exp(kz) · (α(exp(-z)) - z β(exp(-z)))`,
i.e. `genFnForward M = expKzPS k * genFn M`. The `expKzPS k`
factor is a unit (constant term 1), so it preserves "first p+1
coefficients vanish". -/
theorem genFnForward_eq_expKzPS_mul_genFn {k : ℕ}
    (M : LinearMultistepMethod k) :
    genFnForward M = expKzPS k * genFn M := by
  unfold genFnForward genFn
  rw [aeval_expPS_ρPoly_eq, aeval_expPS_σPoly_eq]
  ring

/-- **Multiplication by the unit `expKzPS k` preserves vanishing of
low coefficients.**

Since `expKzPS k` has constant term 1, the iff holds: the first
p+1 coefficients of `expKzPS k * g` vanish if and only if the first
p+1 coefficients of `g` vanish. The forward direction uses
induction on `p`, isolating the `(0, j)` term in the Cauchy
product (where `expKzPS k`'s coefficient is 1). The reverse
direction is direct from the Cauchy product, since each
`coeff b g` term has `b ≤ j ≤ p` so vanishes. -/
theorem coeff_expKzPS_mul_eq_zero_iff {k : ℕ} (g : PowerSeries ℝ)
    (p : ℕ) :
    (∀ j ≤ p, (PowerSeries.coeff (R := ℝ) j) (expKzPS k * g) = 0)
      ↔ (∀ j ≤ p, (PowerSeries.coeff (R := ℝ) j) g = 0) := by
  constructor
  · intro h
    induction p with
    | zero =>
      intro l hl
      interval_cases l
      have h0 := h 0 (le_refl 0)
      rw [PowerSeries.coeff_zero_eq_constantCoeff] at h0 ⊢
      rw [map_mul, expKzPS_constantCoeff, one_mul] at h0
      exact h0
    | succ p ih =>
      have h_restr : ∀ j ≤ p,
          (PowerSeries.coeff (R := ℝ) j) (expKzPS k * g) = 0 :=
        fun j hj => h j (le_trans hj (Nat.le_succ p))
      have ih_g : ∀ j ≤ p, (PowerSeries.coeff (R := ℝ) j) g = 0 := ih h_restr
      intro l hl
      by_cases hl_le : l ≤ p
      · exact ih_g l hl_le
      · have hl_eq : l = p + 1 := by omega
        subst hl_eq
        have hmul := h (p + 1) (le_refl _)
        rw [PowerSeries.coeff_mul] at hmul
        rw [Finset.sum_eq_single (0, p + 1) ?_ ?_] at hmul
        · have h0 : (PowerSeries.coeff (R := ℝ) 0) (expKzPS k) = 1 := by
            rw [PowerSeries.coeff_zero_eq_constantCoeff]
            exact expKzPS_constantCoeff k
          rw [h0, one_mul] at hmul
          exact hmul
        · rintro ⟨a, b⟩ hab hne
          have hsum : a + b = p + 1 := Finset.mem_antidiagonal.mp hab
          have hb_le : b ≤ p := by
            by_contra hbp
            push_neg at hbp
            have ha : a = 0 := by omega
            have hb_eq : b = p + 1 := by omega
            exact hne (by simp [ha, hb_eq])
          rw [ih_g b hb_le, mul_zero]
        · intro hnotmem
          exfalso
          exact hnotmem (Finset.mem_antidiagonal.mpr (by omega))
  · intro h j hj
    rw [PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨a, b⟩ hab
    have hsum : a + b = j := Finset.mem_antidiagonal.mp hab
    have hb_le : b ≤ p := by omega
    rw [h b hb_le, mul_zero]

/-- **Butcher §410 Theorem 410C — (ρ, σ)-form order condition.**

A linear multistep method `(ρ, σ)` has order at least `p` if and
only if the first `p+1` formal power-series coefficients of
`ρ(exp(z)) - z σ(exp(z))` vanish.

Proof: by `thm_410B`, `M.HasOrderAtLeast p` is equivalent to the
first p+1 coefficients of `genFn M = α(exp(-z)) - z β(exp(-z))`
vanishing. By `genFnForward_eq_expKzPS_mul_genFn`,
`genFnForward M = expKzPS k * genFn M`. Multiplication by the unit
`expKzPS k` (constant term 1) preserves vanishing of the first p+1
coefficients (`coeff_expKzPS_mul_eq_zero_iff`). -/
theorem thm_410C {k : ℕ} (M : LinearMultistepMethod k) (p : ℕ) :
    M.HasOrderAtLeast p
      ↔ ∀ j ≤ p, (PowerSeries.coeff (R := ℝ) j) (genFnForward M) = 0 := by
  rw [thm_410B]
  constructor
  · intro h
    have h2 : ∀ j ≤ p,
        (PowerSeries.coeff (R := ℝ) j) (expKzPS k * genFn M) = 0 :=
      (coeff_expKzPS_mul_eq_zero_iff (genFn M) p).mpr h
    intro j hj
    rw [genFnForward_eq_expKzPS_mul_genFn]
    exact h2 j hj
  · intro h
    have h2 : ∀ j ≤ p,
        (PowerSeries.coeff (R := ℝ) j) (expKzPS k * genFn M) = 0 := by
      intro j hj
      have := h j hj
      rwa [genFnForward_eq_expKzPS_mul_genFn] at this
    exact (coeff_expKzPS_mul_eq_zero_iff (genFn M) p).mp h2

/-! ### §410C witnesses -/

/-- **Witness — explicit Euler satisfies `genFnForward = O(z²)`.**

Repackaging cycle 075's `explicitEulerLMM_hasOrderAtLeast_one`
through `thm_410C`. -/
theorem explicitEulerLMM_genFnForward_O_z2 :
    ∀ j ≤ 1, (PowerSeries.coeff (R := ℝ) j)
                (genFnForward explicitEulerLMM) = 0 :=
  (thm_410C explicitEulerLMM 1).mp explicitEulerLMM_hasOrderAtLeast_one

/-- **Witness — explicit Euler has order ≥ 1 via §410C.**

Re-derives `explicitEulerLMM_hasOrderAtLeast_one` through the
`(ρ, σ)`-form order condition `thm_410C`. -/
theorem explicitEulerLMM_hasOrderAtLeast_one_via_410C :
    explicitEulerLMM.HasOrderAtLeast 1 :=
  (thm_410C explicitEulerLMM 1).mpr explicitEulerLMM_genFnForward_O_z2

/-! ### §410D — log-form order condition

Butcher §410D states the order condition in the *log* form by
substituting `exp(-z) ↦ (1+z)^{-1}` (equivalently `z ↦ log(1+z)`)
in the backward-sign generating function `genFn M`:

```
α((1+z)^{-1}) - log(1+z) · β((1+z)^{-1}) = O(z^{p+1}).      (410d)
```

The substitution is `z ↦ logOnePlusPS = z - z²/2 + z³/3 - ⋯`. We
encode the §410D residual as `genFnLog M = subst logOnePlusPS (genFn M)`,
and prove `M.HasOrderAtLeast p ↔ ∀ j ≤ p, coeff j (genFnLog M) = 0`
via `thm_410B` plus a "substitution by unit-leading series preserves
and reflects vanishing of the first p+1 coefficients" pair of lemmas.

The five Aristotle-supplied helper lemmas (cycle 077 batch
`18504be5-2481-4d60-9d7b-12b8a5cd2b47`, completed cycle 078):

1. `onePlusX_mul_oneOverOnePlusPS_eq_one` — `(1 + X) · (1+X)⁻¹ = 1`
2. `coeff_subst_eq_zero_of_coeff_eq_zero` — forward direction
3. `coeff_eq_zero_of_coeff_subst_eq_zero` — reverse direction
4. `subst_logOnePlusPS_expPS_eq_one_add_X` — `exp(log(1+X)) = 1+X`
5. `subst_logOnePlusPS_expNegPS` — `exp(-log(1+X)) = (1+X)⁻¹`
-/

/-- **The geometric series `(1+z)^{-1} = Σ_n (-1)^n z^n`.** -/
noncomputable def oneOverOnePlusPS : PowerSeries ℝ :=
  PowerSeries.mk fun n => (-1 : ℝ) ^ n

/-- **The formal logarithm `log(1+z) = z - z²/2 + z³/3 - ⋯`.** -/
noncomputable def logOnePlusPS : PowerSeries ℝ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (-1 : ℝ) ^ (n - 1) / (n : ℝ)

@[simp] theorem oneOverOnePlusPS_coeff (n : ℕ) :
    (PowerSeries.coeff (R := ℝ) n) oneOverOnePlusPS = (-1 : ℝ) ^ n := by
  simp [oneOverOnePlusPS]

@[simp] theorem logOnePlusPS_constantCoeff :
    (PowerSeries.constantCoeff (R := ℝ)) logOnePlusPS = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [logOnePlusPS]

@[simp] theorem logOnePlusPS_coeff_one :
    (PowerSeries.coeff (R := ℝ) 1) logOnePlusPS = 1 := by
  simp [logOnePlusPS]

/-- **`(1 + X) · (1+X)⁻¹ = 1`.** Cauchy product telescopes via
`(-1)^n + (-1)^{n-1} = 0` for `n ≥ 1`. (Aristotle, cycle 077.) -/
theorem onePlusX_mul_oneOverOnePlusPS_eq_one :
    ((1 : PowerSeries ℝ) + PowerSeries.X) * oneOverOnePlusPS = 1 := by
  ext (_ | n) <;>
    simp_all +decide [PowerSeries.coeff_one, PowerSeries.coeff_X, mul_assoc, add_mul]
  · exact Eq.symm (Real.ext_cauchy rfl)
  · ring

/-- **Forward direction.** Substitution by `g` with `constantCoeff g = 0`
preserves `∀ j ≤ p, coeff j f = 0`. (Aristotle, cycle 077.) -/
theorem coeff_subst_eq_zero_of_coeff_eq_zero
    {g : PowerSeries ℝ} (hg : (PowerSeries.constantCoeff (R := ℝ)) g = 0)
    {f : PowerSeries ℝ} {p : ℕ}
    (h : ∀ j ≤ p, (PowerSeries.coeff (R := ℝ) j) f = 0) :
    ∀ j ≤ p, (PowerSeries.coeff (R := ℝ) j) (PowerSeries.subst g f) = 0 := by
  have h_order_le :
      (PowerSeries.order f : WithTop ℕ) ≤
        (PowerSeries.order (PowerSeries.subst g f) : WithTop ℕ) :=
    PowerSeries.le_order_subst_left' hg
  contrapose! h_order_le
  simp_all +decide [PowerSeries.order]
  split_ifs <;> simp_all +decide [Nat.find_eq_iff]
  grind

/-- **Reverse direction.** Substitution by unit-leading `g` (constant
term 0, linear coeff 1) reflects `∀ j ≤ p, coeff j (subst g f) = 0`.
(Aristotle, cycle 077.) -/
theorem coeff_eq_zero_of_coeff_subst_eq_zero
    {g : PowerSeries ℝ} (hg0 : (PowerSeries.constantCoeff (R := ℝ)) g = 0)
    (hg1 : (PowerSeries.coeff (R := ℝ) 1) g = 1)
    {f : PowerSeries ℝ} {p : ℕ}
    (h : ∀ j ≤ p, (PowerSeries.coeff (R := ℝ) j) (PowerSeries.subst g f) = 0) :
    ∀ j ≤ p, (PowerSeries.coeff (R := ℝ) j) f = 0 := by
  have h_coeff_g_pow : ∀ d j, d ≥ 1 →
      (PowerSeries.coeff j (g ^ d)) = 0 ∨ j ≥ d := by
    intro d j hd
    by_contra h_contra
    induction' hd with d hd ih generalizing j <;>
      simp_all +decide [pow_succ, PowerSeries.coeff_mul]
    · aesop
    · obtain ⟨k, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h_contra.1
      simp_all +decide [Finset.mem_antidiagonal]
      linarith [ih _ hk.2.1, show k.2 > 0 from Nat.pos_of_ne_zero fun h => by aesop]
  have h_subst : ∀ j, (PowerSeries.coeff j (PowerSeries.subst g f)) =
      ∑ d ∈ Finset.range (j + 1),
        (PowerSeries.coeff d f) * (PowerSeries.coeff j (g ^ d)) := by
    simp +decide [Finset.sum_range_succ, PowerSeries.coeff_subst]
    intro j
    convert PowerSeries.coeff_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero' hg0) f (Finsupp.single () j) using 1
    rw [finsum_eq_sum_of_support_subset]
    case s => exact Finset.range (j + 1)
    · simp +decide [Finset.sum_range_succ, PowerSeries.coeff]
    · intro d hd; contrapose! hd; simp_all +decide [MvPowerSeries.coeff]
      cases h_coeff_g_pow d j (by linarith) <;> simp_all +decide [LinearMap.proj]
      · exact?
      · linarith
  intro j hj
  induction' j using Nat.strong_induction_on with j ih
  rcases j with (_ | j) <;> simp_all +decide [Finset.sum_range_succ]
  · specialize h 0; aesop
  · specialize h (j + 1) (by linarith); simp_all +decide [Finset.sum_range_succ]
    have h_coeff_g_pow_succ : (PowerSeries.coeff (j + 1)) (g ^ (j + 1)) = 1 := by
      induction' j + 1 with j ih <;> simp_all +decide [pow_succ, mul_assoc]
      rw [PowerSeries.coeff_mul]
      rw [Finset.sum_eq_single (j, 1)] <;>
        simp_all +decide [Finset.Nat.sum_antidiagonal_succ]
      grind
    simp_all +decide [Finset.sum_eq_zero]
    rw [Finset.sum_eq_zero] at h <;> simp_all +decide [Finset.sum_range_succ]
    · grind +splitIndPred
    · exact fun x hx => Or.inl <| ih x hx.le <| by linarith

theorem derivative_expPS :
    (PowerSeries.derivative ℝ) expPS = expPS := by
  unfold expPS
  ext (_ | n) <;> norm_num [Nat.factorial_ne_zero]
  · norm_num [PowerSeries.derivative]
    norm_num [PowerSeries.derivativeFun]
  · simp +decide [PowerSeries.coeff_derivative, Nat.factorial_succ]
    rw [mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]

theorem derivative_logOnePlusPS :
    (PowerSeries.derivative ℝ) logOnePlusPS = oneOverOnePlusPS := by
  ext n
  simp +decide [logOnePlusPS, PowerSeries.coeff_derivative]
  rw [div_mul_cancel₀ _ (Nat.cast_add_one_ne_zero _)]

/-- If `D(G) = G · (1+X)⁻¹` and `G(0) = 0`, then `G = 0`. -/
theorem eq_zero_of_derivative_eq_mul_oneOverOnePlusPS
    {G : PowerSeries ℝ} (hG0 : (PowerSeries.constantCoeff (R := ℝ)) G = 0)
    (hDE : (PowerSeries.derivative ℝ) G = G * oneOverOnePlusPS) :
    G = 0 := by
  refine PowerSeries.ext ?_
  intro n
  induction' n using Nat.strong_induction_on with n ih
  rcases n <;> simp_all +decide [PowerSeries.coeff_derivative]
  rw [eq_comm, PowerSeries.ext_iff] at hDE
  specialize hDE ‹_›; simp_all +decide [PowerSeries.coeff_mul]
  rw [Finset.sum_eq_zero] at hDE <;> simp_all +decide [PowerSeries.coeff_derivative]
  · exact hDE.resolve_right <| Nat.cast_add_one_ne_zero _
  · exact fun a b hab => ih a <| by linarith

theorem constantCoeff_subst_logOnePlusPS_expPS :
    (PowerSeries.constantCoeff (R := ℝ)) (PowerSeries.subst logOnePlusPS expPS) = 1 := by
  rw [PowerSeries.constantCoeff, PowerSeries.constantCoeff_subst]
  · rw [finsum_eq_single] <;> norm_num
    case a => exact 0
    · unfold expPS; norm_num
    · aesop
  · exact PowerSeries.HasSubst.of_constantCoeff_zero' rfl

/-- **`exp(log(1+X)) = 1 + X`**: substitution of `logOnePlusPS` into
`expPS` yields `1 + X`. Proved via ODE uniqueness — `G := subst log expPS - (1 + X)`
satisfies `D(G) = G · oneOverOnePlusPS` and `G(0) = 0`, hence `G = 0`.
(Aristotle, cycle 077.) -/
theorem subst_logOnePlusPS_expPS_eq_one_add_X :
    PowerSeries.subst logOnePlusPS expPS = (1 : PowerSeries ℝ) + PowerSeries.X := by
  have hF_deriv :
      (PowerSeries.derivative ℝ) (PowerSeries.subst logOnePlusPS expPS) =
        (PowerSeries.subst logOnePlusPS expPS) * oneOverOnePlusPS := by
    have h_chain :
        (PowerSeries.derivative ℝ) (PowerSeries.subst logOnePlusPS expPS) =
          PowerSeries.subst logOnePlusPS ((PowerSeries.derivative ℝ) expPS) *
            (PowerSeries.derivative ℝ) logOnePlusPS := by
      rw [PowerSeries.derivative_subst]
      exact PowerSeries.HasSubst.of_constantCoeff_zero' rfl
    rw [h_chain, derivative_expPS, derivative_logOnePlusPS]
  set G : PowerSeries ℝ := PowerSeries.subst logOnePlusPS expPS - (1 + PowerSeries.X)
  have hG_deriv : (PowerSeries.derivative ℝ) G = G * oneOverOnePlusPS := by
    simp +zetaDelta at *
    rw [hF_deriv, sub_mul]
    rw [onePlusX_mul_oneOverOnePlusPS_eq_one]
  have hG_zero : (PowerSeries.constantCoeff (R := ℝ)) G = 0 := by
    simp +zetaDelta at *
    rw [sub_eq_zero, constantCoeff_subst_logOnePlusPS_expPS]
  exact sub_eq_zero.mp (eq_zero_of_derivative_eq_mul_oneOverOnePlusPS hG_zero hG_deriv)

/-- **`exp(-log(1+X)) = (1+X)⁻¹`**: substitution of `logOnePlusPS` into
`expNegPS` yields the geometric series `oneOverOnePlusPS`. Combines
`subst_logOnePlusPS_expPS_eq_one_add_X`, `expPS_mul_expNegPS_eq_one`,
and `onePlusX_mul_oneOverOnePlusPS_eq_one` via uniqueness of the
multiplicative inverse. (Aristotle, cycle 077.) -/
theorem subst_logOnePlusPS_expNegPS :
    PowerSeries.subst logOnePlusPS expNegPS = oneOverOnePlusPS := by
  have h_inv :
      (1 + PowerSeries.X : PowerSeries ℝ) *
        PowerSeries.subst logOnePlusPS expNegPS = 1 := by
    have h_mul : PowerSeries.subst logOnePlusPS (expPS * expNegPS) =
        (PowerSeries.subst logOnePlusPS expPS) *
          (PowerSeries.subst logOnePlusPS expNegPS) := by
      apply PowerSeries.subst_mul
      exact PowerSeries.HasSubst.of_constantCoeff_zero' rfl
    rw [expPS_mul_expNegPS_eq_one] at h_mul
    convert h_mul.symm using 1
    · rw [show PowerSeries.subst logOnePlusPS expPS = 1 + PowerSeries.X from
        subst_logOnePlusPS_expPS_eq_one_add_X]
    · norm_num [PowerSeries.subst]
      norm_num [MvPowerSeries.subst]
      norm_num [MvPowerSeries.eval₂]
  have h_unique : ∀ f g : PowerSeries ℝ,
      (1 + PowerSeries.X) * f = 1 → (1 + PowerSeries.X) * g = 1 → f = g := by
    grind +ring
  exact h_unique _ _ h_inv onePlusX_mul_oneOverOnePlusPS_eq_one

/-! ### Theorem 410D — log-form order condition -/

/-- **Log-form generating function (Butcher §410D, eq. 410d).**

```
genFnLog M := subst logOnePlusPS (genFn M).
```

Equivalently, substituting `z ↦ log(1+z)` in
`genFn M = α(exp(-z)) - z β(exp(-z))` and using
`subst_logOnePlusPS_expNegPS` (`exp(-log(1+z)) = (1+z)⁻¹`) gives
`α((1+z)^{-1}) - log(1+z) β((1+z)^{-1})`, which is Butcher's
(410d). -/
noncomputable def genFnLog {k : ℕ} (M : LinearMultistepMethod k) :
    PowerSeries ℝ :=
  PowerSeries.subst logOnePlusPS (genFn M)

/-- **Butcher §410 Theorem 410D — log-form order condition.**

A linear multistep method has order at least `p` if and only if
the first `p+1` formal power-series coefficients of
`α((1+z)^{-1}) - log(1+z) · β((1+z)^{-1})` vanish.

Sign convention: Butcher's textbook (§410, p. 351) writes the
condition as `z/log(1+z) · α(1+z) + β(1+z) = O(z^p)` (forward sign).
The context_latex of thm:410D gives the equivalent backward-sign
form `α((1+z)^{-1}) - log(1+z) · β((1+z)^{-1}) = O(z^{p+1})` (eq.
410d), which matches our encoding `genFnLog M = subst logOnePlusPS (genFn M)`.

Proof: by `thm_410B`, order ≥ p ↔ first p+1 coefficients of `genFn M`
vanish. Substitution by `logOnePlusPS` (constant term 0, linear coeff 1)
preserves and reflects this vanishing
(`coeff_subst_eq_zero_of_coeff_eq_zero` and
`coeff_eq_zero_of_coeff_subst_eq_zero`). -/
theorem thm_410D {k : ℕ} (M : LinearMultistepMethod k) (p : ℕ) :
    M.HasOrderAtLeast p
      ↔ ∀ j ≤ p, (PowerSeries.coeff (R := ℝ) j) (genFnLog M) = 0 := by
  rw [thm_410B]
  unfold genFnLog
  refine ⟨coeff_subst_eq_zero_of_coeff_eq_zero logOnePlusPS_constantCoeff,
          coeff_eq_zero_of_coeff_subst_eq_zero logOnePlusPS_constantCoeff
            logOnePlusPS_coeff_one⟩

/-! ### §410D witnesses -/

/-- **Witness — explicit Euler satisfies `genFnLog = O(z²)`.**
Repackaging cycle 075's `explicitEulerLMM_hasOrderAtLeast_one`
through `thm_410D`. -/
theorem explicitEulerLMM_genFnLog_O_z2 :
    ∀ j ≤ 1, (PowerSeries.coeff (R := ℝ) j)
                (genFnLog explicitEulerLMM) = 0 :=
  (thm_410D explicitEulerLMM 1).mp explicitEulerLMM_hasOrderAtLeast_one

/-- **Witness — explicit Euler has order ≥ 1 via §410D.**
Re-derives `explicitEulerLMM_hasOrderAtLeast_one` through the
log-form order condition `thm_410D`. -/
theorem explicitEulerLMM_hasOrderAtLeast_one_via_410D :
    explicitEulerLMM.HasOrderAtLeast 1 :=
  (thm_410D explicitEulerLMM 1).mpr explicitEulerLMM_genFnLog_O_z2

end OpenMath.Chapter4.Section410
