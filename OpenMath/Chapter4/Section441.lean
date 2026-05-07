import OpenMath.Chapter4.Section404
import OpenMath.Chapter4.Section410
import OpenMath.Chapter4.Section451

/-!
# Butcher §441 — Maximum order for a convergent k-step method (Phase A)

This file opens Butcher's §441 cluster (`lem:441A`, `lem:441B`,
`thm:441C`, the *Dahlquist barrier* result) by introducing the
auxiliary polynomial `a(z)` of equation (441b) and providing
basic structural lemmas (non-vacuity witnesses, degree bound).

## Textbook source (Butcher §441, p. 375–376)

For a `k`-step linear multistep method with characteristic
polynomial

  `ρ(z) = z^k − α₁z^{k−1} − α₂z^{k−2} − ⋯ − αₖ`,

Butcher introduces the auxiliary polynomial

  `a(z) = (1+z)^k − α₁(1+z)^{k−1}(1−z) − α₂(1+z)^{k−2}(1−z)² − ⋯ − αₖ(1−z)^k`.

Two distinct sequences appear in §441:

1. The polynomial coefficients `a₀, a₁, …, aₖ` of `a(z)` itself.
   These DEPEND on the LMM. **Lemma 441A** asserts that for stable
   `M`, these satisfy `a₁ > 0` and `aᵢ ≥ 0` for `i ∈ {2, …, k}`.

2. The constants `c₀, c₂, c₄, …` defined by the (441c) inverse-
   series identity
   `(2 + (2/3)z² + (2/5)z⁴ + ⋯) · (c₀ + c₂z² + c₄z⁴ + ⋯) = 1`.
   These are UNIVERSAL — they do NOT depend on the LMM. **Lemma
   441B** asserts that these universal constants `c₂, c₄, …` are
   all negative.

## Sign convention

Our §404 LMM structure stores the textbook `α₁, α₂, …, αₖ` as
`M.α i.succ` for `i : Fin k`, with `M.α 0 = -1` (the leading-
coefficient normalisation). The polynomial `a(z)` is built from
the textbook `αᵢ`, so the Lean encoding selects `M.α i.succ` for
`i : Fin k` and uses `(i.val + 1)` for the `(1−z)` exponent.

## Phase A — `aPoly` polynomial infrastructure

This file currently provides:

* `LinearMultistepMethod.aPoly` — the §441 polynomial `a(z)`.
* `LinearMultistepMethod.aPoly_natDegree_le` — degree bound.
* `explicitEulerLMM_aPoly_eq` — non-vacuity witness at `k = 1`.

A `k = 2` BDF2 closed-form witness was attempted again in cycle
173 but deferred for the second time: the polynomial identity
`bdf2LMM.aPoly = C(4/3) X + C(8/3) X²` is straightforward to
verify by hand but `ring` does not fold `Polynomial.C` constants
when divisions are involved (`C(4/3) - C(-1/3) = C(5/3)` is
outside `ring`'s normal form). A `Polynomial.ext` skeleton
encounters the issue that the simp set for resolving
`Polynomial.coeff` of mixed numeral / `C` expressions on
`Polynomial ℝ` is incomplete without further helpers. The
standalone algebraic check appears in
`.prover-state/issues/lem_441B_misinterpretation.md` as the
explicit refutation of cycle 171's misreading.

## Lemma 441B — DEFERRED

`lem:441B` concerns the *universal* constants `c₂, c₄, …` defined
by the inverse-series identity (441c) for `log((1+z)/(1−z))/z`.
These constants have NO dependency on the LMM — they are a fact
about a single power-series identity. Cycle 171 conflated these
universal `c_{2i}` with the polynomial coefficients `aᵢ` of
`aPoly`; that conflation has been rolled back. See
`.prover-state/issues/lem_441B_misinterpretation.md` for the
algebraic refutation (BDF2's `aPoly = (4/3)X + (8/3)X²` has
positive even coefficients despite BDF2 being stable, directly
contradicting the cycle 171 misreading) and the corrected
multi-cycle plan for `lem:441B`.

## References

* Butcher, *Numerical Methods for Ordinary Differential Equations*,
  3rd ed., §441 "Maximum order for a convergent k-step method",
  pp. 375–376.
* `extraction/formalization_data/entities/lem_441B.json`
* `extraction/raw_text/ch04.txt:1947–2030` (raw Butcher §441 text).
* `OpenMath/Chapter4/Section410.lean::αPoly` — companion §410
  generating polynomial (different from `a(z)`).
* `OpenMath/Chapter4/Section404.lean::LinearMultistepMethod` —
  base structure and `explicitEulerLMM` witness.
-/

open Polynomial

namespace OpenMath.Chapter4.Section404

/-- **Butcher §441 polynomial `a(z)`** (equation following ρ on p. 375).

For a `k`-step LMM with textbook coefficients `α₁, …, αₖ` (stored
as `M.α i.succ` for `i : Fin k` in our §404 encoding),

  `a(z) = (1+z)^k − Σ_{i=1}^{k} αᵢ (1+z)^{k−i} (1−z)^i`.

This is the *defining* formula from Butcher; the coefficient
expansion `a(z) = a₀ + a₁z + a₂z² + ⋯` is an *output* derived from
this polynomial, not an independent definition (defining `aPoly`
by its coefficients would be smuggling).

Lives in the `Section404.LinearMultistepMethod` namespace so that
the dot notation `M.aPoly` resolves through to this definition. -/
noncomputable def LinearMultistepMethod.aPoly
    {k : ℕ} (M : LinearMultistepMethod k) : Polynomial ℝ :=
  (1 + Polynomial.X) ^ k -
    ∑ i : Fin k,
      Polynomial.C (M.α i.succ) *
      (1 + Polynomial.X) ^ (k - (i.val + 1)) *
      (1 - Polynomial.X) ^ (i.val + 1)

/-- **Degree bound on `aPoly`.** As a polynomial in `z`, `a(z)` has
degree at most `k`: it is the difference of `(1+z)^k` and a sum of
products `(1+z)^{k-(i+1)} · (1-z)^{i+1}`, each of total degree `k`.

This is structural infrastructure for §441; the (441b) polynomial-
identity argument expects `aPoly.natDegree ≤ k` as a side condition. -/
theorem LinearMultistepMethod.aPoly_natDegree_le
    {k : ℕ} (M : LinearMultistepMethod k) :
    M.aPoly.natDegree ≤ k := by
  unfold LinearMultistepMethod.aPoly
  have h1pX : (1 + Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_add_le _ _).trans ?_
    simp
  have h1mX : (1 - Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    simp
  refine (Polynomial.natDegree_sub_le _ _).trans ?_
  refine max_le ?_ ?_
  · -- `(1 + X)^k` has degree ≤ k.
    refine Polynomial.natDegree_pow_le.trans ?_
    calc k * (1 + Polynomial.X : Polynomial ℝ).natDegree
        ≤ k * 1 := Nat.mul_le_mul_left k h1pX
      _ = k := mul_one k
  · -- Sum bound: each summand has degree ≤ k.
    refine (Polynomial.natDegree_sum_le _ _).trans ?_
    refine Finset.sup_le ?_
    intro i _
    refine Polynomial.natDegree_mul_le.trans ?_
    have hpow1 :
        ((1 + Polynomial.X : Polynomial ℝ) ^ (k - (i.val + 1))).natDegree
          ≤ k - (i.val + 1) := by
      refine Polynomial.natDegree_pow_le.trans ?_
      calc (k - (i.val + 1)) * (1 + Polynomial.X : Polynomial ℝ).natDegree
          ≤ (k - (i.val + 1)) * 1 := Nat.mul_le_mul_left _ h1pX
        _ = k - (i.val + 1) := mul_one _
    have hpow2 :
        ((1 - Polynomial.X : Polynomial ℝ) ^ (i.val + 1)).natDegree
          ≤ i.val + 1 := by
      refine Polynomial.natDegree_pow_le.trans ?_
      calc (i.val + 1) * (1 - Polynomial.X : Polynomial ℝ).natDegree
          ≤ (i.val + 1) * 1 := Nat.mul_le_mul_left _ h1mX
        _ = i.val + 1 := mul_one _
    have hCmul :
        (Polynomial.C (M.α i.succ) *
            (1 + Polynomial.X : Polynomial ℝ) ^ (k - (i.val + 1))).natDegree
          ≤ k - (i.val + 1) :=
      (Polynomial.natDegree_C_mul_le _ _).trans hpow1
    have hile : i.val + 1 ≤ k := i.isLt
    calc (Polynomial.C (M.α i.succ) *
            (1 + Polynomial.X : Polynomial ℝ) ^ (k - (i.val + 1))).natDegree +
          ((1 - Polynomial.X : Polynomial ℝ) ^ (i.val + 1)).natDegree
        ≤ (k - (i.val + 1)) + (i.val + 1) := Nat.add_le_add hCmul hpow2
      _ = k := Nat.sub_add_cancel hile

/-- **`aPoly.coeff 0 = 0` for preconsistent LMMs.**

Setting `z = 0` in `a(z) = (1+z)^k − Σᵢ αᵢ (1+z)^{k−i} (1−z)^i`
gives `a(0) = 1 − Σᵢ αᵢ`, which equals `0` by preconsistency.

This is `lem:441A`'s implicit claim that `a₀ = 0` (Butcher's
`a(z) = a₀ + a₁z + ⋯` expansion has `a₀ = 0` for any preconsistent
method, since `α(1) = 0`). -/
theorem LinearMultistepMethod.aPoly_coeff_zero_of_preconsistent
    {k : ℕ} (M : LinearMultistepMethod k) (hPre : M.IsPreconsistent) :
    M.aPoly.coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  unfold LinearMultistepMethod.aPoly
  unfold LinearMultistepMethod.IsPreconsistent at hPre
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_add,
             Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_finset_sum,
             Polynomial.eval_mul, Polynomial.eval_C, add_zero, sub_zero, one_pow, mul_one]
  linarith

/-- **Closed form for `a₁` (unconditional).** Butcher §441 p. 376.

For ANY `k`-step LMM (no preconsistency assumed), the coefficient
of `z` in `a(z)` decomposes as

  `a₁ = k · (1 − Σᵢ αᵢ) − 2 · α'(1)`,

where `α(z) = 1 − Σᵢ αᵢ z^i` is the §410 generating polynomial.
Under preconsistency the first term vanishes (since `Σ αᵢ = 1`),
recovering Butcher's identity `a₁ = −2α'(1)`. -/
theorem LinearMultistepMethod.aPoly_coeff_one_unconditional
    {k : ℕ} (M : LinearMultistepMethod k) :
    M.aPoly.coeff 1 =
      (k : ℝ) * (1 - ∑ i : Fin k, M.α i.succ)
        - 2 * (OpenMath.Chapter4.Section410.αPoly M).derivative.eval 1 := by
  -- Helper A: ((1 - X)^n).coeff 0 = 1
  have h_one_sub_X_coeff_zero : ∀ n : ℕ,
      ((1 - Polynomial.X : Polynomial ℝ) ^ n).coeff 0 = 1 := by
    intro n
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp
  -- Helper B: ((1 - X)^n).coeff 1 = -n
  have h_one_sub_X_coeff_one : ∀ n : ℕ,
      ((1 - Polynomial.X : Polynomial ℝ) ^ n).coeff 1 = -(n : ℝ) := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, Polynomial.coeff_one]
      simp
    | succ m ih =>
      rw [pow_succ, Polynomial.mul_coeff_one, ih, h_one_sub_X_coeff_zero]
      have h1 : ((1 - Polynomial.X : Polynomial ℝ)).coeff 0 = 1 := by
        rw [Polynomial.coeff_sub, Polynomial.coeff_one_zero, Polynomial.coeff_X_zero]
        ring
      have h2 : ((1 - Polynomial.X : Polynomial ℝ)).coeff 1 = -1 := by
        rw [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X]
        norm_num
      rw [h1, h2]
      push_cast
      ring
  -- Per-summand coefficient formula
  have h_summand : ∀ i : Fin k,
      (Polynomial.C (M.α i.succ) *
        (1 + Polynomial.X) ^ (k - (i.val + 1)) *
        (1 - Polynomial.X) ^ (i.val + 1)).coeff 1 =
      M.α i.succ * ((k : ℝ) - 2 * ((i.val : ℝ) + 1)) := by
    intro i
    rw [Polynomial.mul_coeff_one]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
    rw [Polynomial.coeff_one_add_X_pow, Polynomial.coeff_one_add_X_pow]
    rw [h_one_sub_X_coeff_zero, h_one_sub_X_coeff_one]
    rw [Nat.choose_zero_right, Nat.choose_one_right]
    have hile : i.val + 1 ≤ k := i.isLt
    push_cast [Nat.cast_sub hile]
    ring
  -- Step 1: Compute aPoly.coeff 1 in terms of α values
  have h_lhs : M.aPoly.coeff 1 =
      (k : ℝ) - ∑ i : Fin k, M.α i.succ * ((k : ℝ) - 2 * ((i.val : ℝ) + 1)) := by
    unfold LinearMultistepMethod.aPoly
    rw [Polynomial.coeff_sub, Polynomial.coeff_one_add_X_pow, Nat.choose_one_right]
    rw [Polynomial.finset_sum_coeff]
    congr 1
    apply Finset.sum_congr rfl
    intros i _
    exact h_summand i
  -- Step 2: Compute αPoly.derivative.eval 1
  have h_alpha_deriv :
      (OpenMath.Chapter4.Section410.αPoly M).derivative.eval 1 =
        -∑ i : Fin k, M.α i.succ * ((i.val : ℝ) + 1) := by
    unfold OpenMath.Chapter4.Section410.αPoly
    rw [Polynomial.derivative_sub, Polynomial.derivative_one, zero_sub]
    rw [Polynomial.derivative_sum]
    rw [Polynomial.eval_neg, Polynomial.eval_finset_sum]
    rw [neg_inj]
    apply Finset.sum_congr rfl
    intros i _
    rw [Polynomial.derivative_C_mul_X_pow]
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        one_pow, mul_one]
    push_cast
    ring
  -- Step 3: Combine
  rw [h_lhs, h_alpha_deriv]
  -- Decompose `∑ αᵢ·(k − 2(i+1))` into `k·∑ αᵢ − 2·∑ αᵢ(i+1)`.
  have h_decomp :
      (∑ i : Fin k, M.α i.succ * ((k : ℝ) - 2 * ((i.val : ℝ) + 1))) =
      (k : ℝ) * (∑ i : Fin k, M.α i.succ) -
        2 * ∑ i : Fin k, M.α i.succ * ((i.val : ℝ) + 1) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intros i _
    ring
  rw [h_decomp]
  ring

/-- **Butcher §441 p. 376 calculation `a₁ = −2 α'(1)`.**

Under preconsistency, the `kα(1)` term vanishes (since `α(1) = 0`),
so the coefficient `a₁` reduces to `−2 α'(1)`. This is the precise
identity Butcher writes as `kα(1) − 2α'(1) = −2α'(1)` on p. 376
and is the starting point of `lem:441A`'s `a₁ > 0` argument. -/
theorem LinearMultistepMethod.aPoly_coeff_one_eq_neg_two_alpha_deriv_at_one_of_preconsistent
    {k : ℕ} (M : LinearMultistepMethod k) (hPre : M.IsPreconsistent) :
    M.aPoly.coeff 1 = -2 * (OpenMath.Chapter4.Section410.αPoly M).derivative.eval 1 := by
  rw [M.aPoly_coeff_one_unconditional]
  have hpre : (∑ i : Fin k, M.α i.succ) = 1 := by
    unfold LinearMultistepMethod.IsPreconsistent at hPre
    linarith
  rw [hpre]
  ring

/-- **Butcher §441 stability polynomial `ρ(z)`** (p. 375).

For a `k`-step LMM with textbook coefficients `α₁, …, αₖ` (stored
as `M.α i.succ` for `i : Fin k`),

  `ρ(z) = z^k − α₁·z^{k−1} − α₂·z^{k−2} − ⋯ − αₖ`.

Sign convention: matches Butcher; `M.α 0 = -1` is the normalisation
factor and is NOT used here (only `M.α i.succ` for `i : Fin k`).
The substitution `i ↦ i.val + 1` gives the textbook indexing
`α₁, α₂, …, αₖ` from our `Fin k`-indexed `M.α i.succ`. -/
noncomputable def LinearMultistepMethod.ρPoly
    {k : ℕ} (M : LinearMultistepMethod k) : Polynomial ℝ :=
  Polynomial.X ^ k -
    ∑ i : Fin k,
      Polynomial.C (M.α i.succ) * Polynomial.X ^ (k - (i.val + 1))

/-- **Evaluation of `ρPoly` at `1` (unconditional).** Butcher §441 p. 375.

For ANY `k`-step LMM (no preconsistency assumed),
`ρ(1) = 1 − Σ αᵢ`. -/
theorem LinearMultistepMethod.ρPoly_eval_one
    {k : ℕ} (M : LinearMultistepMethod k) :
    M.ρPoly.eval 1 = 1 - ∑ i : Fin k, M.α i.succ := by
  unfold LinearMultistepMethod.ρPoly
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
             one_pow, Polynomial.eval_finset_sum, Polynomial.eval_mul,
             Polynomial.eval_C, mul_one]

/-- **`ρ(1) = 0` for preconsistent LMMs.** Butcher §441 p. 376.

Under preconsistency (`Σ αᵢ = 1`), the unconditional formula
`ρ(1) = 1 − Σ αᵢ` collapses to `0`. This is the textbook fact
"`ρ(1) = 0`" used as the entry point of the `ρ'(1) > 0` argument. -/
theorem LinearMultistepMethod.ρPoly_eval_one_eq_zero_of_preconsistent
    {k : ℕ} (M : LinearMultistepMethod k) (hPre : M.IsPreconsistent) :
    M.ρPoly.eval 1 = 0 := by
  rw [M.ρPoly_eval_one]
  unfold LinearMultistepMethod.IsPreconsistent at hPre
  linarith

/-- **Degree bound on `ρPoly`.** As a polynomial in `z`, `ρ(z)` has
degree at most `k`: it is the difference of `X^k` and a sum of
monomials `C(αᵢ) · X^(k-(i+1))`, each of degree at most `k`. -/
theorem LinearMultistepMethod.ρPoly_natDegree_le
    {k : ℕ} (M : LinearMultistepMethod k) :
    M.ρPoly.natDegree ≤ k := by
  unfold LinearMultistepMethod.ρPoly
  refine (Polynomial.natDegree_sub_le _ _).trans ?_
  refine max_le ?_ ?_
  · refine Polynomial.natDegree_pow_le.trans ?_
    simp
  · refine (Polynomial.natDegree_sum_le _ _).trans ?_
    refine Finset.sup_le ?_
    intro i _
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine Polynomial.natDegree_pow_le.trans ?_
    have hsub : k - (i.val + 1) ≤ k := Nat.sub_le _ _
    calc (k - (i.val + 1)) * (Polynomial.X : Polynomial ℝ).natDegree
        ≤ (k - (i.val + 1)) * 1 := by simp
      _ = k - (i.val + 1) := mul_one _
      _ ≤ k := hsub

/-- **`ρ'(1)` closed form (unconditional).** Butcher §441 p. 376.

For ANY `k`-step LMM (no preconsistency assumed),

  `ρ'(1) = k − Σᵢ αᵢ · (k − (i+1))`.

When `i.val + 1 = k` (the constant term `αₖ`), the multiplier
`(k - (i+1))` is `0` and the term vanishes — consistent with the
textbook formula `ρ'(1) = k − (k−1)α₁ − (k−2)α₂ − ⋯ − αₖ₋₁`. -/
theorem LinearMultistepMethod.ρPoly_deriv_eval_one_unconditional
    {k : ℕ} (M : LinearMultistepMethod k) :
    M.ρPoly.derivative.eval 1 =
      (k : ℝ) - ∑ i : Fin k, M.α i.succ * ((k : ℝ) - ((i.val : ℝ) + 1)) := by
  unfold LinearMultistepMethod.ρPoly
  rw [Polynomial.derivative_sub]
  rw [Polynomial.derivative_X_pow]
  rw [Polynomial.derivative_sum]
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one]
  congr 1
  rw [Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intros i _
  rw [Polynomial.derivative_C_mul_X_pow]
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, one_pow, mul_one]
  have hile : i.val + 1 ≤ k := i.isLt
  push_cast [Nat.cast_sub hile]
  ring

/-- **Bridge identity: `ρ'(1) = −α'(1)` under preconsistency.**
Butcher §441 p. 376 (the line "We calculate the value of `a₁` …
to be `kα(1) − 2α'(1)`").

Algebraically, expanding `ρ'(1) = k − Σ αᵢ(k − (i+1))` and using
`Σ αᵢ = 1` gives `ρ'(1) = Σ αᵢ(i+1)`, which equals `−α'(1)` since
`α(z) = 1 − Σ αᵢ z^{i+1}`. This is purely algebraic — no real-
analytic Mathlib hooks needed. -/
theorem LinearMultistepMethod.ρPoly_deriv_eval_one_eq_neg_alpha_deriv_at_one_of_preconsistent
    {k : ℕ} (M : LinearMultistepMethod k) (hPre : M.IsPreconsistent) :
    M.ρPoly.derivative.eval 1 =
      -(OpenMath.Chapter4.Section410.αPoly M).derivative.eval 1 := by
  rw [M.ρPoly_deriv_eval_one_unconditional]
  have h_alpha_deriv :
      (OpenMath.Chapter4.Section410.αPoly M).derivative.eval 1 =
        -∑ i : Fin k, M.α i.succ * ((i.val : ℝ) + 1) := by
    unfold OpenMath.Chapter4.Section410.αPoly
    rw [Polynomial.derivative_sub, Polynomial.derivative_one, zero_sub]
    rw [Polynomial.derivative_sum]
    rw [Polynomial.eval_neg, Polynomial.eval_finset_sum]
    rw [neg_inj]
    apply Finset.sum_congr rfl
    intros i _
    rw [Polynomial.derivative_C_mul_X_pow]
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X, one_pow, mul_one]
    push_cast
    ring
  rw [h_alpha_deriv]
  have hpre : (∑ i : Fin k, M.α i.succ) = 1 := by
    unfold LinearMultistepMethod.IsPreconsistent at hPre
    linarith
  have hdistrib :
      (∑ i : Fin k, M.α i.succ * ((k : ℝ) - ((i.val : ℝ) + 1))) =
      (k : ℝ) * (∑ i : Fin k, M.α i.succ) -
        ∑ i : Fin k, M.α i.succ * ((i.val : ℝ) + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intros i _
    ring
  rw [hdistrib, hpre]
  ring

/-- **Headline identity: `a₁ = 2·ρ'(1)` under preconsistency.**

Combining cycle 173's `aPoly_coeff_one_eq_neg_two_alpha_deriv_at_one_of_preconsistent`
(`a₁ = −2·α'(1)`) with the cycle 174 bridge `ρ'(1) = −α'(1)`
(under preconsistency) gives Butcher's identity `a₁ = 2·ρ'(1)`. This
reduces the `lem:441A` `a₁ > 0` half to the polynomial-root claim
`ρ'(1) > 0`, exactly matching the textbook strategy on p. 376.

Note (cycle 175): Butcher's text on p. 376 reads `ρ'(1) = a₁`, but
the calculation above (and the algebraic derivation via `α'(1)`)
yields the relation `a₁ = 2·ρ'(1)`, off by a factor of 2 from the
textbook line. Numerical verification on explicit Euler (a₁ = 2,
ρ'(1) = 1) and BDF2 (a₁ = 4/3, ρ'(1) = 2/3) confirms the factor of
2; the textbook line appears to drop the leading 2. The textbook
*strategy* is unaffected: `a₁ > 0 ↔ ρ'(1) > 0` is the load-bearing
claim, and that biconditional holds with either constant. -/
theorem LinearMultistepMethod.aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent
    {k : ℕ} (M : LinearMultistepMethod k) (hPre : M.IsPreconsistent) :
    M.aPoly.coeff 1 = 2 * M.ρPoly.derivative.eval 1 := by
  rw [M.aPoly_coeff_one_eq_neg_two_alpha_deriv_at_one_of_preconsistent hPre]
  rw [M.ρPoly_deriv_eval_one_eq_neg_alpha_deriv_at_one_of_preconsistent hPre]
  ring

/-- **Auxiliary: a real root of `ρPoly` yields a geometric homogeneous
solution.** If `z₀` satisfies `ρ(z₀) = 0`, then `n ↦ z₀^n` solves the
homogeneous recurrence (403a). This is the standard "characteristic-
root → solution" link for linear difference equations: substituting
`y_n := z₀^n` into the recurrence reduces to `ρ(z₀) = 0`. -/
private theorem geomSeq_isHomogeneousSolution_of_ρPoly_isRoot
    {k : ℕ} (M : LinearMultistepMethod k) {z₀ : ℝ}
    (hroot : M.ρPoly.IsRoot z₀) :
    M.IsHomogeneousSolution (fun n : ℕ => z₀ ^ n) := by
  unfold LinearMultistepMethod.IsHomogeneousSolution
  intro m
  -- From `hroot` (= `M.ρPoly.eval z₀ = 0`) extract
  -- `z₀^k = ∑ i, M.α i.succ * z₀^(k-(i.val+1))`.
  have hroot_eq : z₀ ^ k = ∑ i : Fin k, M.α i.succ * z₀ ^ (k - (i.val + 1)) := by
    have hev := hroot
    unfold Polynomial.IsRoot at hev
    unfold LinearMultistepMethod.ρPoly at hev
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
               Polynomial.eval_finset_sum, Polynomial.eval_mul,
               Polynomial.eval_C] at hev
    linarith
  -- Goal (after beta-reduction): z₀^(m+k) = ∑ i, M.α i.succ * z₀^(m+k-(i.val+1))
  show z₀ ^ (m + k) = ∑ i : Fin k, M.α i.succ * z₀ ^ (m + k - (i.val + 1))
  rw [pow_add, hroot_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hile : i.val + 1 ≤ k := i.isLt
  have hsub : m + k - (i.val + 1) = m + (k - (i.val + 1)) := by omega
  rw [hsub, pow_add]
  ring

/-- **Stability ⇒ ρ has no real root > 1.** Butcher §441 p. 376
(implicit step of the `lem:441A` `a₁ > 0` argument).

If `M : LinearMultistepMethod k` is Dahlquist-stable (`M.IsStable` of
§403A) and `z₀ : ℝ` is a real root of the characteristic polynomial
`ρ` (`M.ρPoly.IsRoot z₀`), then `z₀ ≤ 1`.

Textbook proof: a real root `z₀ > 1` of `ρ` would mean the geometric
sequence `y_n := z₀^n` solves the homogeneous recurrence (403a) — but
`|z₀^n| = z₀^n → ∞` since `z₀ > 1`, contradicting boundedness of all
homogeneous solutions. -/
theorem LinearMultistepMethod.ρPoly_no_real_root_gt_one
    {k : ℕ} (M : LinearMultistepMethod k)
    (hStable : M.IsStable) {z₀ : ℝ} (hroot : M.ρPoly.IsRoot z₀) :
    z₀ ≤ 1 := by
  by_contra hgt
  push_neg at hgt   -- hgt : 1 < z₀
  -- Build the geometric homogeneous solution.
  have hsol : M.IsHomogeneousSolution (fun n : ℕ => z₀ ^ n) :=
    geomSeq_isHomogeneousSolution_of_ρPoly_isRoot M hroot
  -- Stability gives a uniform bound C.
  obtain ⟨C, hC⟩ := hStable _ hsol
  -- But z₀^n is eventually > C (Archimedean property).
  obtain ⟨n, hn_pow⟩ := pow_unbounded_of_one_lt C hgt
  -- Combine: |z₀^n| ≤ C and z₀^n > C contradict (z₀^n ≥ 0).
  have habs_le : |z₀ ^ n| ≤ C := hC n
  have hpos : 0 ≤ z₀ ^ n :=
    pow_nonneg (le_of_lt (lt_trans zero_lt_one hgt)) n
  have habs_eq : |z₀ ^ n| = z₀ ^ n := abs_of_nonneg hpos
  linarith [habs_eq ▸ habs_le, hn_pow]

/-- **Auxiliary: `ρ(1) = 0` and `ρ'(1) = 0` (under preconsistency)
yield the unbounded homogeneous solution `n ↦ n`.**

Under preconsistency `Σᵢ αᵢ = 1` and `ρ'(1) = Σᵢ αᵢ · (i+1) = 0`
(via the unconditional closed form for `ρ'(1)`), the sequence
`y_n := (n : ℝ)` satisfies the (403a) homogeneous recurrence
`y(m+k) = Σᵢ αᵢ y(m+k-i)` for all `m`. -/
private theorem idSeq_isHomogeneousSolution_of_preconsistent_ρPoly_deriv_zero
    {k : ℕ} (M : LinearMultistepMethod k)
    (hPre : M.IsPreconsistent)
    (hDeriv : M.ρPoly.derivative.eval 1 = 0) :
    M.IsHomogeneousSolution (fun n : ℕ => (n : ℝ)) := by
  unfold LinearMultistepMethod.IsHomogeneousSolution
  intro m
  -- Extract `Σᵢ αᵢ = 1` from preconsistency.
  have hpre : (∑ i : Fin k, M.α i.succ) = 1 := by
    unfold LinearMultistepMethod.IsPreconsistent at hPre
    linarith
  -- From `ρ'(1) = 0` plus the unconditional closed form,
  -- derive `Σᵢ αᵢ · (i+1) = 0`.
  have hsum_zero : (∑ i : Fin k, M.α i.succ * ((i.val : ℝ) + 1)) = 0 := by
    have hev := M.ρPoly_deriv_eval_one_unconditional
    rw [hDeriv] at hev
    have hdistrib :
        (∑ i : Fin k, M.α i.succ * ((k : ℝ) - ((i.val : ℝ) + 1))) =
        (k : ℝ) * (∑ i : Fin k, M.α i.succ) -
          ∑ i : Fin k, M.α i.succ * ((i.val : ℝ) + 1) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intros i _
      ring
    rw [hdistrib, hpre] at hev
    linarith
  -- Goal (after beta-reduction):
  --   ((m + k : ℕ) : ℝ) = ∑ i, M.α i.succ * ((m + k - (i.val + 1) : ℕ) : ℝ)
  show ((m + k : ℕ) : ℝ)
        = ∑ i : Fin k, M.α i.succ * ((m + k - (i.val + 1) : ℕ) : ℝ)
  have hrhs_eq :
      (∑ i : Fin k, M.α i.succ * ((m + k - (i.val + 1) : ℕ) : ℝ))
      = ((m : ℝ) + (k : ℝ)) * (∑ i : Fin k, M.α i.succ)
        - ∑ i : Fin k, M.α i.succ * ((i.val : ℝ) + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hile : i.val + 1 ≤ k := i.isLt
    have hcast :
        ((m + k - (i.val + 1) : ℕ) : ℝ)
          = (m : ℝ) + (k : ℝ) - ((i.val : ℝ) + 1) := by
      have h1 : m + k - (i.val + 1) = m + (k - (i.val + 1)) := by omega
      rw [h1]
      push_cast [Nat.cast_sub hile]
      ring
    rw [hcast]
    ring
  rw [hrhs_eq, hpre, hsum_zero]
  push_cast
  ring

/-- **Stability + preconsistency ⇒ `ρ'(1) ≠ 0` (simple root at 1).**

Butcher §441 p. 376 (the simple-root half of the `lem:441A` `a₁ > 0`
argument).

If `M : LinearMultistepMethod k` is Dahlquist-stable (`M.IsStable`)
and preconsistent (`M.IsPreconsistent`), then the characteristic
polynomial's derivative `ρ'` does not vanish at 1.

Combined with cycle 175's `ρPoly_no_real_root_gt_one` and a future
cycle's IVT-style `ρ > 0` on `(1, ∞)` argument, this will give
`ρ'(1) > 0` — the load-bearing quantitative statement of `lem:441A`.

Textbook proof: a vanishing `ρ'(1)` (combined with `ρ(1) = 0` from
preconsistency) would mean the unbounded sequence `y_n := n` solves
the (403a) homogeneous recurrence — contradicting boundedness of all
homogeneous solutions under stability. -/
theorem LinearMultistepMethod.ρPoly_deriv_eval_one_ne_zero_of_stable_preconsistent
    {k : ℕ} (M : LinearMultistepMethod k)
    (hStable : M.IsStable) (hPre : M.IsPreconsistent) :
    M.ρPoly.derivative.eval 1 ≠ 0 := by
  intro hDeriv
  -- Build the unbounded homogeneous solution.
  have hsol : M.IsHomogeneousSolution (fun n : ℕ => (n : ℝ)) :=
    idSeq_isHomogeneousSolution_of_preconsistent_ρPoly_deriv_zero M hPre hDeriv
  -- Stability gives a uniform bound C.
  obtain ⟨C, hC⟩ := hStable _ hsol
  -- But ℕ is unbounded as ℝ (Archimedean property).
  obtain ⟨n, hngt⟩ := exists_nat_gt C
  have habs : |(n : ℝ)| ≤ C := hC n
  have hpos : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have habs_eq : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg hpos
  linarith

/-- **Leading coefficient of `ρPoly` at degree `k` is `1`.**

The polynomial `ρ(z) = z^k − Σ αᵢ z^{k−(i+1)}` has its `k`-th
coefficient equal to `1`: the `X^k` term contributes `1`, and the
subtracted sum has natDegree at most `k−1` (each summand `C(αᵢ) ·
X^{k−(i+1)}` has natDegree `≤ k − (i+1) ≤ k − 1` since `i+1 ≥ 1`
and `0 < k`), so does not contribute to the `k`-th coefficient. -/
private theorem LinearMultistepMethod.ρPoly_coeff_top_eq_one
    {k : ℕ} (hk : 0 < k) (M : LinearMultistepMethod k) :
    M.ρPoly.coeff k = 1 := by
  unfold LinearMultistepMethod.ρPoly
  have hsum_lt : (∑ i : Fin k,
      Polynomial.C (M.α i.succ) * Polynomial.X ^ (k - (i.val + 1))).natDegree < k := by
    have hsum_le :
        (∑ i : Fin k,
            Polynomial.C (M.α i.succ) * Polynomial.X ^ (k - (i.val + 1))).natDegree
          ≤ k - 1 :=
      Polynomial.natDegree_sum_le_of_forall_le
        (s := (Finset.univ : Finset (Fin k)))
        (f := fun i : Fin k =>
          Polynomial.C (M.α i.succ) * Polynomial.X ^ (k - (i.val + 1)))
        (n := k - 1)
        (by
          intro i _
          refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
          have hi : i.val + 1 ≤ k := i.isLt
          omega)
    omega
  rw [Polynomial.coeff_sub_eq_left_of_lt hsum_lt]
  rw [Polynomial.coeff_X_pow, if_pos rfl]

/-- **`natDegree` of `ρPoly` is exactly `k`.** Combines the upper
bound `ρPoly_natDegree_le` (cycle 172) with the lower bound from
`ρPoly_coeff_top_eq_one`: a polynomial whose `k`-th coefficient is
nonzero has natDegree at least `k`. -/
private theorem LinearMultistepMethod.ρPoly_natDegree_eq_k
    {k : ℕ} (hk : 0 < k) (M : LinearMultistepMethod k) :
    M.ρPoly.natDegree = k := by
  apply Nat.le_antisymm M.ρPoly_natDegree_le
  apply Polynomial.le_natDegree_of_ne_zero
  rw [M.ρPoly_coeff_top_eq_one hk]
  exact one_ne_zero

/-- **`ρPoly` is monic.** Direct corollary of Helpers 1 and 2:
`leadingCoeff = coeff (natDegree)` reduces to `coeff k = 1`. -/
private theorem LinearMultistepMethod.ρPoly_leadingCoeff_eq_one
    {k : ℕ} (hk : 0 < k) (M : LinearMultistepMethod k) :
    M.ρPoly.leadingCoeff = 1 := by
  unfold Polynomial.leadingCoeff
  rw [M.ρPoly_natDegree_eq_k hk, M.ρPoly_coeff_top_eq_one hk]

/-- **`ρ(z) → +∞` as `z → +∞`.** Butcher §441 p. 376 (implicit
step in the `ρ > 0` on `(1, ∞)` argument). The polynomial `ρ` has
positive degree `k > 0` and leading coefficient `1 ≥ 0`, so
Mathlib's `tendsto_atTop_of_leadingCoeff_nonneg` applies. -/
private theorem LinearMultistepMethod.ρPoly_tendsto_atTop
    {k : ℕ} (hk : 0 < k) (M : LinearMultistepMethod k) :
    Filter.Tendsto (fun z : ℝ => M.ρPoly.eval z)
      Filter.atTop Filter.atTop := by
  have h_nd : M.ρPoly.natDegree = k := M.ρPoly_natDegree_eq_k hk
  have h_ne : M.ρPoly ≠ 0 := by
    intro hzero
    have hcoeff := M.ρPoly_coeff_top_eq_one hk
    rw [hzero, Polynomial.coeff_zero] at hcoeff
    exact one_ne_zero hcoeff.symm
  have hdeg : 0 < M.ρPoly.degree := by
    rw [Polynomial.degree_eq_natDegree h_ne, h_nd]
    exact_mod_cast hk
  have hlc : 0 ≤ M.ρPoly.leadingCoeff := by
    rw [M.ρPoly_leadingCoeff_eq_one hk]
    exact zero_le_one
  exact Polynomial.tendsto_atTop_of_leadingCoeff_nonneg M.ρPoly hdeg hlc

/-- **`ρ > 0` on `(1, ∞)` for stable preconsistent k-step LMMs.**
Butcher §441 p. 376 (Phase B.3 Step 1 of `lem:441A`'s `a₁ > 0`
argument).

If `M : LinearMultistepMethod k` with `0 < k` is Dahlquist-stable
and preconsistent, then for every real `z > 1`, `ρ(z) > 0`.

Textbook proof (combining cycle 174's `ρ(1) = 0`, cycle 175's "no
real root > 1" under stability, leading-coefficient `1 > 0`, and
the IVT): `ρ` tends to `+∞` at `+∞` (Helper 4). If `ρ(z) ≤ 0` for
some `z > 1`, then either `ρ(z) = 0` (a real root > 1, ruled out
by cycle 175) or `ρ(z) < 0` (the IVT on `[z, w']` for some `w' > z`
with `ρ(w') ≥ 1` produces a root `ζ ∈ [z, w']` with `ζ > 1`,
again contradicting cycle 175).

The `_hPre` hypothesis is propagated for downstream-signature
alignment (Phase B.3 Step 2 + B.4 use it); it is unused in this
proof. -/
theorem LinearMultistepMethod.ρPoly_pos_on_Ioi_one
    {k : ℕ} (hk : 0 < k) (M : LinearMultistepMethod k)
    (hStable : M.IsStable) (_hPre : M.IsPreconsistent) :
    ∀ z : ℝ, 1 < z → 0 < M.ρPoly.eval z := by
  intro z hz1
  by_contra hle
  push_neg at hle  -- hle : M.ρPoly.eval z ≤ 0
  rcases eq_or_lt_of_le hle with heq | hlt
  · -- ρ(z) = 0 ⇒ z is a real root > 1, ruled out by cycle 175.
    have hroot : M.ρPoly.IsRoot z := heq
    have hzle : z ≤ 1 := M.ρPoly_no_real_root_gt_one hStable hroot
    linarith
  · -- ρ(z) < 0. Use ρPoly_tendsto_atTop to get w' > z with ρ(w') ≥ 1,
    -- then IVT on [z, w'] yields ζ ∈ [z, w'] with ρ(ζ) = 0 and ζ > 1.
    have htend := M.ρPoly_tendsto_atTop hk
    rw [Filter.tendsto_atTop_atTop] at htend
    obtain ⟨w, hw⟩ := htend 1
    set w' := max w z + 1 with hw'_def
    have hw'_ge_w : w ≤ w' := by
      have := le_max_left w z
      simp [w']
      linarith
    have hw'_gt_z : z < w' := by
      have := le_max_right w z
      simp [w']
      linarith
    have hρw' : 1 ≤ M.ρPoly.eval w' := hw _ hw'_ge_w
    have hcont : ContinuousOn (fun x : ℝ => M.ρPoly.eval x) (Set.Icc z w') :=
      M.ρPoly.continuous.continuousOn
    have hzero_mem :
        (0 : ℝ) ∈ Set.Icc (M.ρPoly.eval z) (M.ρPoly.eval w') := by
      refine ⟨le_of_lt hlt, ?_⟩
      linarith
    have hivt :=
      intermediate_value_Icc (le_of_lt hw'_gt_z) hcont hzero_mem
    obtain ⟨ζ, hζ_mem, hζ_eval⟩ := hivt
    have hζ_root : M.ρPoly.IsRoot ζ := hζ_eval
    have hζ_le_one : ζ ≤ 1 :=
      M.ρPoly_no_real_root_gt_one hStable hζ_root
    have hζ_gt_one : 1 < ζ := lt_of_lt_of_le hz1 hζ_mem.1
    linarith

/-- **`ρ'(1) > 0` for stable preconsistent k-step LMMs.** Butcher §441
p. 376 (Phase B.3 Step 2 of `lem:441A`'s `a₁ > 0` argument).

If `M : LinearMultistepMethod k` with `0 < k` is Dahlquist-stable and
preconsistent, then `ρ'(1) > 0`.

Textbook proof: by `ρPoly_pos_on_Ioi_one` (cycle 177), `ρ(z) > 0` for
`z > 1`. Combined with `ρ(1) = 0` (cycle 174), the slope `(ρ(1+h) -
ρ(1))/h` is strictly positive for every `h > 0`. Taking the limit as
`h → 0⁺` gives `ρ'(1) ≥ 0` (limit of nonnegative is nonnegative). By
`ρPoly_deriv_eval_one_ne_zero_of_stable_preconsistent` (cycle 176),
`ρ'(1) ≠ 0`, so `ρ'(1) > 0`.

Lean structure: convert `Polynomial.hasDerivAt` to a slope-Tendsto via
`HasDerivAt.tendsto_slope`, restrict the punctured neighbourhood
filter `𝓝[≠] 1` down to the right-sided neighbourhood `𝓝[>] 1` via
`Filter.Tendsto.mono_left`, then apply `ge_of_tendsto` with the
eventual non-negativity claim. -/
theorem LinearMultistepMethod.ρPoly_deriv_eval_one_pos_of_stable_preconsistent
    {k : ℕ} (M : LinearMultistepMethod k) (hk : 0 < k)
    (hStable : M.IsStable) (hPre : M.IsPreconsistent) :
    0 < M.ρPoly.derivative.eval 1 := by
  have hne : M.ρPoly.derivative.eval 1 ≠ 0 :=
    M.ρPoly_deriv_eval_one_ne_zero_of_stable_preconsistent hStable hPre
  have hderiv : HasDerivAt (fun z : ℝ => M.ρPoly.eval z)
                  (M.ρPoly.derivative.eval 1) 1 :=
    M.ρPoly.hasDerivAt 1
  have hρ1 : M.ρPoly.eval 1 = 0 :=
    M.ρPoly_eval_one_eq_zero_of_preconsistent hPre
  have hpos : ∀ z : ℝ, 1 < z → 0 < M.ρPoly.eval z :=
    M.ρPoly_pos_on_Ioi_one hk hStable hPre
  have hslope : Filter.Tendsto (slope (fun z : ℝ => M.ρPoly.eval z) 1)
                  (nhdsWithin 1 (Set.Ioi 1))
                  (nhds (M.ρPoly.derivative.eval 1)) := by
    refine Filter.Tendsto.mono_left hderiv.tendsto_slope ?_
    exact nhdsWithin_mono _ (fun z hz => ne_of_gt hz)
  have hslope_nonneg : ∀ᶠ z in nhdsWithin (1 : ℝ) (Set.Ioi 1),
      0 ≤ slope (fun w : ℝ => M.ρPoly.eval w) 1 z := by
    refine Filter.eventually_iff.mpr (Filter.mem_of_superset self_mem_nhdsWithin ?_)
    intro z hz
    show 0 ≤ slope (fun w : ℝ => M.ρPoly.eval w) 1 z
    have hnum : 0 < M.ρPoly.eval z - M.ρPoly.eval 1 := by
      rw [hρ1, sub_zero]; exact hpos z hz
    have hden : 0 < z - 1 := sub_pos.mpr hz
    rw [slope_def_field]
    positivity
  have hge : 0 ≤ M.ρPoly.derivative.eval 1 :=
    ge_of_tendsto hslope hslope_nonneg
  exact lt_of_le_of_ne hge (Ne.symm hne)

end OpenMath.Chapter4.Section404

namespace OpenMath.Chapter4.Section441

open OpenMath.Chapter4.Section404
open OpenMath.Chapter4.Section451

/-- **Non-vacuity witness — explicit Euler's `a(z)` is `2X`.**

For `k = 1`, `α₁ = 1` (explicit Euler, see
`Section404.lean::explicitEulerLMM`):

  `a(z) = (1+z) − 1·(1+z)^0·(1−z)^1 = (1+z) − (1−z) = 2z`.

This is the smallest non-trivial witness that the `aPoly` formula
matches Butcher's §441 definition. -/
theorem explicitEulerLMM_aPoly_eq :
    explicitEulerLMM.aPoly = 2 * Polynomial.X := by
  unfold LinearMultistepMethod.aPoly
  simp [explicitEulerLMM]
  ring

/-- **Non-vacuity witness — explicit Euler's `ρ(z) = z − 1`.**

For `k = 1`, `α₁ = 1` (explicit Euler, see
`Section404.lean::explicitEulerLMM`):

  `ρ(z) = z − α₁·z^0 = z − 1`.

This confirms the `ρPoly` formula matches Butcher's §441
characteristic polynomial on the smallest non-trivial example. -/
theorem explicitEulerLMM_ρPoly_eq :
    explicitEulerLMM.ρPoly = Polynomial.X - 1 := by
  unfold LinearMultistepMethod.ρPoly
  simp [explicitEulerLMM]

/-- **BDF2 is preconsistent.** The textbook `α₁ = 4/3, α₂ = -1/3`
satisfy `α₁ + α₂ = 1`, so `bdf2LMM` is preconsistent (Butcher §404a). -/
theorem bdf2LMM_isPreconsistent : bdf2LMM.IsPreconsistent := by
  simp [LinearMultistepMethod.IsPreconsistent, bdf2LMM, Fin.sum_univ_two]
  norm_num

/-- **`a₀ = 0` for BDF2.** Direct corollary of preconsistency
(`aPoly_coeff_zero_of_preconsistent`). -/
theorem bdf2LMM_aPoly_coeff_zero_eq :
    bdf2LMM.aPoly.coeff 0 = 0 :=
  bdf2LMM.aPoly_coeff_zero_of_preconsistent bdf2LMM_isPreconsistent

/-- **BDF2 `a₁` sanity witness.** Combining cycle 174's bridge
`a₁ = 2·ρ'(1)` (under preconsistency) with the unconditional closed
form `ρ'(1) = k − Σᵢ αᵢ(k − (i+1))`, the BDF2 method's `aPoly`
coefficient at degree 1 is `4/3`.

Numerically: `ρ'(1) = 2 − [(4/3)·1 + (−1/3)·0] = 2/3`, so
`a₁ = 2·(2/3) = 4/3`.

This witnesses Butcher's §441 a-coefficient calculation on the
canonical `k = 2` example, sidestepping the deferred full closed
form `bdf2LMM.aPoly = C(4/3) X + C(8/3) X²` (cycle 172/173). -/
theorem bdf2LMM_aPoly_coeff_one_eq :
    bdf2LMM.aPoly.coeff 1 = 4 / 3 := by
  rw [bdf2LMM.aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent
        bdf2LMM_isPreconsistent]
  rw [LinearMultistepMethod.ρPoly_deriv_eval_one_unconditional]
  simp [bdf2LMM, Fin.sum_univ_two]
  norm_num

/-- **BDF2 has a simple root at 1.** Direct corollary of the
unconditional ρ'(1) closed form: `ρ'(1) = 2 − [(4/3)·1 + (−1/3)·0]
= 2/3 ≠ 0`. Witnesses cycle 176's
`ρPoly_deriv_eval_one_ne_zero_of_stable_preconsistent` numerically
on the canonical `k = 2` example. The bridge `a₁ = 2·ρ'(1)` (cycle
174) is made explicit on `k = 2`: `a₁ = 4/3 = 2·(2/3) = 2·ρ'(1)`. -/
theorem bdf2LMM_ρPoly_deriv_eval_one_eq :
    bdf2LMM.ρPoly.derivative.eval 1 = 2 / 3 := by
  rw [LinearMultistepMethod.ρPoly_deriv_eval_one_unconditional]
  simp [bdf2LMM, Fin.sum_univ_two]
  norm_num

/-- **BDF2 numerical sanity for `ρPoly_deriv_eval_one_pos_of_stable_preconsistent`.**
Lifts cycle 176's closed form `bdf2LMM.ρPoly.derivative.eval 1 = 2/3`
to a strict positivity witness, numerically verifying cycle 178's
`ρPoly_deriv_eval_one_pos_of_stable_preconsistent` on the canonical
`k = 2` example. Pairs with `bdf2LMM_aPoly_coeff_one_eq` (cycle 175,
`a₁ = 4/3`) to confirm the sign half of the cycle 174 bridge
`a₁ = 2·ρ'(1)` for BDF2: `4/3 > 0` and `2·(2/3) = 4/3 > 0`. -/
theorem bdf2LMM_ρPoly_deriv_eval_one_pos :
    0 < bdf2LMM.ρPoly.derivative.eval 1 := by
  rw [bdf2LMM_ρPoly_deriv_eval_one_eq]
  norm_num

/-- **BDF2 numerical sanity for `ρPoly_pos_on_Ioi_one`.** For BDF2,
`ρ(z) = z² − (4/3)z + 1/3`, so `ρ(2) = 4 − 8/3 + 1/3 = 5/3 > 0`.
Direct numerical witness; does not route through
`ρPoly_pos_on_Ioi_one` (which would require `bdf2LMM.IsStable`,
not yet shipped). -/
theorem bdf2LMM_ρPoly_pos_at_two : 0 < bdf2LMM.ρPoly.eval 2 := by
  unfold LinearMultistepMethod.ρPoly
  simp [bdf2LMM, Fin.sum_univ_two]
  norm_num

/-- **Phase B.4: `a₁ > 0` for stable preconsistent LMMs.**

Combines cycle 174's bridge `a₁ = 2·ρ'(1)` (under preconsistency,
`aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent`) with
cycle 178's positivity result `ρ'(1) > 0` (under stability +
preconsistency, `ρPoly_deriv_eval_one_pos_of_stable_preconsistent`).
Together with `aPoly_coeff_zero_of_preconsistent` (cycle 173,
`a₀ = 0`), this closes the `a₁ > 0` half of Butcher's Lemma 441A
(Butcher §441 p. 376).

The remaining `aᵢ ≥ 0 for i ∈ [2, k]` half (Phase C) requires a
complex-root decomposition argument over `aPoly` and is multi-cycle
work, deferred to a fresh strategy. -/
theorem LinearMultistepMethod.aPoly_coeff_one_pos_of_stable_preconsistent
    {k : ℕ} (M : LinearMultistepMethod k) (hk : 0 < k)
    (hStable : M.IsStable) (hPre : M.IsPreconsistent) :
    0 < M.aPoly.coeff 1 := by
  rw [M.aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent hPre]
  have hρ : 0 < M.ρPoly.derivative.eval 1 :=
    M.ρPoly_deriv_eval_one_pos_of_stable_preconsistent hk hStable hPre
  linarith

/-- **BDF2 numerical sanity for `aPoly_coeff_one_pos_of_stable_preconsistent`.**
Lifts cycle 175's closed form `bdf2LMM.aPoly.coeff 1 = 4/3`
(`bdf2LMM_aPoly_coeff_one_eq`) to a strict positivity witness, numerically
confirming `a₁ > 0` on the canonical `k = 2` example. The cycle 174
bridge `a₁ = 2·ρ'(1)` is fully witnessed: `4/3 = 2·(2/3)` (cycle 175 +
176/178). -/
theorem bdf2LMM_aPoly_coeff_one_pos : 0 < bdf2LMM.aPoly.coeff 1 := by
  rw [bdf2LMM_aPoly_coeff_one_eq]
  norm_num

/-- **BDF2 closed-form `aPoly`.**

For BDF2 (`k = 2`, `α₁ = 4/3`, `α₂ = -1/3`),

  `a(z) = (1+z)² − (4/3)(1+z)(1-z) − (−1/3)(1-z)²`
        `= 1 + 2z + z² − 4/3 + (4/3)z² + 1/3 − (2/3)z + (1/3)z²`
        `= (4/3) z + (8/3) z²`.

Cycles 172/173 stalled on this identity using `Polynomial.ext` + per-
coefficient `simp`; the obstruction was that `ring` cannot fold
`Polynomial.C` arithmetic over the rationals.

This cycle (180, Priority 2) closes the identity via `Polynomial.funext`
(which requires `IsDomain ℝ` + `Infinite ℝ`, both available) — the
proof lifts to pointwise evaluation in `ℝ`, where `ring` does fold. -/
theorem bdf2LMM_aPoly_eq :
    bdf2LMM.aPoly =
      Polynomial.C (4 / 3) * Polynomial.X +
      Polynomial.C (8 / 3) * Polynomial.X ^ 2 := by
  apply Polynomial.funext
  intro x
  unfold LinearMultistepMethod.aPoly
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one,
             Polynomial.eval_add, Polynomial.eval_sub,
             Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
             Polynomial.eval_X, Polynomial.eval_one]
  have h1 : bdf2LMM.α (Fin.succ 0) = 4 / 3 := rfl
  have h2 : bdf2LMM.α (Fin.succ 1) = -1 / 3 := rfl
  rw [h1, h2]
  ring

/-- **BDF2 `a₂` closed form.** Direct corollary of `bdf2LMM_aPoly_eq`. -/
theorem bdf2LMM_aPoly_coeff_two_eq :
    bdf2LMM.aPoly.coeff 2 = 8 / 3 := by
  rw [bdf2LMM_aPoly_eq]
  simp

/-- **BDF2 `a₂ > 0` numerical witness.** Witnesses Phase C's headline
`aᵢ ≥ 0` for `i ≥ 2` on the canonical `k = 2` example, sidestepping
the multi-cycle Phase C complex-root infrastructure (see
`.prover-state/issues/lem_441A_phase_C_scoping.md`). -/
theorem bdf2LMM_aPoly_coeff_two_pos : 0 < bdf2LMM.aPoly.coeff 2 := by
  rw [bdf2LMM_aPoly_coeff_two_eq]
  norm_num

/-! ## Phase C.1 — Möbius algebraic bridge

This section opens Phase C of `lem:441A` (Butcher §441 p. 376) by
introducing the *Möbius transform* of a polynomial and proving the
algebraic bridge identity that connects `aPoly` to the §410
characteristic polynomial `αPoly`.

The textbook substitution is `ψ(z) = (1−z)/(1+z)`, which sends the
exterior `|w| > 1` of the closed unit disc to the right half plane
`Re(z) > 0` (and conversely). Under this substitution Butcher's
`a(z) = (1+z)^k − Σᵢ αᵢ (1+z)^{k−i}(1−z)^i` factors as

  `a(z) = (1+z)^k · α(ψ(z))`,

where `α(w) = 1 − Σᵢ αᵢ w^i` is the §410 generating polynomial.
This factorisation is the crux of §441's proof: stability of `M`
(no roots of `ρ` outside `|w| ≤ 1`, simple roots on the boundary)
translates via `ψ` to a *real-coefficient factorisation* of `aPoly`
into linear factors `(1 + cᵢ X)` and quadratic factors with
non-negative coefficients — from which `aᵢ ≥ 0` follows by induction.

To avoid division in `ℝ[X]`, we encode the substitution via the
homogenised `mobiusTransform n p`, which evaluates `p` at the
projective point `(1−X : 1+X)` with total degree `n`.

Phase C.1 (this cycle) ships:

* `mobiusTransform` — the homogenised transform.
* `aPoly_eq_mobiusTransform_αPoly` — the algebraic bridge.
* `aPoly_aeval_eq_mul_αPoly_aeval` — pointwise identity at any
  complex argument, expressing `aPoly(ζ) = (1+ζ)^k · αPoly(ψ(ζ))`.
* `aPoly_aeval_eq_zero_iff_αPoly_aeval_at_mobiusArg` — complex-side
  root bridge for `ζ ≠ −1`.
* BDF2 numerical sanity witness composing with `bdf2LMM_aPoly_eq`.

Phases C.2–C.4 (stability ⇒ left-half-plane root pattern, real
factorisation, closure) are scheduled for cycles 182+. See
`.prover-state/issues/lem_441A_phase_C_scoping.md` for the parent
plan. -/

/-- **Möbius transform of a real polynomial (homogenised).**

Given `n : ℕ` and `p : Polynomial ℝ`, the *Möbius transform of `p`
at total degree `n`* is the polynomial

  `mobiusTransform n p = Σᵢ₌₀ⁿ (p.coeff i) · (1 − X)^i · (1 + X)^{n−i}`.

Mathematically this is the homogeneous evaluation of `p` at the
projective ratio `(1 − X) / (1 + X)` with total degree `n`: when
`p.natDegree ≤ n` and `(1 + X)` is invertible (e.g. evaluated at
`x ≠ −1`), one has

  `mobiusTransform n p = (1 + X)^n · p((1 − X) / (1 + X))`

as a rational-function identity. The polynomial form avoids the
division and is what we use throughout §441.

Used to bridge `aPoly` (Section441) and `αPoly` (Section410): see
`aPoly_eq_mobiusTransform_αPoly`.

The total-degree parameter `n` is independent of `p.natDegree`
because §441's substitution requires homogenisation at the LMM
step count `k`, not at `αPoly.natDegree` (which can drop below `k`
when `αₖ = 0`, e.g. for Adams-Bashforth methods). -/
noncomputable def mobiusTransform (n : ℕ) (p : Polynomial ℝ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    Polynomial.C (p.coeff i) *
    (1 - Polynomial.X) ^ i * (1 + Polynomial.X) ^ (n - i)

/-- **`αPoly`'s constant coefficient is 1.**

By the §410 sign convention `αPoly M = 1 − Σⱼ αⱼ X^(j+1)`, the
constant term comes from the leading `1` (every `X^(j+1)` term has
zero constant coefficient since `j+1 ≥ 1`). -/
private lemma αPoly_coeff_zero {k : ℕ} (M : LinearMultistepMethod k) :
    (OpenMath.Chapter4.Section410.αPoly M).coeff 0 = 1 := by
  unfold OpenMath.Chapter4.Section410.αPoly
  rw [Polynomial.coeff_sub, Polynomial.coeff_one_zero,
      Polynomial.finset_sum_coeff]
  have h : ∀ j : Fin k,
      (Polynomial.C (M.α j.succ) * Polynomial.X ^ (j.val + 1)).coeff 0 = 0 := by
    intro j
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_neg (Nat.succ_ne_zero j.val).symm]
    ring
  simp [h]

/-- **`αPoly`'s coefficient at `j+1` (for `j : Fin k`) equals `-αⱼ`.**

By the §410 sign convention `αPoly M = 1 − Σⱼ' αⱼ' X^(j'+1)`, the
coefficient of `X^(j+1)` for `j : Fin k` comes solely from the
`j' = j` summand. -/
private lemma αPoly_coeff_succ {k : ℕ} (M : LinearMultistepMethod k)
    (j : Fin k) :
    (OpenMath.Chapter4.Section410.αPoly M).coeff (j.val + 1) = -M.α j.succ := by
  unfold OpenMath.Chapter4.Section410.αPoly
  rw [Polynomial.coeff_sub, Polynomial.coeff_one,
      if_neg (Nat.succ_ne_zero j.val), Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single j]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl]
    ring
  · intro j' _ hne
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    have hne' : j.val + 1 ≠ j'.val + 1 := by
      intro h
      apply hne
      apply Fin.ext
      exact Nat.succ_injective h.symm
    rw [if_neg hne']
    ring
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- **§441 algebraic bridge — `aPoly = mobiusTransform k αPoly`.**

This is the polynomial form of Butcher's textbook identity (§441
p. 376) `a(z) = (1+z)^k · α(ψ(z))`, with `ψ(z) = (1−z)/(1+z)`.
Homogenising at `k` clears the denominator `(1+z)^k`, giving the
polynomial identity

  `aPoly = Σᵢ₌₀ᵏ (αPoly.coeff i) · (1 − X)^i · (1 + X)^(k−i)`.

The proof splits the RHS sum at `i = 0` (the `(1 + X)^k` term),
substitutes `αPoly.coeff 0 = 1` and `αPoly.coeff (j+1) = −αⱼ` (for
`j : Fin k`), and reindexes the remaining range-`k` sum to `Fin k`
to match `aPoly`'s definition.

This is the workhorse of Phase C: every subsequent step of the
factorisation argument routes through this identity. -/
theorem aPoly_eq_mobiusTransform_αPoly {k : ℕ}
    (M : LinearMultistepMethod k) :
    M.aPoly = mobiusTransform k (OpenMath.Chapter4.Section410.αPoly M) := by
  apply Polynomial.funext
  intro x
  unfold LinearMultistepMethod.aPoly mobiusTransform
  simp only [Polynomial.eval_sub, Polynomial.eval_finset_sum,
             Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
             Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_C]
  rw [Finset.sum_range_succ' (fun i =>
        (OpenMath.Chapter4.Section410.αPoly M).coeff i *
          (1 - x) ^ i * (1 + x) ^ (k - i)) k]
  simp only [pow_zero, mul_one, Nat.sub_zero]
  rw [αPoly_coeff_zero M]
  rw [show (∑ i ∈ Finset.range k,
        (OpenMath.Chapter4.Section410.αPoly M).coeff (i + 1) *
          (1 - x) ^ (i + 1) * (1 + x) ^ (k - (i + 1)))
      = ∑ j : Fin k,
        (OpenMath.Chapter4.Section410.αPoly M).coeff (j.val + 1) *
          (1 - x) ^ (j.val + 1) * (1 + x) ^ (k - (j.val + 1)) from ?_]
  · simp_rw [αPoly_coeff_succ M]
    have hexpand :
        ∀ j : Fin k,
          (-M.α j.succ) * (1 - x) ^ (j.val + 1) * (1 + x) ^ (k - (j.val + 1))
            = -(M.α j.succ * (1 + x) ^ (k - (j.val + 1)) * (1 - x) ^ (j.val + 1)) := by
      intro j
      ring
    simp_rw [hexpand, Finset.sum_neg_distrib]
    ring
  · rw [Fin.sum_univ_eq_sum_range
        (fun i => (OpenMath.Chapter4.Section410.αPoly M).coeff (i + 1) *
          (1 - x) ^ (i + 1) * (1 + x) ^ (k - (i + 1)))]

/-- **§441 multiplicative bridge — `aPoly(ζ) = (1+ζ)^k · αPoly(ψ(ζ))`.**

For `ζ : ℂ` with `1 + ζ ≠ 0`, evaluating the Phase C.1 algebraic
bridge `aPoly = mobiusTransform k αPoly` at `ζ` yields the
multiplicative identity

  `aPoly.aeval ζ = (1 + ζ)^k · αPoly.aeval ((1 − ζ) / (1 + ζ))`.

The proof routes through the polynomial bridge, expands the
`mobiusTransform` summands via `eval₂`, and factors out `(1+ζ)^k`
using the algebraic identity `(1−ζ)^i · (1+ζ)^(k−i) = (1+ζ)^k ·
((1−ζ)/(1+ζ))^i` (valid because `(1+ζ)^i ≠ 0`).

The hypothesis `αPoly.natDegree ≤ k` (cycle 073's `αPoly_natDegree_le`)
is used to identify the truncated sum `Σᵢ₌₀ᵏ αPoly.coeff i · w^i` with
`αPoly.aeval w`. -/
theorem aPoly_aeval_eq_mul_αPoly_aeval {k : ℕ} (M : LinearMultistepMethod k)
    (ζ : ℂ) (hζ : (1 : ℂ) + ζ ≠ 0) :
    Polynomial.aeval ζ M.aPoly =
      (1 + ζ) ^ k *
        Polynomial.aeval ((1 - ζ) / (1 + ζ))
          (OpenMath.Chapter4.Section410.αPoly M) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def]
  rw [aPoly_eq_mobiusTransform_αPoly M]
  unfold mobiusTransform
  rw [Polynomial.eval₂_finset_sum]
  rw [Polynomial.eval₂_eq_sum_range' (algebraMap ℝ ℂ)
        (Nat.lt_succ_of_le (OpenMath.Chapter4.Section410.αPoly_natDegree_le M))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_add,
      Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_one]
  have hpow : (1 + ζ : ℂ) ^ k = (1 + ζ) ^ i * (1 + ζ) ^ (k - i) := by
    rw [← pow_add]
    congr 1
    omega
  have hpowi_ne : (1 + ζ : ℂ) ^ i ≠ 0 := pow_ne_zero _ hζ
  rw [hpow, div_pow]
  field_simp

/-- **§441 complex-side root bridge.**

For `ζ : ℂ` with `ζ ≠ −1`, `ζ` is a root of `aPoly` iff its Möbius
image `ψ(ζ) = (1 − ζ) / (1 + ζ)` is a root of `αPoly`. The boundary
case `ζ = −1` corresponds to a degree drop in `αPoly` (i.e. `αₖ = 0`),
which is handled separately in Phase C.2.

This is the workhorse complex-analytic bridge that translates
stability of `M` (no `ρ`-roots outside `|w| ≤ 1`) into a constraint
on `aPoly`'s roots — the next step in §441's factorisation argument. -/
theorem aPoly_aeval_eq_zero_iff_αPoly_aeval_at_mobiusArg {k : ℕ}
    (M : LinearMultistepMethod k) (ζ : ℂ) (hζ : ζ ≠ -1) :
    Polynomial.aeval ζ M.aPoly = 0 ↔
      Polynomial.aeval ((1 - ζ) / (1 + ζ))
        (OpenMath.Chapter4.Section410.αPoly M) = 0 := by
  have h1pζ : (1 : ℂ) + ζ ≠ 0 := by
    intro h
    apply hζ
    linear_combination h
  have hpow : (1 + ζ : ℂ) ^ k ≠ 0 := pow_ne_zero _ h1pζ
  rw [aPoly_aeval_eq_mul_αPoly_aeval M ζ h1pζ]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hpow
    · exact h
  · intro h
    rw [h, mul_zero]

/-- **BDF2 numerical sanity for the Möbius bridge.** Specialises
`aPoly_eq_mobiusTransform_αPoly` to the canonical `k = 2` example. -/
theorem bdf2LMM_aPoly_eq_mobiusTransform :
    bdf2LMM.aPoly =
      mobiusTransform 2 (OpenMath.Chapter4.Section410.αPoly bdf2LMM) :=
  aPoly_eq_mobiusTransform_αPoly bdf2LMM

/-- **BDF2 closed form for `mobiusTransform 2 αPoly`.** Composes the
cycle 180 closed form (`bdf2LMM_aPoly_eq`) with the Phase C.1 bridge
to yield a fully evaluated form for the Möbius transform on BDF2. -/
theorem bdf2LMM_mobiusTransform_αPoly_eq :
    mobiusTransform 2 (OpenMath.Chapter4.Section410.αPoly bdf2LMM) =
      Polynomial.C (4 / 3) * Polynomial.X +
      Polynomial.C (8 / 3) * Polynomial.X ^ 2 := by
  rw [← aPoly_eq_mobiusTransform_αPoly bdf2LMM, bdf2LMM_aPoly_eq]

end OpenMath.Chapter4.Section441
