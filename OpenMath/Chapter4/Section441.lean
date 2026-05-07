import OpenMath.Chapter4.Section404
import OpenMath.Chapter4.Section410

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
`ρ'(1) > 0`, exactly matching the textbook strategy on p. 376. -/
theorem LinearMultistepMethod.aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent
    {k : ℕ} (M : LinearMultistepMethod k) (hPre : M.IsPreconsistent) :
    M.aPoly.coeff 1 = 2 * M.ρPoly.derivative.eval 1 := by
  rw [M.aPoly_coeff_one_eq_neg_two_alpha_deriv_at_one_of_preconsistent hPre]
  rw [M.ρPoly_deriv_eval_one_eq_neg_alpha_deriv_at_one_of_preconsistent hPre]
  ring

end OpenMath.Chapter4.Section404

namespace OpenMath.Chapter4.Section441

open OpenMath.Chapter4.Section404

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

end OpenMath.Chapter4.Section441
