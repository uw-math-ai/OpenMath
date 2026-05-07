import OpenMath.Chapter4.Section404

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

A `k = 2` BDF2 closed-form witness was attempted in cycle 172 but
deferred: the polynomial identity
`bdf2LMM.aPoly = C(4/3) X + C(8/3) X²` is straightforward to
verify by hand but `ring` (the obvious finisher) does not fold
`Polynomial.C` constants automatically (`C(4/3) - C(-1/3) = C(5/3)`
is not in `ring`'s normal form). The standalone algebraic check
appears in `.prover-state/issues/lem_441B_misinterpretation.md`
as the explicit refutation of cycle 171's misreading.

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

end OpenMath.Chapter4.Section441
