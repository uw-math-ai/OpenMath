import OpenMath.Chapter4.Section404

/-!
# Butcher §441 — Maximum order for a convergent k-step method (Phase A)

This file opens Butcher's §441 cluster (`lem:441A`, `lem:441B`,
`thm:441C`, the *Dahlquist barrier* result) by introducing the
polynomial `a(z)` of equation (441b) and stating the headline
`lem:441B` (negativity of even coefficients) as a `sorry` for
multi-cycle closure.

## Textbook source (Butcher §441, p. 375–376)

For a `k`-step linear multistep method with characteristic
polynomial

  `ρ(z) = z^k − α₁z^{k−1} − α₂z^{k−2} − ⋯ − αₖ`,

Butcher introduces the auxiliary polynomial

  `a(z) = (1+z)^k − α₁(1+z)^{k−1}(1−z) − α₂(1+z)^{k−2}(1−z)² − ⋯ − αₖ(1−z)^k`.

Lemma 441B then asserts that the coefficients `c₂, c₄, …` of the
expansion `a(z) = c₀ + c₁z + c₂z² + c₄z⁴ + ⋯` are all negative.

## Sign convention

Our §404 LMM structure stores the textbook `α₁, α₂, …, αₖ` as
`M.α i.succ` for `i : Fin k`, with `M.α 0 = -1` (the leading-
coefficient normalisation). The polynomial `a(z)` is built from
the textbook `αᵢ`, so the Lean encoding selects `M.α i.succ` for
`i : Fin k` and uses `(i.val + 1)` for the `(1−z)` exponent.

## Phase status

* Cycle 171 (Phase A) — this file: `aPoly` definition,
  `explicitEulerLMM_aPoly_eq` non-vacuity witness, and the
  headline statement `aPoly_even_coeff_neg` as `sorry`.
* Cycle 172+ (Phase B) — the (441c) recurrence
  `(2 + (2/3)z² + (2/5)z⁴ + ⋯)(c₀ + c₂z² + c₄z⁴ + ⋯) = 1`,
  base cases `c₀ = 1/2`, `c₂ = -1/6`, and the `aPoly` degree
  bound `(aPoly M).natDegree ≤ k`.
* Cycle 173+ (Phase C) — the strong induction discharging
  `aPoly_even_coeff_neg`.

## References

* Butcher, *Numerical Methods for Ordinary Differential Equations*,
  3rd ed., §441 "Maximum order for a convergent k-step method",
  pp. 375–376.
* `extraction/formalization_data/entities/lem_441B.json`
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

This is the *defining* formula from Butcher; the c-coefficient
expansion `a(z) = c₀ + c₁z + c₂z² + ⋯` is an *output* derived from
this polynomial, not an independent definition (defining `aPoly`
by its c-coefficients would be smuggling).

Lives in the `Section404.LinearMultistepMethod` namespace so that
the dot notation `M.aPoly` resolves through to this definition. -/
noncomputable def LinearMultistepMethod.aPoly
    {k : ℕ} (M : LinearMultistepMethod k) : Polynomial ℝ :=
  (1 + Polynomial.X) ^ k -
    ∑ i : Fin k,
      Polynomial.C (M.α i.succ) *
      (1 + Polynomial.X) ^ (k - (i.val + 1)) *
      (1 - Polynomial.X) ^ (i.val + 1)

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

/-- **Headline `lem:441B` — Butcher §441, p. 376.**

The even coefficients `c₂, c₄, …` of `aPoly` (i.e. all even-index
coefficients with `2 ≤ index ≤ k`) are strictly negative whenever
the LMM is stable.

**Status: `sorry` (multi-cycle plan).** The proof requires:

1. The (441c) recurrence
   `(2 + (2/3)z² + (2/5)z⁴ + ⋯)·(c₀ + c₂z² + c₄z⁴ + ⋯) = 1`
   relating `aPoly`'s even coefficients to the inverse of the
   power-series `(1/z)·log((1+z)/(1−z))`.
2. Base cases `c₀ = 1/2` and `c₂ = -1/6`.
3. Strong induction on `n` per Butcher §441
   (the (441d) multiplication trick by `2n+1 − (2n−1)z²`).

Phase B (cycle 172+) will formalise (1) and (2). Phase C
(cycle 173+) discharges this `sorry` via the induction.

The coefficient-of-`y(x_n)`-stays-zero argument from §403 stability
enters via the `IsStable` hypothesis: a non-stable LMM can have
positive even coefficients (e.g. classical zero-stability counter-
examples). -/
theorem LinearMultistepMethod.aPoly_even_coeff_neg
    {k : ℕ} (M : LinearMultistepMethod k) (_hStable : M.IsStable) :
    ∀ n : ℕ, 2 ≤ 2 * n → 2 * n ≤ k →
      M.aPoly.coeff (2 * n) < 0 := by
  sorry

end OpenMath.Chapter4.Section441
