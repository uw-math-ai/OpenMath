import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Real.Basic

/-!
# Butcher §441 — universal series `c_{2i}` for `log((1+z)/(1-z))/z` (Phase B)

This file formalises Butcher Lemma 441B's underlying construction:
the universal constants `c_0, c_2, c_4, …` defined by the
power-series inverse identity (441c)

```
(2 + (2/3) z² + (2/5) z⁴ + ⋯) · (c₀ + c₂ z² + c₄ z⁴ + ⋯) = 1.
```

These constants are **independent of any LMM** — they are pure
ℝ-valued constants attached to the universal function
`log((1+z)/(1-z)) / z`. They are NOT to be confused with the
LMM-dependent `aPoly` coefficients of `lem:441A`; cycle 171
conflated the two and was rolled back in cycle 172. See
`.prover-state/issues/lem_441B_misinterpretation.md` for the
full diagnosis.

## What this file contains (Phase B)

* `cInverseLogSeries : PowerSeries ℝ` — the LHS series of (441c),
  `2 + (2/3) X² + (2/5) X⁴ + ⋯`. Odd coefficients are zero.
* `cInverseLogSeries_constantCoeff_eq_two` — its constant term
  is `2`, making it invertible in `PowerSeries ℝ`.
* `cSeries : PowerSeries ℝ` — the algebraic inverse of
  `cInverseLogSeries` via `PowerSeries.invOfUnit`.
* `cInverseLogSeries_mul_cSeries_eq_one` — the (441c) identity.
* `cInverseLog (n : ℕ) : ℝ` — the textbook constants `c_{2n}`,
  extracted as `coeff (2*n) cSeries`.
* `cInverseLog_zero_eq_half`, `cInverseLog_one_eq_neg_one_sixth`
  — the base cases `c₀ = 1/2`, `c₂ = -1/6` (Butcher p. 376).
* `cInverseLog_zero_pos`, `cInverseLog_one_neg` — base-case
  sign witnesses (Phase D non-vacuity for Phase C's negativity
  claim).

## What this file does NOT contain

* **Phase C — `∀ n, 1 ≤ n → cInverseLog n < 0`** (the headline
  `lem:441B` claim). Requires strong induction on `n` plus
  sign analysis of the (441d) auxiliary `d_{2i}` series.
  Cycle 238+ deliverable.
* The full collapsed recurrence
  `2·c_{2n} = − ∑_{i=1}^{n} (2/(2i+1))·c_{2(n-i)}`.
  The (441c) identity is shipped here as the multiplicative
  power-series identity; coefficient-extraction into the
  explicit recurrence is deferred to Phase C alongside the
  induction. (See Backup B1 in cycle 237 strategy §L.)
* Any reference to `LinearMultistepMethod` — by design, this is
  a stand-alone universal-PowerSeries cycle.
-/

namespace OpenMath.Chapter4.Section441B

/-- **The LHS series of Butcher's (441c) identity** —
`2 + (2/3) X² + (2/5) X⁴ + ⋯`. The coefficient of `X^(2i)` is
`2/(2i+1)`; the coefficient of `X^(2i+1)` is `0`.

This is the power-series for `log((1+z)/(1-z)) / z`, written
verbatim from Butcher §441 p. 376 (eq. 441c LHS). -/
noncomputable def cInverseLogSeries : PowerSeries ℝ :=
  PowerSeries.mk fun n => if Even n then 2 / (n + 1 : ℝ) else 0

/-- Closed-form coefficient: the `n`-th coefficient of
`cInverseLogSeries` is `2/(n+1)` if `n` is even, `0` otherwise. -/
@[simp] lemma coeff_cInverseLogSeries (n : ℕ) :
    (PowerSeries.coeff (R := ℝ) n) cInverseLogSeries =
      (if Even n then 2 / (n + 1 : ℝ) else 0) := by
  simp [cInverseLogSeries]

/-- **(441c) at `i = 0`** — the constant term of
`cInverseLogSeries` is `2`. Required for invoking
`PowerSeries.invOfUnit`. -/
lemma cInverseLogSeries_constantCoeff_eq_two :
    (PowerSeries.constantCoeff (R := ℝ)) cInverseLogSeries = 2 := by
  have h : (PowerSeries.coeff (R := ℝ) 0) cInverseLogSeries
      = (PowerSeries.constantCoeff (R := ℝ)) cInverseLogSeries := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff]
  rw [← h, coeff_cInverseLogSeries]
  simp

/-- The unit-witness for `2 : ℝ` used to invoke
`PowerSeries.invOfUnit`. -/
noncomputable def twoUnit : ℝˣ := Units.mk0 (2 : ℝ) (by norm_num)

@[simp] lemma twoUnit_val : (twoUnit : ℝ) = 2 := rfl

/-- **The universal series `c₀ + c₂ X² + c₄ X⁴ + ⋯`** — defined as
the formal-power-series inverse of `cInverseLogSeries` via
`PowerSeries.invOfUnit`. By Butcher's (441c) identity, this is
the formal expansion of `z / log((1+z)/(1-z))`. -/
noncomputable def cSeries : PowerSeries ℝ :=
  cInverseLogSeries.invOfUnit twoUnit

/-- **Butcher's (441c) identity** (left-hand form): the product
`cInverseLogSeries * cSeries` equals `1` in `PowerSeries ℝ`. -/
theorem cInverseLogSeries_mul_cSeries_eq_one :
    cInverseLogSeries * cSeries = 1 := by
  unfold cSeries
  exact PowerSeries.mul_invOfUnit cInverseLogSeries twoUnit
    (by rw [cInverseLogSeries_constantCoeff_eq_two]; rfl)

/-- **The textbook constants `c_{2n}`**, extracted as the
`(2n)`-th coefficient of `cSeries`. Following Butcher p. 376,
`cInverseLog n := c_{2n}`. -/
noncomputable def cInverseLog (n : ℕ) : ℝ :=
  (PowerSeries.coeff (R := ℝ) (2 * n)) cSeries

/-- **Base case (441c) at `z⁰`** — `c₀ = 1/2`. -/
theorem cInverseLog_zero_eq_half : cInverseLog 0 = 1 / 2 := by
  unfold cInverseLog
  have h : (PowerSeries.coeff (R := ℝ) 0) cSeries
      = (PowerSeries.constantCoeff (R := ℝ)) cSeries := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff]
  have h2 : (PowerSeries.constantCoeff (R := ℝ)) cSeries
      = ((twoUnit : ℝˣ)⁻¹ : ℝ) := by
    unfold cSeries
    exact PowerSeries.constantCoeff_invOfUnit cInverseLogSeries twoUnit
  rw [Nat.mul_zero, h, h2]
  -- goal: ((twoUnit : ℝˣ)⁻¹ : ℝ) = 1 / 2
  simp [twoUnit]

/-- **Base case (441c) at `z²`** — `c₂ = -1/6`.

Computed by extracting the `X²` coefficient from
`cInverseLogSeries * cSeries = 1`. The contributing terms are:
* `coeff 0 cIL * coeff 2 cS = 2 · cInverseLog 1`
* `coeff 1 cIL * coeff 1 cS = 0 · _ = 0`
* `coeff 2 cIL * coeff 0 cS = (2/3) · (1/2) = 1/3`

Together: `0 = 2·cInverseLog 1 + 1/3`, so `cInverseLog 1 = -1/6`. -/
theorem cInverseLog_one_eq_neg_one_sixth : cInverseLog 1 = -1 / 6 := by
  have hmul := cInverseLogSeries_mul_cSeries_eq_one
  have hcoeff : (PowerSeries.coeff (R := ℝ) 2) (cInverseLogSeries * cSeries)
      = (PowerSeries.coeff (R := ℝ) 2) (1 : PowerSeries ℝ) := by
    rw [hmul]
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_one] at hcoeff
  simp only [show (2 : ℕ) ≠ 0 by decide, if_false] at hcoeff
  -- Expand antidiagonal 2 = {(0,2), (1,1), (2,0)}
  rw [show (Finset.antidiagonal 2 : Finset (ℕ × ℕ)) =
      {(0, 2), (1, 1), (2, 0)} from by decide] at hcoeff
  rw [show ({(0, 2), (1, 1), (2, 0)} : Finset (ℕ × ℕ)) =
      insert (0, 2) (insert (1, 1) {(2, 0)}) from rfl] at hcoeff
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton] at hcoeff
  rw [coeff_cInverseLogSeries 0, coeff_cInverseLogSeries 1,
      coeff_cInverseLogSeries 2] at hcoeff
  simp only [show Even (0 : ℕ) from ⟨0, by decide⟩,
             show ¬ Even (1 : ℕ) from Nat.not_even_one,
             show Even (2 : ℕ) from ⟨1, by decide⟩,
             if_true, if_false] at hcoeff
  have h0 : (PowerSeries.coeff (R := ℝ) 0) cSeries = 1 / 2 := by
    have := cInverseLog_zero_eq_half
    unfold cInverseLog at this
    simpa using this
  rw [h0] at hcoeff
  -- hcoeff: 2/(↑0+1) * c₂ + (0 * c₁ + 2/(↑2+1) * (1/2)) = 0
  -- normalize numerical coefficients
  norm_num at hcoeff
  -- Now hcoeff: 2 * (coeff 2 cSeries) + 1/3 = 0  (or similar simplification)
  unfold cInverseLog
  have hex : (2 * 1 : ℕ) = 2 := by norm_num
  rw [hex]
  linarith

/-- **Non-vacuity P5 witness** — `c₀ > 0`. -/
theorem cInverseLog_zero_pos : 0 < cInverseLog 0 := by
  rw [cInverseLog_zero_eq_half]; norm_num

/-- **Non-vacuity P5 witness** — `c₂ < 0`. This is the base case
of Butcher's induction for Phase C, and the first non-trivial
instance of the negativity claim of `lem:441B`. -/
theorem cInverseLog_one_neg : cInverseLog 1 < 0 := by
  rw [cInverseLog_one_eq_neg_one_sixth]; norm_num

end OpenMath.Chapter4.Section441B
