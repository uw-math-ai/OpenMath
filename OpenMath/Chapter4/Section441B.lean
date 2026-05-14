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

/-! ## Phase C — strict negativity of `cInverseLog n` for `n ≥ 1`

Butcher §441 p. 376 proves the headline `lem:441B` claim by strong
induction on `n`. The induction step multiplies the (441c) identity
by the polynomial `2n+1 - (2n-1)z²`, producing an auxiliary series
`dSeries n` with the property `dSeries n * cSeries = 2n+1 - (2n-1)z²`
(eq. 441d). The `z^{2n}` coefficient of (441d) gives a recurrence
that forces `cInverseLog n < 0` given the inductive hypothesis on
smaller indices.

We define `dSeries n` algebraically as
`(C(2n+1) - C(2n-1)·X²) · cInverseLogSeries`. With this definition,
the (441d) identity becomes a one-line consequence of (441c) and
associativity. The closed-form coefficient computation
`coeff (2i) (dSeries n) = -8(n-i)/((2i+1)(2i-1))` for `i ≥ 1` is
then proved as a separate lemma.
-/

/-- **The auxiliary series `dSeries n`** of Butcher's (441d) identity.

Defined algebraically as the product
`(C(2n+1) - C(2n-1)·X²) · cInverseLogSeries`. By Butcher's calculation
(p. 376), the coefficient of `X^(2i)` for `1 ≤ i ≤ n` is
`-8(n-i)/((2i+1)(2i-1))` (in particular `d_{2n} = 0`), the constant
term is `2(2n+1)`, and odd coefficients vanish. -/
noncomputable def dSeries (n : ℕ) : PowerSeries ℝ :=
  (PowerSeries.C (R := ℝ) (2 * (n : ℝ) + 1) -
    PowerSeries.C (R := ℝ) (2 * (n : ℝ) - 1) * PowerSeries.X ^ 2)
    * cInverseLogSeries

/-- **(441d) identity** — `dSeries n * cSeries = 2n+1 - (2n-1)·X²`.

Immediate from the algebraic definition of `dSeries`, the (441c)
identity `cInverseLogSeries * cSeries = 1`, and `mul_assoc`. -/
theorem dSeries_mul_cSeries_eq (n : ℕ) :
    dSeries n * cSeries =
      PowerSeries.C (R := ℝ) (2 * (n : ℝ) + 1) -
      PowerSeries.C (R := ℝ) (2 * (n : ℝ) - 1) * PowerSeries.X ^ 2 := by
  unfold dSeries
  rw [mul_assoc, cInverseLogSeries_mul_cSeries_eq_one, mul_one]

/-- Closed-form: constant term of `dSeries n` is `2(2n+1)`. -/
@[simp] lemma coeff_dSeries_zero (n : ℕ) :
    (PowerSeries.coeff (R := ℝ) 0) (dSeries n) = 2 * (2 * (n : ℝ) + 1) := by
  unfold dSeries
  rw [PowerSeries.coeff_zero_eq_constantCoeff]
  simp [cInverseLogSeries_constantCoeff_eq_two]
  ring

/-- Closed-form: odd coefficients of `dSeries n` vanish. -/
lemma coeff_dSeries_odd (n k : ℕ) (h : ¬ Even k) :
    (PowerSeries.coeff (R := ℝ) k) (dSeries n) = 0 := by
  unfold dSeries
  rw [sub_mul, map_sub, PowerSeries.coeff_C_mul, mul_assoc,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  simp [coeff_cInverseLogSeries, h]
  intro hk
  have : ¬ Even (k - 2) := fun ⟨a, ha⟩ => h ⟨a + 1, by omega⟩
  simp [this]

/-- Closed-form: the `(2i)`-th coefficient of `dSeries n` for `i ≥ 1`
is `-8(n-i)/((2i+1)(2i-1))`. -/
lemma coeff_dSeries_two_mul (n i : ℕ) (hi : 1 ≤ i) :
    (PowerSeries.coeff (R := ℝ) (2 * i)) (dSeries n) =
      -8 * ((n : ℝ) - i) / ((2 * (i : ℝ) + 1) * (2 * (i : ℝ) - 1)) := by
  unfold dSeries
  rw [sub_mul, map_sub, PowerSeries.coeff_C_mul, mul_assoc,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  have h2i : 2 ≤ 2 * i := by omega
  have he1 : Even (2 * i) := ⟨i, by ring⟩
  have he2 : Even (2 * i - 2) := ⟨i - 1, by omega⟩
  rw [if_pos h2i, coeff_cInverseLogSeries, coeff_cInverseLogSeries,
      if_pos he1, if_pos he2]
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hi2 : (2 * (i : ℝ) - 1) ≠ 0 := by linarith
  have hi3 : (2 * (i : ℝ) + 1) ≠ 0 := by positivity
  have hcast1 : (((2 * i : ℕ) : ℝ) + 1) = 2 * (i : ℝ) + 1 := by push_cast; ring
  have hcast2 : (((2 * i - 2 : ℕ) : ℝ) + 1) = 2 * (i : ℝ) - 1 := by
    have : ((2 * i - 2 : ℕ) : ℝ) = 2 * (i : ℝ) - 2 := by
      have : (2 * i - 2 : ℕ) = 2 * (i - 1) := by omega
      rw [this]; push_cast; ring_nf
      have : (1 : ℝ) ≤ i := hi1
      have hi' : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
        rw [Nat.cast_sub hi]; push_cast; ring
      rw [hi']; ring
    linarith
  rw [hcast1, hcast2]
  field_simp
  ring

/-- **Sign of `d_{2i}`** for `1 ≤ i ≤ n - 1`: strictly negative.

This is the key intermediate inequality in Butcher's induction. -/
theorem coeff_dSeries_neg (n i : ℕ) (h₁ : 1 ≤ i) (h₂ : i ≤ n - 1) :
    (PowerSeries.coeff (R := ℝ) (2 * i)) (dSeries n) < 0 := by
  rw [coeff_dSeries_two_mul n i h₁]
  have hi_lt_n : i < n := by omega
  have hni : (i : ℝ) < (n : ℝ) := by exact_mod_cast hi_lt_n
  have hi1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast h₁
  have hnum : -8 * ((n : ℝ) - i) < 0 := by nlinarith
  have hden : (2 * (i : ℝ) + 1) * (2 * (i : ℝ) - 1) > 0 := by nlinarith
  exact div_neg_of_neg_of_pos hnum hden

/-- **Butcher Lemma 441B (headline)** — `cInverseLog n < 0` for all
`n ≥ 1`. The coefficients `c₂, c₄, c₆, …` in the expansion of
`z / log((1+z)/(1-z))` are all negative.

Proof: strong induction on `n`. Base case `n = 1` is
`cInverseLog_one_neg`. Inductive step extracts the `X^(2n)`
coefficient from the (441d) identity, rearranges to solve for
`cInverseLog n`, and uses the inductive hypothesis together with
`coeff_dSeries_neg` to conclude. -/
theorem cInverseLog_neg : ∀ n : ℕ, 1 ≤ n → cInverseLog n < 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn
    -- Split: n = 1 (base case) or n ≥ 2 (inductive step)
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · -- n < 2 and 1 ≤ n, so n = 1
      have : n = 1 := by omega
      rw [this]; exact cInverseLog_one_neg
    -- n ≥ 2: extract z^(2n) coefficient from (441d)
    have hKey : (PowerSeries.coeff (R := ℝ) (2 * n)) (dSeries n * cSeries) = 0 := by
      rw [dSeries_mul_cSeries_eq, map_sub, PowerSeries.coeff_C,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      have h0 : (2 * n : ℕ) ≠ 0 := by omega
      have h2 : (2 * n : ℕ) ≠ 2 := by omega
      simp [h0, h2]
    rw [PowerSeries.coeff_mul] at hKey
    -- Isolate (0, 2n): pulls out the 2(2n+1)·c_{2n} term
    have h0mem : ((0 : ℕ), 2 * n) ∈ Finset.antidiagonal (2 * n) := by
      rw [Finset.mem_antidiagonal]; simp
    rw [← Finset.add_sum_erase _ _ h0mem] at hKey
    -- The (0, 2n) term: coeff 0 dSeries · coeff (2n) cSeries
    -- = 2(2n+1) · cInverseLog n
    -- The remaining sum (over erased antidiag): need to show > 0
    -- Then linarith concludes cInverseLog n < 0
    simp only [coeff_dSeries_zero] at hKey
    -- hKey : 2*(2*↑n+1) * coeff (2n) cSeries + ∑erase = 0
    -- coeff (2n) cSeries = cInverseLog n
    change 2 * (2 * (n : ℝ) + 1) * cInverseLog n + _ = 0 at hKey
    -- Now show: ∑erase > 0. We split off (2, 2n-2) and bound the rest ≥ 0.
    have h2mem : ((2 : ℕ), 2 * n - 2) ∈
        (Finset.antidiagonal (2 * n)).erase (0, 2 * n) := by
      rw [Finset.mem_erase, Finset.mem_antidiagonal]
      refine ⟨?_, by omega⟩
      intro h; simp at h
    rw [← Finset.add_sum_erase _ _ h2mem] at hKey
    -- The (2, 2n-2) term: d_2 · c_{2(n-1)}
    -- = coeff_dSeries_two_mul n 1 _ · cInverseLog (n-1)
    have hd2_val : (PowerSeries.coeff (R := ℝ) 2) (dSeries n) =
        -8 * ((n : ℝ) - 1) / ((2 * (1 : ℝ) + 1) * (2 * (1 : ℝ) - 1)) := by
      have := coeff_dSeries_two_mul n 1 (by omega)
      simpa using this
    -- coeff (2*n-2) cSeries = cInverseLog (n-1)
    have hcLnm1 : (PowerSeries.coeff (R := ℝ) (2 * n - 2)) cSeries = cInverseLog (n - 1) := by
      have h_eq : 2 * n - 2 = 2 * (n - 1) := by omega
      rw [h_eq]; rfl
    -- Apply IH at n-1
    have hcLnm1_neg : cInverseLog (n - 1) < 0 := IH (n - 1) (by omega) (by omega)
    -- d_2 < 0 (sign of d_{2·1})
    have hd2_neg : (PowerSeries.coeff (R := ℝ) 2) (dSeries n) < 0 := by
      have := coeff_dSeries_neg n 1 (by omega) (by omega)
      simpa using this
    -- The (2, 2n-2) term is positive
    have h2term_pos : (PowerSeries.coeff (R := ℝ) ((2 : ℕ), 2 * n - 2).1) (dSeries n) *
        (PowerSeries.coeff (R := ℝ) ((2 : ℕ), 2 * n - 2).2) cSeries > 0 := by
      simp only
      rw [hcLnm1]
      exact mul_pos_of_neg_of_neg hd2_neg hcLnm1_neg
    -- Show ∑double-erase ≥ 0
    have h_rest_nonneg :
        (0 : ℝ) ≤ ∑ pq ∈ ((Finset.antidiagonal (2 * n)).erase (0, 2 * n)).erase (2, 2 * n - 2),
          (PowerSeries.coeff (R := ℝ) pq.1) (dSeries n) *
          (PowerSeries.coeff (R := ℝ) pq.2) cSeries := by
      apply Finset.sum_nonneg
      rintro ⟨p, q⟩ hpq
      rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_antidiagonal] at hpq
      obtain ⟨hne2, hne0, hpq_eq⟩ := hpq
      -- Case split on parity of p
      by_cases hp_even : Even p
      · -- p even: p = 2*i
        obtain ⟨i, hi⟩ := hp_even
        -- p = i + i = 2*i (using Mathlib's definition Even n ↔ ∃ r, n = r + r)
        have hp_eq : p = 2 * i := by omega
        -- i ranges: i = 0 ⇒ p = 0, q = 2n, but excluded (hne0)
        --           i ≥ 1 ⇒ ...
        rcases Nat.eq_zero_or_pos i with hi0 | hi1
        · -- i = 0 ⇒ p = 0 ⇒ pq = (0, 2n), contradicts hne0
          exfalso; apply hne0
          ext <;> simp_all
        -- i ≥ 1
        -- Subcase: i = 1 ⇒ p = 2 ⇒ pq = (2, 2n-2), contradicts hne2
        rcases (Nat.lt_or_ge 1 i) with hi_gt1 | hi_le1
        · -- i ≥ 2: 1 ≤ i and i ≤ n? need to check
          -- p = 2i, q = 2n - 2i = 2(n-i)
          -- Need: coeff (2i) dSeries · coeff (2(n-i)) cSeries ≥ 0
          have hpq_eq2 : 2 * i + q = 2 * n := by rw [← hp_eq]; exact hpq_eq
          have hi_le_n : i ≤ n := by omega
          rcases eq_or_lt_of_le hi_le_n with hi_eq_n | hi_lt_n
          · -- i = n ⇒ p = 2n, q = 0
            -- coeff (2n) dSeries = d_{2n} = 0 (by coeff_dSeries_two_mul n n)
            have : (PowerSeries.coeff (R := ℝ) p) (dSeries n) = 0 := by
              rw [hp_eq, hi_eq_n]
              rw [coeff_dSeries_two_mul n n (by omega)]
              ring
            rw [this]; simp
          · -- 1 ≤ i ≤ n - 1
            have hi_le_nm1 : i ≤ n - 1 := by omega
            -- coeff (2i) dSeries = d_{2i} < 0
            have hdi_neg : (PowerSeries.coeff (R := ℝ) p) (dSeries n) < 0 := by
              rw [hp_eq]
              exact coeff_dSeries_neg n i (by omega) hi_le_nm1
            -- q = 2(n-i), 1 ≤ n - i ≤ n - 1 (so IH applies)
            have hq_eq : q = 2 * (n - i) := by omega
            have hni_pos : 1 ≤ n - i := by omega
            have hni_lt : n - i < n := by omega
            have hcL_neg : (PowerSeries.coeff (R := ℝ) q) cSeries = cInverseLog (n - i) := by
              rw [hq_eq]; rfl
            have hcLni_neg : cInverseLog (n - i) < 0 := IH (n - i) hni_lt hni_pos
            rw [hcL_neg]
            exact le_of_lt (mul_pos_of_neg_of_neg hdi_neg hcLni_neg)
        · -- i ≤ 1, combined with i ≥ 1 ⇒ i = 1 ⇒ p = 2 ⇒ contradicts hne2
          have : i = 1 := by omega
          exfalso; apply hne2
          subst this
          have hq : q = 2 * n - 2 := by omega
          ext
          · simp [hp_eq]
          · simp [hq]
      · -- p odd: coeff p dSeries = 0
        have : (PowerSeries.coeff (R := ℝ) p) (dSeries n) = 0 :=
          coeff_dSeries_odd n p hp_even
        rw [this]; simp
    -- Combine: hKey says (2·(2n+1)·cIL n) + ((2, 2n-2) term) + (sum) = 0
    -- (2, 2n-2) term > 0 and sum ≥ 0, so 2·(2n+1)·cIL n ≤ -((2, 2n-2) term) < 0
    have h2n_pos : (0 : ℝ) < 2 * (2 * (n : ℝ) + 1) := by positivity
    -- From hKey: 2(2n+1) · cIL n + (positive) + (≥0) = 0
    -- So 2(2n+1) · cIL n < 0, hence cIL n < 0
    nlinarith [hKey, h2term_pos, h_rest_nonneg, h2n_pos]

end OpenMath.Chapter4.Section441B
