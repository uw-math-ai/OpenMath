import OpenMath.MultistepMethods

/-!
# BDF Methods and A(α)-Stability (Section 4.5)

## Backward Differentiation Formulas

The k-step BDF method approximates the derivative via backward differences:
  ∑_{j=1}^{k} (1/j) ∇^j y_{n+k} = h f_{n+k}

yielding an implicit multistep method where only β_k ≠ 0.

## A(α)-Stability (Iserles, Definition 4.12)

A method is **A(α)-stable** if its stability region contains the sector
  S_α = {z ∈ ℂ : z.re ≤ -‖z‖ · cos(α)}

Key facts:
- A-stability equals A(π/2)-stability (since cos(π/2) = 0)
- BDF1 (= backward Euler) and BDF2 are A-stable
- BDF3–6 are NOT A-stable (Dahlquist's second barrier)
- BDF5 and BDF6 are defined here with order proofs

Reference: Iserles, *A First Course in the Numerical Analysis of
Differential Equations*, Sections 3.3 and 4.5.
-/

open Finset Real

/-! ## A(α)-Stability Definition -/

namespace LMM

variable {s : ℕ}

/-- The **sector** S_α = {z ∈ ℂ : z.re ≤ -‖z‖ · cos(α)}.
  For α = π/2, cos(π/2) = 0, so the sector is the closed left half-plane {z : z.re ≤ 0}.
  For 0 < α < π/2, cos(α) > 0, so the sector is a proper wedge. -/
def InSector (z : ℂ) (α : ℝ) : Prop :=
  z.re ≤ -(‖z‖ * Real.cos α)

/-- A method is **A(α)-stable** if its stability region contains the sector S_α.
  Reference: Iserles, Definition 4.12. -/
def IsAAlphaStable (m : LMM s) (α : ℝ) : Prop :=
  ∀ z : ℂ, InSector z α → m.InStabilityRegion z

/-- A-stability equals A(π/2)-stability, since cos(π/2) = 0. -/
theorem isAStable_iff_aAlpha_pi_div_two {m : LMM s} :
    m.IsAStable ↔ m.IsAAlphaStable (π / 2) := by
  simp only [IsAStable, IsAAlphaStable, InSector, Real.cos_pi_div_two, mul_zero, neg_zero]

/-- A(α)-stability is monotone: A(α)-stable implies A(α')-stable for α' ≤ α
  within [0, π/2], since the sector S_{α'} ⊆ S_α when α' ≤ α (larger α = wider sector). -/
theorem IsAAlphaStable.mono {m : LMM s} {α α' : ℝ}
    (h : m.IsAAlphaStable α) (hle : α' ≤ α)
    (hα' : 0 ≤ α') (hα : α ≤ π / 2) :
    m.IsAAlphaStable α' := by
  intro z hz
  apply h
  unfold InSector at hz ⊢
  -- cos is antitone on [0, π/2], so α' ≤ α implies cos α ≤ cos α'
  have hα_pi : α ∈ Set.Icc 0 π := ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hα'_pi : α' ∈ Set.Icc 0 π := ⟨hα', by linarith [Real.pi_pos]⟩
  have hcos : Real.cos α ≤ Real.cos α' :=
    Real.strictAntiOn_cos.antitoneOn hα'_pi hα_pi hle
  nlinarith [norm_nonneg z]

/-- A-stability implies A(α)-stability for any α ∈ [0, π/2]. -/
theorem IsAStable.toAAlphaStable {m : LMM s} (ha : m.IsAStable)
    {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ π / 2) :
    m.IsAAlphaStable α :=
  (isAStable_iff_aAlpha_pi_div_two.mp ha).mono hα2 hα (le_refl _)

end LMM

/-! ## BDF1 = Backward Euler

The 1-step BDF method is exactly backward Euler: y_{n+1} - y_n = hf_{n+1}.
Its A-stability and A(α)-stability follow from `backwardEuler_aStable`. -/

/-- Backward Euler is A(α)-stable for any α ∈ [0, π/2]. -/
theorem backwardEuler_aAlphaStable {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ π / 2) :
    backwardEuler.IsAAlphaStable α :=
  backwardEuler_aStable.toAAlphaStable hα hα2

/-! ## BDF2: A-stable

BDF2 is A-stable (the last A-stable BDF): all roots of the stability polynomial
ρ(ξ) − zσ(ξ) = (1 − 2z/3)ξ² − (4/3)ξ + 1/3 lie in the closed unit disk when Re(z) ≤ 0.

**Proof outline.** By contraposition: if |ξ| > 1, show Re(z) > 0.
From the stability polynomial, 2zξ² = 3ξ² − 4ξ + 1. Multiply by conj(ξ²) and take Re:
  2 Re(z) · |ξ|⁴ = 2(Re(ξ) − |ξ|²)² + |ξ|²(|ξ|² − 1) > 0.

Reference: Iserles, Section 4.5. -/

/-- **BDF2 is A-stable**: all roots of the stability polynomial lie in the closed unit disk
  when Re(z) ≤ 0.

  Proof: By contrapositive. If |ξ| > 1, solve for z from π(ξ,z) = 0:
    z = 3(ξ-1)(ξ-1/3)/(2ξ²)
  Setting w = 1/ξ with |w| < 1, this becomes z = (3/2)(1-w)(1-w/3).
  Write w = a+bi with a²+b² < 1. Then
    Re(z) = (3-4a+a²-b²)/2 = (2(a-1)² + (1-a²-b²))/2 > 0
  since a²+b² < 1 and (a-1)² ≥ 0. This contradicts Re(z) ≤ 0.

  Reference: Iserles, Theorem 3.5. -/
theorem bdf2_aStable : bdf2.IsAStable := by
  intro z hz ξ hξ
  simp only [LMM.stabilityPoly, LMM.rhoC, LMM.sigmaC, bdf2] at hξ
  simp [Fin.sum_univ_three] at hξ
  -- hξ : equation involving z and ξ with rational coefficients
  -- Goal : ‖ξ‖ ≤ 1
  by_contra hgt
  push_neg at hgt -- hgt : 1 < ‖ξ‖
  -- Decompose ξ into real and imaginary parts
  set a := ξ.re with ha_def
  set b := ξ.im with hb_def
  have hξ_eq : ξ = ⟨a, b⟩ := (Complex.eta ξ).symm
  -- |ξ|² > 1
  have hr2 : 1 < a ^ 2 + b ^ 2 := by
    have h1 : 1 < ‖ξ‖ ^ 2 := by
      nlinarith [hgt, norm_nonneg ξ]
    have hnorm : ‖ξ‖ ^ 2 = a ^ 2 + b ^ 2 := by
      calc
        ‖ξ‖ ^ 2 = Complex.normSq ξ := by
          symm
          exact Complex.normSq_eq_norm_sq ξ
        _ = a ^ 2 + b ^ 2 := by
          rw [Complex.normSq_apply, hξ_eq]
          ring_nf
    nlinarith [h1]
  -- ξ ≠ 0
  have hξ_ne : ξ ≠ 0 := by
    intro heq
    rw [heq, norm_zero] at hgt
    linarith
  -- Compute ξ² parts
  have hp2 : (⟨a, b⟩ : ℂ) ^ 2 = ⟨a * a - b * b, a * b + b * a⟩ := by rw [sq]; rfl
  -- Extract real and imaginary parts of hξ
  rw [hξ_eq] at hξ
  rw [hp2] at hξ
  -- Split the complex equation into Re and Im parts
  obtain ⟨hξ_re, hξ_im⟩ := Complex.ext_iff.mp hξ
  simp only [Complex.zero_re, Complex.zero_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_im, Complex.one_re, Complex.one_im] at hξ_re hξ_im
  norm_num at hξ_re hξ_im
  -- hξ_re/hξ_im are now real equations in a, b, z.re, z.im
  -- Multiply hξ_re by (a²-b²) and hξ_im by 2ab, add to eliminate z.im:
  -- This yields: z.re * (2/3) * ((a²-b²)² + (2ab)²) = [RHS]
  -- Note (a²-b²)² + (2ab)² = (a²+b²)² = r⁴
  set r2 := a ^ 2 + b ^ 2 with hr2_def
  -- Key: 2 * z.re * r2 ^ 2 = 3 * r2 ^ 2 - 4 * r2 * a + 2 * a ^ 2 - r2
  -- This is derived from the Re/Im equations above.
  have hzre : 2 * z.re * r2 ^ 2 = 3 * r2 ^ 2 - 4 * r2 * a + 2 * a ^ 2 - r2 := by
    have h1 : (a * a - b * b) ^ 2 + (a * b + b * a) ^ 2 = r2 ^ 2 := by
      rw [hr2_def]; ring
    ring_nf at hξ_re hξ_im ⊢
    have hcomb :
        z.re * a ^ 2 * b ^ 2 * (-4 / 3) + z.re * a ^ 4 * (-2 / 3) +
            z.re * b ^ 4 * (-2 / 3) + a * b ^ 2 * (-4 / 3) + a ^ 2 * (1 / 3) +
            a ^ 2 * b ^ 2 * 2 + a ^ 3 * (-4 / 3) + a ^ 4 + b ^ 2 * (-1 / 3) + b ^ 4 = 0 := by
      linear_combination (a * a - b * b) * hξ_re + (a * b + b * a) * hξ_im
    -- From hξ_re and hξ_im, eliminate z.im:
    -- hξ_re * (a*a-b*b) + hξ_im * (a*b+b*a) eliminates z.im terms
    nlinarith [hcomb, h1]
  -- Now show z.re > 0
  -- Key algebraic identity: 3r⁴ - 4r²a + 2a² - r² = 2(r²-a)² + r²(r²-1)
  have hpos : 0 < 3 * r2 ^ 2 - 4 * r2 * a + 2 * a ^ 2 - r2 := by
    have h1 : 3 * r2 ^ 2 - 4 * r2 * a + 2 * a ^ 2 - r2 =
      2 * (r2 - a) ^ 2 + r2 * (r2 - 1) := by ring
    rw [h1]
    have hmul : 0 < r2 * (r2 - 1) := by
      nlinarith
    have hsq : 0 ≤ 2 * (r2 - a) ^ 2 := by positivity
    linarith
  have hr2_pos : (0 : ℝ) < r2 ^ 2 := by
    nlinarith
  -- From hzre and hpos: z.re > 0
  have : 0 < z.re := by nlinarith
  linarith -- contradicts hz : z.re ≤ 0

/-- BDF2 is A(α)-stable for any α ∈ [0, π/2]. -/
theorem bdf2_aAlphaStable {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ π / 2) :
    bdf2.IsAAlphaStable α :=
  bdf2_aStable.toAAlphaStable hα hα2

/-! ## BDF3 and BDF4: NOT A-stable

These follow immediately from Dahlquist's second barrier: a zero-stable,
A-stable LMM has order at most 2. Since BDF3 has order 3 and BDF4 has order 4,
and both are zero-stable, neither can be A-stable.

Reference: Iserles, Theorem 3.4. -/

/-- **BDF3 is NOT A-stable**: order 3 > 2 contradicts Dahlquist's second barrier. -/
theorem bdf3_not_aStable : ¬bdf3.IsAStable := by
  intro ha
  have hbarrier : 3 ≤ 2 := LMM.dahlquist_second_barrier bdf3 3 bdf3_order_three ha bdf3_zeroStable
    (by
      intro ζ hζ hunit
      simp only [LMM.rhoC, bdf3] at hζ
      simp [Fin.sum_univ_four] at hζ
      have h11 : (ζ - 1) * (11 * ζ ^ 2 - 7 * ζ + 2) = 0 := by
        linear_combination 11 * hζ
      rcases mul_eq_zero.mp h11 with h0 | h1
      · linear_combination h0
      · exfalso
        have h_eq : (11 : ℂ) * ζ ^ 2 = 7 * ζ - 2 := by
          linear_combination h1
        have h_norm_eq : 11 * ‖ζ‖ ^ 2 = ‖7 * ζ - 2‖ := by
          have := congrArg norm h_eq
          rwa [norm_mul, norm_pow, show ‖(11 : ℂ)‖ = 11 by norm_num] at this
        have h_tri : ‖(7 : ℂ) * ζ - 2‖ ≤ 7 * ‖ζ‖ + 2 := by
          calc
            ‖(7 : ℂ) * ζ - 2‖ ≤ ‖(7 : ℂ) * ζ‖ + ‖(2 : ℂ)‖ := norm_sub_le _ _
            _ = 7 * ‖ζ‖ + 2 := by rw [norm_mul]; norm_num
        rw [hunit] at h_norm_eq h_tri
        linarith)
  norm_num at hbarrier

/-- **BDF4 is NOT A-stable**: order 4 > 2 contradicts Dahlquist's second barrier. -/
theorem bdf4_not_aStable : ¬bdf4.IsAStable := by
  intro ha
  have hbarrier : 4 ≤ 2 := LMM.dahlquist_second_barrier bdf4 4 bdf4_order_four ha bdf4_zeroStable
    (by
      intro ζ hζ hunit
      simp only [LMM.rhoC, bdf4] at hζ
      simp [Fin.sum_univ_five] at hζ
      have h25 : (ζ - 1) * (25 * ζ ^ 3 - 23 * ζ ^ 2 + 13 * ζ - 3) = 0 := by
        linear_combination 25 * hζ
      rcases mul_eq_zero.mp h25 with h0 | h1
      · linear_combination h0
      · exfalso
        have hζ_ne : ζ ≠ 0 := by
          intro h
          rw [h] at hunit
          simp at hunit
        have h_nsq : Complex.normSq ζ = 1 := by
          rw [Complex.normSq_eq_norm_sq, hunit]
          norm_num
        have h_mc : ζ * starRingEnd ℂ ζ = 1 := by
          rw [Complex.mul_conj, ← Complex.ofReal_one, Complex.ofReal_inj]
          exact h_nsq
        have h_conj_eq : starRingEnd ℂ ζ = ζ⁻¹ := eq_inv_of_mul_eq_one_right h_mc
        have h_rev : -3 * ζ ^ 3 + 13 * ζ ^ 2 - 23 * ζ + 25 = 0 := by
          have h := congr_arg (starRingEnd ℂ) h1
          simp only [map_sub, map_mul, map_pow, map_add, map_ofNat, map_zero] at h
          rw [h_conj_eq] at h
          field_simp at h
          linear_combination h
        have h_quad : 32 * ζ ^ 2 - 67 * ζ + 77 = 0 := by
          linear_combination 3 / 8 * h1 + 25 / 8 * h_rev
        have h_quad_rev : 77 * ζ ^ 2 - 67 * ζ + 32 = 0 := by
          have h := congr_arg (starRingEnd ℂ) h_quad
          simp only [map_sub, map_mul, map_pow, map_add, map_ofNat, map_zero] at h
          rw [h_conj_eq] at h
          field_simp at h
          linear_combination h
        have h_sq : ζ ^ 2 = 1 := by
          have : -45 * ζ ^ 2 + 45 = 0 := by
            linear_combination h_quad - h_quad_rev
          linear_combination -this / 45
        have hζ_val : ζ = 13 / 19 := by
          have : 25 * ζ * ζ ^ 2 - 23 * ζ ^ 2 + 13 * ζ - 3 = 0 := by
            ring_nf
            linear_combination h1
          rw [h_sq] at this
          linear_combination this / 38
        rw [hζ_val] at h_sq
        norm_num at h_sq)
  norm_num at hbarrier

/-! ## Higher BDF Methods

`bdf5`, `bdf6`, their consistency/order facts, and zero-stability proofs are
defined in `OpenMath.MultistepMethods`. This file focuses on the A-stability
story and reuses those imported definitions. -/
