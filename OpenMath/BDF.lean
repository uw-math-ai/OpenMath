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
    have h1 : 1 < ‖ξ‖ ^ 2 := one_lt_sq_iff_one_lt_abs.mpr hgt
    rwa [Complex.sq_norm, Complex.normSq_apply, hξ_eq,
         show (⟨a, b⟩ : ℂ).re * (⟨a, b⟩ : ℂ).re +
              (⟨a, b⟩ : ℂ).im * (⟨a, b⟩ : ℂ).im = a ^ 2 + b ^ 2 from by ring] at h1
  -- ξ ≠ 0
  have hξ_ne : ξ ≠ 0 := by intro heq; rw [heq] at hgt; simp at hgt
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
    Complex.ofReal_re, Complex.ofReal_im, Complex.mk_re, Complex.mk_im,
    Complex.one_re, Complex.one_im] at hξ_re hξ_im
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
    -- From hξ_re and hξ_im, eliminate z.im:
    -- hξ_re * (a*a-b*b) + hξ_im * (a*b+b*a) eliminates z.im terms
    nlinarith [hξ_re, hξ_im, sq_nonneg a, sq_nonneg b,
               mul_comm a b, sq_nonneg (a * a - b * b),
               sq_nonneg (a * b + b * a)]
  -- Now show z.re > 0
  -- Key algebraic identity: 3r⁴ - 4r²a + 2a² - r² = 2(r²-a)² + r²(r²-1)
  have hpos : 0 < 3 * r2 ^ 2 - 4 * r2 * a + 2 * a ^ 2 - r2 := by
    have h1 : 3 * r2 ^ 2 - 4 * r2 * a + 2 * a ^ 2 - r2 =
      2 * (r2 - a) ^ 2 + r2 * (r2 - 1) := by ring
    rw [h1]
    have : 0 < r2 * (r2 - 1) := by positivity
    have : 0 ≤ 2 * (r2 - a) ^ 2 := by positivity
    linarith
  have hr2_pos : (0 : ℝ) < r2 ^ 2 := by positivity
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
  have := LMM.dahlquist_second_barrier bdf3 3 bdf3_order_three ha bdf3_zeroStable
  omega

/-- **BDF4 is NOT A-stable**: order 4 > 2 contradicts Dahlquist's second barrier. -/
theorem bdf4_not_aStable : ¬bdf4.IsAStable := by
  intro ha
  have := LMM.dahlquist_second_barrier bdf4 4 bdf4_order_four ha bdf4_zeroStable
  omega

/-! ## BDF5 (Backward Differentiation Formula, 5-step)

The BDF5 method:
  137y_{n+5} - 300y_{n+4} + 300y_{n+3} - 200y_{n+2} + 75y_{n+1} - 12y_n = 60h·f_{n+5}

After normalization (α₅ = 1):
  α = [-12/137, 75/137, -200/137, 300/137, -300/137, 1]
  β = [0, 0, 0, 0, 0, 60/137]

Order 5, implicit, NOT A-stable.

Reference: Iserles, Section 4.5, Table 4.1. -/

/-- **BDF5** (Backward Differentiation Formula, 5-step). -/
noncomputable def bdf5 : LMM 5 where
  α := ![-12/137, 75/137, -200/137, 300/137, -300/137, 1]
  β := ![0, 0, 0, 0, 0, 60/137]
  normalized := by simp [Fin.last]

/-- BDF5 is consistent: ρ(1) = 0 and ρ'(1) = σ(1). -/
theorem bdf5_consistent : bdf5.IsConsistent :=
  ⟨by simp [LMM.rho, bdf5, Fin.sum_univ_succ]; norm_num,
   by simp [LMM.sigma, bdf5, Fin.sum_univ_succ]; norm_num⟩

/-- BDF5 has order 5. -/
theorem bdf5_order_five : bdf5.HasOrder 5 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, bdf5, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.orderCondVal, bdf5, Fin.sum_univ_succ]; norm_num

/-- BDF5 is implicit (β₅ = 60/137 ≠ 0). -/
theorem bdf5_implicit : bdf5.IsImplicit := by
  simp [LMM.IsImplicit, bdf5, Fin.last]

/-- **BDF5 is NOT A-stable** (conditional on zero-stability):
  order 5 > 2 contradicts Dahlquist's second barrier. -/
theorem bdf5_not_aStable (hzs : bdf5.IsZeroStable) : ¬bdf5.IsAStable := by
  intro ha
  have := LMM.dahlquist_second_barrier bdf5 5 bdf5_order_five ha hzs
  omega

/-! ## BDF6 (Backward Differentiation Formula, 6-step)

The BDF6 method:
  147y_{n+6} - 360y_{n+5} + 450y_{n+4} - 400y_{n+3} + 225y_{n+2} - 72y_{n+1} + 10y_n = 60h·f_{n+6}

After normalization (α₆ = 1):
  α = [10/147, -72/147, 225/147, -400/147, 450/147, -360/147, 1]
  β = [0, 0, 0, 0, 0, 0, 60/147]

Order 6, implicit, NOT A-stable.

Reference: Iserles, Section 4.5, Table 4.1. -/

/-- **BDF6** (Backward Differentiation Formula, 6-step). -/
noncomputable def bdf6 : LMM 6 where
  α := ![10/147, -72/147, 225/147, -400/147, 450/147, -360/147, 1]
  β := ![0, 0, 0, 0, 0, 0, 60/147]
  normalized := by simp [Fin.last]

/-- BDF6 is consistent: ρ(1) = 0 and ρ'(1) = σ(1). -/
theorem bdf6_consistent : bdf6.IsConsistent :=
  ⟨by simp [LMM.rho, bdf6, Fin.sum_univ_succ]; norm_num,
   by simp [LMM.sigma, bdf6, Fin.sum_univ_succ]; norm_num⟩

/-- BDF6 has order 6. -/
theorem bdf6_order_six : bdf6.HasOrder 6 := by
  refine ⟨?_, ?_⟩
  · intro q hq
    interval_cases q <;>
      simp [LMM.orderCondVal, bdf6, Fin.sum_univ_succ] <;> norm_num
  · simp [LMM.orderCondVal, bdf6, Fin.sum_univ_succ]; norm_num

/-- BDF6 is implicit (β₆ = 60/147 ≠ 0). -/
theorem bdf6_implicit : bdf6.IsImplicit := by
  simp [LMM.IsImplicit, bdf6, Fin.last]

/-- **BDF6 is NOT A-stable** (conditional on zero-stability):
  order 6 > 2 contradicts Dahlquist's second barrier. -/
theorem bdf6_not_aStable (hzs : bdf6.IsZeroStable) : ¬bdf6.IsAStable := by
  intro ha
  have := LMM.dahlquist_second_barrier bdf6 6 bdf6_order_six ha hzs
  omega
