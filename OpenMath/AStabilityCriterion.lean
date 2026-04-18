import OpenMath.Basic
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Theorem 351B: A-Stability Criterion for Rational Stability Functions

This file formalizes the E-function

`E(y) = |D(iy)|² - |N(iy)|²`

attached to a rational stability function `R(z) = N(z) / D(z)`.

## Main results

**Necessity**: If D has no zeros on the closed left half-plane and `|R(z)| ≤ 1`
for `Re z ≤ 0`, then `E(y) ≥ 0` for all `y`.

**Sufficiency**: If D has no zeros on the closed left half-plane, `E(y) ≥ 0`
for all `y`, and `deg N ≤ deg D`, then `|R(z)| ≤ 1` for `Re z ≤ 0`.
This uses the Phragmén–Lindelöf principle on the right half-plane.
-/

open Complex Polynomial Filter Asymptotics

noncomputable section

/-- The `E`-function from Theorem 351B:
`E(y) = |D(iy)|² - |N(iy)|²`, where `R(z) = N(z) / D(z)`. -/
def ePoly (N D : Polynomial ℂ) (y : ℝ) : ℝ :=
  ‖D.eval ((y : ℂ) * I)‖ ^ 2 - ‖N.eval ((y : ℂ) * I)‖ ^ 2

/-- A convenient abbreviation for evaluation on the imaginary axis. -/
def evalImag (P : Polynomial ℂ) (y : ℝ) : ℂ :=
  P.eval ((y : ℂ) * I)

@[simp] theorem evalImag_def (P : Polynomial ℂ) (y : ℝ) :
    evalImag P y = P.eval ((y : ℂ) * I) := rfl

@[simp] theorem ePoly_eq (N D : Polynomial ℂ) (y : ℝ) :
    ePoly N D y = ‖evalImag D y‖ ^ 2 - ‖evalImag N y‖ ^ 2 := rfl

/-- If every pole of `N/D` lies in the open right half-plane, then the denominator
is nonzero on the imaginary axis. -/
theorem evalImag_ne_zero_of_poles_rhp
    (D : Polynomial ℂ)
    (hPoles : ∀ z : ℂ, D.eval z = 0 → 0 < z.re) :
    ∀ y : ℝ, evalImag D y ≠ 0 := by
  intro y hDy
  have hRe : (((y : ℂ) * I).re) = 0 := by simp [Complex.mul_re]
  have hpos := hPoles ((y : ℂ) * I) hDy
  rw [hRe] at hpos
  linarith

/-- On the imaginary axis, the pointwise bound `|N/D| ≤ 1` implies `E(y) ≥ 0`. -/
theorem ePoly_nonneg_of_imag_axis_bound
    (N D : Polynomial ℂ) (y : ℝ)
    (hDy : evalImag D y ≠ 0)
    (hbound : ‖evalImag N y / evalImag D y‖ ≤ 1) :
    0 ≤ ePoly N D y := by
  rw [ePoly_eq]
  have hDpos : 0 < ‖evalImag D y‖ := norm_pos_iff.mpr hDy
  rw [norm_div, div_le_one hDpos] at hbound
  have hsquare : ‖evalImag N y‖ ^ 2 ≤ ‖evalImag D y‖ ^ 2 := by
    nlinarith [hbound, norm_nonneg (evalImag N y), norm_nonneg (evalImag D y)]
  linarith

/-- Necessity direction of Theorem 351B, under an explicit nonvanishing hypothesis
on the imaginary axis. -/
theorem ePoly_nonneg_of_aStable
    (N D : Polynomial ℂ)
    (hAstab : ∀ z : ℂ, z.re ≤ 0 → D.eval z ≠ 0 → ‖N.eval z / D.eval z‖ ≤ 1)
    (hImag : ∀ y : ℝ, evalImag D y ≠ 0) :
    ∀ y : ℝ, 0 ≤ ePoly N D y := by
  intro y
  have hRe : (((y : ℂ) * I).re) ≤ 0 := by simp [Complex.mul_re]
  exact ePoly_nonneg_of_imag_axis_bound N D y (hImag y) (hAstab ((y : ℂ) * I) hRe (hImag y))

/-- Necessity direction of Theorem 351B, using the pole-location hypothesis to
discharge the imaginary-axis nonvanishing condition. -/
theorem ePoly_nonneg_of_aStable_and_poles_rhp
    (N D : Polynomial ℂ)
    (hAstab : ∀ z : ℂ, z.re ≤ 0 → D.eval z ≠ 0 → ‖N.eval z / D.eval z‖ ≤ 1)
    (hPoles : ∀ z : ℂ, D.eval z = 0 → 0 < z.re) :
    ∀ y : ℝ, 0 ≤ ePoly N D y := by
  exact ePoly_nonneg_of_aStable N D hAstab (evalImag_ne_zero_of_poles_rhp D hPoles)

/-! ## Sufficiency direction -/

/-- Converse of `ePoly_nonneg_of_imag_axis_bound`: if `E(y) ≥ 0` and `D(iy) ≠ 0`,
then `|N(iy)/D(iy)| ≤ 1`. -/
theorem norm_div_le_one_of_ePoly_nonneg
    (N D : Polynomial ℂ) (y : ℝ)
    (hDy : evalImag D y ≠ 0)
    (hE : 0 ≤ ePoly N D y) :
    ‖evalImag N y / evalImag D y‖ ≤ 1 := by
  rw [ePoly_eq] at hE
  have hDpos : 0 < ‖evalImag D y‖ := norm_pos_iff.mpr hDy
  rw [norm_div, div_le_one hDpos]
  nlinarith [sq_nonneg (‖evalImag N y‖ - ‖evalImag D y‖),
             norm_nonneg (evalImag N y), norm_nonneg (evalImag D y),
             sq_abs (‖evalImag N y‖), sq_abs (‖evalImag D y‖)]

/-- The rational function `z ↦ N(-z)/D(-z)` is `DiffContOnCl` on the open right
half-plane when `D` has no zeros on `{Re z ≤ 0}`. -/
theorem diffContOnCl_neg_ratFunc_rhp
    (N D : Polynomial ℂ)
    (hNonvanish : ∀ z : ℂ, z.re ≤ 0 → D.eval z ≠ 0) :
    DiffContOnCl ℂ (fun z => N.eval (-z) / D.eval (-z)) {z | 0 < z.re} := by
  apply DifferentiableOn.diffContOnCl
  apply DifferentiableOn.div
  · exact (N.differentiable.comp differentiable_neg).differentiableOn
  · exact (D.differentiable.comp differentiable_neg).differentiableOn
  · intro z hz
    have hre : 0 ≤ z.re := closure_lt_subset_le continuous_const Complex.continuous_re hz
    exact hNonvanish (-z) (by rw [Complex.neg_re]; linarith)

-- Helper abbreviation for the rational function z ↦ N(-z)/D(-z)
private def g (N D : Polynomial ℂ) (z : ℂ) : ℂ :=
  N.eval (-z) / D.eval (-z)

-- Numerator bound: ‖N(-z)‖ ≤ C₁ · ‖z‖^(deg D) eventually on cobounded ⊓ RHP
set_option maxHeartbeats 400000 in
private lemma g_numerator_bound (N D : Polynomial ℂ)
    (hDegree : N.natDegree ≤ D.natDegree) :
    ∃ C1 : ℝ, ∀ᶠ z in (Bornology.cobounded ℂ) ⊓ (𝓟 {z : ℂ | 0 < z.re}),
      ‖N.eval (-z)‖ ≤ C1 * ‖z‖ ^ D.natDegree := by
  have hN_bound : ∃ C1 : ℝ, ∀ z : ℂ, ‖N.eval (-z)‖ ≤ C1 * (1 + ‖z‖) ^ D.natDegree := by
    use ∑ i ∈ N.support, ‖N.coeff i‖;
    intro z;
    rw [ eval_eq_sum, sum_def ];
    refine' le_trans ( norm_sum_le _ _ ) _;
    norm_num [ Finset.sum_mul _ _ _ ];
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ( by exact le_trans ( pow_le_pow_left₀ ( by positivity ) ( by linarith [ norm_nonneg z ] ) _ ) ( pow_le_pow_right₀ ( by linarith [ norm_nonneg z ] ) ( by linarith [ le_natDegree_of_mem_supp _ hi ] ) ) ) ( by positivity );
  obtain ⟨C1, hC1⟩ := hN_bound;
  use C1 * 2 ^ D.natDegree;
  have h_bound : ∀ᶠ z in (Bornology.cobounded ℂ) ⊓ (𝓟 {z : ℂ | 0 < z.re}), (1 + ‖z‖) ^ D.natDegree ≤ 2 ^ D.natDegree * ‖z‖ ^ D.natDegree := by
    rw [ eventually_inf_principal ];
    rw [ eventually_iff_exists_mem ];
    refine' ⟨ { z : ℂ | 1 ≤ ‖z‖ }, _, _ ⟩ <;> norm_num;
    · rw [ Metric.cobounded_eq_cocompact ];
      rw [ Filter.mem_cocompact ];
      exact ⟨ Metric.closedBall 0 1, ProperSpace.isCompact_closedBall _ _, fun z hz => not_lt.1 fun h => hz <| mem_closedBall_zero_iff.2 h.le ⟩;
    · exact fun z hz₁ hz₂ => by rw [ ← mul_pow ] ; gcongr ; linarith;
  filter_upwards [ h_bound ] with z hz using by simpa only [ mul_assoc ] using le_trans ( hC1 z ) ( mul_le_mul_of_nonneg_left hz ( show 0 ≤ C1 by exact le_of_not_gt fun h => by have := hC1 0; norm_num at this; linarith [ norm_nonneg ( N.eval 0 ) ] ) )

-- Denominator bound: ‖D(-z)‖ ≥ C₂ · ‖z‖^(deg D) eventually on cobounded ⊓ RHP
set_option maxHeartbeats 400000 in
private lemma g_denominator_bound (D : Polynomial ℂ)
    (hNonvanish : ∀ z : ℂ, z.re ≤ 0 → D.eval z ≠ 0) :
    ∃ C2 : ℝ, 0 < C2 ∧ ∀ᶠ z in (Bornology.cobounded ℂ) ⊓ (𝓟 {z : ℂ | 0 < z.re}),
      ‖D.eval (-z)‖ ≥ C2 * ‖z‖ ^ D.natDegree := by
  by_cases hD : D.natDegree = 0;
  · rw [ eq_C_of_natDegree_eq_zero hD ] at hNonvanish ⊢;
    exact ⟨ ‖D.coeff 0‖, norm_pos_iff.mpr ( show D.coeff 0 ≠ 0 from fun h => hNonvanish 0 ( by norm_num ) <| by simp +decide [ h ] ), Eventually.of_forall fun z => by simp +decide [ hD ] ⟩;
  · have hD_bound : Tendsto (fun z : ℂ => ‖D.eval (-z)‖ / ‖z‖ ^ D.natDegree) (Bornology.cobounded ℂ) (nhds (‖D.leadingCoeff‖)) := by
      have hD_bound : Tendsto (fun z : ℂ => D.eval (-z) / z ^ D.natDegree) (Bornology.cobounded ℂ) (nhds (D.leadingCoeff * (-1) ^ D.natDegree)) := by
        have hD_bound : Tendsto (fun z : ℂ => ∑ i ∈ Finset.range (D.natDegree + 1), D.coeff i * (-1) ^ i / z ^ (D.natDegree - i)) (Bornology.cobounded ℂ) (nhds (D.leadingCoeff * (-1) ^ D.natDegree)) := by
          have hD_bound : ∀ i ∈ Finset.range (D.natDegree), Tendsto (fun z : ℂ => D.coeff i * (-1) ^ i / z ^ (D.natDegree - i)) (Bornology.cobounded ℂ) (nhds 0) := by
            intro i hi;
            rw [ tendsto_zero_iff_norm_tendsto_zero ];
            simpa using tendsto_const_nhds.div_atTop ( tendsto_pow_atTop ( Nat.sub_ne_zero_of_lt ( Finset.mem_range.mp hi ) ) |> Tendsto.comp <| tendsto_norm_cobounded_atTop );
          simpa [ Finset.sum_range_succ ] using tendsto_finset_sum _ hD_bound |> Tendsto.add_const ( D.leadingCoeff * ( -1 ) ^ D.natDegree );
        refine hD_bound.congr' ?_;
        filter_upwards [ Bornology.eventually_ne_cobounded 0 ] with z hz;
        rw [ eval_eq_sum_range ];
        rw [ Finset.sum_div _ _ _ ] ; refine' Finset.sum_congr rfl fun i hi => _ ; rw [ div_eq_div_iff ] <;> ring <;> simp +decide [ hz, pow_add, pow_one, pow_mul, mul_assoc, mul_comm, mul_left_comm ] ;
        rw [ show z ^ D.natDegree = z ^ i * z ^ ( D.natDegree - i ) by rw [ ← pow_add, Nat.add_sub_of_le ( Finset.mem_range_succ_iff.mp hi ) ] ] ; ring;
      convert hD_bound.norm using 2 <;> norm_num;
    have hD_bound_pos : 0 < ‖D.leadingCoeff‖ := by aesop;
    have := hD_bound.eventually ( lt_mem_nhds <| show ‖D.leadingCoeff‖ > ‖D.leadingCoeff‖ / 2 by linarith );
    refine' ⟨ ‖D.leadingCoeff‖ / 2, half_pos hD_bound_pos, _ ⟩;
    rw [ eventually_inf_principal ];
    filter_upwards [ this, Bornology.eventually_ne_cobounded 0 ] with x hx hx' using fun hx'' => by rw [ lt_div_iff₀ ( pow_pos ( norm_pos_iff.mpr hx' ) _ ) ] at hx; linarith

-- Combining bounds: g = N(-z)/D(-z) is O(1) on cobounded ⊓ RHP
private lemma g_isBigO_one (N D : Polynomial ℂ)
    (hNonvanish : ∀ z : ℂ, z.re ≤ 0 → D.eval z ≠ 0)
    (hDegree : N.natDegree ≤ D.natDegree) :
    ∃ c : ℝ, c < 2 ∧ ∃ B : ℝ, (g N D) =O[
      Bornology.cobounded ℂ ⊓ principal {z : ℂ | 0 < z.re}]
      fun z => Real.exp (B * ‖z‖ ^ c) := by
  obtain ⟨C1, hC1⟩ := g_numerator_bound N D hDegree
  obtain ⟨C2, hC2pos, hC2⟩ := g_denominator_bound D hNonvanish
  have h_bound : ∀ᶠ z in (Bornology.cobounded ℂ) ⊓ (𝓟 {z : ℂ | 0 < z.re}), ‖g N D z‖ ≤ C1 / C2 := by
    filter_upwards [ hC1, hC2, eventually_inf_principal.mpr <| Eventually.of_forall fun x hx => hx.out ] with z hz1 hz2 hz3;
    rw [ g, norm_div ];
    rw [ div_le_div_iff₀ ] <;> nlinarith [ show 0 < ‖z‖ ^ D.natDegree by exact pow_pos ( norm_pos_iff.mpr <| by rintro rfl; norm_num at hz3 ) _, norm_nonneg ( eval ( -z ) N ), norm_nonneg ( eval ( -z ) D ) ];
  refine' ⟨ 1, by norm_num, 0, _ ⟩;
  rw [ isBigO_iff ];
  exact ⟨ C1 / C2, by simpa using h_bound ⟩

-- g is bounded on positive reals (limit at infinity exists)
set_option maxHeartbeats 800000 in
private lemma g_bounded_real (N D : Polynomial ℂ)
    (hNonvanish : ∀ z : ℂ, z.re ≤ 0 → D.eval z ≠ 0)
    (hDegree : N.natDegree ≤ D.natDegree) :
    IsBoundedUnder (· ≤ ·) atTop
      (fun x : ℝ => ‖g N D (↑x)‖) := by
  have h_lim : ∃ L : ℂ, Tendsto (fun x : ℝ => N.eval (-(x : ℂ)) / D.eval (-(x : ℂ))) atTop (nhds L) := by
    by_cases hD : D = 0 <;> by_cases hN : N = 0 <;> simp_all +decide [ eval_eq_sum_range ];
    suffices h_suff : ∃ L : ℂ, Tendsto (fun x : ℝ => (∑ i ∈ Finset.range (N.natDegree + 1), N.coeff i * (-1 : ℂ) ^ i * (1 / x ^ (D.natDegree - i))) / (∑ i ∈ Finset.range (D.natDegree + 1), D.coeff i * (-1 : ℂ) ^ i * (1 / x ^ (D.natDegree - i)))) atTop (nhds L) by
      obtain ⟨ L, hL ⟩ := h_suff; use L; refine' hL.congr' _; filter_upwards [ eventually_gt_atTop 0 ] with x hx; simp +decide [ hx.ne', pow_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, div_eq_mul_inv ] ;
      field_simp;
      rw [ show ( ∑ i ∈ Finset.range ( N.natDegree + 1 ), ( -1 : ℂ ) ^ i * N.coeff i / x ^ ( D.natDegree - i ) ) = ( ∑ i ∈ Finset.range ( N.natDegree + 1 ), ( -x : ℂ ) ^ i * N.coeff i ) / x ^ D.natDegree from ?_, show ( ∑ i ∈ Finset.range ( D.natDegree + 1 ), ( -1 : ℂ ) ^ i * D.coeff i / x ^ ( D.natDegree - i ) ) = ( ∑ i ∈ Finset.range ( D.natDegree + 1 ), ( -x : ℂ ) ^ i * D.coeff i ) / x ^ D.natDegree from ?_ ];
      · rw [ div_div_div_cancel_right₀ ( by norm_cast; positivity ) ];
      · rw [ Finset.sum_div _ _ _ ] ; refine' Finset.sum_congr rfl fun i hi => _ ; rw [ div_eq_div_iff ] <;> ring <;> norm_num [ hx.ne' ] ;
        rw [ mul_assoc, ← pow_add, Nat.add_sub_of_le ( Finset.mem_range_succ_iff.mp hi ) ];
      · rw [ Finset.sum_div _ _ _ ] ; refine' Finset.sum_congr rfl fun i hi => _ ; rw [ div_eq_div_iff ] <;> norm_cast <;> ring <;> norm_num [ hx.ne' ] ;
        rw [ show ( x : ℂ ) ^ D.natDegree = x ^ i * x ^ ( D.natDegree - i ) by rw [ ← pow_add, Nat.add_sub_of_le ( by linarith [ Finset.mem_range.mp hi ] ) ] ] ; ring;
    have h_tendsto_zero : ∀ i < D.natDegree, Tendsto (fun x : ℝ => (1 / x ^ (D.natDegree - i) : ℂ)) atTop (nhds 0) := by
      intro i hi; rw [ tendsto_zero_iff_norm_tendsto_zero ] ; norm_num;
      exact tendsto_inv_atTop_zero.comp ( tendsto_pow_atTop ( Nat.sub_ne_zero_of_lt hi ) |> Tendsto.comp <| tendsto_abs_atTop_atTop );
    have h_limit_quotient : Tendsto (fun x : ℝ => (∑ i ∈ Finset.range (N.natDegree + 1), N.coeff i * (-1 : ℂ) ^ i * (1 / x ^ (D.natDegree - i)))) atTop (nhds (∑ i ∈ Finset.range (N.natDegree + 1), N.coeff i * (-1 : ℂ) ^ i * (if i = D.natDegree then 1 else 0))) ∧ Tendsto (fun x : ℝ => (∑ i ∈ Finset.range (D.natDegree + 1), D.coeff i * (-1 : ℂ) ^ i * (1 / x ^ (D.natDegree - i)))) atTop (nhds (∑ i ∈ Finset.range (D.natDegree + 1), D.coeff i * (-1 : ℂ) ^ i * (if i = D.natDegree then 1 else 0))) := by
      constructor <;> refine' tendsto_finset_sum _ fun i hi => _;
      · split_ifs <;> simp_all +decide [ Nat.sub_eq_zero_of_le ];
        simpa using tendsto_const_nhds.mul ( h_tendsto_zero i ( lt_of_le_of_ne ( by linarith ) ‹_› ) );
      · by_cases hi' : i = D.natDegree <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
        simpa using tendsto_const_nhds.mul ( tendsto_const_nhds.mul ( h_tendsto_zero i ( lt_of_le_of_ne hi hi' ) ) );
    refine' ⟨ _, h_limit_quotient.1.div h_limit_quotient.2 _ ⟩ ; simp_all +decide [ Finset.sum_range_succ ];
  exact Tendsto.isBoundedUnder_le ( h_lim.choose_spec.norm )

/-- A rational function `N(-z)/D(-z)` with `deg N ≤ deg D` satisfies
the PhragmenLindelof growth condition on the right half-plane. -/
theorem isBigO_neg_ratFunc_rhp
    (N D : Polynomial ℂ)
    (hNonvanish : ∀ z : ℂ, z.re ≤ 0 → D.eval z ≠ 0)
    (hDegree : N.natDegree ≤ D.natDegree) :
    ∃ c : ℝ, c < 2 ∧ ∃ B : ℝ, (fun z => N.eval (-z) / D.eval (-z)) =O[
      Bornology.cobounded ℂ ⊓ Filter.principal {z : ℂ | 0 < z.re}]
      fun z => Real.exp (B * ‖z‖ ^ c) :=
  g_isBigO_one N D hNonvanish hDegree

/-- A rational function `N(-z)/D(-z)` with `deg N ≤ deg D` is bounded on the
positive real axis. -/
theorem isBoundedUnder_neg_ratFunc_real
    (N D : Polynomial ℂ)
    (hNonvanish : ∀ z : ℂ, z.re ≤ 0 → D.eval z ≠ 0)
    (hDegree : N.natDegree ≤ D.natDegree) :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun x : ℝ => ‖N.eval (-(x : ℂ)) / D.eval (-(x : ℂ))‖) :=
  g_bounded_real N D hNonvanish hDegree

/-- Sufficiency direction of Theorem 351B: if `D` has no zeros on `{Re z ≤ 0}`,
`E(y) ≥ 0` for all `y`, and `deg N ≤ deg D`, then `|N(z)/D(z)| ≤ 1` on
`{Re z ≤ 0}`. -/
theorem aStable_of_nonvanishing_and_ePoly_nonneg
    (N D : Polynomial ℂ)
    (hNonvanish : ∀ z : ℂ, z.re ≤ 0 → D.eval z ≠ 0)
    (hBoundary : ∀ y : ℝ, 0 ≤ ePoly N D y)
    (hDegree : N.natDegree ≤ D.natDegree) :
    ∀ z : ℂ, z.re ≤ 0 → ‖N.eval z / D.eval z‖ ≤ 1 := by
  intro z hz
  -- Apply PhragmenLindelof to g(w) = N(-w)/D(-w) on the right half-plane
  -- Then g(-z) = N(z)/D(z) and (-z).re ≥ 0
  have hReNeg : 0 ≤ (-z).re := by simp; linarith
  -- The key application: PhragmenLindelof.right_half_plane_of_bounded_on_real
  have key := PhragmenLindelof.right_half_plane_of_bounded_on_real
    (f := fun w => N.eval (-w) / D.eval (-w))
    (C := 1)
    (diffContOnCl_neg_ratFunc_rhp N D hNonvanish)
    (isBigO_neg_ratFunc_rhp N D hNonvanish hDegree)
    (isBoundedUnder_neg_ratFunc_real N D hNonvanish hDegree)
    (fun x => by
      -- On the imaginary axis: f(x*I) = N(-x*I)/D(-x*I) = N((-x)*I)/D((-x)*I)
      have hRe : ((-((x : ℂ) * I)).re) ≤ 0 := by simp [Complex.mul_re]
      have hD : D.eval (-((x : ℂ) * I)) ≠ 0 := hNonvanish _ hRe
      show ‖N.eval (-((x : ℂ) * I)) / D.eval (-((x : ℂ) * I))‖ ≤ 1
      have heq : -((x : ℂ) * I) = ((-x : ℝ) : ℂ) * I := by push_cast; ring
      rw [heq]
      have hD' : evalImag D (-x) ≠ 0 := by
        simp only [evalImag_def]
        rw [heq] at hD
        exact hD
      exact norm_div_le_one_of_ePoly_nonneg N D (-x) hD' (hBoundary (-x)))
    hReNeg
  show ‖N.eval z / D.eval z‖ ≤ 1
  have : N.eval (- -z) / D.eval (- -z) = N.eval z / D.eval z := by simp
  rw [← this]
  exact key

/-- Theorem 351B (Iserles): Under `deg N ≤ deg D`, A-stability (with nonvanishing
denominator) is equivalent to all poles being in the open right half-plane and
`E(y) ≥ 0` for all `y`. -/
theorem aStable_with_nonvanishing_iff
    (N D : Polynomial ℂ) (hDegree : N.natDegree ≤ D.natDegree) :
    ((∀ z : ℂ, z.re ≤ 0 → D.eval z ≠ 0) ∧
     (∀ z : ℂ, z.re ≤ 0 → ‖N.eval z / D.eval z‖ ≤ 1)) ↔
    ((∀ z : ℂ, D.eval z = 0 → 0 < z.re) ∧
     (∀ y : ℝ, 0 ≤ ePoly N D y)) := by
  constructor
  · rintro ⟨hNV, hAstab⟩
    exact ⟨fun z hDz => by
      by_contra h
      push_neg at h
      exact hNV z h hDz,
     ePoly_nonneg_of_aStable N D (fun z hz hDz => hAstab z hz) (fun y => by
      have hRe : (((y : ℂ) * I).re) ≤ 0 := by simp [Complex.mul_re]
      exact hNV _ hRe)⟩
  · rintro ⟨hPoles, hE⟩
    exact ⟨fun z hz hDz => by
      have := hPoles z hDz
      linarith,
     aStable_of_nonvanishing_and_ePoly_nonneg N D
      (fun z hz hDz => by have := hPoles z hDz; linarith)
      hE hDegree⟩
