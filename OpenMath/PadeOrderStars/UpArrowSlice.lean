import OpenMath.PadeOrderStars.OddDownArrowSlice

open Complex

/-- The even up-arrow continuation is the same positive-real-axis connected
order-web support used on the even down-arrow side; only the tangent packaging
changes. -/
theorem padeR_even_upArrowOrderWebSameComponentContinuation_of_neg_errorConst
    (n d : ℕ) (_hC : padePhiErrorConst n d < 0) :
    ∃ z0 ∈ orderWeb (padeR n d),
      ∀ aperture > 0, ∀ radius > 0,
        ∃ z : ℂ,
          z ∈ connectedComponentIn (orderWeb (padeR n d)) z0 ∧
            z ∈ rayConeNearOrigin 0 aperture radius := by
  let t0 : ℝ := min (1 / 2) (1 / 2)
  obtain ⟨δ, hδpos, hreal_web⟩ := padeR_mem_orderWeb_on_posRealAxis_of_small_radius n d
  let r0 : ℝ := min t0 (δ / 2)
  have hr0_pos : 0 < r0 := by
    dsimp [r0, t0]
    exact lt_min (by norm_num) (half_pos hδpos)
  have hr0_lt_δ : r0 < δ := by
    have hhalf : δ / 2 < δ := by linarith
    exact lt_of_le_of_lt (min_le_right _ _) hhalf
  have hz0web : ((↑r0 : ℂ)) ∈ orderWeb (padeR n d) :=
    hreal_web r0 ⟨hr0_pos, hr0_lt_δ⟩
  refine ⟨(↑r0 : ℂ), hz0web, ?_⟩
  intro aperture haperture radius hradius
  let r : ℝ := min (radius / 2) (r0 / 2)
  have hr_pos : 0 < r := by
    dsimp [r]
    exact lt_min (half_pos hradius) (half_pos hr0_pos)
  have hr_lt_radius : r < radius := by
    have hhalf : radius / 2 < radius := by
      linarith
    exact lt_of_le_of_lt (min_le_left _ _) hhalf
  have hr_le_r0 : r ≤ r0 := by
    have hhalf : r0 / 2 ≤ r0 := by
      linarith
    exact le_trans (min_le_right _ _) hhalf
  have hr_lt_δ : r < δ := lt_of_le_of_lt hr_le_r0 hr0_lt_δ
  have hzweb : ((↑r : ℂ)) ∈ orderWeb (padeR n d) :=
    hreal_web r ⟨hr_pos, hr_lt_δ⟩
  have hzcone : ((↑r : ℂ)) ∈ rayConeNearOrigin 0 aperture radius := by
    simpa using
      exact_ray_mem_rayConeNearOrigin 0 aperture radius r haperture ⟨hr_pos, hr_lt_radius⟩
  let support : Set ℂ := (fun x : ℝ => (↑x : ℂ)) '' Set.Icc r r0
  have hsupport_conn : IsConnected support := by
    refine (isConnected_Icc hr_le_r0).image (fun x : ℝ => (↑x : ℂ)) ?_
    exact continuous_ofReal.continuousOn
  have hz0support : ((↑r0 : ℂ)) ∈ support := by
    refine ⟨r0, ?_, by simp⟩
    exact ⟨hr_le_r0, le_rfl⟩
  have hzsupport : ((↑r : ℂ)) ∈ support := by
    refine ⟨r, ?_, by simp⟩
    exact ⟨le_rfl, hr_le_r0⟩
  have hsupport_web : support ⊆ orderWeb (padeR n d) := by
    intro z hz
    rcases hz with ⟨x, hxIcc, rfl⟩
    have hx_pos : 0 < x := lt_of_lt_of_le hr_pos hxIcc.1
    have hx_le_r0 : x ≤ r0 := hxIcc.2
    have hx_lt_δ : x < δ := lt_of_le_of_lt hx_le_r0 hr0_lt_δ
    exact hreal_web x ⟨hx_pos, hx_lt_δ⟩
  have hsupport_comp :
      support ⊆ connectedComponentIn (orderWeb (padeR n d)) (↑r0 : ℂ) :=
    hsupport_conn.2.subset_connectedComponentIn hz0support hsupport_web
  exact ⟨(↑r : ℂ), hsupport_comp hzsupport, hzcone⟩

theorem padeR_even_upArrowOrderWebMeetsRayConeNearOriginInConnectedComponent_of_neg_errorConst
    (n d : ℕ) (hC : padePhiErrorConst n d < 0) :
    PadeROrderWebMeetsRayConeNearOriginInConnectedComponent n d 0 := by
  rcases
      padeR_even_upArrowOrderWebSameComponentContinuation_of_neg_errorConst n d hC with
    ⟨z0, hz0, hcontinue⟩
  refine ⟨z0, hz0, ?_⟩
  intro aperture haperture radius hradius
  rcases hcontinue aperture haperture radius hradius with ⟨z, hzcomp, hzcone⟩
  exact ⟨z, ⟨hzcomp, hzcone⟩⟩

theorem padeRUpArrowOrderWebConnectedComponentMeetInput_of_neg_errorConst
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hC : padePhiErrorConst n d < 0) :
    PadeRUpArrowOrderWebConnectedComponentMeetInput n d data := by
  refine ⟨?_⟩
  intro _
  refine ⟨0, ?_, ?_⟩
  · simpa using padeR_upArrowDir_of_neg_errorConst n d 0 hC
  · simpa using
      padeR_even_upArrowOrderWebMeetsRayConeNearOriginInConnectedComponent_of_neg_errorConst
        n d hC

theorem padeRUpArrowConnectedRayConeSupportInput_of_neg_errorConst
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hC : padePhiErrorConst n d < 0) :
    PadeRUpArrowConnectedRayConeSupportInput n d data := by
  exact
    (padeRUpArrowOrderWebConnectedComponentMeetInput_of_neg_errorConst n d data hC).toConnectedRayConeSupportInput

theorem padeRUpArrowRayTrackingSupportInput_of_neg_errorConst
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hC : padePhiErrorConst n d < 0) :
    PadeRUpArrowRayTrackingSupportInput n d data := by
  exact
    (padeRUpArrowConnectedRayConeSupportInput_of_neg_errorConst n d data hC).toRayTrackingSupportInput

theorem padeRUpArrowBranchTrackingInput_of_neg_errorConst
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hC : padePhiErrorConst n d < 0) :
    PadeRUpArrowBranchTrackingInput n d data := by
  exact
    (padeRUpArrowRayTrackingSupportInput_of_neg_errorConst n d data hC).toTrackingInput

private theorem padeR_odd_upArrowUniformRadiusPhaseStrip_of_pos_errorConst
    (n d : ℕ) {η : ℝ}
    (hC : 0 < padePhiErrorConst n d)
    (hη : 0 < η)
    (hηpi : ((↑(n + d) + 1) : ℝ) * η < Real.pi) :
    ∃ δ > 0,
      (∀ r ∈ Set.Ioo (0 : ℝ) δ, ∀ s ∈ Set.Icc (-η) η,
        let w : ℂ :=
          (↑r : ℂ) * exp (↑(Real.pi / ((↑(n + d) + 1) : ℝ) + s) * I)
        0 < Complex.re (padeR n d w * exp (-w))) ∧
      (∀ r ∈ Set.Ioo (0 : ℝ) δ,
        let w : ℂ :=
          (↑r : ℂ) * exp (↑(Real.pi / ((↑(n + d) + 1) : ℝ) - η) * I)
        Complex.im (padeR n d w * exp (-w)) < 0) ∧
      (∀ r ∈ Set.Ioo (0 : ℝ) δ,
        let w : ℂ :=
          (↑r : ℂ) * exp (↑(Real.pi / ((↑(n + d) + 1) : ℝ) + η) * I)
        0 < Complex.im (padeR n d w * exp (-w))) := by
  obtain ⟨K, δ₀, hK, hδ, hφ⟩ := padeR_exp_neg_local_bound n d
  let Cabs : ℝ := |padePhiErrorConst n d|
  let δre : ℝ := min (δ₀ / 2) (min 1 (1 / (4 * (Cabs + K))))
  have hδre : 0 < δre := by
    refine lt_min (half_pos hδ) ?_
    refine lt_min zero_lt_one ?_
    positivity
  have hre_small : ∀ z : ℂ, ‖z‖ < δre →
      0 < Complex.re (padeR n d z * exp (-z)) := by
    intro z hz
    have hzδ₀ : ‖z‖ < δ₀ := by
      have hzδhalf : ‖z‖ < δ₀ / 2 := lt_of_lt_of_le hz (min_le_left _ _)
      linarith
    have hznorm_one : ‖z‖ < 1 := by
      exact lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_left _ _))
    have hznorm_small : ‖z‖ < 1 / (4 * (Cabs + K)) := by
      exact lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_right _ _))
    have hpow1_le : ‖z‖ ^ (n + d + 1) ≤ ‖z‖ := by
      calc
        ‖z‖ ^ (n + d + 1) ≤ ‖z‖ ^ 1 := by
          exact pow_le_pow_of_le_one (norm_nonneg z) hznorm_one.le (by omega : 1 ≤ n + d + 1)
        _ = ‖z‖ := by simp
    have hpow2_le : ‖z‖ ^ (n + d + 2) ≤ ‖z‖ := by
      calc
        ‖z‖ ^ (n + d + 2) ≤ ‖z‖ ^ 1 := by
          exact pow_le_pow_of_le_one (norm_nonneg z) hznorm_one.le (by omega : 1 ≤ n + d + 2)
        _ = ‖z‖ := by simp
    have hsum_le :
        Cabs * ‖z‖ ^ (n + d + 1) + K * ‖z‖ ^ (n + d + 2) ≤ (Cabs + K) * ‖z‖ := by
      have hterm1 : Cabs * ‖z‖ ^ (n + d + 1) ≤ Cabs * ‖z‖ := by
        exact mul_le_mul_of_nonneg_left hpow1_le (by dsimp [Cabs]; positivity)
      have hterm2 : K * ‖z‖ ^ (n + d + 2) ≤ K * ‖z‖ := by
        exact mul_le_mul_of_nonneg_left hpow2_le hK.le
      nlinarith
    have hsum_lt :
        Cabs * ‖z‖ ^ (n + d + 1) + K * ‖z‖ ^ (n + d + 2) < 1 / 4 := by
      have hprod_lt : (Cabs + K) * ‖z‖ < 1 / 4 := by
        have hden_pos : 0 < 4 * (Cabs + K) := by positivity
        have htmp := (lt_div_iff₀ hden_pos).mp hznorm_small
        nlinarith
      exact lt_of_le_of_lt hsum_le hprod_lt
    have hre_main_lower :
        1 - Cabs * ‖z‖ ^ (n + d + 1) ≤
          Complex.re ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1)) := by
      have hre_term :
          Complex.re ((padePhiErrorConst n d : ℂ) * z ^ (n + d + 1)) ≤
            Cabs * ‖z‖ ^ (n + d + 1) := by
        calc
          Complex.re ((padePhiErrorConst n d : ℂ) * z ^ (n + d + 1)) ≤
              ‖(padePhiErrorConst n d : ℂ) * z ^ (n + d + 1)‖ := Complex.re_le_norm _
          _ = Cabs * ‖z‖ ^ (n + d + 1) := by
            simp [Cabs, norm_pow]
      rw [show Complex.re ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1)) =
          1 - Complex.re ((padePhiErrorConst n d : ℂ) * z ^ (n + d + 1)) by simp]
      linarith
    have hre_diff :
        abs
          (Complex.re (padeR n d z * exp (-z)) -
            Complex.re ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1))) ≤
          K * ‖z‖ ^ (n + d + 2) := by
      have hre_le :
          abs
            (Complex.re (padeR n d z * exp (-z) -
              ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1)))) ≤
            ‖padeR n d z * exp (-z) -
              ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1))‖ := by
        simpa using
          Complex.abs_re_le_norm
            (padeR n d z * exp (-z) -
              ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1)))
      have happrox := hφ z hzδ₀
      simpa [Complex.sub_re] using le_trans hre_le happrox
    have hre_lower :
        1 - Cabs * ‖z‖ ^ (n + d + 1) - K * ‖z‖ ^ (n + d + 2) ≤
          Complex.re (padeR n d z * exp (-z)) := by
      have h' := abs_le.mp hre_diff
      linarith
    have hpos :
        0 < 1 - Cabs * ‖z‖ ^ (n + d + 1) - K * ‖z‖ ^ (n + d + 2) := by
      nlinarith
    exact lt_of_lt_of_le hpos hre_lower
  let p1 : ℝ := ((↑(n + d) + 1) : ℝ)
  let θ0 : ℝ := Real.pi / p1
  let α : ℝ := p1 * η
  have hp1_pos : 0 < p1 := by
    dsimp [p1]
    positivity
  have hαpos : 0 < α := by
    dsimp [α]
    positivity
  have hsin : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hαpos hηpi
  let δsign : ℝ := padePhiErrorConst n d * Real.sin α / (2 * K)
  have hδsign : 0 < δsign := by
    dsimp [δsign]
    exact div_pos (mul_pos hC hsin) (by positivity)
  let δ : ℝ := min δre (min δ₀ δsign)
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min hδre (lt_min hδ hδsign)
  refine ⟨δ, hδpos, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro r hr s _hs
    apply hre_small
    have hrδre : r < δre := by
      exact lt_of_lt_of_le hr.2 (min_le_left _ _)
    exact (norm_ofReal_mul_exp_I r (θ0 + s) hr.1.le).trans_lt hrδre
  · intro r hr
    have hr_delta : r < δ₀ := by
      exact lt_of_lt_of_le hr.2 (le_trans (min_le_right _ _) (min_le_left _ _))
    have hr_sign : r < δsign := by
      exact lt_of_lt_of_le hr.2 (le_trans (min_le_right _ _) (min_le_right _ _))
    have hKt : K * r < padePhiErrorConst n d * Real.sin α / 2 := by
      have h := (lt_div_iff₀ (show 0 < 2 * K by positivity)).mp hr_sign
      nlinarith
    let zL : ℂ := (↑r : ℂ) * exp (↑(θ0 - η) * I)
    have hzL_norm : ‖zL‖ = r := by
      simpa [zL] using norm_ofReal_mul_exp_I r (θ0 - η) hr.1.le
    have hzL_delta : ‖zL‖ < δ₀ := by
      simpa [hzL_norm] using hr_delta
    have hboundL := hφ zL hzL_delta
    have hmainL :
        Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1)) =
          (-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin α := by
      simpa [zL, p1, θ0, α] using
        (im_main_term_odd_down_left (p := n + d) (c := padePhiErrorConst n d) r η)
    have himdiffL :
        abs
          (Complex.im (padeR n d zL * exp (-zL)) -
            Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1))) ≤
          K * r ^ (n + d + 2) := by
      have him_le :
          abs
            (Complex.im (padeR n d zL * exp (-zL)) -
              Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1))) ≤
            ‖padeR n d zL * exp (-zL) -
              ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1))‖ := by
        simpa using
          abs_im_sub_le_norm_sub
            (a := padeR n d zL * exp (-zL))
            (b := (1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1))
      have hboundL' :
          ‖padeR n d zL * exp (-zL) -
            ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1))‖ ≤
          K * r ^ (n + d + 2) := by
        simpa [hzL_norm] using hboundL
      exact le_trans him_le hboundL'
    have hleft_core :
        (-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin α +
          K * r ^ (n + d + 2) < 0 := by
      have hpow_pos : 0 < r ^ (n + d + 1) := pow_pos hr.1 _
      have hlin : K * r - padePhiErrorConst n d * Real.sin α < 0 := by
        nlinarith [hKt, hC, hsin]
      have hrewrite :
          (-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin α + K * r ^ (n + d + 2) =
            r ^ (n + d + 1) * (K * r - padePhiErrorConst n d * Real.sin α) := by
        ring
      rw [hrewrite]
      exact mul_neg_of_pos_of_neg hpow_pos hlin
    have hleft_bound :
        Complex.im (padeR n d zL * exp (-zL)) ≤
          (-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin α +
            K * r ^ (n + d + 2) := by
      have h' := abs_le.mp himdiffL
      linarith [hmainL]
    exact lt_of_le_of_lt hleft_bound hleft_core
  · intro r hr
    have hr_delta : r < δ₀ := by
      exact lt_of_lt_of_le hr.2 (le_trans (min_le_right _ _) (min_le_left _ _))
    have hr_sign : r < δsign := by
      exact lt_of_lt_of_le hr.2 (le_trans (min_le_right _ _) (min_le_right _ _))
    have hKt : K * r < padePhiErrorConst n d * Real.sin α / 2 := by
      have h := (lt_div_iff₀ (show 0 < 2 * K by positivity)).mp hr_sign
      nlinarith
    let zR : ℂ := (↑r : ℂ) * exp (↑(θ0 + η) * I)
    have hzR_norm : ‖zR‖ = r := by
      simpa [zR] using norm_ofReal_mul_exp_I r (θ0 + η) hr.1.le
    have hzR_delta : ‖zR‖ < δ₀ := by
      simpa [hzR_norm] using hr_delta
    have hboundR := hφ zR hzR_delta
    have hmainR :
        Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1)) =
          -((-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin α) := by
      simpa [zR, p1, θ0, α] using
        (im_main_term_odd_down_right (p := n + d) (c := padePhiErrorConst n d) r η)
    have himdiffR :
        abs
          (Complex.im (padeR n d zR * exp (-zR)) -
            Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1))) ≤
          K * r ^ (n + d + 2) := by
      have him_le :
          abs
            (Complex.im (padeR n d zR * exp (-zR)) -
              Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1))) ≤
            ‖padeR n d zR * exp (-zR) -
              ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1))‖ := by
        simpa using
          abs_im_sub_le_norm_sub
            (a := padeR n d zR * exp (-zR))
            (b := (1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1))
      have hboundR' :
          ‖padeR n d zR * exp (-zR) -
            ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1))‖ ≤
          K * r ^ (n + d + 2) := by
        simpa [hzR_norm] using hboundR
      exact le_trans him_le hboundR'
    have hright_core :
        0 < -((-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin α) -
          K * r ^ (n + d + 2) := by
      have hpow_pos : 0 < r ^ (n + d + 1) := pow_pos hr.1 _
      have hlin : 0 < padePhiErrorConst n d * Real.sin α - K * r := by
        nlinarith [hKt, hC, hsin]
      have hrewrite :
          -((-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin α) - K * r ^ (n + d + 2) =
            r ^ (n + d + 1) * (padePhiErrorConst n d * Real.sin α - K * r) := by
        ring
      rw [hrewrite]
      exact mul_pos hpow_pos hlin
    have hright_bound :
        -((-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin α) -
          K * r ^ (n + d + 2) ≤
          Complex.im (padeR n d zR * exp (-zR)) := by
      have h' := abs_le.mp himdiffR
      linarith [hmainR]
    exact lt_of_lt_of_le hright_core hright_bound

private theorem padeR_odd_upArrowArcEndpointSigns_of_pos_errorConst
    (n d : ℕ) {η : ℝ}
    (hC : 0 < padePhiErrorConst n d)
    (hη : 0 < η)
    (hηpi : ((↑(n + d) + 1) : ℝ) * η < Real.pi) :
    ∀ radius > 0,
      ∃ t ∈ Set.Ioo (0 : ℝ) radius,
        Complex.im
          (padeR n d
              (((↑t : ℂ) *
                  exp (↑(Real.pi / ((↑(n + d) + 1) : ℝ) - η) * I))) *
            exp (-(((↑t : ℂ) *
                exp (↑(Real.pi / ((↑(n + d) + 1) : ℝ) - η) * I))))) < 0 ∧
        0 < Complex.im
          (padeR n d
              (((↑t : ℂ) *
                  exp (↑(Real.pi / ((↑(n + d) + 1) : ℝ) + η) * I))) *
            exp (-(((↑t : ℂ) *
                exp (↑(Real.pi / ((↑(n + d) + 1) : ℝ) + η) * I))))) := by
  obtain ⟨δ, hδ, _hre, hleft, hright⟩ :=
    padeR_odd_upArrowUniformRadiusPhaseStrip_of_pos_errorConst n d hC hη hηpi
  intro radius hradius
  let t : ℝ := min (radius / 2) (δ / 2)
  have ht_radius : t ∈ Set.Ioo (0 : ℝ) radius := by
    refine ⟨?_, ?_⟩
    · dsimp [t]
      exact lt_min (half_pos hradius) (half_pos hδ)
    · dsimp [t]
      have hhalf : radius / 2 < radius := by
        linarith
      exact lt_of_le_of_lt (min_le_left _ _) hhalf
  have ht_δ : t ∈ Set.Ioo (0 : ℝ) δ := by
    refine ⟨?_, ?_⟩
    · dsimp [t]
      exact lt_min (half_pos hradius) (half_pos hδ)
    · dsimp [t]
      have hhalf : δ / 2 < δ := by
        linarith
      exact lt_of_le_of_lt (min_le_right _ _) hhalf
  refine ⟨t, ht_radius, ?_⟩
  exact ⟨by simpa using hleft t ht_δ, by simpa using hright t ht_δ⟩

theorem padeR_odd_upArrowOrderWebMeetsRayConeNearOrigin_of_pos_errorConst
    (n d : ℕ) (hC : 0 < padePhiErrorConst n d) :
    PadeROrderWebMeetsRayConeNearOrigin n d
      (Real.pi / ((↑(n + d) + 1) : ℝ)) := by
  intro aperture haperture radius hradius
  obtain ⟨δQ, hδQ, hQ⟩ := padeQ_nonzero_near_zero n d
  let p1 : ℝ := ((↑(n + d) + 1) : ℝ)
  let θ0 : ℝ := Real.pi / p1
  have hp1_pos : 0 < p1 := by
    dsimp [p1]
    positivity
  let η : ℝ := min (aperture / 2) (1 / p1)
  have hη_pos : 0 < η := by
    refine lt_min (half_pos haperture) ?_
    exact one_div_pos.mpr hp1_pos
  have hη_lt_aperture : η < aperture := by
    have hhalf : aperture / 2 < aperture := by
      linarith
    exact lt_of_le_of_lt (min_le_left _ _) hhalf
  have hηpi : p1 * η < Real.pi := by
    have hη_one : p1 * η ≤ 1 := by
      have hη_le : η ≤ 1 / p1 := min_le_right _ _
      have hmul := mul_le_mul_of_nonneg_left hη_le hp1_pos.le
      have hp1_ne : p1 ≠ 0 := ne_of_gt hp1_pos
      rw [show p1 * (1 / p1) = 1 by field_simp [hp1_ne]] at hmul
      exact hmul
    linarith [Real.pi_gt_three]
  obtain ⟨δ, hδ, hre, _hleft, _hright⟩ :=
    padeR_odd_upArrowUniformRadiusPhaseStrip_of_pos_errorConst n d hC hη_pos hηpi
  let radius' : ℝ := min radius (min (δQ / 2) δ)
  have hradius' : 0 < radius' := by
    dsimp [radius']
    exact lt_min hradius (lt_min (half_pos hδQ) hδ)
  rcases
      padeR_odd_upArrowArcEndpointSigns_of_pos_errorConst n d hC hη_pos hηpi radius' hradius' with
    ⟨t, ht, him_left, him_right⟩
  have ht_radius : t ∈ Set.Ioo (0 : ℝ) radius := by
    refine ⟨ht.1, ?_⟩
    exact lt_of_lt_of_le ht.2 (min_le_left _ _)
  have ht_δQ : t < δQ := by
    have ht_min : t < min (δQ / 2) δ := lt_of_lt_of_le ht.2 (min_le_right _ _)
    have ht_half : t < δQ / 2 := lt_of_lt_of_le ht_min (min_le_left _ _)
    have hhalf : δQ / 2 < δQ := by
      linarith
    exact lt_trans ht_half hhalf
  have ht_δ : t ∈ Set.Ioo (0 : ℝ) δ := by
    refine ⟨ht.1, ?_⟩
    exact lt_of_lt_of_le ht.2 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hcont_complex :
      ContinuousOn
        (fun s : ℝ =>
          padeR n d ((↑t : ℂ) * exp (↑(θ0 + s) * I)) *
            exp (-((↑t : ℂ) * exp (↑(θ0 + s) * I))))
        (Set.Icc (-η) η) :=
    padeR_exp_neg_continuousOn_angleArc n d θ0 t η δQ ht.1 ht_δQ hQ
  have him_cont : ContinuousOn (fun z : ℂ => Complex.im z) Set.univ :=
    Complex.continuous_im.continuousOn
  have hcont_im :
      ContinuousOn
        (fun s : ℝ =>
          Complex.im
            (padeR n d ((↑t : ℂ) * exp (↑(θ0 + s) * I)) *
              exp (-((↑t : ℂ) * exp (↑(θ0 + s) * I)))))
        (Set.Icc (-η) η) := by
    simpa [Function.comp] using
      (him_cont.comp hcont_complex (by
        intro x hx
        simp))
  have hzero_mem :
      (0 : ℝ) ∈ Set.Icc
        (Complex.im
          (padeR n d ((↑t : ℂ) * exp (↑(θ0 - η) * I)) *
            exp (-((↑t : ℂ) * exp (↑(θ0 - η) * I)))))
        (Complex.im
          (padeR n d ((↑t : ℂ) * exp (↑(θ0 + η) * I)) *
            exp (-((↑t : ℂ) * exp (↑(θ0 + η) * I))))) := by
    exact ⟨le_of_lt him_left, le_of_lt him_right⟩
  have hpre : IsPreconnected (Set.Icc (-η) η) := by
    simpa using isPreconnected_Icc
  have himage :=
    hpre.intermediate_value
      (show -η ∈ Set.Icc (-η) η by simp [hη_pos.le])
      (show η ∈ Set.Icc (-η) η by simp [hη_pos.le])
      hcont_im
  rcases himage hzero_mem with ⟨s, hsIcc, hszero⟩
  let z : ℂ := (↑t : ℂ) * exp (↑(θ0 + s) * I)
  have hzcone' : z ∈ rayConeNearOrigin θ0 aperture radius' := by
    simpa [z] using
      exact_angle_arc_mem_rayConeNearOrigin θ0 aperture radius' t η haperture ht hη_lt_aperture s hsIcc
  have hzcone : z ∈ rayConeNearOrigin θ0 aperture radius := by
    rcases hzcone' with ⟨u, hu, hudist⟩
    exact ⟨u, ⟨hu.1, lt_of_lt_of_le hu.2 (min_le_left _ _)⟩, hudist⟩
  have hrez : 0 < Complex.re (padeR n d z * exp (-z)) := by
    simpa [z, θ0, p1] using hre t ht_δ s hsIcc
  have himz : Complex.im (padeR n d z * exp (-z)) = 0 := by
    simpa [z] using hszero
  exact ⟨z, mem_orderWeb_of_im_zero_of_re_pos hrez himz, hzcone⟩

private theorem padeRExpNegSecondCoeff_abs_lt_half_main_pos
    (n d : ℕ) (hm : 0 < n + d) (hC : 0 < padePhiErrorConst n d) :
    |padeRExpNegSecondCoeff n d| <
      padePhiErrorConst n d * (((↑(n + d) + 1) : ℝ) / 2) := by
  let m : ℕ := n + d
  have hm : 0 < m := by
    simpa [m] using hm
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast hm
  have hm1_pos : 0 < ((m : ℝ) + 1) := by positivity
  have hm2_pos : 0 < ((m : ℝ) + 2) := by positivity
  have habsC : |padePhiErrorConst n d| = padePhiErrorConst n d := abs_of_pos hC
  have habs_nd : |(n : ℝ) - d| ≤ (m : ℝ) := by
    refine abs_le.mpr ?_
    constructor <;> linarith [show (m : ℝ) = (n : ℝ) + d by
      norm_num [m, Nat.cast_add]]
  have hratio :
      |(((n : ℝ) - d) * ((m : ℝ) + 1)) / ((m : ℝ) * ((m : ℝ) + 2))| <
        ((m : ℝ) + 1) / 2 := by
    have hmprod_pos : 0 < (m : ℝ) * ((m : ℝ) + 2) := by positivity
    have habsden : |(m : ℝ) * ((m : ℝ) + 2)| = (m : ℝ) * ((m : ℝ) + 2) := by
      rw [abs_of_pos hmprod_pos]
    rw [abs_div, abs_mul, abs_of_nonneg (show 0 ≤ (m : ℝ) + 1 by positivity), habsden]
    have hratio_le :
        |(n : ℝ) - d| * ((m : ℝ) + 1) / ((m : ℝ) * ((m : ℝ) + 2)) ≤
            ((m : ℝ) + 1) / ((m : ℝ) + 2) := by
      calc
        |(n : ℝ) - d| * ((m : ℝ) + 1) / ((m : ℝ) * ((m : ℝ) + 2)) ≤
            (m : ℝ) * ((m : ℝ) + 1) / ((m : ℝ) * ((m : ℝ) + 2)) := by
              gcongr
        _ = ((m : ℝ) + 1) / ((m : ℝ) + 2) := by
              field_simp [show (m : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hm)]
    have hfrac :
        ((m : ℝ) + 1) / ((m : ℝ) + 2) < ((m : ℝ) + 1) / 2 := by
      have hinv : (1 : ℝ) / ((m : ℝ) + 2) < 1 / 2 := by
        rw [one_div_lt_one_div hm2_pos (by positivity : (0 : ℝ) < 2)]
        linarith
      have hmul :
          ((m : ℝ) + 1) * ((1 : ℝ) / ((m : ℝ) + 2)) <
            ((m : ℝ) + 1) * (1 / 2) := by
              exact mul_lt_mul_of_pos_left hinv hm1_pos
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    exact lt_of_le_of_lt hratio_le hfrac
  have hformula :
      |padeRExpNegSecondCoeff n d| =
        |padePhiErrorConst n d| *
          |(((n : ℝ) - d) * ((m : ℝ) + 1)) / ((m : ℝ) * ((m : ℝ) + 2))| := by
    simp [padeRExpNegSecondCoeff, m, abs_mul, div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm]
  calc
    |padeRExpNegSecondCoeff n d| =
        |padePhiErrorConst n d| *
          |(((n : ℝ) - d) * ((m : ℝ) + 1)) / ((m : ℝ) * ((m : ℝ) + 2))| := hformula
    _ = padePhiErrorConst n d *
          |(((n : ℝ) - d) * ((m : ℝ) + 1)) / ((m : ℝ) * ((m : ℝ) + 2))| := by
            rw [habsC]
    _ < padePhiErrorConst n d * (((m : ℝ) + 1) / 2) := by
          exact mul_lt_mul_of_pos_left hratio hC
    _ = padePhiErrorConst n d * (((↑(n + d) + 1) : ℝ) / 2) := by
          simp [m]

private theorem padeR00_oddDownArrowTrueSlice_left_im
    (r : ℝ) :
    Complex.im
      (padeR 0 0
          (((↑r : ℂ) * exp (↑(oddDownArrowRadiusPhaseCenter 0 0 - r) * I))) *
        exp (-(((↑r : ℂ) * exp (↑(oddDownArrowRadiusPhaseCenter 0 0 - r) * I))))) =
      -Real.exp (r * Real.cos r) * Real.sin (r * Real.sin r) := by
  have htrig :
      Real.exp (-(r * Real.cos (Real.pi + -r))) * Real.sin (r * Real.sin (Real.pi + -r)) =
        Real.exp (r * Real.cos r) * Real.sin (r * Real.sin r) := by
    rw [show Real.pi + -r = Real.pi - r by ring]
    rw [Real.cos_pi_sub, Real.sin_pi_sub]
    ring_nf
  simpa [oddDownArrowRadiusPhaseCenter, padeR, padeP_zero_right, padeQ_zero_right,
    Complex.exp_im, Complex.exp_re, Complex.mul_re, Complex.mul_im, sub_eq_add_neg] using htrig

private theorem padeR00_oddDownArrowTrueSlice_right_im
    (r : ℝ) :
    Complex.im
      (padeR 0 0
          (((↑r : ℂ) * exp (↑(oddDownArrowRadiusPhaseCenter 0 0 + r) * I))) *
        exp (-(((↑r : ℂ) * exp (↑(oddDownArrowRadiusPhaseCenter 0 0 + r) * I))))) =
      Real.exp (r * Real.cos r) * Real.sin (r * Real.sin r) := by
  have htrig :
      -(Real.exp (-(r * Real.cos (Real.pi + r))) * Real.sin (r * Real.sin (Real.pi + r))) =
        Real.exp (r * Real.cos r) * Real.sin (r * Real.sin r) := by
    rw [show Real.pi + r = r + Real.pi by ring]
    rw [Real.cos_add_pi, Real.sin_add_pi]
    ring_nf
    rw [Real.sin_neg]
    ring
  simpa [oddDownArrowRadiusPhaseCenter, padeR, padeP_zero_right, padeQ_zero_right,
    Complex.exp_im, Complex.exp_re, Complex.mul_re, Complex.mul_im, sub_eq_add_neg] using htrig

private theorem oddDownArrowRadiusPhaseEndpointSigns_on_trueSlice_of_pos_errorConst
    (n d : ℕ) (hC : 0 < padePhiErrorConst n d) :
    ∃ δ > 0,
      ∀ r ∈ Set.Ioo (0 : ℝ) δ,
        Complex.im
          (padeR n d
              (((↑r : ℂ) *
                  exp (↑(oddDownArrowRadiusPhaseCenter n d - r) * I))) *
            exp (-(((↑r : ℂ) *
                exp (↑(oddDownArrowRadiusPhaseCenter n d - r) * I))))) < 0 ∧
        0 < Complex.im
          (padeR n d
              (((↑r : ℂ) *
                  exp (↑(oddDownArrowRadiusPhaseCenter n d + r) * I))) *
            exp (-(((↑r : ℂ) *
                exp (↑(oddDownArrowRadiusPhaseCenter n d + r) * I))))) := by
  by_cases hm : 0 < n + d
  · obtain ⟨K₂, δ₂, hK₂, hδ₂, hφ₂⟩ := padeR_exp_neg_second_order_local_bound n d hm
    let p1 : ℝ := ((↑(n + d) + 1) : ℝ)
    let θ0 : ℝ := oddDownArrowRadiusPhaseCenter n d
    let absC2 : ℝ := |padeRExpNegSecondCoeff n d|
    have hp1_pos : 0 < p1 := by
      dsimp [p1]
      positivity
    have hC2_lt :
        absC2 < padePhiErrorConst n d * p1 / 2 := by
      have hraw := padeRExpNegSecondCoeff_abs_lt_half_main_pos n d hm hC
      dsimp [absC2, p1] at hraw ⊢
      nlinarith
    let gap : ℝ := padePhiErrorConst n d * p1 / 2 - absC2
    have hgap_pos : 0 < gap := by
      dsimp [gap]
      linarith
    let δ : ℝ := min (δ₂ / 2) (min (1 / p1) (gap / (2 * K₂)))
    have hδpos : 0 < δ := by
      dsimp [δ]
      refine lt_min (half_pos hδ₂) ?_
      refine lt_min (one_div_pos.mpr hp1_pos) ?_
      exact div_pos hgap_pos (mul_pos two_pos hK₂)
    refine ⟨δ, hδpos, ?_⟩
    intro r hr
    have hr_delta : r < δ₂ := by
      have hδ_le_half : δ ≤ δ₂ / 2 := by
        dsimp [δ]
        exact min_le_left _ _
      have hhalf : δ₂ / 2 < δ₂ := by
        linarith
      exact lt_trans (lt_of_lt_of_le hr.2 hδ_le_half) hhalf
    have hr_inv : r < 1 / p1 := by
      exact lt_of_lt_of_le hr.2 (le_trans (min_le_right _ _) (min_le_left _ _))
    have hαlt_one : p1 * r < 1 := by
      have hmul : p1 * r < p1 * (1 / p1) := mul_lt_mul_of_pos_left hr_inv hp1_pos
      have hp1_ne : p1 ≠ 0 := ne_of_gt hp1_pos
      rw [show p1 * (1 / p1) = 1 by field_simp [hp1_ne]] at hmul
      exact hmul
    have hαpi2 : p1 * r < Real.pi / 2 := by
      linarith [hαlt_one, Real.pi_gt_three]
    have hαpos : 0 < p1 * r := mul_pos hp1_pos hr.1
    have hhalf_lt_coeff :
        p1 * r / 2 < (2 / Real.pi) * (p1 * r) := by
      have hconst : (1 / 2 : ℝ) < 2 / Real.pi := by
        have hnum : 0 < 4 - Real.pi := by
          linarith [Real.pi_lt_four]
        have hden : 0 < 2 * Real.pi := by positivity
        have hcalc : 2 / Real.pi - 1 / 2 = (4 - Real.pi) / (2 * Real.pi) := by
          field_simp [show (Real.pi : ℝ) ≠ 0 by exact Real.pi_ne_zero]
          ring
        have : 0 < 2 / Real.pi - 1 / 2 := by
          rw [hcalc]
          exact div_pos hnum hden
        linarith
      have := mul_lt_mul_of_pos_right hconst hαpos
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    have hhalf_lt_sin : p1 * r / 2 < Real.sin (p1 * r) := by
      exact lt_trans hhalf_lt_coeff (Real.mul_lt_sin hαpos hαpi2)
    have hgap_bound : K₂ * r < gap := by
      have hr_gap : r < gap / (2 * K₂) := by
        exact lt_of_lt_of_le hr.2 (le_trans (min_le_right _ _) (min_le_right _ _))
      calc
        K₂ * r < K₂ * (gap / (2 * K₂)) := mul_lt_mul_of_pos_left hr_gap hK₂
        _ = gap / 2 := by
              field_simp [show (K₂ : ℝ) ≠ 0 by linarith]
        _ < gap := by linarith
    let zL : ℂ := (↑r : ℂ) * exp (↑(θ0 - r) * I)
    let zR : ℂ := (↑r : ℂ) * exp (↑(θ0 + r) * I)
    have hzL_norm : ‖zL‖ = r := by
      simpa [zL] using norm_ofReal_mul_exp_I r (θ0 - r) hr.1.le
    have hzR_norm : ‖zR‖ = r := by
      simpa [zR] using norm_ofReal_mul_exp_I r (θ0 + r) hr.1.le
    have hzL_delta : ‖zL‖ < δ₂ := by
      simpa [hzL_norm] using hr_delta
    have hzR_delta : ‖zR‖ < δ₂ := by
      simpa [hzR_norm] using hr_delta
    have hboundL := hφ₂ zL hzL_delta
    have hboundR := hφ₂ zR hzR_delta
    have hmainL :
        Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1)) =
          (-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin (p1 * r) := by
      simpa [zL, p1, θ0, oddDownArrowRadiusPhaseCenter] using
        (im_main_term_odd_down_left (p := n + d) (c := padePhiErrorConst n d) r r)
    have hmainR :
        Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1)) =
          -((-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin (p1 * r)) := by
      simpa [zR, p1, θ0, oddDownArrowRadiusPhaseCenter] using
        (im_main_term_odd_down_right (p := n + d) (c := padePhiErrorConst n d) r r)
    have him_rem_L :
        abs
          (Complex.im (padeR n d zL * exp (-zL)) -
            Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1) +
              (padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2))) ≤
          K₂ * r ^ (n + d + 3) := by
      have him_le :
          abs
            (Complex.im (padeR n d zL * exp (-zL)) -
              Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1) +
                (padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2))) ≤
            ‖padeR n d zL * exp (-zL) -
              ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1) +
                (padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2))‖ := by
        simpa using
          abs_im_sub_le_norm_sub
            (a := padeR n d zL * exp (-zL))
            (b := (1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1) +
              (padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2))
      have hboundL' :
          ‖padeR n d zL * exp (-zL) -
            ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1) +
              (padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2))‖ ≤
          K₂ * r ^ (n + d + 3) := by
        simpa [hzL_norm] using hboundL
      exact le_trans him_le hboundL'
    have him_rem_R :
        abs
          (Complex.im (padeR n d zR * exp (-zR)) -
            Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1) +
              (padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2))) ≤
          K₂ * r ^ (n + d + 3) := by
      have him_le :
          abs
            (Complex.im (padeR n d zR * exp (-zR)) -
              Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1) +
                (padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2))) ≤
            ‖padeR n d zR * exp (-zR) -
              ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1) +
                (padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2))‖ := by
        simpa using
          abs_im_sub_le_norm_sub
            (a := padeR n d zR * exp (-zR))
            (b := (1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1) +
              (padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2))
      have hboundR' :
          ‖padeR n d zR * exp (-zR) -
            ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1) +
              (padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2))‖ ≤
          K₂ * r ^ (n + d + 3) := by
        simpa [hzR_norm] using hboundR
      exact le_trans him_le hboundR'
    have him_C2_L :
        abs (Complex.im ((padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2))) ≤
          absC2 * r ^ (n + d + 2) := by
      calc
        abs (Complex.im ((padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2))) ≤
            ‖(padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2)‖ := Complex.abs_im_le_norm _
        _ = absC2 * r ^ (n + d + 2) := by
              rw [norm_mul, norm_pow, hzL_norm, Complex.norm_real]
              simp [absC2, Real.norm_eq_abs]
    have him_C2_R :
        abs (Complex.im ((padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2))) ≤
          absC2 * r ^ (n + d + 2) := by
      calc
        abs (Complex.im ((padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2))) ≤
            ‖(padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2)‖ := Complex.abs_im_le_norm _
        _ = absC2 * r ^ (n + d + 2) := by
              rw [norm_mul, norm_pow, hzR_norm, Complex.norm_real]
              simp [absC2, Real.norm_eq_abs]
    have himdiffL :
        abs
          (Complex.im (padeR n d zL * exp (-zL)) -
            Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1))) ≤
          absC2 * r ^ (n + d + 2) + K₂ * r ^ (n + d + 3) := by
      have him_approx2 :
          Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1) +
              (padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2)) =
            Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1)) +
              Complex.im ((padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2)) := by
        rw [Complex.add_im]
      have hsplit_im :
          Complex.im (padeR n d zL * exp (-zL)) -
              Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1)) =
            (Complex.im (padeR n d zL * exp (-zL)) -
                Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1) +
                  (padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2))) +
              Complex.im ((padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2)) := by
        rw [him_approx2]
        ring
      rw [hsplit_im]
      calc
        abs
            ((Complex.im (padeR n d zL * exp (-zL)) -
                  Complex.im
                    ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1) +
                      (padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2))) +
              Complex.im ((padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2))) ≤
          abs
              (Complex.im (padeR n d zL * exp (-zL)) -
                Complex.im
                  ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1) +
                    (padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2))) +
            abs (Complex.im ((padeRExpNegSecondCoeff n d : ℂ) * zL ^ (n + d + 2))) := by
              exact abs_add_le _ _
        _ ≤ K₂ * r ^ (n + d + 3) + absC2 * r ^ (n + d + 2) := by
              exact add_le_add him_rem_L him_C2_L
        _ = absC2 * r ^ (n + d + 2) + K₂ * r ^ (n + d + 3) := by ring
    have himdiffR :
        abs
          (Complex.im (padeR n d zR * exp (-zR)) -
            Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1))) ≤
          absC2 * r ^ (n + d + 2) + K₂ * r ^ (n + d + 3) := by
      have him_approx2 :
          Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1) +
              (padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2)) =
            Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1)) +
              Complex.im ((padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2)) := by
        rw [Complex.add_im]
      have hsplit_im :
          Complex.im (padeR n d zR * exp (-zR)) -
              Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1)) =
            (Complex.im (padeR n d zR * exp (-zR)) -
                Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1) +
                  (padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2))) +
              Complex.im ((padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2)) := by
        rw [him_approx2]
        ring
      rw [hsplit_im]
      calc
        abs
            ((Complex.im (padeR n d zR * exp (-zR)) -
                  Complex.im
                    ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1) +
                      (padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2))) +
              Complex.im ((padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2))) ≤
          abs
              (Complex.im (padeR n d zR * exp (-zR)) -
                Complex.im
                  ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1) +
                    (padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2))) +
            abs (Complex.im ((padeRExpNegSecondCoeff n d : ℂ) * zR ^ (n + d + 2))) := by
              exact abs_add_le _ _
        _ ≤ K₂ * r ^ (n + d + 3) + absC2 * r ^ (n + d + 2) := by
              exact add_le_add him_rem_R him_C2_R
        _ = absC2 * r ^ (n + d + 2) + K₂ * r ^ (n + d + 3) := by ring
    have hpow_pos : 0 < r ^ (n + d + 1) := pow_pos hr.1 _
    have hpow2_pos : 0 < r ^ (n + d + 2) := pow_pos hr.1 _
    have hmain_lower :
        padePhiErrorConst n d * p1 / 2 * r ^ (n + d + 2) <
          padePhiErrorConst n d * r ^ (n + d + 1) * Real.sin (p1 * r) := by
      rw [show r ^ (n + d + 2) = r * r ^ (n + d + 1) by rw [pow_succ']]
      rw [show padePhiErrorConst n d * p1 / 2 * (r * r ^ (n + d + 1)) =
          r ^ (n + d + 1) * (padePhiErrorConst n d * (p1 * r / 2)) by ring]
      rw [show padePhiErrorConst n d * r ^ (n + d + 1) * Real.sin (p1 * r) =
          r ^ (n + d + 1) * (padePhiErrorConst n d * Real.sin (p1 * r)) by ring]
      exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hhalf_lt_sin hC) hpow_pos
    have hcorr_small :
        absC2 * r ^ (n + d + 2) + K₂ * r ^ (n + d + 3) <
          padePhiErrorConst n d * p1 / 2 * r ^ (n + d + 2) := by
      have hlin :
          absC2 + K₂ * r < padePhiErrorConst n d * p1 / 2 := by
        dsimp [gap] at hgap_bound hgap_pos ⊢
        nlinarith
      have hrewrite :
          absC2 * r ^ (n + d + 2) + K₂ * r ^ (n + d + 3) =
            r ^ (n + d + 2) * (absC2 + K₂ * r) := by
        rw [show r ^ (n + d + 3) = r * r ^ (n + d + 2) by rw [pow_succ']]
        ring
      rw [hrewrite]
      have hmul :
          r ^ (n + d + 2) * (absC2 + K₂ * r) <
            r ^ (n + d + 2) * (padePhiErrorConst n d * p1 / 2) := by
        exact mul_lt_mul_of_pos_left hlin hpow2_pos
      have htarget :
          r ^ (n + d + 2) * (padePhiErrorConst n d * p1 / 2) =
            padePhiErrorConst n d * p1 / 2 * r ^ (n + d + 2) := by ring
      exact htarget ▸ hmul
    have hcorr_lt_main :
        absC2 * r ^ (n + d + 2) + K₂ * r ^ (n + d + 3) <
          -((-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin (p1 * r)) := by
      have hmain_lower' :
          padePhiErrorConst n d * p1 / 2 * r ^ (n + d + 2) <
            -((-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin (p1 * r)) := by
        simpa using hmain_lower
      exact lt_trans hcorr_small hmain_lower'
    have hleft_core :
        (-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin (p1 * r) +
          (absC2 * r ^ (n + d + 2) + K₂ * r ^ (n + d + 3)) < 0 := by
      linarith [hcorr_lt_main]
    have hright_core :
        0 < -((-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin (p1 * r)) -
          (absC2 * r ^ (n + d + 2) + K₂ * r ^ (n + d + 3)) := by
      linarith [hcorr_lt_main]
    have hleft_bound :
        Complex.im (padeR n d zL * exp (-zL)) ≤
          (-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin (p1 * r) +
            (absC2 * r ^ (n + d + 2) + K₂ * r ^ (n + d + 3)) := by
      have h' := abs_le.mp himdiffL
      linarith [hmainL]
    have hright_bound :
        -((-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin (p1 * r)) -
          (absC2 * r ^ (n + d + 2) + K₂ * r ^ (n + d + 3)) ≤
          Complex.im (padeR n d zR * exp (-zR)) := by
      have h' := abs_le.mp himdiffR
      linarith [hmainR]
    exact ⟨lt_of_le_of_lt hleft_bound hleft_core, lt_of_lt_of_le hright_core hright_bound⟩
  · have hnz : n = 0 := by omega
    have hdz : d = 0 := by omega
    subst hnz
    subst hdz
    refine ⟨1, by norm_num, ?_⟩
    intro r hr
    have hsinr_pos : 0 < Real.sin r := by
      apply Real.sin_pos_of_pos_of_lt_pi hr.1
      exact lt_trans hr.2 (by linarith [Real.pi_gt_three])
    have hsin_bound : Real.sin r ≤ 1 := by
      nlinarith [Real.sin_sq_add_cos_sq r, sq_nonneg (Real.cos r)]
    have hrsin_pos : 0 < r * Real.sin r := by
      exact mul_pos hr.1 hsinr_pos
    have hrsin_lt_pi : r * Real.sin r < Real.pi := by
      have hle : r * Real.sin r ≤ r := by
        nlinarith
      have hr_lt_pi : r < Real.pi := lt_trans hr.2 (by linarith [Real.pi_gt_three])
      exact lt_of_le_of_lt hle hr_lt_pi
    have hsin_pos2 : 0 < Real.sin (r * Real.sin r) :=
      Real.sin_pos_of_pos_of_lt_pi hrsin_pos hrsin_lt_pi
    have hexp_pos : 0 < Real.exp (r * Real.cos r) := Real.exp_pos _
    have hmul_pos : 0 < Real.exp (r * Real.cos r) * Real.sin (r * Real.sin r) :=
      mul_pos hexp_pos hsin_pos2
    refine ⟨?_, ?_⟩
    · rw [padeR00_oddDownArrowTrueSlice_left_im]
      linarith
    · rw [padeR00_oddDownArrowTrueSlice_right_im]
      exact hmul_pos

private theorem oddDownArrowRadiusPhaseSliceZero_of_pos_errorConst
    (n d : ℕ) (hC : 0 < padePhiErrorConst n d) :
    ∃ δ > 0,
      (∀ p ∈ oddDownArrowRadiusPhaseWedge δ,
        0 < Complex.re (oddDownArrowRadiusPhaseValue n d p)) ∧
      (∀ r ∈ Set.Icc (0 : ℝ) δ,
        ∃ s ∈ Set.Icc (-r) r,
          (r, s) ∈ oddDownArrowRadiusPhaseZeroSet n d δ) := by
  obtain ⟨δre, hδre, hre_small⟩ := padeR_exp_neg_re_pos_of_small_norm n d
  obtain ⟨δQ, hδQ, hQ⟩ := padeQ_nonzero_near_zero n d
  obtain ⟨δslice, hδslice, hendpoint⟩ :=
    oddDownArrowRadiusPhaseEndpointSigns_on_trueSlice_of_pos_errorConst n d hC
  let δ : ℝ := min (δre / 2) (min (δQ / 2) (δslice / 2))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (half_pos hδre) (lt_min (half_pos hδQ) (half_pos hδslice))
  have hδlt_re : δ < δre := by
    dsimp [δ]
    have hhalf : δre / 2 < δre := by
      linarith
    exact lt_of_le_of_lt (min_le_left _ _) hhalf
  have hδlt_Q : δ < δQ := by
    dsimp [δ]
    have hhalf : δQ / 2 < δQ := by
      linarith
    exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _)) hhalf
  have hre_wedge :
      ∀ p ∈ oddDownArrowRadiusPhaseWedge δ,
        0 < Complex.re (oddDownArrowRadiusPhaseValue n d p) :=
    oddDownArrowRadiusPhaseRe_pos_on_wedge_of_small_norm n d hre_small hδlt_re
  refine ⟨δ, hδ, hre_wedge, ?_⟩
  intro r hr
  rcases eq_or_lt_of_le hr.1 with rfl | hrpos
  · refine ⟨0, by simp, ?_⟩
    simpa using mem_oddDownArrowRadiusPhaseZeroSet_zero n d hδ.le
  · let θ0 : ℝ := oddDownArrowRadiusPhaseCenter n d
    have hrδQ : r < δQ := lt_of_le_of_lt hr.2 hδlt_Q
    have hr_slice : r ∈ Set.Ioo (0 : ℝ) δslice := by
      refine ⟨hrpos, ?_⟩
      have hδ_le_slice_half : δ ≤ δslice / 2 := by
        dsimp [δ]
        exact le_trans (min_le_right _ _) (min_le_right _ _)
      have hhalf : δslice / 2 < δslice := by
        linarith
      exact lt_of_le_of_lt hr.2 (lt_of_le_of_lt hδ_le_slice_half hhalf)
    have hcont_complex :
        ContinuousOn
          (fun s : ℝ =>
            padeR n d ((↑r : ℂ) * exp (↑(θ0 + s) * I)) *
              exp (-((↑r : ℂ) * exp (↑(θ0 + s) * I))))
          (Set.Icc (-r) r) :=
      padeR_exp_neg_continuousOn_angleArc n d θ0 r r δQ hrpos hrδQ hQ
    have him_cont : ContinuousOn (fun z : ℂ => Complex.im z) Set.univ :=
      Complex.continuous_im.continuousOn
    have hcont_im :
        ContinuousOn
          (fun s : ℝ =>
            Complex.im
              (padeR n d ((↑r : ℂ) * exp (↑(θ0 + s) * I)) *
                exp (-((↑r : ℂ) * exp (↑(θ0 + s) * I)))))
          (Set.Icc (-r) r) := by
      simpa [Function.comp] using
        (him_cont.comp hcont_complex (by
          intro x hx
          simp))
    have him_slice := hendpoint r hr_slice
    have him_left' :
        Complex.im
          (padeR n d ((↑r : ℂ) * exp (↑(θ0 - r) * I)) *
            exp (-((↑r : ℂ) * exp (↑(θ0 - r) * I)))) < 0 := by
      simpa [θ0, oddDownArrowRadiusPhaseCenter] using him_slice.1
    have him_right' :
        0 < Complex.im
            (padeR n d ((↑r : ℂ) * exp (↑(θ0 + r) * I)) *
              exp (-((↑r : ℂ) * exp (↑(θ0 + r) * I)))) := by
      simpa [θ0, oddDownArrowRadiusPhaseCenter] using him_slice.2
    have hzero_mem :
        (0 : ℝ) ∈ Set.Icc
          (Complex.im
            (padeR n d ((↑r : ℂ) * exp (↑(θ0 - r) * I)) *
              exp (-((↑r : ℂ) * exp (↑(θ0 - r) * I)))))
          (Complex.im
            (padeR n d ((↑r : ℂ) * exp (↑(θ0 + r) * I)) *
              exp (-((↑r : ℂ) * exp (↑(θ0 + r) * I))))) := by
      exact ⟨le_of_lt him_left', le_of_lt him_right'⟩
    have hpre : IsPreconnected (Set.Icc (-r) r) := by
      simpa using isPreconnected_Icc
    have himage :=
      hpre.intermediate_value
        (show -r ∈ Set.Icc (-r) r by simp [hrpos.le])
        (show r ∈ Set.Icc (-r) r by simp [hrpos.le])
        hcont_im
    rcases himage hzero_mem with ⟨s, hsIcc, hszero⟩
    have hsZero :
        oddDownArrowRadiusPhaseIm n d (r, s) = 0 := by
      simpa [oddDownArrowRadiusPhaseIm, oddDownArrowRadiusPhaseValue,
        oddDownArrowRadiusPhasePoint, oddDownArrowRadiusPhaseCenter, θ0] using hszero
    exact ⟨s, hsIcc, ⟨⟨hr, hsIcc⟩, hsZero⟩⟩

private theorem main_term_im_diff_bound_of_pos_errorConst
    (n d : ℕ) (hC : 0 < padePhiErrorConst n d)
    {ρ s₁ s₂ : ℝ} (hρ : 0 < ρ) (hρ_small : (↑(n + d) + 1 : ℝ) * ρ ≤ Real.pi / 3)
    (hs₁ : s₁ ∈ Set.Icc (-ρ) ρ) (hs₂ : s₂ ∈ Set.Icc (-ρ) ρ) (hlt : s₁ < s₂) :
    let θ₀ := oddDownArrowRadiusPhaseCenter n d
    let z₁ := (↑ρ : ℂ) * exp (↑(θ₀ + s₁) * I)
    let z₂ := (↑ρ : ℂ) * exp (↑(θ₀ + s₂) * I)
    Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * z₂ ^ (n + d + 1)) -
      Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * z₁ ^ (n + d + 1)) ≥
      padePhiErrorConst n d * ((↑(n + d) + 1 : ℝ)) *
        ρ ^ (n + d + 1) * (s₂ - s₁) / 2 := by
  let A : ℝ := (n + d + 1 : ℝ)
  have hmain₁ :
      Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) *
        (((↑ρ : ℂ) * exp (↑(oddDownArrowRadiusPhaseCenter n d + s₁) * I)) ^ (n + d + 1))) =
        padePhiErrorConst n d * ρ ^ (n + d + 1) * Real.sin (A * s₁) := by
    simpa [A, oddDownArrowRadiusPhaseCenter] using
      (im_main_term_odd_down_right (p := n + d) (c := padePhiErrorConst n d) ρ s₁)
  have hmain₂ :
      Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) *
        (((↑ρ : ℂ) * exp (↑(oddDownArrowRadiusPhaseCenter n d + s₂) * I)) ^ (n + d + 1))) =
        padePhiErrorConst n d * ρ ^ (n + d + 1) * Real.sin (A * s₂) := by
    simpa [A, oddDownArrowRadiusPhaseCenter] using
      (im_main_term_odd_down_right (p := n + d) (c := padePhiErrorConst n d) ρ s₂)
  have hρA : A * ρ ≤ Real.pi / 3 := by
    simpa [A] using hρ_small
  have hcont :
      ContinuousOn (fun x : ℝ => Real.sin (A * x)) (Set.Icc s₁ s₂) := by
    simpa [A, mul_comm] using
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hdiff :
      DifferentiableOn ℝ (fun x : ℝ => Real.sin (A * x)) (Set.Ioo s₁ s₂) := by
    intro x hx
    change DifferentiableWithinAt ℝ (fun y : ℝ => Real.sin (A * y)) (Set.Ioo s₁ s₂) x
    exact
      (((Real.hasDerivAt_sin (A * x)).comp x
        ((hasDerivAt_const x A).mul (hasDerivAt_id x))).differentiableAt.differentiableWithinAt)
  obtain ⟨c, hc, hcd⟩ :=
    exists_deriv_eq_slope (f := fun x : ℝ => Real.sin (A * x)) hlt hcont hdiff
  have hcIcc : c ∈ Set.Icc (-ρ) ρ := by
    refine ⟨?_, ?_⟩
    · linarith [hs₁.1, hs₂.1, hc.1, hc.2]
    · linarith [hs₁.2, hs₂.2, hc.1, hc.2]
  have hcmul_abs : |A * c| ≤ Real.pi / 3 := by
    calc
      |A * c| = A * |c| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ A * ρ := by
        gcongr
        exact abs_le.mpr hcIcc
      _ ≤ Real.pi / 3 := hρA
  have h_cos_bound : (1 / 2 : ℝ) ≤ Real.cos (A * c) :=
    cos_ge_half_of_abs_le' hcmul_abs
  have hderiv :
      deriv (fun x : ℝ => Real.sin (A * x)) c = A * Real.cos (A * c) := by
    simpa [A, mul_assoc, mul_left_comm, mul_comm] using
      (((Real.hasDerivAt_sin (A * c)).comp c
        ((hasDerivAt_const c A).mul (hasDerivAt_id c))).deriv)
  have hneq : s₂ - s₁ ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlt)
  have hratio :
      Real.sin (A * s₂) - Real.sin (A * s₁) =
        A * Real.cos (A * c) * (s₂ - s₁) := by
    rw [hderiv] at hcd
    field_simp [hneq] at hcd
    linarith
  have hsine_bound :
      A * (s₂ - s₁) / 2 ≤ Real.sin (A * s₂) - Real.sin (A * s₁) := by
    have hA_half : A / 2 ≤ A * Real.cos (A * c) := by
      have hA_nonneg : 0 ≤ A := by positivity
      nlinarith [h_cos_bound, hA_nonneg]
    have hdiff_nonneg : 0 ≤ s₂ - s₁ := le_of_lt (sub_pos.mpr hlt)
    calc
      A * (s₂ - s₁) / 2 = (A / 2) * (s₂ - s₁) := by ring
      _ ≤ (A * Real.cos (A * c)) * (s₂ - s₁) := by
        gcongr
      _ = Real.sin (A * s₂) - Real.sin (A * s₁) := by
        symm
        exact hratio
  have hfac_nonneg : 0 ≤ padePhiErrorConst n d * ρ ^ (n + d + 1) := by
    exact mul_nonneg hC.le (pow_nonneg hρ.le _)
  simpa [A] using
    (calc
      Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) *
          (((↑ρ : ℂ) * exp (↑(oddDownArrowRadiusPhaseCenter n d + s₂) * I)) ^ (n + d + 1))) -
        Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) *
          (((↑ρ : ℂ) * exp (↑(oddDownArrowRadiusPhaseCenter n d + s₁) * I)) ^ (n + d + 1)))
          = padePhiErrorConst n d * ρ ^ (n + d + 1) *
              (Real.sin (A * s₂) - Real.sin (A * s₁)) := by
                nlinarith [hmain₁, hmain₂]
      _ ≥ padePhiErrorConst n d * ρ ^ (n + d + 1) * (A * (s₂ - s₁) / 2) := by
        gcongr
      _ = padePhiErrorConst n d * A * ρ ^ (n + d + 1) * (s₂ - s₁) / 2 := by
        ring)

private theorem oddDownArrowRadiusPhaseFixedRadiusSlice_atMostOne_zero_of_pos_errorConst
    (n d : ℕ) (hC : 0 < padePhiErrorConst n d) :
    ∃ δmono > 0, ∀ ρ ∈ Set.Ioo (0 : ℝ) δmono,
      ∀ s₁ ∈ Set.Icc (-ρ) ρ,
      ∀ s₂ ∈ Set.Icc (-ρ) ρ,
          oddDownArrowRadiusPhaseIm n d (ρ, s₁) = 0 →
          oddDownArrowRadiusPhaseIm n d (ρ, s₂) = 0 →
          s₁ = s₂ := by
  obtain ⟨K, δ₀, hK₀, hδ₀₀, hφ⟩ := padeR_exp_neg_local_bound n d
  obtain ⟨δQ, hδQ₀, hQ⟩ := padeQ_nonzero_near_zero n d
  obtain ⟨δmono, hδmono_pos, hδmono⟩ :
      ∃ δmono > 0, ∀ ρ ∈ Set.Ioo (0 : ℝ) δmono,
        2 * ρ < δ₀ ∧ 2 * ρ < δQ ∧
        (n + d + 1 : ℝ) * ρ ≤ Real.pi / 3 ∧
        padePhiErrorConst n d * (n + d + 1 : ℝ) >
          4 * K * (2 ^ (n + d + 2) + 1) * ρ := by
    let a : ℝ := δ₀ / 2
    let b : ℝ := δQ / 2
    let c : ℝ := (Real.pi / 3) / (n + d + 1 : ℝ)
    let d' : ℝ :=
      (padePhiErrorConst n d * (n + d + 1 : ℝ)) /
        (4 * K * (2 ^ (n + d + 2) + 1))
    refine ⟨min a (min b (min c d')), ?_, ?_⟩
    · dsimp [a, b, c, d']
      refine lt_min (half_pos hδ₀₀) ?_
      refine lt_min (half_pos hδQ₀) ?_
      refine lt_min ?_ ?_
      · positivity
      · exact div_pos (by positivity [hC]) (by positivity)
    · intro ρ hρ
      have hρa : ρ < a := lt_of_lt_of_le hρ.2 (min_le_left _ _)
      have hρb : ρ < b := lt_of_lt_of_le hρ.2 (le_trans (min_le_right _ _) (min_le_left _ _))
      have hρc : ρ < c := lt_of_lt_of_le hρ.2
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
      have hρd : ρ < d' := lt_of_lt_of_le hρ.2
        (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
      refine ⟨?_, ?_, ?_, ?_⟩
      · dsimp [a] at hρa
        linarith
      · dsimp [b] at hρb
        linarith
      · dsimp [c] at hρc
        have hnd : 0 < (n + d + 1 : ℝ) := by positivity
        rw [lt_div_iff₀ hnd] at hρc
        linarith
      · dsimp [d'] at hρd
        have hden : 0 < 4 * K * (2 ^ (n + d + 2) + 1) := by positivity
        rw [lt_div_iff₀ hden] at hρd
        linarith
  refine ⟨δmono, hδmono_pos, ?_⟩
  intro ρ hρ s₁ hs₁ s₂ hs₂ hs₁_zero hs₂_zero
  by_cases h_eq : s₁ = s₂
  · exact h_eq
  have hρsmall' : (↑(n + d) + 1 : ℝ) * ρ ≤ Real.pi / 3 := by
    simpa using (hδmono ρ hρ).2.2.1
  have hcontra :
      ∀ {a b : ℝ}, a < b →
        a ∈ Set.Icc (-ρ) ρ →
        b ∈ Set.Icc (-ρ) ρ →
        oddDownArrowRadiusPhaseIm n d (ρ, a) = 0 →
        oddDownArrowRadiusPhaseIm n d (ρ, b) = 0 →
        False := by
    intro a b hab ha hb hza hzb
    have hmain :
        Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) *
            ((↑ρ : ℂ) * exp (↑(oddDownArrowRadiusPhaseCenter n d + b) * I)) ^ (n + d + 1)) -
          Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) *
            ((↑ρ : ℂ) * exp (↑(oddDownArrowRadiusPhaseCenter n d + a) * I)) ^ (n + d + 1)) ≥
          padePhiErrorConst n d * (↑(n + d) + 1 : ℝ) * ρ ^ (n + d + 1) * (b - a) / 2 := by
      simpa using
        main_term_im_diff_bound_of_pos_errorConst
          n d hC hρ.1 hρsmall' ha hb hab
    let z₁ : ℂ := (↑ρ : ℂ) * exp (↑(oddDownArrowRadiusPhaseCenter n d + a) * I)
    let z₂ : ℂ := (↑ρ : ℂ) * exp (↑(oddDownArrowRadiusPhaseCenter n d + b) * I)
    let M₁ : ℂ := (1 : ℂ) - (padePhiErrorConst n d : ℂ) * z₁ ^ (n + d + 1)
    let M₂ : ℂ := (1 : ℂ) - (padePhiErrorConst n d : ℂ) * z₂ ^ (n + d + 1)
    let E₁ : ℂ := padeR n d z₁ * exp (-z₁) - M₁
    let E₂ : ℂ := padeR n d z₂ * exp (-z₂) - M₂
    have herr :
        ‖E₂ - E₁‖ ≤
          K * (2 ^ (n + d + 2) + 1) * ρ ^ (n + d + 1) * ρ * |b - a| := by
      have hz₁mem : z₁ ∈ Metric.closedBall (0 : ℂ) ρ := by
        have hz₁norm : ‖z₁‖ = ρ := by
          simpa [z₁, oddDownArrowRadiusPhaseCenter] using
            norm_ofReal_mul_exp_I ρ (oddDownArrowRadiusPhaseCenter n d + a) hρ.1.le
        simpa [Metric.mem_closedBall, dist_eq_norm, hz₁norm]
      have hz₂mem : z₂ ∈ Metric.closedBall (0 : ℂ) ρ := by
        have hz₂norm : ‖z₂‖ = ρ := by
          simpa [z₂, oddDownArrowRadiusPhaseCenter] using
            norm_ofReal_mul_exp_I ρ (oddDownArrowRadiusPhaseCenter n d + b) hρ.1.le
        simpa [Metric.mem_closedBall, dist_eq_norm, hz₂norm]
      refine le_trans
        (error_lipschitz_on_ball_of_padeQ_ne_zero
          n d hK₀ hδ₀₀ hδQ₀ hρ.1 (hδmono ρ hρ).1 (hδmono ρ hρ).2.1 hQ hφ _ _
          hz₁mem hz₂mem)
        ?_
      have hcoeff_nonneg :
          0 ≤ K * (2 ^ (n + d + 2) + 1) * ρ ^ (n + d + 1) := by
        exact mul_nonneg (mul_nonneg hK₀.le (by positivity)) (pow_nonneg hρ.1.le _)
      refine le_trans
        (mul_le_mul_of_nonneg_left
          (arc_norm_sub_le_of_phase hρ.1.le)
          hcoeff_nonneg)
        ?_
      ring_nf
      gcongr
    have himerr :
        |Complex.im (E₂ - E₁)| ≤
          K * (2 ^ (n + d + 2) + 1) * ρ ^ (n + d + 1) * ρ * |b - a| := by
      have himle : |Complex.im (E₂ - E₁)| ≤ ‖E₂ - E₁‖ := by
        simpa using Complex.abs_im_le_norm (E₂ - E₁)
      exact le_trans himle herr
    have hz₁ : Complex.im (M₁ + E₁) = 0 := by
      simpa [z₁, M₁, E₁, oddDownArrowRadiusPhaseIm, oddDownArrowRadiusPhaseValue,
        oddDownArrowRadiusPhasePoint] using hza
    have hz₂ : Complex.im (M₂ + E₂) = 0 := by
      simpa [z₂, M₂, E₂, oddDownArrowRadiusPhaseIm, oddDownArrowRadiusPhaseValue,
        oddDownArrowRadiusPhasePoint] using hzb
    have hmain_eq : Complex.im M₂ - Complex.im M₁ = -(Complex.im (E₂ - E₁)) := by
      have hz₁' : Complex.im M₁ + Complex.im E₁ = 0 := by
        simpa using hz₁
      have hz₂' : Complex.im M₂ + Complex.im E₂ = 0 := by
        simpa using hz₂
      have himsub : Complex.im (E₂ - E₁) = Complex.im E₂ - Complex.im E₁ := by
        simp [sub_eq_add_neg]
      linarith
    have hmain_abs :
        |Complex.im M₂ - Complex.im M₁| ≤
          K * (2 ^ (n + d + 2) + 1) * ρ ^ (n + d + 1) * ρ * |b - a| := by
      rw [hmain_eq]
      rw [abs_neg]
      exact himerr
    have hsmall := (hδmono ρ hρ).2.2.2
    have hpow : 0 < ρ ^ (n + d + 1) := pow_pos hρ.1 _
    have hdist : 0 < b - a := sub_pos.mpr hab
    have hbound_pos :
        0 < K * (2 ^ (n + d + 2) + 1) * ρ ^ (n + d + 1) * ρ * |b - a| := by
      rw [abs_of_pos hdist]
      have htwo : 0 < (2 ^ (n + d + 2) + 1 : ℝ) := by positivity
      have hcoeff_pos : 0 < K * (2 ^ (n + d + 2) + 1 : ℝ) := by
        exact mul_pos hK₀ htwo
      exact mul_pos (mul_pos (mul_pos hcoeff_pos hpow) hρ.1) hdist
    have hsmall_mul :
        (padePhiErrorConst n d * (↑(n + d) + 1 : ℝ)) * (ρ ^ (n + d + 1) * (b - a)) >
          (4 * (K * (2 ^ (n + d + 2) + 1) * ρ)) * (ρ ^ (n + d + 1) * (b - a)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (mul_lt_mul_of_pos_right hsmall (mul_pos hpow hdist))
    have hlead_gt :
        K * (2 ^ (n + d + 2) + 1) * ρ ^ (n + d + 1) * ρ * |b - a| <
          padePhiErrorConst n d * (↑(n + d) + 1 : ℝ) * ρ ^ (n + d + 1) * (b - a) / 2 := by
      rw [abs_of_pos hdist]
      have htmp := hsmall_mul
      have hrew :
          (4 * (K * (2 ^ (n + d + 2) + 1) * ρ)) * (ρ ^ (n + d + 1) * (b - a)) =
            4 * (K * (2 ^ (n + d + 2) + 1) * ρ ^ (n + d + 1) * ρ * (b - a)) := by
        ring
      rw [hrew] at htmp
      let B : ℝ := K * (2 ^ (n + d + 2) + 1) * ρ ^ (n + d + 1) * ρ * (b - a)
      have hBpos : 0 < B := by
        simpa [B, abs_of_pos hdist] using hbound_pos
      have hBlt2B : B < 2 * B := by
        nlinarith [hBpos]
      have h2B : 2 * B <
          padePhiErrorConst n d * (↑(n + d) + 1 : ℝ) * ρ ^ (n + d + 1) * (b - a) / 2 := by
        dsimp [B] at htmp ⊢
        nlinarith [htmp]
      exact lt_trans hBlt2B h2B
    have hlead_pos :
        K * (2 ^ (n + d + 2) + 1) * ρ ^ (n + d + 1) * ρ * |b - a| <
          Complex.im M₂ - Complex.im M₁ := by
      exact lt_of_lt_of_le hlead_gt hmain
    have hmain_nonneg : 0 ≤ Complex.im M₂ - Complex.im M₁ := by
      exact le_of_lt (lt_trans hbound_pos hlead_pos)
    rw [abs_of_nonneg hmain_nonneg] at hmain_abs
    linarith
  rcases lt_or_gt_of_ne h_eq with hlt | hgt
  · exact False.elim (hcontra hlt hs₁ hs₂ hs₁_zero hs₂_zero)
  · exact False.elim (hcontra hgt hs₂ hs₁ hs₂_zero hs₁_zero)

private theorem oddDownArrowRadiusPhaseProjectionNoStop_of_pos_errorConst
    (n d : ℕ) (hC : 0 < padePhiErrorConst n d) :
    ∃ δ > 0,
      (∀ p ∈ oddDownArrowRadiusPhaseWedge δ,
        0 < Complex.re (oddDownArrowRadiusPhaseValue n d p)) ∧
      Set.Icc (0 : ℝ) δ ⊆
        Prod.fst '' connectedComponentIn (oddDownArrowRadiusPhaseZeroSet n d δ) (0, 0) := by
  obtain ⟨δ0, hδ0, hre_wedge0, hsliceZero0⟩ :=
    oddDownArrowRadiusPhaseSliceZero_of_pos_errorConst n d hC
  obtain ⟨δQ, hδQ, hQ⟩ := padeQ_nonzero_near_zero n d
  obtain ⟨δmono, hδmono, hatMostOne⟩ :=
    oddDownArrowRadiusPhaseFixedRadiusSlice_atMostOne_zero_of_pos_errorConst n d hC
  let δ : ℝ := min δ0 (min (δQ / 2) (δmono / 2))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hδ0 (lt_min (half_pos hδQ) (half_pos hδmono))
  have hδlt_Q : δ < δQ := by
    dsimp [δ]
    have hhalf : δQ / 2 < δQ := by linarith
    exact lt_of_le_of_lt
      (le_trans (min_le_right _ _) (min_le_left _ _))
      hhalf
  have hδlt_mono : δ < δmono := by
    dsimp [δ]
    have hhalf : δmono / 2 < δmono := by linarith
    exact lt_of_le_of_lt
      (le_trans (min_le_right _ _) (min_le_right _ _))
      hhalf
  have hre_wedge :
      ∀ p ∈ oddDownArrowRadiusPhaseWedge δ,
        0 < Complex.re (oddDownArrowRadiusPhaseValue n d p) := by
    intro p hpw
    exact hre_wedge0 p
      ⟨⟨hpw.1.1, le_trans hpw.1.2 (min_le_left _ _)⟩, hpw.2⟩
  have hsliceZero :
      ∀ r ∈ Set.Icc (0 : ℝ) δ,
        ∃ s ∈ Set.Icc (-r) r,
          (r, s) ∈ oddDownArrowRadiusPhaseZeroSet n d δ := by
    intro r hr
    rcases hsliceZero0 r ⟨hr.1, le_trans hr.2 (min_le_left _ _)⟩ with
      ⟨s, hs, hslice⟩
    refine ⟨s, hs, ?_⟩
    rcases hslice with ⟨_, hsIm⟩
    exact ⟨⟨hr, hs⟩, hsIm⟩
  have hprojClosed :
      IsClosed
        (Prod.fst '' connectedComponentIn (oddDownArrowRadiusPhaseZeroSet n d δ) (0, 0)) :=
    isClosed_fstImage_connectedComponentIn_oddDownArrowRadiusPhaseZeroSet
      n d hδ.le hQ hδlt_Q
  have hzero :
      (0, 0) ∈ oddDownArrowRadiusPhaseZeroSet n d δ :=
    mem_oddDownArrowRadiusPhaseZeroSet_zero n d hδ.le
  have hcompact :
      IsCompact (oddDownArrowRadiusPhaseZeroSet n d δ) :=
    isCompact_oddDownArrowRadiusPhaseZeroSet n d hQ hδlt_Q
  refine ⟨δ, hδ, hre_wedge, ?_⟩
  intro r hr
  by_contra hrmiss
  let K : Set (ℝ × ℝ) := oddDownArrowRadiusPhaseZeroSet n d δ
  let X := {p // p ∈ K}
  let x0 : X := ⟨(0, 0), hzero⟩
  rcases
      exists_clopen_separating_origin_from_radiusSlice_in_oddDownArrowRadiusPhaseZeroSet
        n d hδ.le hQ hδlt_Q hrmiss with
    ⟨C, hCclopen, hx0C, hsliceC⟩
  have hprojClosed' :
      IsClosed (Prod.fst '' connectedComponentIn K (0, 0)) := by
    simpa [K] using hprojClosed
  have hcompact' : IsCompact K := by
    simpa [K] using hcompact
  haveI : CompactSpace X := isCompact_iff_compactSpace.mp hcompact'
  have hx0C' : x0 ∈ C := hx0C (by simp [x0])
  have hcoordCont : Continuous fun p : X => p.1.1 :=
    continuous_fst.comp continuous_subtype_val
  let L : Set ℝ := (fun p : X => p.1.1) '' C
  let R : Set ℝ := (fun p : X => p.1.1) '' Cᶜ
  have hLclosed : IsClosed L := by
    have hCcompact : IsCompact C := hCclopen.isClosed.isCompact
    simpa [L] using (hCcompact.image hcoordCont).isClosed
  have hRclosed : IsClosed R := by
    have hRcompact : IsCompact Cᶜ := hCclopen.compl.isClosed.isCompact
    simpa [R] using (hRcompact.image hcoordCont).isClosed
  have h0L : (0 : ℝ) ∈ L := by
    exact ⟨x0, hx0C', rfl⟩
  have hprojSubsetL : Prod.fst '' connectedComponentIn K (0, 0) ⊆ L := by
    intro ρ hρ
    rcases hρ with ⟨p, hpconn, rfl⟩
    let xp : X := ⟨p, connectedComponentIn_subset _ _ hpconn⟩
    have hxp_conn : xp ∈ connectedComponent x0 := by
      have hpimg : p ∈ Subtype.val '' connectedComponent x0 := by
        simpa [K, x0, connectedComponentIn_eq_image hzero] using hpconn
      rcases hpimg with ⟨y, hy, hyval⟩
      have hy_eq : y = xp := by
        apply Subtype.ext
        simpa using hyval
      exact hy_eq ▸ hy
    exact ⟨xp, hCclopen.connectedComponent_subset hx0C' hxp_conn, rfl⟩
  have hrR : r ∈ R := by
    rcases hsliceZero r hr with ⟨s, hs, hslice⟩
    let xr : X := ⟨(r, s), hslice⟩
    have hxrC : xr ∈ Cᶜ := hsliceC (by
      change ((⟨(r, s), hslice⟩ : X).1.1 = r)
      simp)
    exact ⟨xr, hxrC, rfl⟩
  have hcover : Set.Icc (0 : ℝ) δ ⊆ L ∪ R := by
    intro ρ hρ
    rcases hsliceZero ρ hρ with ⟨s, hs, hslice⟩
    let xρ : X := ⟨(ρ, s), hslice⟩
    by_cases hxρC : xρ ∈ C
    · exact Or.inl ⟨xρ, hxρC, rfl⟩
    · exact Or.inr ⟨xρ, by simpa using hxρC, rfl⟩
  have hLR :
      (Set.Icc (0 : ℝ) δ ∩ (L ∩ R)).Nonempty := by
    have hpre : IsPreconnected (Set.Icc (0 : ℝ) δ) := isPreconnected_Icc
    refine (isPreconnected_closed_iff.mp hpre) L R hLclosed hRclosed hcover ?_ ?_
    · exact ⟨0, by simp [hδ.le, h0L]⟩
    · exact ⟨r, by exact ⟨hr, hrR⟩⟩
  rcases hLR with ⟨ρ, hρIcc, hρL, hρR⟩
  rcases hρL with ⟨xρL, hxρLC, hρeqL⟩
  rcases hρR with ⟨xρR, hxρRC, hρeqR⟩
  have hρpos : 0 < ρ := by
    by_contra hρnpos
    have hρzero : ρ = 0 := by
      linarith [hρIcc.1]
    have hxρR_snd_zero : xρR.1.2 = 0 := by
      rcases xρR.2 with ⟨hxρRw, _hxρRzero⟩
      have hsρR : xρR.1.2 ∈ Set.Icc (-ρ) ρ := by
        simpa [hρeqR] using hxρRw.2
      have hs0 : xρR.1.2 ∈ Set.Icc (0 : ℝ) 0 := by
        simpa [hρzero] using hsρR
      rcases hs0 with ⟨hs0_lo, hs0_hi⟩
      linarith
    have hxρR_eq_x0 : xρR = x0 := by
      apply Subtype.ext
      show xρR.1 = x0.1
      apply Prod.ext
      · simpa [x0, hρzero] using hρeqR
      · simpa [x0] using hxρR_snd_zero
    exact hxρRC (hxρR_eq_x0.symm ▸ hx0C')
  have hρsmall : ρ ∈ Set.Ioo (0 : ℝ) δmono := by
    exact ⟨hρpos, lt_of_le_of_lt hρIcc.2 hδlt_mono⟩
  exact
    oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both
      n d hρsmall hatMostOne C hCclopen xρL xρR hxρLC hxρRC hρeqL hρeqR

private theorem padeR_odd_upArrowConnectedRadiusPhaseZeroSet_of_pos_errorConst
    (n d : ℕ) (hC : 0 < padePhiErrorConst n d) :
    ∃ δ > 0, ∃ Z : Set (ℝ × ℝ),
      IsConnected Z ∧
        Z ⊆ {p : ℝ × ℝ |
          p.1 ∈ Set.Icc (0 : ℝ) δ ∧
            p.2 ∈ Set.Icc (-p.1) p.1 ∧
              let w : ℂ :=
                (↑p.1 : ℂ) *
                  exp (↑(Real.pi / ((↑(n + d) + 1) : ℝ) + p.2) * I)
              Complex.im (padeR n d w * exp (-w)) = 0 ∧
                0 < Complex.re (padeR n d w * exp (-w))} ∧
        Set.Icc (0 : ℝ) δ ⊆ Prod.fst '' Z := by
  obtain ⟨δ, hδ, hre_wedge, hproj⟩ :=
    oddDownArrowRadiusPhaseProjectionNoStop_of_pos_errorConst n d hC
  let Z : Set (ℝ × ℝ) := connectedComponentIn (oddDownArrowRadiusPhaseZeroSet n d δ) (0, 0)
  have hzero : (0, 0) ∈ oddDownArrowRadiusPhaseZeroSet n d δ :=
    mem_oddDownArrowRadiusPhaseZeroSet_zero n d hδ.le
  refine ⟨δ, hδ, Z, ?_, ?_, ?_⟩
  · exact isConnected_connectedComponentIn_iff.mpr hzero
  · intro p hpZ
    have hpK : p ∈ oddDownArrowRadiusPhaseZeroSet n d δ :=
      connectedComponentIn_subset _ _ hpZ
    rcases hpK with ⟨hpw, hpim⟩
    refine ⟨hpw.1, hpw.2, ?_, ?_⟩
    · simpa [oddDownArrowRadiusPhaseIm, oddDownArrowRadiusPhaseValue,
        oddDownArrowRadiusPhasePoint, oddDownArrowRadiusPhaseCenter] using hpim
    · simpa [oddDownArrowRadiusPhaseValue, oddDownArrowRadiusPhasePoint,
        oddDownArrowRadiusPhaseCenter] using hre_wedge p hpw
  · simpa [Z] using hproj

private theorem padeR_odd_upArrowSameComponentRadiusPhaseBound_of_pos_errorConst
    (n d : ℕ) (hC : 0 < padePhiErrorConst n d) :
    ∃ z0 ∈ orderWeb (padeR n d), ∃ δ > 0,
      ∀ r ∈ Set.Ioo (0 : ℝ) δ,
        ∃ z : ℂ,
          z ∈ connectedComponentIn (orderWeb (padeR n d)) z0 ∧
            ∃ s ∈ Set.Icc (-r) r,
              z =
                (↑r : ℂ) *
                  exp (↑(Real.pi / ((↑(n + d) + 1) : ℝ) + s) * I) := by
  obtain ⟨δ, hδ, Z, hZconn, hZsub, hZproj⟩ :=
    padeR_odd_upArrowConnectedRadiusPhaseZeroSet_of_pos_errorConst n d hC
  let θ0 : ℝ := Real.pi / ((↑(n + d) + 1) : ℝ)
  let f : ℝ × ℝ → ℂ := fun p =>
    (↑p.1 : ℂ) * exp (↑(θ0 + p.2) * I)
  let support : Set ℂ := f '' Z
  have hsupport_conn : IsConnected support := by
    refine hZconn.image f ?_
    exact Continuous.continuousOn (by
      continuity : Continuous f)
  have hsupport_web : support ⊆ orderWeb (padeR n d) := by
    intro z hz
    rcases hz with ⟨p, hpZ, rfl⟩
    rcases hZsub hpZ with ⟨_hp1, _hp2, him, hre⟩
    exact mem_orderWeb_of_im_zero_of_re_pos hre him
  have hzero_fst : (0 : ℝ) ∈ Prod.fst '' Z := by
    apply hZproj
    exact Set.left_mem_Icc.mpr hδ.le
  rcases hzero_fst with ⟨p0, hp0Z, hp0fst⟩
  have hp0r : p0.1 = 0 := by
    simpa using hp0fst
  have hzero_support : (0 : ℂ) ∈ support := by
    refine ⟨p0, hp0Z, ?_⟩
    simp [f, hp0r]
  have hsupport_comp :
      support ⊆ connectedComponentIn (orderWeb (padeR n d)) (0 : ℂ) :=
    hsupport_conn.2.subset_connectedComponentIn hzero_support hsupport_web
  refine ⟨0, padeR_mem_orderWeb_zero n d, δ, hδ, ?_⟩
  intro r hr
  have hr_mem : r ∈ Set.Icc (0 : ℝ) δ := ⟨le_of_lt hr.1, le_of_lt hr.2⟩
  rcases hZproj hr_mem with ⟨p, hpZ, hpfst⟩
  have hpr : p.1 = r := by
    simpa using hpfst
  rcases hZsub hpZ with ⟨_hp1, hp2, _him, _hre⟩
  refine ⟨f p, hsupport_comp ⟨p, hpZ, rfl⟩, p.2, ?_, ?_⟩
  · simpa [hpr] using hp2
  · simp [f, θ0, hpr]

private theorem padeR_odd_upArrowConnectedRayConeSupport_of_pos_errorConst
    (n d : ℕ) (hC : 0 < padePhiErrorConst n d) :
    Nonempty
      (PadeRConnectedRayConeOrderWebSupport n d
        (Real.pi / ((↑(n + d) + 1) : ℝ))) := by
  obtain ⟨z0, hz0, δ, hδ, hcomponent⟩ :=
    padeR_odd_upArrowSameComponentRadiusPhaseBound_of_pos_errorConst n d hC
  let θ0 : ℝ := Real.pi / ((↑(n + d) + 1) : ℝ)
  refine ⟨⟨connectedComponentIn (orderWeb (padeR n d)) z0,
    isConnected_connectedComponentIn_iff.mpr hz0,
    connectedComponentIn_subset _ _,
    ?_⟩⟩
  intro aperture haperture radius hradius
  let r : ℝ := min (δ / 2) (min (radius / 2) (aperture / 2))
  have hr_pos : 0 < r := by
    dsimp [r]
    exact lt_min (half_pos hδ) (lt_min (half_pos hradius) (half_pos haperture))
  have hr_lt_δ : r < δ := by
    dsimp [r]
    have hhalf : δ / 2 < δ := by
      linarith
    exact lt_of_le_of_lt (min_le_left _ _) hhalf
  have hr_lt_radius : r < radius := by
    dsimp [r]
    have hhalf : radius / 2 < radius := by
      linarith
    exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _)) hhalf
  have hr_lt_aperture : r < aperture := by
    dsimp [r]
    have hhalf : aperture / 2 < aperture := by
      linarith
    exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) hhalf
  rcases hcomponent r ⟨hr_pos, hr_lt_δ⟩ with
    ⟨z, hzcomp, s, hs, rfl⟩
  refine ⟨_, hzcomp, ?_⟩
  simpa [θ0] using
    exact_angle_arc_mem_rayConeNearOrigin θ0 aperture radius r r haperture
      ⟨hr_pos, hr_lt_radius⟩ hr_lt_aperture s hs

theorem padeR_odd_upArrowOrderWebSameComponentContinuation_of_pos_errorConst
    (n d : ℕ) (hC : 0 < padePhiErrorConst n d) :
    ∃ z0 ∈ orderWeb (padeR n d),
      ∀ aperture > 0, ∀ radius > 0,
        ∃ z : ℂ,
          z ∈ connectedComponentIn (orderWeb (padeR n d)) z0 ∧
            z ∈ rayConeNearOrigin
              (Real.pi / ((↑(n + d) + 1) : ℝ)) aperture radius := by
  obtain ⟨support⟩ :=
    padeR_odd_upArrowConnectedRayConeSupport_of_pos_errorConst n d hC
  obtain ⟨z0, hz0support, _hz0cone⟩ :=
    support.meets_rayConeNearOrigin 1 zero_lt_one 1 zero_lt_one
  have hz0 : z0 ∈ orderWeb (padeR n d) := support.support_subset_orderWeb hz0support
  have hsubset_comp :
      support.support ⊆ connectedComponentIn (orderWeb (padeR n d)) z0 :=
    support.support_connected.2.subset_connectedComponentIn
      hz0support support.support_subset_orderWeb
  refine ⟨z0, hz0, ?_⟩
  intro aperture haperture radius hradius
  obtain ⟨z, hzsupport, hzcone⟩ :=
    support.meets_rayConeNearOrigin aperture haperture radius hradius
  exact ⟨z, hsubset_comp hzsupport, hzcone⟩

theorem padeR_odd_upArrowOrderWebMeetsRayConeNearOriginInConnectedComponent_of_pos_errorConst
    (n d : ℕ) (hC : 0 < padePhiErrorConst n d) :
    PadeROrderWebMeetsRayConeNearOriginInConnectedComponent n d
      (Real.pi / ((↑(n + d) + 1) : ℝ)) := by
  rcases
      padeR_odd_upArrowOrderWebSameComponentContinuation_of_pos_errorConst n d hC with
    ⟨z0, hz0, hcontinue⟩
  refine ⟨z0, hz0, ?_⟩
  intro aperture haperture radius hradius
  rcases hcontinue aperture haperture radius hradius with ⟨z, hzcomp, hzcone⟩
  exact ⟨z, ⟨hzcomp, hzcone⟩⟩

theorem padeRUpArrowOrderWebConnectedComponentMeetInput_of_pos_errorConst
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hC : 0 < padePhiErrorConst n d) :
    PadeRUpArrowOrderWebConnectedComponentMeetInput n d data := by
  refine ⟨?_⟩
  intro _
  refine ⟨Real.pi / ((↑(n + d) + 1) : ℝ), ?_, ?_⟩
  · simpa using padeR_upArrowDir_of_pos_errorConst_oddAngle n d 0 hC
  · simpa using
      padeR_odd_upArrowOrderWebMeetsRayConeNearOriginInConnectedComponent_of_pos_errorConst
        n d hC

theorem padeRUpArrowConnectedRayConeSupportInput_of_pos_errorConst
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hC : 0 < padePhiErrorConst n d) :
    PadeRUpArrowConnectedRayConeSupportInput n d data := by
  exact
    (padeRUpArrowOrderWebConnectedComponentMeetInput_of_pos_errorConst n d data hC).toConnectedRayConeSupportInput

theorem padeRUpArrowRayTrackingSupportInput_of_pos_errorConst
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hC : 0 < padePhiErrorConst n d) :
    PadeRUpArrowRayTrackingSupportInput n d data := by
  exact
    (padeRUpArrowConnectedRayConeSupportInput_of_pos_errorConst n d data hC).toRayTrackingSupportInput

theorem padeRUpArrowBranchTrackingInput_of_pos_errorConst
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hC : 0 < padePhiErrorConst n d) :
    PadeRUpArrowBranchTrackingInput n d data := by
  exact
    (padeRUpArrowRayTrackingSupportInput_of_pos_errorConst n d data hC).toTrackingInput

/-- Exact remaining obstruction after the honest explicit-sign refactor:
to upgrade the weak raywise bridge below to the strict sign bridge, one still
has to exclude zero-cosine exact-ray arrows. -/
def PadeRDownArrowZeroCosExclusion (n d : ℕ) : Prop :=
  ∀ θ : ℝ, IsDownArrowDir (padeR n d) θ →
    padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) ≠ 0

/-- Up-arrow companion to `PadeRDownArrowZeroCosExclusion`. -/
def PadeRUpArrowZeroCosExclusion (n d : ℕ) : Prop :=
  ∀ θ : ℝ, IsUpArrowDir (padeR n d) θ →
    padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) ≠ 0

/-- Honest weakened bridge: a Padé down-arrow direction cannot have negative
leading cosine sign, because the live explicit-sign `> 1` cone feeder would
contradict the exact-ray `< 1` definition of `IsDownArrowDir`. The unresolved
boundary case is exactly zero cosine sign. -/
theorem padeR_nonneg_sign_of_downArrowDir
    (n d : ℕ) :
    ∀ θ : ℝ, IsDownArrowDir (padeR n d) θ →
      0 ≤ padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) := by
  intro θ hθ
  by_contra hneg
  have hneg' : padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) < 0 :=
    lt_of_not_ge hneg
  obtain ⟨aperture, haperture, radius, hradius, hplus⟩ :=
    padeR_local_plus_near_of_errorConst_cos_neg n d θ hneg'
  obtain ⟨ε, hε, hdown⟩ := hθ
  let t : ℝ := min (ε / 2) (radius / 2)
  have ht_mem_eps : t ∈ Set.Ioo (0 : ℝ) ε := by
    refine ⟨?_, ?_⟩
    · dsimp [t]
      exact lt_min (half_pos hε) (half_pos hradius)
    · dsimp [t]
      have hhalf : ε / 2 < ε := by linarith
      exact lt_of_le_of_lt (min_le_left _ _) hhalf
  have ht_mem_radius : t ∈ Set.Ioo (0 : ℝ) radius := by
    refine ⟨?_, ?_⟩
    · dsimp [t]
      exact lt_min (half_pos hε) (half_pos hradius)
    · dsimp [t]
      have hhalf : radius / 2 < radius := by linarith
      exact lt_of_le_of_lt (min_le_right _ _) hhalf
  let z : ℂ := (↑t : ℂ) * exp (↑θ * I)
  have hz_cone : z ∈ rayConeNearOrigin θ aperture radius := by
    simpa [z, t] using
      exact_ray_mem_rayConeNearOrigin θ aperture radius t haperture ht_mem_radius
  have hlt : ‖padeR n d z * exp (-z)‖ < 1 := by
    simpa [z, t] using hdown t ht_mem_eps
  have hgt : 1 < ‖padeR n d z * exp (-z)‖ := hplus z hz_cone
  linarith

/-- Up-arrow companion to `padeR_nonneg_sign_of_downArrowDir`. -/
theorem padeR_nonpos_sign_of_upArrowDir
    (n d : ℕ) :
    ∀ θ : ℝ, IsUpArrowDir (padeR n d) θ →
      padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) ≤ 0 := by
  intro θ hθ
  by_contra hpos
  have hpos' : 0 < padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) :=
    lt_of_not_ge hpos
  obtain ⟨aperture, haperture, radius, hradius, hminus⟩ :=
    padeR_local_minus_near_of_errorConst_cos_pos n d θ hpos'
  obtain ⟨ε, hε, hup⟩ := hθ
  let t : ℝ := min (ε / 2) (radius / 2)
  have ht_mem_eps : t ∈ Set.Ioo (0 : ℝ) ε := by
    refine ⟨?_, ?_⟩
    · dsimp [t]
      exact lt_min (half_pos hε) (half_pos hradius)
    · dsimp [t]
      have hhalf : ε / 2 < ε := by linarith
      exact lt_of_le_of_lt (min_le_left _ _) hhalf
  have ht_mem_radius : t ∈ Set.Ioo (0 : ℝ) radius := by
    refine ⟨?_, ?_⟩
    · dsimp [t]
      exact lt_min (half_pos hε) (half_pos hradius)
    · dsimp [t]
      have hhalf : radius / 2 < radius := by linarith
      exact lt_of_le_of_lt (min_le_right _ _) hhalf
  let z : ℂ := (↑t : ℂ) * exp (↑θ * I)
  have hz_cone : z ∈ rayConeNearOrigin θ aperture radius := by
    simpa [z, t] using
      exact_ray_mem_rayConeNearOrigin θ aperture radius t haperture ht_mem_radius
  have hgt : 1 < ‖padeR n d z * exp (-z)‖ := by
    simpa [z, t] using hup t ht_mem_eps
  have hlt : ‖padeR n d z * exp (-z)‖ < 1 := hminus z hz_cone
  linarith

private theorem padeR10_pi_div_four_radial_weight_hasDerivAt
    (t : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        (1 + Real.sqrt 2 * t + t ^ 2) * Real.exp (-(Real.sqrt 2 * t)))
      (-(Real.sqrt 2) * t ^ 2 * Real.exp (-(Real.sqrt 2 * t))) t := by
  have hf :
      HasDerivAt (fun t : ℝ => 1 + Real.sqrt 2 * t + t ^ 2)
        (Real.sqrt 2 + 2 * t) t := by
    have htmp :=
      (((hasDerivAt_const t 1).add ((hasDerivAt_id t).const_mul (Real.sqrt 2))).add
        ((hasDerivAt_id t).mul (hasDerivAt_id t)))
    convert htmp using 1
    · funext x
      simp [pow_two]
    · simp [two_mul]
  have hg :
      HasDerivAt (fun t : ℝ => Real.exp (-(Real.sqrt 2 * t)))
        (-(Real.sqrt 2) * Real.exp (-(Real.sqrt 2 * t))) t := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (show HasDerivAt (fun t : ℝ => Real.exp (-(Real.sqrt 2 * t)))
          (Real.exp (-(Real.sqrt 2 * t)) * (-(Real.sqrt 2))) t from
        (show HasDerivAt (fun t : ℝ => -(Real.sqrt 2 * t)) (-(Real.sqrt 2)) t from by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            ((hasDerivAt_id t).const_mul (Real.sqrt 2)).neg).exp)
  have hderiv :
      (Real.sqrt 2 + 2 * t) * Real.exp (-(Real.sqrt 2 * t)) +
        (1 + Real.sqrt 2 * t + t ^ 2) *
          (-(Real.sqrt 2) * Real.exp (-(Real.sqrt 2 * t))) =
      -(Real.sqrt 2) * t ^ 2 * Real.exp (-(Real.sqrt 2 * t)) := by
    have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]
    ring_nf
    rw [hsqrt]
    ring
  exact hderiv ▸ hf.mul hg

private theorem padeR10_pi_div_four_radial_weight_lt_one
    {t : ℝ} (ht : 0 < t) :
    (1 + Real.sqrt 2 * t + t ^ 2) * Real.exp (-(Real.sqrt 2 * t)) < 1 := by
  let f : ℝ → ℝ := fun t =>
    (1 + Real.sqrt 2 * t + t ^ 2) * Real.exp (-(Real.sqrt 2 * t))
  have hcont : ContinuousOn f (Set.Ici 0) := by
    fun_prop
  have hanti : StrictAntiOn f (Set.Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 0) hcont
    intro x hx
    have hx0 : 0 < x := by
      simpa using hx
    have hderiv :
        deriv f x = -(Real.sqrt 2) * x ^ 2 * Real.exp (-(Real.sqrt 2 * x)) := by
      simpa [f] using (padeR10_pi_div_four_radial_weight_hasDerivAt x).deriv
    rw [hderiv]
    have hpos :
        0 < Real.sqrt 2 * x ^ 2 * Real.exp (-(Real.sqrt 2 * x)) := by
      have hsqrt : 0 < Real.sqrt 2 := by positivity
      have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx0.ne'
      have hexp : 0 < Real.exp (-(Real.sqrt 2 * x)) := Real.exp_pos _
      positivity
    linarith
  have hlt : f t < f 0 := hanti (by simp) (by simpa using ht.le) ht
  simpa [f] using hlt

private theorem padeR10_pi_div_four_normSq
    (t : ℝ) :
    Complex.normSq
      (1 + ((↑t : ℂ) * exp (((Real.pi / 4 : ℝ) : ℂ) * I))) =
      1 + Real.sqrt 2 * t + t ^ 2 := by
  rw [Complex.normSq_apply]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp [Real.cos_pi_div_four, Real.sin_pi_div_four, pow_two]
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]
  ring_nf
  rw [hsqrt]
  ring

/-- The forward-Euler Padé witness already lies on the zero-cosine boundary. -/
theorem padeR10_pi_div_four_zeroCos :
    padePhiErrorConst 1 0 * Real.cos ((↑(1 + 0) + 1) * (Real.pi / 4)) = 0 := by
  norm_num [padePhiErrorConst]
  rw [show (2 : ℝ) * (Real.pi / 4) = Real.pi / 2 by ring]
  norm_num [Real.cos_pi_div_two]

/-- The exact ray `θ = π / 4` is nevertheless a live down-arrow direction for
`padeR 1 0 = 1 + z`, so the remaining strict bridge target is false already in
the forward-Euler case. -/
theorem padeR10_pi_div_four_isDownArrowDir :
    IsDownArrowDir (padeR 1 0) (Real.pi / 4) := by
  refine ⟨1, one_pos, ?_⟩
  intro t ht
  let z : ℂ := (↑t : ℂ) * exp (((Real.pi / 4 : ℝ) : ℂ) * I)
  have ht0 : 0 < t := ht.1
  have hsq_real :
      (1 + Real.sqrt 2 * t + t ^ 2) * Real.exp (-(Real.sqrt 2 * t)) < 1 :=
    padeR10_pi_div_four_radial_weight_lt_one ht0
  have hz_re : z.re = t * (Real.sqrt 2 / 2) := by
    dsimp [z]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp [Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hnorm : ‖(1 + z) * exp (-z)‖ = ‖1 + z‖ * Real.exp (-z.re) := by
    simpa using (orderStar_norm_eq (fun w : ℂ => 1 + w) z)
  have hnorm_sq_eq : ‖1 + z‖ ^ 2 = 1 + Real.sqrt 2 * t + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simpa [z] using padeR10_pi_div_four_normSq t
  have hexp_sq : (Real.exp (-z.re)) ^ 2 = Real.exp (-(Real.sqrt 2 * t)) := by
    rw [hz_re, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq : (‖1 + z‖ * Real.exp (-z.re)) ^ 2 < 1 := by
    calc
      (‖1 + z‖ * Real.exp (-z.re)) ^ 2 = ‖1 + z‖ ^ 2 * (Real.exp (-z.re)) ^ 2 := by
        ring
      _ = (1 + Real.sqrt 2 * t + t ^ 2) * (Real.exp (-z.re)) ^ 2 := by
        rw [hnorm_sq_eq]
      _ = (1 + Real.sqrt 2 * t + t ^ 2) * Real.exp (-(Real.sqrt 2 * t)) := by
        rw [hexp_sq]
      _ < 1 := hsq_real
  have hmain : ‖1 + z‖ * Real.exp (-z.re) < 1 := by
    have hnonneg : 0 ≤ ‖1 + z‖ * Real.exp (-z.re) := by positivity
    nlinarith
  calc
    ‖padeR 1 0 z * exp (-z)‖ = ‖(1 + z) * exp (-z)‖ := by
      simp [z, padeR, padeP_zero_right, padeQ_zero_right, expTaylor_one]
    _ = ‖1 + z‖ * Real.exp (-z.re) := hnorm
    _ < 1 := hmain

theorem not_padeRDownArrowZeroCosExclusion_one_zero :
    ¬ PadeRDownArrowZeroCosExclusion 1 0 := by
  intro hzero
  have hne := hzero (Real.pi / 4) padeR10_pi_div_four_isDownArrowDir
  have hzero' := padeR10_pi_div_four_zeroCos
  norm_num at hne hzero' ⊢
  rcases hzero' with hC | hcos
  · exact hne.1 hC
  · exact hne.2 hcos

theorem not_padeRDownArrowSignBridge_one_zero :
    ¬ PadeRDownArrowSignBridge 1 0 := by
  intro hbridge
  have hpos := hbridge (Real.pi / 4) padeR10_pi_div_four_isDownArrowDir
  have hzero' := padeR10_pi_div_four_zeroCos
  norm_num at hpos hzero' ⊢
  rcases hzero' with hC | hcos
  · have hnot : ¬ 0 < padePhiErrorConst 1 0 * Real.cos (2 * (Real.pi / 4)) := by
      simp [hC]
    exact hnot hpos
  · have hnot : ¬ 0 < padePhiErrorConst 1 0 * Real.cos (2 * (Real.pi / 4)) := by
      simp [hcos]
    exact hnot hpos

private theorem padeR10_three_pi_div_four_radial_weight_hasDerivAt
    (t : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        (1 - Real.sqrt 2 * t + t ^ 2) * Real.exp (Real.sqrt 2 * t))
      (Real.sqrt 2 * t ^ 2 * Real.exp (Real.sqrt 2 * t)) t := by
  have hf :
      HasDerivAt (fun t : ℝ => 1 - Real.sqrt 2 * t + t ^ 2)
        (-Real.sqrt 2 + 2 * t) t := by
    have htmp :=
      (((hasDerivAt_const t 1).sub ((hasDerivAt_id t).const_mul (Real.sqrt 2))).add
        ((hasDerivAt_id t).mul (hasDerivAt_id t)))
    convert htmp using 1
    · funext x
      simp [pow_two]
    · simp [two_mul]
  have hg :
      HasDerivAt (fun t : ℝ => Real.exp (Real.sqrt 2 * t))
        (Real.sqrt 2 * Real.exp (Real.sqrt 2 * t)) t := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (show HasDerivAt (fun t : ℝ => Real.exp (Real.sqrt 2 * t))
          (Real.exp (Real.sqrt 2 * t) * Real.sqrt 2) t from
        (show HasDerivAt (fun t : ℝ => Real.sqrt 2 * t) (Real.sqrt 2) t from by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (hasDerivAt_id t).const_mul (Real.sqrt 2)).exp)
  have hderiv :
      (-Real.sqrt 2 + 2 * t) * Real.exp (Real.sqrt 2 * t) +
        (1 - Real.sqrt 2 * t + t ^ 2) *
          (Real.sqrt 2 * Real.exp (Real.sqrt 2 * t)) =
      Real.sqrt 2 * t ^ 2 * Real.exp (Real.sqrt 2 * t) := by
    have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]
    ring_nf
    rw [hsqrt]
    ring
  exact hderiv ▸ hf.mul hg

private theorem padeR10_three_pi_div_four_radial_weight_gt_one
    {t : ℝ} (ht : 0 < t) :
    1 < (1 - Real.sqrt 2 * t + t ^ 2) * Real.exp (Real.sqrt 2 * t) := by
  let f : ℝ → ℝ := fun t =>
    (1 - Real.sqrt 2 * t + t ^ 2) * Real.exp (Real.sqrt 2 * t)
  have hcont : ContinuousOn f (Set.Ici 0) := by
    fun_prop
  have hmono : StrictMonoOn f (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hcont
    intro x hx
    have hx0 : 0 < x := by
      simpa using hx
    have hderiv :
        deriv f x = Real.sqrt 2 * x ^ 2 * Real.exp (Real.sqrt 2 * x) := by
      simpa [f] using (padeR10_three_pi_div_four_radial_weight_hasDerivAt x).deriv
    rw [hderiv]
    have hsqrt : 0 < Real.sqrt 2 := by positivity
    have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx0.ne'
    have hexp : 0 < Real.exp (Real.sqrt 2 * x) := Real.exp_pos _
    positivity
  have hgt : f 0 < f t := by
    exact hmono (by simp) (by simpa using ht.le) ht
  simpa [f] using hgt

private theorem padeR10_three_pi_div_four_normSq
    (t : ℝ) :
    Complex.normSq
      (1 + ((↑t : ℂ) * exp ((((3 * Real.pi / 4 : ℝ)) : ℂ) * I))) =
      1 - Real.sqrt 2 * t + t ^ 2 := by
  rw [Complex.normSq_apply]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hcos : Real.cos (3 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
    rw [show (3 : ℝ) * Real.pi / 4 = Real.pi / 2 + Real.pi / 4 by ring]
    have : Real.cos (Real.pi / 2 + Real.pi / 4) = -(Real.sqrt 2 / 2) := by
      simp [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two,
        Real.cos_pi_div_four, Real.sin_pi_div_four]
    exact this
  have hsin : Real.sin (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
    rw [show (3 : ℝ) * Real.pi / 4 = Real.pi / 2 + Real.pi / 4 by ring]
    simp [Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
  simp [hcos, hsin, pow_two]
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]
  ring_nf
  rw [hsqrt]
  ring

/-- The forward-Euler Padé up-arrow witness also lies on a zero-cosine exact
ray. -/
theorem padeR10_three_pi_div_four_zeroCos :
    padePhiErrorConst 1 0 * Real.cos ((↑(1 + 0) + 1) * (3 * Real.pi / 4)) = 0 := by
  norm_num [padePhiErrorConst]
  rw [show (2 : ℝ) * (3 * Real.pi / 4) = 3 * Real.pi / 2 by ring]
  rw [show (3 : ℝ) * Real.pi / 2 = Real.pi + Real.pi / 2 by ring]
  simp [Real.cos_add, Real.cos_pi_div_two]

/-- The exact ray `θ = 3π / 4` is a live up-arrow direction for
`padeR 1 0 = 1 + z`, so the global up-arrow zero-cos / strict-sign bridge
fails already in the forward-Euler case. -/
theorem padeR10_three_pi_div_four_isUpArrowDir :
    IsUpArrowDir (padeR 1 0) (3 * Real.pi / 4) := by
  refine ⟨1, one_pos, ?_⟩
  intro t ht
  let z : ℂ := (↑t : ℂ) * exp ((((3 * Real.pi / 4 : ℝ)) : ℂ) * I)
  have ht0 : 0 < t := ht.1
  have hsq_real :
      1 < (1 - Real.sqrt 2 * t + t ^ 2) * Real.exp (Real.sqrt 2 * t) := by
    simpa using padeR10_three_pi_div_four_radial_weight_gt_one ht0
  have hz_re : z.re = t * (-(Real.sqrt 2 / 2)) := by
    dsimp [z]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hcos : Real.cos (3 * Real.pi / 4) = -(Real.sqrt 2 / 2) := by
      rw [show (3 : ℝ) * Real.pi / 4 = Real.pi / 2 + Real.pi / 4 by ring]
      have : Real.cos (Real.pi / 2 + Real.pi / 4) = -(Real.sqrt 2 / 2) := by
        simp [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two,
          Real.cos_pi_div_four, Real.sin_pi_div_four]
      exact this
    have hsin : Real.sin (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [show (3 : ℝ) * Real.pi / 4 = Real.pi / 2 + Real.pi / 4 by ring]
      simp [Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two,
        Real.cos_pi_div_four, Real.sin_pi_div_four]
    simp [hcos, hsin]
  have hnorm : ‖(1 + z) * exp (-z)‖ = ‖1 + z‖ * Real.exp (-z.re) := by
    simpa using (orderStar_norm_eq (fun w : ℂ => 1 + w) z)
  have hnorm_sq_eq : ‖1 + z‖ ^ 2 = 1 - Real.sqrt 2 * t + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simpa [z] using padeR10_three_pi_div_four_normSq t
  have hexp_sq : (Real.exp (-z.re)) ^ 2 = Real.exp (Real.sqrt 2 * t) := by
    rw [hz_re, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq : 1 < (‖1 + z‖ * Real.exp (-z.re)) ^ 2 := by
    calc
      (‖1 + z‖ * Real.exp (-z.re)) ^ 2 = ‖1 + z‖ ^ 2 * (Real.exp (-z.re)) ^ 2 := by
        ring
      _ = (1 - Real.sqrt 2 * t + t ^ 2) * (Real.exp (-z.re)) ^ 2 := by
        rw [hnorm_sq_eq]
      _ = (1 - Real.sqrt 2 * t + t ^ 2) * Real.exp (Real.sqrt 2 * t) := by
        rw [hexp_sq]
      _ > 1 := hsq_real
  have hmain : 1 < ‖1 + z‖ * Real.exp (-z.re) := by
    have hnonneg : 0 ≤ ‖1 + z‖ * Real.exp (-z.re) := by positivity
    nlinarith
  calc
    1 < ‖1 + z‖ * Real.exp (-z.re) := hmain
    _ = ‖(1 + z) * exp (-z)‖ := by rw [hnorm]
    _ = ‖padeR 1 0 z * exp (-z)‖ := by
      simp [z, padeR, padeP_zero_right, padeQ_zero_right, expTaylor_one]

theorem not_padeRUpArrowZeroCosExclusion_one_zero :
    ¬ PadeRUpArrowZeroCosExclusion 1 0 := by
  intro hzero
  have hne := hzero (3 * Real.pi / 4) padeR10_three_pi_div_four_isUpArrowDir
  have hzero' := padeR10_three_pi_div_four_zeroCos
  norm_num at hne hzero' ⊢
  rcases hzero' with hC | hcos
  · exact hne.1 hC
  · exact hne.2 hcos

theorem not_padeRUpArrowSignBridge_one_zero :
    ¬ PadeRUpArrowSignBridge 1 0 := by
  intro hbridge
  have hneg := hbridge (3 * Real.pi / 4) padeR10_three_pi_div_four_isUpArrowDir
  have hzero' := padeR10_three_pi_div_four_zeroCos
  norm_num at hneg hzero' ⊢
  rcases hzero' with hC | hcos
  · have hnot : ¬ padePhiErrorConst 1 0 * Real.cos (2 * (3 * Real.pi / 4)) < 0 := by
      simp [hC]
    exact hnot hneg
  · have hnot : ¬ padePhiErrorConst 1 0 * Real.cos (2 * (3 * Real.pi / 4)) < 0 := by
      simp [hcos]
    exact hnot hneg

/-- The strict down-arrow sign bridge now reduces to the single remaining
zero-cosine exclusion input. -/
theorem padeR_downArrowSignBridge_of_zeroCosExclusion
    {n d : ℕ}
    (hzero : PadeRDownArrowZeroCosExclusion n d) :
    PadeRDownArrowSignBridge n d := by
  intro θ hθ
  have hnonneg := padeR_nonneg_sign_of_downArrowDir n d θ hθ
  have hne : padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) ≠ 0 :=
    hzero θ hθ
  exact lt_of_le_of_ne hnonneg hne.symm

/-- Up-arrow companion to `padeR_downArrowSignBridge_of_zeroCosExclusion`. -/
theorem padeR_upArrowSignBridge_of_zeroCosExclusion
    {n d : ℕ}
    (hzero : PadeRUpArrowZeroCosExclusion n d) :
    PadeRUpArrowSignBridge n d := by
  intro θ hθ
  have hnonpos := padeR_nonpos_sign_of_upArrowDir n d θ hθ
  have hne : padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) ≠ 0 :=
    hzero θ hθ
  exact lt_of_le_of_ne hnonpos hne
