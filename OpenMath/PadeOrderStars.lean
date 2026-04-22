import OpenMath.Pade
import OpenMath.PadeAsymptotics
import OpenMath.OrderStars

open Complex

theorem padeQ_ne_zero_of_mem_orderWeb
    {n d : ℕ} {z : ℂ}
    (hz : z ∈ orderWeb (padeR n d)) :
    padeQ n d z ≠ 0 := by
  rcases hz with ⟨r, hrpos, hr_eq⟩
  intro hq
  have hr_zero : (r : ℂ) = 0 := by
    calc
      (r : ℂ) = padeR n d z * exp (-z) := hr_eq.symm
      _ = 0 := by simp [padeR, hq]
  have hr_zero' : r = 0 := by
    simpa using congrArg Complex.re hr_zero
  linarith

theorem padeR_norm_exp_neg_continuousOn_orderWeb
    (n d : ℕ) :
    ContinuousOn (fun z => ‖padeR n d z * exp (-z)‖)
      (orderWeb (padeR n d)) := by
  have hp : Continuous (padeP n d) := by
    unfold padeP
    fun_prop
  have hq : Continuous (padeQ n d) := padeQ_continuous n d
  have hR : ContinuousOn (padeR n d) (orderWeb (padeR n d)) := by
    simpa [padeR] using hp.continuousOn.div hq.continuousOn
      (fun z hz => padeQ_ne_zero_of_mem_orderWeb hz)
  have hexp : Continuous (fun z : ℂ => exp (-z)) := by
    fun_prop
  simpa using (hR.mul hexp.continuousOn).norm

/-- Concrete Padé feeder from the new local asymptotic bound into the even-angle,
positive-error-constant cone lemma from `OrderStars`. -/
theorem padeR_local_minus_near_even_angle_of_pos_errorConst
    (n d k : ℕ) (hC : 0 < padePhiErrorConst n d) :
    ∃ aperture > 0, ∃ radius > 0,
      ∀ z : ℂ, z ∈ rayConeNearOrigin (2 * ↑k * Real.pi / (↑(n + d) + 1)) aperture radius →
        ‖padeR n d z * exp (-z)‖ < 1 := by
  obtain ⟨K, δ₀, hK, hδ, hφ⟩ := padeR_exp_neg_local_bound n d
  exact
    local_minus_near_even_angle_of_pos_errorConst
      (R := padeR n d) (p := n + d) (k := k)
      (C := padePhiErrorConst n d) K δ₀ hC hK hδ hφ

/-- Padé companion to the even-angle, negative-error-constant cone lemma from
`OrderStars`. -/
theorem padeR_local_plus_near_even_angle_of_neg_errorConst
    (n d k : ℕ) (hC : padePhiErrorConst n d < 0) :
    ∃ aperture > 0, ∃ radius > 0,
      ∀ z : ℂ, z ∈ rayConeNearOrigin (2 * ↑k * Real.pi / (↑(n + d) + 1)) aperture radius →
        1 < ‖padeR n d z * exp (-z)‖ := by
  obtain ⟨K, δ₀, hK, hδ, hφ⟩ := padeR_exp_neg_local_bound n d
  exact
    local_plus_near_even_angle_of_neg_errorConst
      (R := padeR n d) (p := n + d) (k := k)
      (C := padePhiErrorConst n d) K δ₀ hC hK hδ hφ

theorem padeR_local_minus_near_of_errorConst_cos_pos
    (n d : ℕ) (θ : ℝ)
    (hsign : 0 < padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ)) :
    ∃ aperture > 0, ∃ radius > 0,
      ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius ->
        ‖padeR n d z * exp (-z)‖ < 1 := by
  obtain ⟨K, δ₀, hK, hδ, hφ⟩ := padeR_exp_neg_local_bound n d
  have hsign' : 0 < padePhiErrorConst n d * Real.cos ((↑(n + d + 1) : ℝ) * θ) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using hsign
  exact
    local_minus_near_of_errorConst_cos_pos
      (R := padeR n d) (p := n + d) (θ := θ)
      (C := padePhiErrorConst n d) K δ₀ hsign' hK.le hδ hφ

theorem padeR_local_plus_near_of_errorConst_cos_neg
    (n d : ℕ) (θ : ℝ)
    (hsign : padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) < 0) :
    ∃ aperture > 0, ∃ radius > 0,
      ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius ->
        1 < ‖padeR n d z * exp (-z)‖ := by
  obtain ⟨K, δ₀, hK, hδ, hφ⟩ := padeR_exp_neg_local_bound n d
  have hsign' : padePhiErrorConst n d * Real.cos ((↑(n + d + 1) : ℝ) * θ) < 0 := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using hsign
  exact
    local_plus_near_of_errorConst_cos_neg
      (R := padeR n d) (p := n + d) (θ := θ)
      (C := padePhiErrorConst n d) K δ₀ hsign' hK.le hδ hφ

private theorem padePhiErrorConst_pos_of_even
    (n d : ℕ) (hd : Even d) :
    0 < padePhiErrorConst n d := by
  rcases hd with ⟨k, rfl⟩
  have hpow : ((-1 : ℝ) ^ (k + k)) = 1 := by
    rw [← two_mul, pow_mul]
    norm_num
  rw [padePhiErrorConst, hpow]
  positivity

private theorem padePhiErrorConst_neg_of_odd
    (n d : ℕ) (hd : Odd d) :
    padePhiErrorConst n d < 0 := by
  rcases hd with ⟨k, rfl⟩
  have hpow : ((-1 : ℝ) ^ (2 * k + 1)) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [padePhiErrorConst, hpow]
  set A : ℝ := ((n.factorial : ℝ) * ((2 * k + 1).factorial : ℝ)) /
      (((n + (2 * k + 1)).factorial : ℝ) * ((n + (2 * k + 1) + 1).factorial : ℝ))
  have hpos : 0 < A := by
    dsimp [A]
    positivity
  have hrewrite : (-1 : ℝ) * ((n.factorial : ℝ) * ((2 * k + 1).factorial : ℝ)) /
      (((n + (2 * k + 1)).factorial : ℝ) * ((n + (2 * k + 1) + 1).factorial : ℝ)) = -A := by
    dsimp [A]
    ring
  rw [hrewrite]
  exact neg_neg_of_pos hpos

theorem padeR_downArrowDir_of_pos_errorConst
    (n d k : ℕ) (hC : 0 < padePhiErrorConst n d) :
    IsDownArrowDir (padeR n d) (2 * ↑k * Real.pi / (↑(n + d) + 1)) := by
  obtain ⟨K, δ₀, hK, hδ, hφ⟩ := padeR_exp_neg_local_bound n d
  simpa using
    (arrow_down_of_pos_errorConst
      (R := padeR n d) (p := n + d) (C := padePhiErrorConst n d)
      K δ₀ hC hK hδ hφ k)

theorem padeR_downArrowDir_of_neg_errorConst_oddAngle
    (n d k : ℕ) (hC : padePhiErrorConst n d < 0) :
    IsDownArrowDir (padeR n d) ((2 * ↑k + 1) * Real.pi / (↑(n + d) + 1)) := by
  obtain ⟨K, δ₀, hK, hδ, hφ⟩ := padeR_exp_neg_local_bound n d
  simpa using
    (arrow_down_of_neg_errorConst_odd
      (R := padeR n d) (p := n + d) (C := padePhiErrorConst n d)
      K δ₀ hC hK hδ hφ k)

theorem padeR_exists_downArrowDir
    (n d : ℕ) :
    ∃ θ : ℝ, IsDownArrowDir (padeR n d) θ := by
  rcases Nat.even_or_odd d with hd | hd
  · refine ⟨2 * (↑(0 : ℕ) : ℝ) * Real.pi / (↑(n + d) + 1), ?_⟩
    simpa using padeR_downArrowDir_of_pos_errorConst n d 0
      (padePhiErrorConst_pos_of_even n d hd)
  · refine ⟨(2 * (↑(0 : ℕ) : ℝ) + 1) * Real.pi / (↑(n + d) + 1), ?_⟩
    simpa using padeR_downArrowDir_of_neg_errorConst_oddAngle n d 0
      (padePhiErrorConst_neg_of_odd n d hd)

theorem padeR_upArrowDir_of_neg_errorConst
    (n d k : ℕ) (hC : padePhiErrorConst n d < 0) :
    IsUpArrowDir (padeR n d) (2 * ↑k * Real.pi / (↑(n + d) + 1)) := by
  obtain ⟨K, δ₀, hK, hδ, hφ⟩ := padeR_exp_neg_local_bound n d
  simpa using
    (arrow_up_of_neg_errorConst
      (R := padeR n d) (p := n + d) (C := padePhiErrorConst n d)
      K δ₀ hC hK hδ hφ k)

theorem padeR_upArrowDir_of_pos_errorConst_oddAngle
    (n d k : ℕ) (hC : 0 < padePhiErrorConst n d) :
    IsUpArrowDir (padeR n d) ((2 * ↑k + 1) * Real.pi / (↑(n + d) + 1)) := by
  obtain ⟨K, δ₀, hK, hδ, hφ⟩ := padeR_exp_neg_local_bound n d
  simpa using
    (arrow_up_of_pos_errorConst_odd
      (R := padeR n d) (p := n + d) (C := padePhiErrorConst n d)
      K δ₀ hC hK hδ hφ k)

theorem padeR_exists_upArrowDir
    (n d : ℕ) :
    ∃ θ : ℝ, IsUpArrowDir (padeR n d) θ := by
  rcases Nat.even_or_odd d with hd | hd
  · refine ⟨(2 * (↑(0 : ℕ) : ℝ) + 1) * Real.pi / (↑(n + d) + 1), ?_⟩
    simpa using padeR_upArrowDir_of_pos_errorConst_oddAngle n d 0
      (padePhiErrorConst_pos_of_even n d hd)
  · refine ⟨2 * (↑(0 : ℕ) : ℝ) * Real.pi / (↑(n + d) + 1), ?_⟩
    simpa using padeR_upArrowDir_of_neg_errorConst n d 0
      (padePhiErrorConst_neg_of_odd n d hd)

abbrev PadeRRealizedDownArrowInfinityWitnessFamily
    (n d : ℕ) (data : OrderArrowTerminationData) :=
  ∀ _ : Fin data.downArrowsAtInfinity,
    RealizedDownArrowInfinityBranch (padeR n d)

/-- The first genuinely missing down-arrow realization ingredient is not an
escaping witness but a concrete global branch that actually tracks the local
Padé down-arrow ray near the origin. This is strictly weaker than a full
`RealizedDownArrowInfinityBranch`, which still needs the separate far-field
escape input. -/
abbrev PadeRTrackedDownArrowBranch (n d : ℕ) :=
  { branch : GlobalDownArrowBranch (padeR n d) //
      BranchTracksRayNearOrigin
        branch.toGlobalOrderArrowBranch branch.tangentAngle }

/-- Raw order-web cone-meeting property around a fixed ray near the origin.
This isolates the first genuinely analytic statement still missing from the
current Padé down-arrow support seam. -/
def PadeROrderWebMeetsRayConeNearOrigin
    (n d : ℕ) (θ : ℝ) : Prop :=
  ∀ aperture > 0, ∀ radius > 0,
    (orderWeb (padeR n d) ∩ rayConeNearOrigin θ aperture radius).Nonempty

/-- A complex value with positive real part and zero imaginary part is a point of
the order web. -/
private theorem mem_orderWeb_of_im_zero_of_re_pos
    {R : ℂ → ℂ} {z : ℂ}
    (hre : 0 < (R z * exp (-z)).re)
    (him : (R z * exp (-z)).im = 0) :
    z ∈ orderWeb R := by
  refine ⟨(R z * exp (-z)).re, hre, ?_⟩
  apply Complex.ext <;> simp [him]

/-- The Padé order-star amplitude is continuous along a short exact angle arc once
the Padé denominator is known to stay nonzero there. -/
private theorem padeR_exp_neg_continuousOn_angleArc
    (n d : ℕ) (θ t η δ : ℝ)
    (htpos : 0 < t) (htδ : t < δ)
    (hQ : ∀ z : ℂ, ‖z‖ < δ → padeQ n d z ≠ 0) :
    ContinuousOn
      (fun s : ℝ =>
        padeR n d ((↑t : ℂ) * exp (↑(θ + s) * I)) *
          exp (-((↑t : ℂ) * exp (↑(θ + s) * I))))
      (Set.Icc (-η) η) := by
  have hp : Continuous (padeP n d) := by
    unfold padeP
    fun_prop
  have hq : Continuous (padeQ n d) := padeQ_continuous n d
  have hgamma : Continuous (fun s : ℝ => ((↑t : ℂ) * exp (↑(θ + s) * I))) := by
    fun_prop
  have hq_ne : ∀ s ∈ Set.Icc (-η) η,
      padeQ n d (((↑t : ℂ) * exp (↑(θ + s) * I))) ≠ 0 := by
    intro s hs
    apply hQ
    simpa using (norm_ofReal_mul_exp_I t (θ + s) htpos.le).trans_lt htδ
  have hR : ContinuousOn
      (fun s : ℝ => padeR n d (((↑t : ℂ) * exp (↑(θ + s) * I))))
      (Set.Icc (-η) η) := by
    simpa [padeR] using
      (hp.comp hgamma).continuousOn.div (hq.comp hgamma).continuousOn hq_ne
  have hexp : Continuous (fun s : ℝ => exp (-(((↑t : ℂ) * exp (↑(θ + s) * I))))) := by
    fun_prop
  simpa using hR.mul hexp.continuousOn

private theorem abs_im_sub_le_norm_sub (a b : ℂ) :
    abs (Complex.im a - Complex.im b) ≤ ‖a - b‖ := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    Complex.abs_im_le_norm (a - b)

private theorem im_one_sub_ofReal_mul_exp_neg (a x : ℝ) :
    Complex.im ((1 : ℂ) - ((a : ℝ) : ℂ) * Complex.exp (↑(-x) * I)) = a * Real.sin x := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp [Complex.mul_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
    Complex.cos_ofReal_re, Complex.cos_ofReal_im]

private theorem im_one_sub_ofReal_mul_exp_pos (a x : ℝ) :
    Complex.im ((1 : ℂ) - ((a : ℝ) : ℂ) * Complex.exp (↑x * I)) = -(a * Real.sin x) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp [Complex.mul_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
    Complex.cos_ofReal_re, Complex.cos_ofReal_im]

private theorem im_main_term_even_down_left
    (p : ℕ) (c t η : ℝ) :
    Complex.im ((1 : ℂ) - (c : ℂ) * (((↑t : ℂ) * exp (↑(-η) * I)) ^ (p + 1))) =
      c * t ^ (p + 1) * Real.sin (((↑(p + 1) : ℝ) * η)) := by
  have hzpow : (((↑t : ℂ) * exp (↑(-η) * I)) ^ (p + 1)) =
      ((t ^ (p + 1) : ℝ) : ℂ) * exp (↑(-((↑(p + 1) : ℝ) * η)) * I) := by
    rw [mul_pow, Complex.ofReal_pow]
    rw [← Complex.exp_nsmul, nsmul_eq_mul]
    congr 1
    push_cast
    ring_nf
  rw [hzpow, ← mul_assoc, ← Complex.ofReal_mul]
  simpa using
    im_one_sub_ofReal_mul_exp_neg (a := c * t ^ (p + 1))
      (x := ((↑(p + 1) : ℝ) * η))

private theorem im_main_term_even_down_right
    (p : ℕ) (c t η : ℝ) :
    Complex.im ((1 : ℂ) - (c : ℂ) * (((↑t : ℂ) * exp (↑η * I)) ^ (p + 1))) =
      -(c * t ^ (p + 1) * Real.sin (((↑(p + 1) : ℝ) * η))) := by
  have hzpow : (((↑t : ℂ) * exp (↑η * I)) ^ (p + 1)) =
      ((t ^ (p + 1) : ℝ) : ℂ) * exp (↑(((↑(p + 1) : ℝ) * η)) * I) := by
    rw [mul_pow, Complex.ofReal_pow]
    rw [← Complex.exp_nsmul, nsmul_eq_mul]
    congr 1
    push_cast
    ring_nf
  rw [hzpow, ← mul_assoc, ← Complex.ofReal_mul]
  simpa using
    im_one_sub_ofReal_mul_exp_pos (a := c * t ^ (p + 1))
      (x := ((↑(p + 1) : ℝ) * η))

private theorem im_main_term_odd_down_left
    (p : ℕ) (c t η : ℝ) :
    Complex.im
        ((1 : ℂ) - (c : ℂ) *
          (((↑t : ℂ) *
              exp (↑(Real.pi / ((↑(p + 1) : ℝ)) - η) * I)) ^ (p + 1))) =
      (-c) * t ^ (p + 1) * Real.sin (((↑(p + 1) : ℝ) * η)) := by
  let p1 : ℝ := ((↑(p + 1) : ℝ))
  let θ0 : ℝ := Real.pi / p1
  let α : ℝ := p1 * η
  have hp1_pos : 0 < p1 := by
    dsimp [p1]
    positivity
  have hp1_ne : p1 ≠ 0 := ne_of_gt hp1_pos
  have hzpow :
      (((↑t : ℂ) * exp (↑(θ0 - η) * I)) ^ (p + 1)) =
        -((t ^ (p + 1) : ℝ) : ℂ) * exp (↑(-α) * I) := by
    rw [mul_pow, Complex.ofReal_pow]
    rw [← Complex.exp_nsmul, nsmul_eq_mul]
    have hangle :
        (↑(p + 1 : ℕ) : ℂ) * (↑(θ0 - η) * I) =
          (↑Real.pi : ℂ) * I + (↑(-α) : ℂ) * I := by
      have hθ0 : p1 * θ0 = Real.pi := by
        dsimp [θ0]
        field_simp [hp1_ne]
      have hθ0c : (↑(p + 1 : ℕ) : ℂ) * (↑θ0 * I) = (↑Real.pi : ℂ) * I := by
        simpa [p1, mul_assoc] using congrArg (fun x : ℝ => (x : ℂ) * I) hθ0
      have hηc : (↑(p + 1 : ℕ) : ℂ) * (↑η * I) = (↑((↑(p + 1) : ℝ) * η) : ℂ) * I := by
        push_cast
        ring
      calc
        (↑(p + 1 : ℕ) : ℂ) * (↑(θ0 - η) * I)
            = (↑(p + 1 : ℕ) : ℂ) * (↑θ0 * I) - (↑(p + 1 : ℕ) : ℂ) * (↑η * I) := by
                push_cast
                ring
        _ = (↑Real.pi : ℂ) * I - (↑((↑(p + 1) : ℝ) * η) : ℂ) * I := by
              rw [hθ0c, hηc]
        _ = (↑Real.pi : ℂ) * I + (↑(-α) : ℂ) * I := by
              dsimp [α, p1]
              push_cast
              ring_nf
    rw [hangle, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have him :
      Complex.im
          ((1 : ℂ) - ((-c * t ^ (p + 1) : ℝ) : ℂ) * exp (↑(-α) * I)) =
        (-c) * t ^ (p + 1) * Real.sin α := by
    simpa using
      im_one_sub_ofReal_mul_exp_neg (a := -c * t ^ (p + 1)) (x := α)
  rw [hzpow]
  convert him using 2
  push_cast
  ring

private theorem im_main_term_odd_down_right
    (p : ℕ) (c t η : ℝ) :
    Complex.im
        ((1 : ℂ) - (c : ℂ) *
          (((↑t : ℂ) *
              exp (↑(Real.pi / ((↑(p + 1) : ℝ)) + η) * I)) ^ (p + 1))) =
      -((-c) * t ^ (p + 1) * Real.sin (((↑(p + 1) : ℝ) * η))) := by
  let p1 : ℝ := ((↑(p + 1) : ℝ))
  let θ0 : ℝ := Real.pi / p1
  let α : ℝ := p1 * η
  have hp1_pos : 0 < p1 := by
    dsimp [p1]
    positivity
  have hp1_ne : p1 ≠ 0 := ne_of_gt hp1_pos
  have hzpow :
      (((↑t : ℂ) * exp (↑(θ0 + η) * I)) ^ (p + 1)) =
        -((t ^ (p + 1) : ℝ) : ℂ) * exp (↑α * I) := by
    rw [mul_pow, Complex.ofReal_pow]
    rw [← Complex.exp_nsmul, nsmul_eq_mul]
    have hangle :
        (↑(p + 1 : ℕ) : ℂ) * (↑(θ0 + η) * I) =
          (↑Real.pi : ℂ) * I + (↑α : ℂ) * I := by
      have hθ0 : p1 * θ0 = Real.pi := by
        dsimp [θ0]
        field_simp [hp1_ne]
      have hθ0c : (↑(p + 1 : ℕ) : ℂ) * (↑θ0 * I) = (↑Real.pi : ℂ) * I := by
        simpa [p1, mul_assoc] using congrArg (fun x : ℝ => (x : ℂ) * I) hθ0
      have hηc : (↑(p + 1 : ℕ) : ℂ) * (↑η * I) = (↑((↑(p + 1) : ℝ) * η) : ℂ) * I := by
        push_cast
        ring
      calc
        (↑(p + 1 : ℕ) : ℂ) * (↑(θ0 + η) * I)
            = (↑(p + 1 : ℕ) : ℂ) * (↑θ0 * I) + (↑(p + 1 : ℕ) : ℂ) * (↑η * I) := by
                push_cast
                ring
        _ = (↑Real.pi : ℂ) * I + (↑((↑(p + 1) : ℝ) * η) : ℂ) * I := by
              rw [hθ0c, hηc]
        _ = (↑Real.pi : ℂ) * I + (↑α : ℂ) * I := by
              dsimp [α]
    rw [hangle, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have him :
      Complex.im
          ((1 : ℂ) - ((-c * t ^ (p + 1) : ℝ) : ℂ) * exp (↑α * I)) =
        -((-c) * t ^ (p + 1) * Real.sin α) := by
    simpa using
      im_one_sub_ofReal_mul_exp_pos (a := -c * t ^ (p + 1)) (x := α)
  rw [hzpow]
  convert him using 2
  push_cast
  ring

/-- Next smaller analytic seam below raw cone-meeting: in every sufficiently small
cone around the ray, a short exact-angle arc at fixed radius stays in the cone,
the Padé order-star amplitude keeps positive real part on that arc, and the
imaginary part changes sign between the two endpoints. IVT then yields an
`orderWeb` point in the cone. -/
def PadeROrderWebArcPhaseBridgeNearOrigin
    (n d : ℕ) (θ : ℝ) : Prop :=
  ∀ aperture > 0, ∀ radius > 0,
    ∃ t ∈ Set.Ioo (0 : ℝ) radius, ∃ η > 0,
      (∀ s ∈ Set.Icc (-η) η,
        ((↑t : ℂ) * exp (↑(θ + s) * I)) ∈ rayConeNearOrigin θ aperture radius) ∧
      (∀ s ∈ Set.Icc (-η) η,
        0 < Complex.re
          (padeR n d (((↑t : ℂ) * exp (↑(θ + s) * I))) *
            exp (-(((↑t : ℂ) * exp (↑(θ + s) * I)))))) ∧
      0 < Complex.im
          (padeR n d (((↑t : ℂ) * exp (↑(θ - η) * I))) *
            exp (-(((↑t : ℂ) * exp (↑(θ - η) * I))))) ∧
      Complex.im
          (padeR n d (((↑t : ℂ) * exp (↑(θ + η) * I))) *
            exp (-(((↑t : ℂ) * exp (↑(θ + η) * I))))) < 0

private theorem padeR_even_downArrowArcEndpointSigns_of_pos_errorConst
    (n d : ℕ) {η : ℝ}
    (hC : 0 < padePhiErrorConst n d)
    (hη : 0 < η)
    (hηpi : ((↑(n + d) + 1) : ℝ) * η < Real.pi) :
    ∀ radius > 0,
      ∃ t ∈ Set.Ioo (0 : ℝ) radius,
        0 < Complex.im
          (padeR n d (((↑t : ℂ) * exp (↑(-η) * I))) *
            exp (-(((↑t : ℂ) * exp (↑(-η) * I))))) ∧
        Complex.im
          (padeR n d (((↑t : ℂ) * exp (↑η * I))) *
            exp (-(((↑t : ℂ) * exp (↑η * I))))) < 0 := by
  obtain ⟨K, δ₀, hK, hδ, hφ⟩ := padeR_exp_neg_local_bound n d
  let α : ℝ := ((↑(n + d) + 1) : ℝ) * η
  have hαpos : 0 < α := by
    dsimp [α]
    positivity
  have hsin : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hαpos hηpi
  let δsign : ℝ := padePhiErrorConst n d * Real.sin α / (2 * K)
  have hδsign : 0 < δsign := by
    dsimp [δsign]
    positivity
  intro radius hradius
  let t : ℝ := min (radius / 2) (min (δ₀ / 2) (δsign / 2))
  have ht_mem : t ∈ Set.Ioo (0 : ℝ) radius := by
    refine ⟨?_, ?_⟩
    · dsimp [t]
      exact lt_min (half_pos hradius) (lt_min (half_pos hδ) (half_pos hδsign))
    · dsimp [t]
      have hhalf : radius / 2 < radius := by
        linarith
      exact lt_of_le_of_lt (min_le_left _ _) hhalf
  have ht_delta : t < δ₀ := by
    have hle : t ≤ δ₀ / 2 := by
      dsimp [t]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hhalf : δ₀ / 2 < δ₀ := by
      linarith
    exact lt_of_le_of_lt hle hhalf
  have ht_sign : t < δsign := by
    have hle : t ≤ δsign / 2 := by
      dsimp [t]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hhalf : δsign / 2 < δsign := by
      linarith
    exact lt_of_le_of_lt hle hhalf
  have hKt : K * t < padePhiErrorConst n d * Real.sin α / 2 := by
    have h := (lt_div_iff₀ (show 0 < 2 * K by positivity)).mp ht_sign
    nlinarith
  refine ⟨t, ht_mem, ?_⟩
  let zL : ℂ := (↑t : ℂ) * exp (↑(-η) * I)
  let zR : ℂ := (↑t : ℂ) * exp (↑η * I)
  have hzL_norm : ‖zL‖ = t := by
    simpa [zL] using norm_ofReal_mul_exp_I t (-η) ht_mem.1.le
  have hzR_norm : ‖zR‖ = t := by
    simpa [zR] using norm_ofReal_mul_exp_I t η ht_mem.1.le
  have hzL_delta : ‖zL‖ < δ₀ := by
    simpa [hzL_norm] using ht_delta
  have hzR_delta : ‖zR‖ < δ₀ := by
    simpa [hzR_norm] using ht_delta
  have hboundL := hφ zL hzL_delta
  have hboundR := hφ zR hzR_delta
  have hmainL :
      Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1)) =
        padePhiErrorConst n d * t ^ (n + d + 1) * Real.sin α := by
    simpa [zL, α] using
      (im_main_term_even_down_left (p := n + d) (c := padePhiErrorConst n d) t η)
  have hmainR :
      Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1)) =
        -(padePhiErrorConst n d * t ^ (n + d + 1) * Real.sin α) := by
    simpa [zR, α] using
      (im_main_term_even_down_right (p := n + d) (c := padePhiErrorConst n d) t η)
  have himdiffL :
      abs
        (Complex.im (padeR n d zL * exp (-zL)) -
          Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1))) ≤
        K * t ^ (n + d + 2) := by
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
        K * t ^ (n + d + 2) := by
      simpa [hzL_norm] using hboundL
    exact le_trans him_le hboundL'
  have himdiffR :
      abs
        (Complex.im (padeR n d zR * exp (-zR)) -
          Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1))) ≤
        K * t ^ (n + d + 2) := by
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
        K * t ^ (n + d + 2) := by
      simpa [hzR_norm] using hboundR
    exact le_trans him_le hboundR'
  have hleft_core :
      0 < padePhiErrorConst n d * t ^ (n + d + 1) * Real.sin α - K * t ^ (n + d + 2) := by
    have hpow_pos : 0 < t ^ (n + d + 1) := pow_pos ht_mem.1 _
    have hlin : 0 < padePhiErrorConst n d * Real.sin α - K * t := by
      nlinarith [hKt, hC, hsin]
    have hrewrite :
        padePhiErrorConst n d * t ^ (n + d + 1) * Real.sin α - K * t ^ (n + d + 2) =
          t ^ (n + d + 1) * (padePhiErrorConst n d * Real.sin α - K * t) := by
      ring
    rw [hrewrite]
    exact mul_pos hpow_pos hlin
  have hright_core :
      -(padePhiErrorConst n d * t ^ (n + d + 1) * Real.sin α) + K * t ^ (n + d + 2) < 0 := by
    have hpow_pos : 0 < t ^ (n + d + 1) := pow_pos ht_mem.1 _
    have hlin : K * t - padePhiErrorConst n d * Real.sin α < 0 := by
      nlinarith [hKt, hC, hsin]
    have hrewrite :
        -(padePhiErrorConst n d * t ^ (n + d + 1) * Real.sin α) + K * t ^ (n + d + 2) =
          t ^ (n + d + 1) * (K * t - padePhiErrorConst n d * Real.sin α) := by
      ring
    rw [hrewrite]
    exact mul_neg_of_pos_of_neg hpow_pos hlin
  constructor
  · have hleft_bound :
        padePhiErrorConst n d * t ^ (n + d + 1) * Real.sin α - K * t ^ (n + d + 2) ≤
          Complex.im (padeR n d zL * exp (-zL)) := by
      have h' := abs_le.mp himdiffL
      linarith [hmainL]
    exact lt_of_lt_of_le hleft_core hleft_bound
  · have hright_bound :
        Complex.im (padeR n d zR * exp (-zR)) ≤
          -(padePhiErrorConst n d * t ^ (n + d + 1) * Real.sin α) + K * t ^ (n + d + 2) := by
      have h' := abs_le.mp himdiffR
      linarith [hmainR]
    exact lt_of_le_of_lt hright_bound hright_core

private theorem padeR_odd_downArrowArcEndpointSigns_of_neg_errorConst
    (n d : ℕ) {η : ℝ}
    (hC : padePhiErrorConst n d < 0)
    (hη : 0 < η)
    (hηpi : ((↑(n + d) + 1) : ℝ) * η < Real.pi) :
    ∀ radius > 0,
      ∃ t ∈ Set.Ioo (0 : ℝ) radius,
        0 < Complex.im
          (padeR n d
              (((↑t : ℂ) *
                  exp (↑(Real.pi / ((↑(n + d) + 1) : ℝ) - η) * I))) *
            exp (-(((↑t : ℂ) *
                exp (↑(Real.pi / ((↑(n + d) + 1) : ℝ) - η) * I))))) ∧
        Complex.im
          (padeR n d
              (((↑t : ℂ) *
                  exp (↑(Real.pi / ((↑(n + d) + 1) : ℝ) + η) * I))) *
            exp (-(((↑t : ℂ) *
                exp (↑(Real.pi / ((↑(n + d) + 1) : ℝ) + η) * I))))) < 0 := by
  obtain ⟨K, δ₀, hK, hδ, hφ⟩ := padeR_exp_neg_local_bound n d
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
  let δsign : ℝ := (-padePhiErrorConst n d) * Real.sin α / (2 * K)
  have hnegC : 0 < -padePhiErrorConst n d := by
    linarith
  have hδsign : 0 < δsign := by
    dsimp [δsign]
    exact div_pos (mul_pos hnegC hsin) (by positivity)
  intro radius hradius
  let t : ℝ := min (radius / 2) (min (δ₀ / 2) (δsign / 2))
  have ht_mem : t ∈ Set.Ioo (0 : ℝ) radius := by
    refine ⟨?_, ?_⟩
    · dsimp [t]
      exact lt_min (half_pos hradius) (lt_min (half_pos hδ) (half_pos hδsign))
    · dsimp [t]
      have hhalf : radius / 2 < radius := by
        linarith
      exact lt_of_le_of_lt (min_le_left _ _) hhalf
  have ht_delta : t < δ₀ := by
    have hle : t ≤ δ₀ / 2 := by
      dsimp [t]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hhalf : δ₀ / 2 < δ₀ := by
      linarith
    exact lt_of_le_of_lt hle hhalf
  have ht_sign : t < δsign := by
    have hle : t ≤ δsign / 2 := by
      dsimp [t]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hhalf : δsign / 2 < δsign := by
      linarith
    exact lt_of_le_of_lt hle hhalf
  have hKt : K * t < (-padePhiErrorConst n d) * Real.sin α / 2 := by
    have h := (lt_div_iff₀ (show 0 < 2 * K by positivity)).mp ht_sign
    nlinarith
  refine ⟨t, ht_mem, ?_⟩
  let zL : ℂ := (↑t : ℂ) * exp (↑(θ0 - η) * I)
  let zR : ℂ := (↑t : ℂ) * exp (↑(θ0 + η) * I)
  have hzL_norm : ‖zL‖ = t := by
    simpa [zL] using norm_ofReal_mul_exp_I t (θ0 - η) ht_mem.1.le
  have hzR_norm : ‖zR‖ = t := by
    simpa [zR] using norm_ofReal_mul_exp_I t (θ0 + η) ht_mem.1.le
  have hzL_delta : ‖zL‖ < δ₀ := by
    simpa [hzL_norm] using ht_delta
  have hzR_delta : ‖zR‖ < δ₀ := by
    simpa [hzR_norm] using ht_delta
  have hboundL := hφ zL hzL_delta
  have hboundR := hφ zR hzR_delta
  have hmainL :
      Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1)) =
        (-padePhiErrorConst n d) * t ^ (n + d + 1) * Real.sin α := by
    simpa [zL, p1, θ0, α] using
      (im_main_term_odd_down_left (p := n + d) (c := padePhiErrorConst n d) t η)
  have hmainR :
      Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1)) =
        -((-padePhiErrorConst n d) * t ^ (n + d + 1) * Real.sin α) := by
    simpa [zR, p1, θ0, α] using
      (im_main_term_odd_down_right (p := n + d) (c := padePhiErrorConst n d) t η)
  have himdiffL :
      abs
        (Complex.im (padeR n d zL * exp (-zL)) -
          Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zL ^ (n + d + 1))) ≤
        K * t ^ (n + d + 2) := by
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
        K * t ^ (n + d + 2) := by
      simpa [hzL_norm] using hboundL
    exact le_trans him_le hboundL'
  have himdiffR :
      abs
        (Complex.im (padeR n d zR * exp (-zR)) -
          Complex.im ((1 : ℂ) - (padePhiErrorConst n d : ℂ) * zR ^ (n + d + 1))) ≤
        K * t ^ (n + d + 2) := by
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
        K * t ^ (n + d + 2) := by
      simpa [hzR_norm] using hboundR
    exact le_trans him_le hboundR'
  have hleft_core :
      0 < (-padePhiErrorConst n d) * t ^ (n + d + 1) * Real.sin α -
        K * t ^ (n + d + 2) := by
    have hpow_pos : 0 < t ^ (n + d + 1) := pow_pos ht_mem.1 _
    have hlin : 0 < (-padePhiErrorConst n d) * Real.sin α - K * t := by
      nlinarith [hKt, hnegC, hsin]
    have hrewrite :
        (-padePhiErrorConst n d) * t ^ (n + d + 1) * Real.sin α - K * t ^ (n + d + 2) =
          t ^ (n + d + 1) * ((-padePhiErrorConst n d) * Real.sin α - K * t) := by
      ring
    rw [hrewrite]
    exact mul_pos hpow_pos hlin
  have hright_core :
      -((-padePhiErrorConst n d) * t ^ (n + d + 1) * Real.sin α) +
        K * t ^ (n + d + 2) < 0 := by
    have hpow_pos : 0 < t ^ (n + d + 1) := pow_pos ht_mem.1 _
    have hlin : K * t - (-padePhiErrorConst n d) * Real.sin α < 0 := by
      nlinarith [hKt, hnegC, hsin]
    have hrewrite :
        -((-padePhiErrorConst n d) * t ^ (n + d + 1) * Real.sin α) + K * t ^ (n + d + 2) =
          t ^ (n + d + 1) * (K * t - (-padePhiErrorConst n d) * Real.sin α) := by
      ring
    rw [hrewrite]
    exact mul_neg_of_pos_of_neg hpow_pos hlin
  constructor
  · have hleft_bound :
        (-padePhiErrorConst n d) * t ^ (n + d + 1) * Real.sin α -
            K * t ^ (n + d + 2) ≤
          Complex.im (padeR n d zL * exp (-zL)) := by
      have h' := abs_le.mp himdiffL
      linarith [hmainL]
    exact lt_of_lt_of_le hleft_core hleft_bound
  · have hright_bound :
        Complex.im (padeR n d zR * exp (-zR)) ≤
          -((-padePhiErrorConst n d) * t ^ (n + d + 1) * Real.sin α) +
            K * t ^ (n + d + 2) := by
      have h' := abs_le.mp himdiffR
      linarith [hmainR]
    exact lt_of_le_of_lt hright_bound hright_core

/-- A short exact-angle arc with positive real part and opposite imaginary signs
at the endpoints already produces a raw order-web point in the cone. -/
theorem PadeROrderWebMeetsRayConeNearOrigin_of_arcPhaseBridge
    {n d : ℕ} {θ : ℝ}
    (hbridge : PadeROrderWebArcPhaseBridgeNearOrigin n d θ) :
    PadeROrderWebMeetsRayConeNearOrigin n d θ := by
  intro aperture haperture radius hradius
  obtain ⟨δQ, hδQ, hQ⟩ := padeQ_nonzero_near_zero n d
  let radius' : ℝ := min radius (δQ / 2)
  have hradius' : 0 < radius' := by
    dsimp [radius']
    exact lt_min hradius (half_pos hδQ)
  rcases hbridge aperture haperture radius' hradius' with
    ⟨t, ht, η, hη, hcone, hre, himneg, himpos⟩
  have htδQ : t < δQ := by
    have htlt : t < radius' := ht.2
    exact lt_of_lt_of_le htlt (le_trans (min_le_right _ _) (by linarith [hδQ]))
  have hcont_complex :
      ContinuousOn
        (fun s : ℝ =>
          padeR n d ((↑t : ℂ) * exp (↑(θ + s) * I)) *
            exp (-((↑t : ℂ) * exp (↑(θ + s) * I))))
        (Set.Icc (-η) η) :=
    padeR_exp_neg_continuousOn_angleArc n d θ t η δQ ht.1 htδQ hQ
  have him_cont : ContinuousOn (fun z : ℂ => Complex.im z) Set.univ :=
    Complex.continuous_im.continuousOn
  have hcont_im :
      ContinuousOn
        (fun s : ℝ =>
          Complex.im
            (padeR n d ((↑t : ℂ) * exp (↑(θ + s) * I)) *
              exp (-((↑t : ℂ) * exp (↑(θ + s) * I)))))
        (Set.Icc (-η) η) := by
    simpa [Function.comp] using
      (him_cont.comp hcont_complex (by
        intro x hx
        simp))
  have hzero_mem :
      (0 : ℝ) ∈ Set.Icc
        (Complex.im
          (padeR n d ((↑t : ℂ) * exp (↑(θ + η) * I)) *
            exp (-((↑t : ℂ) * exp (↑(θ + η) * I)))))
        (Complex.im
          (padeR n d ((↑t : ℂ) * exp (↑(θ - η) * I)) *
            exp (-((↑t : ℂ) * exp (↑(θ - η) * I))))) := by
    exact ⟨le_of_lt himpos, le_of_lt himneg⟩
  have hpre : IsPreconnected (Set.Icc (-η) η) := by
    simpa using isPreconnected_Icc
  have himage :=
    hpre.intermediate_value
      (show η ∈ Set.Icc (-η) η by simp [hη.le])
      (show -η ∈ Set.Icc (-η) η by simp [hη.le])
      hcont_im
  rcases himage hzero_mem with ⟨s, hsIcc, hszero⟩
  let z : ℂ := (↑t : ℂ) * exp (↑(θ + s) * I)
  have hzcone' : z ∈ rayConeNearOrigin θ aperture radius' := by
    simpa [z] using hcone s hsIcc
  have hzcone : z ∈ rayConeNearOrigin θ aperture radius := by
    rcases hzcone' with ⟨u, hu, hudist⟩
    exact ⟨u, ⟨hu.1, lt_of_lt_of_le hu.2 (min_le_left _ _)⟩, hudist⟩
  have hrez : 0 < Complex.re (padeR n d z * exp (-z)) := by
    simpa [z] using hre s hsIcc
  have himz : Complex.im (padeR n d z * exp (-z)) = 0 := by
    simpa [z] using hszero
  exact ⟨z, mem_orderWeb_of_im_zero_of_re_pos hrez himz, hzcone⟩

/-- Any set that meets every sufficiently small cone around a ray must
accumulate at the origin. -/
private theorem zero_mem_closure_of_meets_rayConeNearOrigin
    {support : Set ℂ} {θ : ℝ}
    (hmeet :
      ∀ aperture > 0, ∀ radius > 0,
        (support ∩ rayConeNearOrigin θ aperture radius).Nonempty) :
    (0 : ℂ) ∈ closure support := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨z, hz⟩ := hmeet 1 zero_lt_one (ε / 2) (half_pos hε)
  rcases hz with ⟨hzsupport, hzcone⟩
  refine ⟨z, hzsupport, ?_⟩
  rcases hzcone with ⟨t, ht, hdist⟩
  have hdist' : ‖z - (↑t * exp (↑θ * I) : ℂ)‖ < t := by
    simpa using hdist
  have htnorm : ‖(↑t : ℂ) * exp (↑θ * I)‖ = t :=
    norm_ofReal_mul_exp_I t θ ht.1.le
  calc
    dist 0 z = ‖z‖ := by simp [dist_eq_norm]
    _ = ‖(z - (↑t * exp (↑θ * I) : ℂ)) + ((↑t : ℂ) * exp (↑θ * I))‖ := by
      ring_nf
    _ ≤ ‖z - (↑t * exp (↑θ * I) : ℂ)‖ + ‖((↑t : ℂ) * exp (↑θ * I))‖ := norm_add_le _ _
    _ < t + t := by
      rw [htnorm]
      gcongr
    _ < ε := by
      linarith [ht.2]

/-- Lower support seam beneath `PadeRRayTrackingOrderWebSupport`: connected
order-web support that already meets every sufficiently small cone around the
ray. The `0 ∈ closure support` field is forced formally downstream. -/
structure PadeRConnectedRayConeOrderWebSupport (n d : ℕ) (θ : ℝ) where
  support : Set ℂ
  support_connected : IsConnected support
  support_subset_orderWeb : support ⊆ orderWeb (padeR n d)
  meets_rayConeNearOrigin :
    ∀ aperture > 0, ∀ radius > 0,
      (support ∩ rayConeNearOrigin θ aperture radius).Nonempty

/-- Smaller theorem-local support seam below `PadeRTrackedDownArrowBranch`: a
connected subset of the Padé order web that already meets every sufficiently
small cone around a fixed ray. This isolates the genuinely geometric support
content still missing from the current `{0}`-support witness. -/
structure PadeRRayTrackingOrderWebSupport (n d : ℕ) (θ : ℝ) where
  support : Set ℂ
  support_connected : IsConnected support
  support_subset_orderWeb : support ⊆ orderWeb (padeR n d)
  origin_mem_closure : (0 : ℂ) ∈ closure support
  meets_rayConeNearOrigin :
    ∀ aperture > 0, ∀ radius > 0,
      (support ∩ rayConeNearOrigin θ aperture radius).Nonempty

def PadeRRayTrackingOrderWebSupport.toGlobalOrderArrowBranch
    {n d : ℕ} {θ : ℝ}
    (h : PadeRRayTrackingOrderWebSupport n d θ) :
    GlobalOrderArrowBranch (padeR n d) :=
  { support := h.support
    support_connected := h.support_connected
    support_subset_orderWeb := h.support_subset_orderWeb
    origin_mem_closure := h.origin_mem_closure }

theorem PadeRRayTrackingOrderWebSupport.branchTracksRayNearOrigin
    {n d : ℕ} {θ : ℝ}
    (h : PadeRRayTrackingOrderWebSupport n d θ) :
    BranchTracksRayNearOrigin h.toGlobalOrderArrowBranch θ :=
  h.meets_rayConeNearOrigin

theorem PadeRConnectedRayConeOrderWebSupport.origin_mem_closure
    {n d : ℕ} {θ : ℝ}
    (h : PadeRConnectedRayConeOrderWebSupport n d θ) :
    (0 : ℂ) ∈ closure h.support := by
  exact zero_mem_closure_of_meets_rayConeNearOrigin h.meets_rayConeNearOrigin

theorem PadeRConnectedRayConeOrderWebSupport.orderWebMeetsRayConeNearOrigin
    {n d : ℕ} {θ : ℝ}
    (h : PadeRConnectedRayConeOrderWebSupport n d θ) :
    PadeROrderWebMeetsRayConeNearOrigin n d θ := by
  intro aperture haperture radius hradius
  rcases h.meets_rayConeNearOrigin aperture haperture radius hradius with
    ⟨z, hzsupport, hzcone⟩
  exact ⟨z, h.support_subset_orderWeb hzsupport, hzcone⟩

/-- Honest compatibility strengthening of raw Padé order-web cone meeting: all
small-cone witnesses can be chosen inside one fixed connected component of the
order web. This is the missing content not recorded by the pointwise
`PadeROrderWebMeetsRayConeNearOrigin` predicate alone. -/
def PadeROrderWebMeetsRayConeNearOriginInConnectedComponent
    (n d : ℕ) (θ : ℝ) : Prop :=
  ∃ z0 ∈ orderWeb (padeR n d),
    ∀ aperture > 0, ∀ radius > 0,
      (connectedComponentIn (orderWeb (padeR n d)) z0 ∩
        rayConeNearOrigin θ aperture radius).Nonempty

theorem nonempty_connectedRayConeSupport_of_meetsRayConeNearOriginInConnectedComponent
    {n d : ℕ} {θ : ℝ}
    (hcomp : PadeROrderWebMeetsRayConeNearOriginInConnectedComponent n d θ) :
    Nonempty (PadeRConnectedRayConeOrderWebSupport n d θ) := by
  obtain ⟨z0, hz0, hmeets⟩ := hcomp
  exact ⟨⟨connectedComponentIn (orderWeb (padeR n d)) z0,
    isConnected_connectedComponentIn_iff.mpr hz0,
    connectedComponentIn_subset _ _,
    hmeets⟩⟩

def PadeRConnectedRayConeOrderWebSupport.toRayTrackingOrderWebSupport
    {n d : ℕ} {θ : ℝ}
    (h : PadeRConnectedRayConeOrderWebSupport n d θ) :
    PadeRRayTrackingOrderWebSupport n d θ :=
  { support := h.support
    support_connected := h.support_connected
    support_subset_orderWeb := h.support_subset_orderWeb
    origin_mem_closure := h.origin_mem_closure
    meets_rayConeNearOrigin := h.meets_rayConeNearOrigin }

def PadeRRayTrackingOrderWebSupport.toConnectedRayConeOrderWebSupport
    {n d : ℕ} {θ : ℝ}
    (h : PadeRRayTrackingOrderWebSupport n d θ) :
    PadeRConnectedRayConeOrderWebSupport n d θ :=
  { support := h.support
    support_connected := h.support_connected
    support_subset_orderWeb := h.support_subset_orderWeb
    meets_rayConeNearOrigin := h.meets_rayConeNearOrigin }

def PadeRRayTrackingOrderWebSupport.toTrackedDownArrowBranch
    {n d : ℕ} {θ : ℝ}
    (h : PadeRRayTrackingOrderWebSupport n d θ)
    (hθ : IsDownArrowDir (padeR n d) θ) :
    PadeRTrackedDownArrowBranch n d :=
  ⟨{ support := h.support
     support_connected := h.support_connected
     support_subset_orderWeb := h.support_subset_orderWeb
     origin_mem_closure := h.origin_mem_closure
     tangentAngle := θ
     tangentDown := hθ }, h.branchTracksRayNearOrigin⟩

def PadeRTrackedDownArrowBranch.toRayTrackingOrderWebSupport
    {n d : ℕ} (branch : PadeRTrackedDownArrowBranch n d) :
    PadeRRayTrackingOrderWebSupport n d branch.1.tangentAngle :=
  { support := branch.1.support
    support_connected := branch.1.support_connected
    support_subset_orderWeb := branch.1.support_subset_orderWeb
    origin_mem_closure := branch.1.origin_mem_closure
    meets_rayConeNearOrigin := branch.2 }

theorem nonempty_padeR_trackedDownArrowBranch_iff_exists_rayTrackingSupport
    (n d : ℕ) :
    Nonempty (PadeRTrackedDownArrowBranch n d) ↔
      ∃ θ : ℝ, IsDownArrowDir (padeR n d) θ ∧
        Nonempty (PadeRRayTrackingOrderWebSupport n d θ) := by
  constructor
  · rintro ⟨branch⟩
    exact ⟨branch.1.tangentAngle, branch.1.tangentDown,
      ⟨branch.toRayTrackingOrderWebSupport⟩⟩
  · rintro ⟨θ, hθ, ⟨support⟩⟩
    exact ⟨support.toTrackedDownArrowBranch hθ⟩

/-- Count-indexed family of down-arrow branches that already satisfy the local
ray-tracking half of the realized-branch interface. -/
abbrev PadeRTrackedDownArrowInfinityWitnessFamily
    (n d : ℕ) (data : OrderArrowTerminationData) :=
  ∀ _ : Fin data.downArrowsAtInfinity, PadeRTrackedDownArrowBranch n d

abbrev PadeRRealizedUpArrowInfinityWitnessFamily
    (n d : ℕ) (data : OrderArrowTerminationData) :=
  ∀ _ : Fin data.upArrowsAtInfinity,
    RealizedUpArrowInfinityBranch (padeR n d)

private theorem nonempty_finFunction_iff_zero_or_nonempty
    {α : Sort*} (n : ℕ) :
    Nonempty (Fin n → α) ↔ n = 0 ∨ Nonempty α := by
  constructor
  · intro h
    cases n with
    | zero =>
        exact Or.inl rfl
    | succ n =>
        exact Or.inr ⟨h.some ⟨0, Nat.succ_pos _⟩⟩
  · intro h
    rcases h with hzero | hα
    · rcases hzero with rfl
      refine ⟨?_⟩
      intro i
      exact Fin.elim0 i
    · rcases hα with ⟨a⟩
      exact ⟨fun _ => a⟩

theorem nonempty_padeR_realizedDownArrowInfinityWitnessFamily_iff
    (n d : ℕ) (data : OrderArrowTerminationData) :
    Nonempty (PadeRRealizedDownArrowInfinityWitnessFamily n d data) ↔
      data.downArrowsAtInfinity = 0 ∨
        Nonempty (RealizedDownArrowInfinityBranch (padeR n d)) := by
  simpa [PadeRRealizedDownArrowInfinityWitnessFamily] using
    (nonempty_finFunction_iff_zero_or_nonempty
      (α := RealizedDownArrowInfinityBranch (padeR n d))
      data.downArrowsAtInfinity)

theorem nonempty_padeR_trackedDownArrowInfinityWitnessFamily_iff
    (n d : ℕ) (data : OrderArrowTerminationData) :
    Nonempty (PadeRTrackedDownArrowInfinityWitnessFamily n d data) ↔
      data.downArrowsAtInfinity = 0 ∨
        Nonempty (PadeRTrackedDownArrowBranch n d) := by
  simpa [PadeRTrackedDownArrowInfinityWitnessFamily] using
    (nonempty_finFunction_iff_zero_or_nonempty
      (α := PadeRTrackedDownArrowBranch n d)
      data.downArrowsAtInfinity)

theorem nonempty_padeR_realizedUpArrowInfinityWitnessFamily_iff
    (n d : ℕ) (data : OrderArrowTerminationData) :
    Nonempty (PadeRRealizedUpArrowInfinityWitnessFamily n d data) ↔
      data.upArrowsAtInfinity = 0 ∨
        Nonempty (RealizedUpArrowInfinityBranch (padeR n d)) := by
  simpa [PadeRRealizedUpArrowInfinityWitnessFamily] using
    (nonempty_finFunction_iff_zero_or_nonempty
      (α := RealizedUpArrowInfinityBranch (padeR n d))
      data.upArrowsAtInfinity)

/-- Smallest live theorem-local blocker below
`PadeRDownArrowRayTrackingSupportInput`: first show that the Padé order web
itself meets every sufficiently small cone around a concrete down-arrow ray.
Packaging those raw cone intersections into connected support is a separate
downstream step. -/
structure PadeRDownArrowOrderWebArcPhaseBridgeInput
    (n d : ℕ) (data : OrderArrowTerminationData) where
  downOrderWebArcPhaseBridge_of_downArrowsAtInfinity_pos :
    0 < data.downArrowsAtInfinity →
      ∃ θ : ℝ, IsDownArrowDir (padeR n d) θ ∧
        PadeROrderWebArcPhaseBridgeNearOrigin n d θ

/-- Smallest live theorem-local blocker below
`PadeRDownArrowRayTrackingSupportInput`: first show that the Padé order web
itself meets every sufficiently small cone around a concrete down-arrow ray.
Packaging those raw cone intersections into connected support is a separate
downstream step. -/
structure PadeRDownArrowOrderWebRayConeMeetInput
    (n d : ℕ) (data : OrderArrowTerminationData) where
  downOrderWebMeetsRayCone_of_downArrowsAtInfinity_pos :
    0 < data.downArrowsAtInfinity →
      ∃ θ : ℝ, IsDownArrowDir (padeR n d) θ ∧
        PadeROrderWebMeetsRayConeNearOrigin n d θ

/-- The arc-phase bridge is the next honest theorem-local input below raw
cone-meeting. -/
def PadeRDownArrowOrderWebArcPhaseBridgeInput.toOrderWebRayConeMeetInput
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeRDownArrowOrderWebArcPhaseBridgeInput n d data) :
    PadeRDownArrowOrderWebRayConeMeetInput n d data := by
  refine ⟨?_⟩
  intro hpos
  rcases h.downOrderWebArcPhaseBridge_of_downArrowsAtInfinity_pos hpos with
    ⟨θ, hθ, hbridge⟩
  exact ⟨θ, hθ, PadeROrderWebMeetsRayConeNearOrigin_of_arcPhaseBridge hbridge⟩

/-- Honest theorem-local compatibility seam below
`PadeRDownArrowConnectedRayConeSupportInput`: a concrete down-arrow ray whose
small-cone order-web witnesses all lie in one connected component. -/
structure PadeRDownArrowOrderWebConnectedComponentMeetInput
    (n d : ℕ) (data : OrderArrowTerminationData) where
  downOrderWebMeetsRayConeInConnectedComponent_of_downArrowsAtInfinity_pos :
    0 < data.downArrowsAtInfinity →
      ∃ θ : ℝ, IsDownArrowDir (padeR n d) θ ∧
        PadeROrderWebMeetsRayConeNearOriginInConnectedComponent n d θ

/-- Intermediate honest seam between raw cone intersections and the current
ray-tracking support input: a connected order-web support meeting every small
cone around a concrete down-arrow ray. -/
structure PadeRDownArrowConnectedRayConeSupportInput
    (n d : ℕ) (data : OrderArrowTerminationData) where
  downConnectedRayConeSupport_of_downArrowsAtInfinity_pos :
    0 < data.downArrowsAtInfinity →
      ∃ θ : ℝ, IsDownArrowDir (padeR n d) θ ∧
        Nonempty (PadeRConnectedRayConeOrderWebSupport n d θ)

def PadeRDownArrowOrderWebConnectedComponentMeetInput.toConnectedRayConeSupportInput
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeRDownArrowOrderWebConnectedComponentMeetInput n d data) :
    PadeRDownArrowConnectedRayConeSupportInput n d data := by
  refine ⟨?_⟩
  intro hpos
  rcases h.downOrderWebMeetsRayConeInConnectedComponent_of_downArrowsAtInfinity_pos hpos with
    ⟨θ, hθ, hcomp⟩
  exact ⟨θ, hθ,
    nonempty_connectedRayConeSupport_of_meetsRayConeNearOriginInConnectedComponent hcomp⟩

/-- Honest one-level-lower seam beneath `PadeRDownArrowBranchTrackingInput`:
positive down-arrow infinity counts would yield a tracked branch once the
missing geometric input is supplied as an order-web support that actually meets
every sufficiently small cone around a concrete down-arrow ray. -/
structure PadeRDownArrowRayTrackingSupportInput
    (n d : ℕ) (data : OrderArrowTerminationData) where
  downRayTrackingSupport_of_downArrowsAtInfinity_pos :
    0 < data.downArrowsAtInfinity →
      ∃ θ : ℝ, IsDownArrowDir (padeR n d) θ ∧
        Nonempty (PadeRRayTrackingOrderWebSupport n d θ)

def PadeRDownArrowConnectedRayConeSupportInput.toRayTrackingSupportInput
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeRDownArrowConnectedRayConeSupportInput n d data) :
    PadeRDownArrowRayTrackingSupportInput n d data := by
  refine ⟨?_⟩
  intro hpos
  rcases h.downConnectedRayConeSupport_of_downArrowsAtInfinity_pos hpos with
    ⟨θ, hθ, ⟨support⟩⟩
  exact ⟨θ, hθ, ⟨support.toRayTrackingOrderWebSupport⟩⟩

theorem padeR_exists_trackedDownArrowBranch_of_exists_rayTrackingSupport
    {n d : ℕ}
    (hexists :
      ∃ θ : ℝ, IsDownArrowDir (padeR n d) θ ∧
        Nonempty (PadeRRayTrackingOrderWebSupport n d θ)) :
    Nonempty (PadeRTrackedDownArrowBranch n d) := by
  rcases hexists with ⟨θ, hθ, hsupport⟩
  rcases hsupport with ⟨support⟩
  exact ⟨support.toTrackedDownArrowBranch hθ⟩

/-- Sharpened cycle-320 seam on the down-arrow side: the current `{0}`-support
global-branch existence theorem does not even provide the local ray-tracking
field of a realized escaping branch, so that theorem-local input has to be
named explicitly before `EscapesEveryClosedBall` becomes relevant. -/
structure PadeRDownArrowBranchTrackingInput
    (n d : ℕ) (data : OrderArrowTerminationData) where
  downTrackedBranch_of_downArrowsAtInfinity_pos :
    0 < data.downArrowsAtInfinity →
      Nonempty (PadeRTrackedDownArrowBranch n d)

def PadeRDownArrowRayTrackingSupportInput.toTrackingInput
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeRDownArrowRayTrackingSupportInput n d data) :
    PadeRDownArrowBranchTrackingInput n d data :=
  ⟨fun hpos =>
    padeR_exists_trackedDownArrowBranch_of_exists_rayTrackingSupport
      (h.downRayTrackingSupport_of_downArrowsAtInfinity_pos hpos)⟩

noncomputable def PadeRDownArrowBranchTrackingInput.downArrowInfinityWitnesses
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeRDownArrowBranchTrackingInput n d data) :
    PadeRTrackedDownArrowInfinityWitnessFamily n d data := by
  intro i
  have hpos : 0 < data.downArrowsAtInfinity := by
    have h1 : 1 ≤ data.downArrowsAtInfinity := by
      exact le_trans (Nat.succ_le_succ (Nat.zero_le i.1)) (Nat.succ_le_of_lt i.2)
    exact Nat.succ_le_iff.mp h1
  exact (h.downTrackedBranch_of_downArrowsAtInfinity_pos hpos).some

/-- Honest theorem-local input for the current Padé infinity-branch seam:
positive infinity counts do not themselves determine concrete escaping branch
germs, so the live file has to ask separately for realized branch existence in
each nonempty count case. -/
structure PadeRInfinityBranchExistenceInput
    (n d : ℕ) (data : OrderArrowTerminationData) where
  downBranch_of_downArrowsAtInfinity_pos :
    0 < data.downArrowsAtInfinity →
      Nonempty (RealizedDownArrowInfinityBranch (padeR n d))
  upBranch_of_upArrowsAtInfinity_pos :
    0 < data.upArrowsAtInfinity →
      Nonempty (RealizedUpArrowInfinityBranch (padeR n d))

noncomputable def PadeRInfinityBranchExistenceInput.downArrowInfinityWitnesses
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeRInfinityBranchExistenceInput n d data) :
    PadeRRealizedDownArrowInfinityWitnessFamily n d data := by
  intro i
  have hpos : 0 < data.downArrowsAtInfinity := by
    have h1 : 1 ≤ data.downArrowsAtInfinity := by
      exact le_trans (Nat.succ_le_succ (Nat.zero_le i.1)) (Nat.succ_le_of_lt i.2)
    exact Nat.succ_le_iff.mp h1
  exact (h.downBranch_of_downArrowsAtInfinity_pos hpos).some

noncomputable def PadeRInfinityBranchExistenceInput.upArrowInfinityWitnesses
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeRInfinityBranchExistenceInput n d data) :
    PadeRRealizedUpArrowInfinityWitnessFamily n d data := by
  intro i
  have hpos : 0 < data.upArrowsAtInfinity := by
    have h1 : 1 ≤ data.upArrowsAtInfinity := by
      exact le_trans (Nat.succ_le_succ (Nat.zero_le i.1)) (Nat.succ_le_of_lt i.2)
    exact Nat.succ_le_iff.mp h1
  exact (h.upBranch_of_upArrowsAtInfinity_pos hpos).some

noncomputable def PadeRInfinityBranchExistenceInput.realizesInfinityBranchGerms
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeRInfinityBranchExistenceInput n d data) :
    RealizesInfinityBranchGerms (padeR n d) data := by
  exact ⟨h.downArrowInfinityWitnesses, h.upArrowInfinityWitnesses⟩

private theorem padeR_mem_orderWeb_zero (n d : ℕ) :
    (0 : ℂ) ∈ orderWeb (padeR n d) := by
  exact mem_orderWeb_zero (R := padeR n d) (by
    simp [padeR, padeP_eval_zero, padeQ_eval_zero])

private theorem isConnected_union_zero_of_zero_mem_closure
    {support : Set ℂ} (hsupport : IsConnected support)
    (hzero : (0 : ℂ) ∈ closure support) :
    IsConnected (support ∪ ({0} : Set ℂ)) := by
  refine hsupport.subset_closure ?_ ?_
  · intro z hz
    exact Or.inl hz
  · intro z hz
    rcases hz with hz | hz
    · exact subset_closure hz
    · have hz0 : z = 0 := by simpa using hz
      subst hz0
      exact hzero

theorem padeR_exists_orderWebBranchSupport_of_downArrowsAtInfinity_pos
    (n d : ℕ) (data : OrderArrowTerminationData)
    (_hpos : 0 < data.downArrowsAtInfinity) :
    ∃ support : Set ℂ,
      IsConnected support ∧
        support ⊆ orderWeb (padeR n d) ∧
        (0 : ℂ) ∈ closure support := by
  refine ⟨{0}, ?_, ?_, ?_⟩
  · simpa using isConnected_singleton
  · intro z hz
    have hz0 : z = 0 := by simpa using hz
    subst hz0
    exact mem_orderWeb_zero (R := padeR n d) (by
      simp [padeR, padeP_eval_zero, padeQ_eval_zero])
  · exact subset_closure (by simp : (0 : ℂ) ∈ ({0} : Set ℂ))

theorem padeR_exists_globalDownArrowBranch_of_downArrowsAtInfinity_pos_of_exists_downArrowDir
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hpos : 0 < data.downArrowsAtInfinity)
    (hdir : ∃ θ : ℝ, IsDownArrowDir (padeR n d) θ) :
    Nonempty (GlobalDownArrowBranch (padeR n d)) := by
  rcases
      padeR_exists_orderWebBranchSupport_of_downArrowsAtInfinity_pos n d data hpos with
    ⟨support, hsupport_connected, hsupport_subset_orderWeb, horigin_mem_closure⟩
  rcases hdir with ⟨θ, hθ⟩
  exact
    ⟨{ support := support
       support_connected := hsupport_connected
       support_subset_orderWeb := hsupport_subset_orderWeb
       origin_mem_closure := horigin_mem_closure
       tangentAngle := θ
       tangentDown := hθ }⟩

theorem padeR_exists_globalDownArrowBranch_of_downArrowsAtInfinity_pos
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hpos : 0 < data.downArrowsAtInfinity) :
    Nonempty (GlobalDownArrowBranch (padeR n d)) := by
  have hdir : ∃ θ : ℝ, IsDownArrowDir (padeR n d) θ := by
    exact padeR_exists_downArrowDir n d
  exact
    padeR_exists_globalDownArrowBranch_of_downArrowsAtInfinity_pos_of_exists_downArrowDir
      n d data hpos hdir

theorem padeR_exists_orderWebBranchSupport_of_upArrowsAtInfinity_pos
    (n d : ℕ) (data : OrderArrowTerminationData)
    (_hpos : 0 < data.upArrowsAtInfinity) :
    ∃ support : Set ℂ,
      IsConnected support ∧
        support ⊆ orderWeb (padeR n d) ∧
        (0 : ℂ) ∈ closure support := by
  refine ⟨{0}, ?_, ?_, ?_⟩
  · simpa using isConnected_singleton
  · intro z hz
    have hz0 : z = 0 := by simpa using hz
    subst hz0
    exact mem_orderWeb_zero (R := padeR n d) (by
      simp [padeR, padeP_eval_zero, padeQ_eval_zero])
  · exact subset_closure (by simp : (0 : ℂ) ∈ ({0} : Set ℂ))

theorem padeR_exists_globalUpArrowBranch_of_upArrowsAtInfinity_pos_of_exists_upArrowDir
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hpos : 0 < data.upArrowsAtInfinity)
    (hdir : ∃ θ : ℝ, IsUpArrowDir (padeR n d) θ) :
    Nonempty (GlobalUpArrowBranch (padeR n d)) := by
  rcases
      padeR_exists_orderWebBranchSupport_of_upArrowsAtInfinity_pos n d data hpos with
    ⟨support, hsupport_connected, hsupport_subset_orderWeb, horigin_mem_closure⟩
  rcases hdir with ⟨θ, hθ⟩
  exact
    ⟨{ support := support
       support_connected := hsupport_connected
       support_subset_orderWeb := hsupport_subset_orderWeb
       origin_mem_closure := horigin_mem_closure
       tangentAngle := θ
       tangentUp := hθ }⟩

theorem padeR_exists_globalUpArrowBranch_of_upArrowsAtInfinity_pos
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hpos : 0 < data.upArrowsAtInfinity) :
    Nonempty (GlobalUpArrowBranch (padeR n d)) := by
  have hdir : ∃ θ : ℝ, IsUpArrowDir (padeR n d) θ := by
    exact padeR_exists_upArrowDir n d
  exact
    padeR_exists_globalUpArrowBranch_of_upArrowsAtInfinity_pos_of_exists_upArrowDir
      n d data hpos hdir

/-- Cycle-300 truth audit: adjoining `{0}` to the support of a realized Padé
down-arrow infinity branch preserves the realized-branch interface. -/
private def padeR_realizedDownArrowInfinityBranch_withZeroSupport
    {n d : ℕ}
    (branch : RealizedDownArrowInfinityBranch (padeR n d)) :
    RealizedDownArrowInfinityBranch (padeR n d) := by
  refine
    { branch :=
        { support := branch.branch.toGlobalOrderArrowBranch.support ∪ ({0} : Set ℂ)
          support_connected := ?_
          support_subset_orderWeb := ?_
          origin_mem_closure := ?_
          tangentAngle := branch.branch.tangentAngle
          tangentDown := branch.branch.tangentDown }
      continuesLocalGerm := ?_
      escapesEveryClosedBall := ?_ }
  · exact isConnected_union_zero_of_zero_mem_closure
      branch.branch.toGlobalOrderArrowBranch.support_connected
      branch.branch.toGlobalOrderArrowBranch.origin_mem_closure
  · intro z hz
    rcases hz with hz | hz
    · exact branch.branch.toGlobalOrderArrowBranch.support_subset_orderWeb hz
    · have hz0 : z = 0 := by simpa using hz
      subst hz0
      exact padeR_mem_orderWeb_zero n d
  · exact subset_closure (by simp : (0 : ℂ) ∈
      (branch.branch.toGlobalOrderArrowBranch.support ∪ ({0} : Set ℂ)))
  · intro aperture haperture radius hradius
    rcases branch.continuesLocalGerm aperture haperture radius hradius with
      ⟨z, hzsupport, hzcone⟩
    exact ⟨z, Or.inl hzsupport, hzcone⟩
  · intro r hr
    rcases branch.escapesEveryClosedBall r hr with ⟨z, hzsupport, hzfar⟩
    exact ⟨z, Or.inl hzsupport, hzfar⟩

theorem padeR_exists_realizedDownArrowInfinityBranch_with_zero_mem_support
    {n d : ℕ}
    (branch : RealizedDownArrowInfinityBranch (padeR n d)) :
    ∃ branch' : RealizedDownArrowInfinityBranch (padeR n d),
      (0 : ℂ) ∈ branch'.branch.toGlobalOrderArrowBranch.support := by
  refine ⟨padeR_realizedDownArrowInfinityBranch_withZeroSupport branch, ?_⟩
  simp [padeR_realizedDownArrowInfinityBranch_withZeroSupport]

/-- Cycle-300 truth audit: adjoining `{0}` to the support of a realized Padé
up-arrow infinity branch preserves the realized-branch interface. -/
private def padeR_realizedUpArrowInfinityBranch_withZeroSupport
    {n d : ℕ}
    (branch : RealizedUpArrowInfinityBranch (padeR n d)) :
    RealizedUpArrowInfinityBranch (padeR n d) := by
  refine
    { branch :=
        { support := branch.branch.toGlobalOrderArrowBranch.support ∪ ({0} : Set ℂ)
          support_connected := ?_
          support_subset_orderWeb := ?_
          origin_mem_closure := ?_
          tangentAngle := branch.branch.tangentAngle
          tangentUp := branch.branch.tangentUp }
      continuesLocalGerm := ?_
      escapesEveryClosedBall := ?_ }
  · exact isConnected_union_zero_of_zero_mem_closure
      branch.branch.toGlobalOrderArrowBranch.support_connected
      branch.branch.toGlobalOrderArrowBranch.origin_mem_closure
  · intro z hz
    rcases hz with hz | hz
    · exact branch.branch.toGlobalOrderArrowBranch.support_subset_orderWeb hz
    · have hz0 : z = 0 := by simpa using hz
      subst hz0
      exact padeR_mem_orderWeb_zero n d
  · exact subset_closure (by simp : (0 : ℂ) ∈
      (branch.branch.toGlobalOrderArrowBranch.support ∪ ({0} : Set ℂ)))
  · intro aperture haperture radius hradius
    rcases branch.continuesLocalGerm aperture haperture radius hradius with
      ⟨z, hzsupport, hzcone⟩
    exact ⟨z, Or.inl hzsupport, hzcone⟩
  · intro r hr
    rcases branch.escapesEveryClosedBall r hr with ⟨z, hzsupport, hzfar⟩
    exact ⟨z, Or.inl hzsupport, hzfar⟩

theorem padeR_exists_realizedUpArrowInfinityBranch_with_zero_mem_support
    {n d : ℕ}
    (branch : RealizedUpArrowInfinityBranch (padeR n d)) :
    ∃ branch' : RealizedUpArrowInfinityBranch (padeR n d),
      (0 : ℂ) ∈ branch'.branch.toGlobalOrderArrowBranch.support := by
  refine ⟨padeR_realizedUpArrowInfinityBranch_withZeroSupport branch, ?_⟩
  simp [padeR_realizedUpArrowInfinityBranch_withZeroSupport]

/-- Padé-local packaging helper for the strengthened no-infinity seam.
This makes the remaining concrete gap explicit: produce the down-arrow and
up-arrow realized infinity witness families separately, then assemble them into
`RealizesInfinityBranchGerms (padeR n d) data`. -/
def realizesInfinityBranchGerms_of_padeR
    {n d : ℕ} {data : OrderArrowTerminationData}
    (hdown : PadeRRealizedDownArrowInfinityWitnessFamily n d data)
    (hup : PadeRRealizedUpArrowInfinityWitnessFamily n d data) :
    RealizesInfinityBranchGerms (padeR n d) data := by
  exact ⟨hdown, hup⟩

def realizesInfinityBranchGermsEquiv_of_padeR
    {n d : ℕ} {data : OrderArrowTerminationData} :
    RealizesInfinityBranchGerms (padeR n d) data ≃
      (PadeRRealizedDownArrowInfinityWitnessFamily n d data ×
        PadeRRealizedUpArrowInfinityWitnessFamily n d data) := by
  refine
    { toFun := fun hreal =>
        ⟨hreal.downArrowInfinityWitnesses, hreal.upArrowInfinityWitnesses⟩
      invFun := fun hreal => ⟨hreal.1, hreal.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro hreal
    cases hreal
    rfl
  · intro hreal
    cases hreal
    rfl

theorem thm_355D_of_padeR
    (n d : ℕ) (data : OrderArrowTerminationData)
    (happrox : IsRationalApproxToExp data)
    (hreal : RealizesInfinityBranchGerms (padeR n d) data)
    (hconcrete : ConcreteRationalApproxToExp (padeR n d) data) :
    SatisfiesArrowCountInequality data.toOrderArrowCountData := by
  simpa using
    (thm_355D_of_concreteRationalApprox
      (R := padeR n d) data happrox hreal hconcrete)

theorem thm_355E'_of_padeR
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hpade : IsPadeApproxToExp data)
    (hreal : RealizesInfinityBranchGerms (padeR n d) data)
    (hconcrete : ConcreteRationalApproxToExp (padeR n d) data) :
    data.downArrowsAtZeros = data.numeratorDegree ∧
    data.upArrowsAtPoles = data.denominatorDegree := by
  simpa using
    (thm_355E'_of_concreteRationalApprox
      (R := padeR n d) data hpade hreal hconcrete)

/-- Remaining theorem-local blocker after the explicit-sign seam repair:
to feed the generic `OrderStars` contradiction theorem, a Padé down-arrow
direction still has to imply the positive cosine sign consumed by the honest
local cone feeder. -/
def PadeRDownArrowSignBridge (n d : ℕ) : Prop :=
  ∀ θ : ℝ, IsDownArrowDir (padeR n d) θ →
    0 < padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ)

/-- Up-arrow companion to `PadeRDownArrowSignBridge`. -/
def PadeRUpArrowSignBridge (n d : ℕ) : Prop :=
  ∀ θ : ℝ, IsUpArrowDir (padeR n d) θ →
    padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) < 0

private theorem exact_ray_mem_rayConeNearOrigin
    (θ aperture radius t : ℝ)
    (haperture : 0 < aperture)
    (ht : t ∈ Set.Ioo (0 : ℝ) radius) :
    ((↑t : ℂ) * exp (↑θ * I)) ∈ rayConeNearOrigin θ aperture radius := by
  refine ⟨t, ht, ?_⟩
  have hclose : 0 < aperture * t := mul_pos haperture ht.1
  simpa using hclose

private theorem exact_angle_arc_mem_rayConeNearOrigin
    (θ aperture radius t η : ℝ)
    (_haperture : 0 < aperture)
    (ht : t ∈ Set.Ioo (0 : ℝ) radius)
    (hη : η < aperture) :
    ∀ s ∈ Set.Icc (-η) η,
      ((↑t : ℂ) * exp (↑(θ + s) * I)) ∈ rayConeNearOrigin θ aperture radius := by
  intro s hs
  refine ⟨t, ht, ?_⟩
  have hs_abs : |s| ≤ η := abs_le.mpr ⟨hs.1, hs.2⟩
  have hs_bound : ‖exp (↑s * I) - (1 : ℂ)‖ < aperture := by
    calc
      ‖exp (↑s * I) - (1 : ℂ)‖ ≤ ‖s‖ := by
        simpa [mul_comm] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := s))
      _ = |s| := by simp
      _ ≤ η := hs_abs
      _ < aperture := hη
  have hangle : ((↑(θ + s) : ℂ) * I) = I * ↑θ + I * ↑s := by
    simp [mul_add, mul_comm]
  have hexp :
      exp (↑(θ + s) * I) = exp (↑θ * I) * exp (↑s * I) := by
    rw [hangle, exp_add]
    simp [mul_comm]
  have hdist_eq :
      (↑t : ℂ) * exp (↑(θ + s) * I) - (↑t : ℂ) * exp (↑θ * I) =
        ((↑t : ℂ) * exp (↑θ * I)) * (exp (↑s * I) - 1) := by
    rw [hexp]
    ring
  calc
    ‖(↑t : ℂ) * exp (↑(θ + s) * I) - (↑t : ℂ) * exp (↑θ * I)‖
        = ‖((↑t : ℂ) * exp (↑θ * I)) * (exp (↑s * I) - 1)‖ := by rw [hdist_eq]
    _ = ‖(↑t : ℂ) * exp (↑θ * I)‖ * ‖exp (↑s * I) - 1‖ := norm_mul _ _
    _ = t * ‖exp (↑s * I) - 1‖ := by rw [norm_ofReal_mul_exp_I t θ ht.1.le]
    _ < t * aperture := mul_lt_mul_of_pos_left hs_bound ht.1
    _ = aperture * t := by ring

private theorem padeR_exp_neg_re_pos_of_small_norm
    (n d : ℕ) :
    ∃ δ > 0, ∀ z : ℂ, ‖z‖ < δ →
      0 < Complex.re (padeR n d z * exp (-z)) := by
  obtain ⟨K, δ₀, hK, hδ, hφ⟩ := padeR_exp_neg_local_bound n d
  let Cabs : ℝ := |padePhiErrorConst n d|
  let δ : ℝ := min (δ₀ / 2) (min 1 (1 / (4 * (Cabs + K))))
  have hsum_pos : 0 < Cabs + K := by
    dsimp [Cabs]
    positivity
  have hδpos : 0 < δ := by
    refine lt_min (half_pos hδ) ?_
    refine lt_min zero_lt_one ?_
    positivity
  refine ⟨δ, hδpos, ?_⟩
  intro z hz
  have hzδhalf : ‖z‖ < δ₀ / 2 := lt_of_lt_of_le hz (min_le_left _ _)
  have hzδ₀ : ‖z‖ < δ₀ := by linarith
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

theorem padeR_even_downArrowArcPhaseBridge_of_pos_errorConst
    (n d : ℕ) (hC : 0 < padePhiErrorConst n d) :
    PadeROrderWebArcPhaseBridgeNearOrigin n d 0 := by
  intro aperture haperture radius hradius
  obtain ⟨δre, hδre_pos, hre_small⟩ := padeR_exp_neg_re_pos_of_small_norm n d
  let p1 : ℝ := ((↑(n + d) + 1) : ℝ)
  have hp1_pos : 0 < p1 := by
    dsimp [p1]
    positivity
  let η : ℝ := min (aperture / 2) (1 / p1)
  have hη_pos : 0 < η := by
    refine lt_min (half_pos haperture) ?_
    exact one_div_pos.mpr hp1_pos
  have hη_lt_aperture : η < aperture := by
    have hhalf : aperture / 2 < aperture := by linarith
    exact lt_of_le_of_lt (min_le_left _ _) hhalf
  have hηpi : p1 * η < Real.pi := by
    have hη_one : p1 * η ≤ 1 := by
      have hη_le : η ≤ 1 / p1 := min_le_right _ _
      have hmul := mul_le_mul_of_nonneg_left hη_le hp1_pos.le
      have hp1_ne : p1 ≠ 0 := ne_of_gt hp1_pos
      rw [show p1 * (1 / p1) = 1 by field_simp [hp1_ne]] at hmul
      exact hmul
    linarith [Real.pi_gt_three]
  let radius' : ℝ := min radius δre
  have hradius' : 0 < radius' := by
    exact lt_min hradius hδre_pos
  rcases padeR_even_downArrowArcEndpointSigns_of_pos_errorConst n d hC hη_pos hηpi radius' hradius' with
    ⟨t, ht, him_left, him_right⟩
  have ht_radius : t ∈ Set.Ioo (0 : ℝ) radius := by
    refine ⟨ht.1, ?_⟩
    exact lt_of_lt_of_le ht.2 (min_le_left _ _)
  have ht_δre : t < δre := by
    exact lt_of_lt_of_le ht.2 (min_le_right _ _)
  refine ⟨t, ht_radius, η, hη_pos, ?_, ?_, ?_, ?_⟩
  · exact exact_angle_arc_mem_rayConeNearOrigin 0 aperture radius t η haperture ht_radius hη_lt_aperture
  · intro s hs
    apply hre_small
    simpa using (norm_ofReal_mul_exp_I t s ht_radius.1.le).trans_lt ht_δre
  · simpa using him_left
  · simpa using him_right

theorem padeR_even_downArrowOrderWebMeetsRayConeNearOrigin_of_pos_errorConst
    (n d : ℕ) (hC : 0 < padePhiErrorConst n d) :
    PadeROrderWebMeetsRayConeNearOrigin n d 0 := by
  exact
    PadeROrderWebMeetsRayConeNearOrigin_of_arcPhaseBridge
      (padeR_even_downArrowArcPhaseBridge_of_pos_errorConst n d hC)

theorem padeRDownArrowOrderWebArcPhaseBridgeInput_of_pos_errorConst
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hC : 0 < padePhiErrorConst n d) :
    PadeRDownArrowOrderWebArcPhaseBridgeInput n d data := by
  refine ⟨?_⟩
  intro _
  refine ⟨0, ?_, ?_⟩
  · simpa using padeR_downArrowDir_of_pos_errorConst n d 0 hC
  · simpa using padeR_even_downArrowArcPhaseBridge_of_pos_errorConst n d hC

theorem padeR_odd_downArrowArcPhaseBridge_of_neg_errorConst
    (n d : ℕ) (hC : padePhiErrorConst n d < 0) :
    PadeROrderWebArcPhaseBridgeNearOrigin n d (Real.pi / ((↑(n + d) + 1) : ℝ)) := by
  intro aperture haperture radius hradius
  obtain ⟨δre, hδre_pos, hre_small⟩ := padeR_exp_neg_re_pos_of_small_norm n d
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
  let radius' : ℝ := min radius δre
  have hradius' : 0 < radius' := by
    exact lt_min hradius hδre_pos
  rcases
      padeR_odd_downArrowArcEndpointSigns_of_neg_errorConst n d hC hη_pos hηpi radius' hradius' with
    ⟨t, ht, him_left, him_right⟩
  have ht_radius : t ∈ Set.Ioo (0 : ℝ) radius := by
    refine ⟨ht.1, ?_⟩
    exact lt_of_lt_of_le ht.2 (min_le_left _ _)
  have ht_δre : t < δre := by
    exact lt_of_lt_of_le ht.2 (min_le_right _ _)
  refine ⟨t, ht_radius, η, hη_pos, ?_, ?_, ?_, ?_⟩
  · exact exact_angle_arc_mem_rayConeNearOrigin θ0 aperture radius t η haperture ht_radius hη_lt_aperture
  · intro s hs
    apply hre_small
    exact (norm_ofReal_mul_exp_I t (θ0 + s) ht_radius.1.le).trans_lt ht_δre
  · exact him_left
  · exact him_right

theorem padeR_odd_downArrowOrderWebMeetsRayConeNearOrigin_of_neg_errorConst
    (n d : ℕ) (hC : padePhiErrorConst n d < 0) :
    PadeROrderWebMeetsRayConeNearOrigin n d (Real.pi / ((↑(n + d) + 1) : ℝ)) := by
  exact
    PadeROrderWebMeetsRayConeNearOrigin_of_arcPhaseBridge
      (padeR_odd_downArrowArcPhaseBridge_of_neg_errorConst n d hC)

theorem padeRDownArrowOrderWebArcPhaseBridgeInput_of_neg_errorConst
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hC : padePhiErrorConst n d < 0) :
    PadeRDownArrowOrderWebArcPhaseBridgeInput n d data := by
  refine ⟨?_⟩
  intro _
  refine ⟨Real.pi / ((↑(n + d) + 1) : ℝ), ?_, ?_⟩
  · simpa using padeR_downArrowDir_of_neg_errorConst_oddAngle n d 0 hC
  · simpa using padeR_odd_downArrowArcPhaseBridge_of_neg_errorConst n d hC

/-- Exact current theorem-local blocker beneath the concrete connected-component
upgrade: the arc-phase bridge already produces order-web witnesses in every
small cone, but it still has to be upgraded to show that all such witnesses can
be chosen inside one fixed connected component of the order web. -/
private theorem padeR_exists_referenceOrderWebWitness_of_arcPhaseBridge
    {n d : ℕ} {θ aperture radius : ℝ}
    (hbridge : PadeROrderWebArcPhaseBridgeNearOrigin n d θ)
    (haperture : 0 < aperture) (hradius : 0 < radius) :
    ∃ z : ℂ,
      z ∈ orderWeb (padeR n d) ∧
        z ∈ rayConeNearOrigin θ aperture radius := by
  rcases
      PadeROrderWebMeetsRayConeNearOrigin_of_arcPhaseBridge
        hbridge aperture haperture radius hradius with
    ⟨z, hzweb, hzcone⟩
  exact ⟨z, hzweb, hzcone⟩

/-- Local component-continuation gap still missing beneath the generic
arc-phase bridge theorem: after fixing one bridge-produced reference witness in
the unit cone, every later bridge-produced witness should lie in the same
connected component of the Padé order web. -/
private theorem padeR_referenceWitness_sameComponentContinuation_of_arcPhaseBridge
    {n d : ℕ} {θ : ℝ}
    (hbridge : PadeROrderWebArcPhaseBridgeNearOrigin n d θ) :
    ∃ z0 ∈ orderWeb (padeR n d),
      z0 ∈ rayConeNearOrigin θ (1 : ℝ) 1 ∧
      ∀ aperture > 0, ∀ radius > 0,
        ∃ z : ℂ,
          z ∈ connectedComponentIn (orderWeb (padeR n d)) z0 ∧
            z ∈ rayConeNearOrigin θ aperture radius := by
  sorry

/-- Exact current theorem-local blocker beneath the concrete connected-component
upgrade: the arc-phase bridge already produces order-web witnesses in every
small cone, but it still has to be upgraded to show that all such witnesses can
be chosen inside one fixed connected component of the order web. -/
theorem PadeROrderWebMeetsRayConeNearOriginInConnectedComponent_of_arcPhaseBridge
    {n d : ℕ} {θ : ℝ}
    (hbridge : PadeROrderWebArcPhaseBridgeNearOrigin n d θ) :
    PadeROrderWebMeetsRayConeNearOriginInConnectedComponent n d θ := by
  rcases
      padeR_referenceWitness_sameComponentContinuation_of_arcPhaseBridge hbridge with
    ⟨z0, hz0, _, hmeets⟩
  refine ⟨z0, hz0, ?_⟩
  intro aperture haperture radius hradius
  rcases hmeets aperture haperture radius hradius with ⟨z, hzcomp, hzcone⟩
  exact ⟨z, ⟨hzcomp, hzcone⟩⟩

/-- Exact current theorem-local gap below the concrete connected-component seam:
choose one even-ray order-web basepoint whose connected component continues to
meet every sufficiently small cone around `θ = 0`. -/
theorem padeR_even_downArrowOrderWebSameComponentContinuation_of_pos_errorConst
    (n d : ℕ) (hC : 0 < padePhiErrorConst n d) :
    ∃ z0 ∈ orderWeb (padeR n d),
      ∀ aperture > 0, ∀ radius > 0,
        ∃ z : ℂ,
          z ∈ connectedComponentIn (orderWeb (padeR n d)) z0 ∧
            z ∈ rayConeNearOrigin 0 aperture radius := by
  have hcomp :=
    PadeROrderWebMeetsRayConeNearOriginInConnectedComponent_of_arcPhaseBridge
      (padeR_even_downArrowArcPhaseBridge_of_pos_errorConst n d hC)
  rcases hcomp with ⟨z0, hz0, hmeets⟩
  refine ⟨z0, hz0, ?_⟩
  intro aperture haperture radius hradius
  rcases hmeets aperture haperture radius hradius with ⟨z, hzmem, hzcone⟩
  exact ⟨z, hzmem, hzcone⟩

/-- Exact current theorem-local gap below the concrete connected-component seam:
choose one odd-ray order-web basepoint whose connected component continues to
meet every sufficiently small cone around
`θ = Real.pi / ((↑(n + d) + 1) : ℝ)`. -/
theorem padeR_odd_downArrowOrderWebSameComponentContinuation_of_neg_errorConst
    (n d : ℕ) (hC : padePhiErrorConst n d < 0) :
    ∃ z0 ∈ orderWeb (padeR n d),
      ∀ aperture > 0, ∀ radius > 0,
        ∃ z : ℂ,
          z ∈ connectedComponentIn (orderWeb (padeR n d)) z0 ∧
            z ∈ rayConeNearOrigin
              (Real.pi / ((↑(n + d) + 1) : ℝ)) aperture radius := by
  have hcomp :=
    PadeROrderWebMeetsRayConeNearOriginInConnectedComponent_of_arcPhaseBridge
      (padeR_odd_downArrowArcPhaseBridge_of_neg_errorConst n d hC)
  rcases hcomp with ⟨z0, hz0, hmeets⟩
  refine ⟨z0, hz0, ?_⟩
  intro aperture haperture radius hradius
  rcases hmeets aperture haperture radius hradius with ⟨z, hzmem, hzcone⟩
  exact ⟨z, hzmem, hzcone⟩

theorem padeR_even_downArrowOrderWebMeetsRayConeNearOriginInConnectedComponent_of_pos_errorConst
    (n d : ℕ) (hC : 0 < padePhiErrorConst n d) :
    PadeROrderWebMeetsRayConeNearOriginInConnectedComponent n d 0 := by
  rcases
      padeR_even_downArrowOrderWebSameComponentContinuation_of_pos_errorConst n d hC with
    ⟨z0, hz0, hcontinue⟩
  refine ⟨z0, hz0, ?_⟩
  intro aperture haperture radius hradius
  rcases hcontinue aperture haperture radius hradius with ⟨z, hzcomp, hzcone⟩
  exact ⟨z, ⟨hzcomp, hzcone⟩⟩

theorem padeR_odd_downArrowOrderWebMeetsRayConeNearOriginInConnectedComponent_of_neg_errorConst
    (n d : ℕ) (hC : padePhiErrorConst n d < 0) :
    PadeROrderWebMeetsRayConeNearOriginInConnectedComponent n d
      (Real.pi / ((↑(n + d) + 1) : ℝ)) := by
  rcases
      padeR_odd_downArrowOrderWebSameComponentContinuation_of_neg_errorConst n d hC with
    ⟨z0, hz0, hcontinue⟩
  refine ⟨z0, hz0, ?_⟩
  intro aperture haperture radius hradius
  rcases hcontinue aperture haperture radius hradius with ⟨z, hzcomp, hzcone⟩
  exact ⟨z, ⟨hzcomp, hzcone⟩⟩

theorem padeRDownArrowOrderWebConnectedComponentMeetInput_of_pos_errorConst
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hC : 0 < padePhiErrorConst n d) :
    PadeRDownArrowOrderWebConnectedComponentMeetInput n d data := by
  refine ⟨?_⟩
  intro _
  refine ⟨0, ?_, ?_⟩
  · simpa using padeR_downArrowDir_of_pos_errorConst n d 0 hC
  · simpa using
      padeR_even_downArrowOrderWebMeetsRayConeNearOriginInConnectedComponent_of_pos_errorConst
        n d hC

theorem padeRDownArrowOrderWebConnectedComponentMeetInput_of_neg_errorConst
    (n d : ℕ) (data : OrderArrowTerminationData)
    (hC : padePhiErrorConst n d < 0) :
    PadeRDownArrowOrderWebConnectedComponentMeetInput n d data := by
  refine ⟨?_⟩
  intro _
  refine ⟨Real.pi / ((↑(n + d) + 1) : ℝ), ?_, ?_⟩
  · simpa using padeR_downArrowDir_of_neg_errorConst_oddAngle n d 0 hC
  · simpa using
      padeR_odd_downArrowOrderWebMeetsRayConeNearOriginInConnectedComponent_of_neg_errorConst
        n d hC

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

theorem concreteRationalApproxToExp_of_padeR
    {n d : ℕ} {data : OrderArrowTerminationData}
    (hcont_orderWeb :
      ContinuousOn (fun z => ‖padeR n d z * exp (-z)‖)
        (orderWeb (padeR n d)))
    (hzero_not_mem_down_support :
      ∀ branch : RealizedDownArrowInfinityBranch (padeR n d),
        (0 : ℂ) ∉ branch.branch.toGlobalOrderArrowBranch.support)
    (hzero_not_mem_up_support :
      ∀ branch : RealizedUpArrowInfinityBranch (padeR n d),
        (0 : ℂ) ∉ branch.branch.toGlobalOrderArrowBranch.support)
    (hno_nonzero_unit_points_on_orderWeb :
      ∀ z : ℂ, z ≠ 0 → z ∈ orderWeb (padeR n d) →
        ‖padeR n d z * exp (-z)‖ = 1 → False)
    (hlocal_minus_near_of_sign :
      ∀ θ : ℝ,
        0 < padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) →
        ∃ aperture > 0, ∃ radius > 0,
          ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
            ‖padeR n d z * exp (-z)‖ < 1)
    (hlocal_plus_near_of_sign :
      ∀ θ : ℝ,
        padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) < 0 →
        ∃ aperture > 0, ∃ radius > 0,
          ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
            1 < ‖padeR n d z * exp (-z)‖)
    (hdown_zeroCosExclusion : PadeRDownArrowZeroCosExclusion n d)
    (hup_zeroCosExclusion : PadeRUpArrowZeroCosExclusion n d)
    (hfar_plus_on_orderWeb :
      ∃ radius > 0, ∀ z : ℂ, z ∈ orderWeb (padeR n d) → radius ≤ ‖z‖ →
        1 < ‖padeR n d z * exp (-z)‖)
    (hfar_minus_on_orderWeb :
      ∃ radius > 0, ∀ z : ℂ, z ∈ orderWeb (padeR n d) → radius ≤ ‖z‖ →
        ‖padeR n d z * exp (-z)‖ < 1) :
    ConcreteRationalApproxToExp (padeR n d) data := by
  have hlocal_minus_near_down :
      ∀ θ : ℝ, IsDownArrowDir (padeR n d) θ →
        ∃ aperture > 0, ∃ radius > 0,
          ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
            ‖padeR n d z * exp (-z)‖ < 1 := by
    intro θ hθ
    have hnonneg := padeR_nonneg_sign_of_downArrowDir n d θ hθ
    have hne : padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) ≠ 0 :=
      hdown_zeroCosExclusion θ hθ
    exact hlocal_minus_near_of_sign θ (lt_of_le_of_ne hnonneg hne.symm)
  have hlocal_plus_near_up :
      ∀ θ : ℝ, IsUpArrowDir (padeR n d) θ →
        ∃ aperture > 0, ∃ radius > 0,
          ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
            1 < ‖padeR n d z * exp (-z)‖ := by
    intro θ hθ
    have hnonpos := padeR_nonpos_sign_of_upArrowDir n d θ hθ
    have hne : padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) ≠ 0 :=
      hup_zeroCosExclusion θ hθ
    exact hlocal_plus_near_of_sign θ (lt_of_le_of_ne hnonpos hne)
  simpa using
    (concreteRationalApproxToExp_of_realizedArrowInfinityBranch_contradictions
      (R := padeR n d) data hcont_orderWeb
      hzero_not_mem_down_support hzero_not_mem_up_support
      hno_nonzero_unit_points_on_orderWeb
      hlocal_minus_near_down hlocal_plus_near_up
      hfar_plus_on_orderWeb hfar_minus_on_orderWeb)

/-- Small Padé-local bundle isolating the cycle-300 blocker: excluding `0`
from the supports of realized infinity branches is extra input, not something
forced by the current realized-branch interface alone. -/
structure PadeRZeroSupportExclusionInput (n d : ℕ) where
  zero_not_mem_down_support :
    ∀ branch : RealizedDownArrowInfinityBranch (padeR n d),
      (0 : ℂ) ∉ branch.branch.toGlobalOrderArrowBranch.support
  zero_not_mem_up_support :
    ∀ branch : RealizedUpArrowInfinityBranch (padeR n d),
      (0 : ℂ) ∉ branch.branch.toGlobalOrderArrowBranch.support

/-- Honest Padé-local unit-level exclusion input. The fully uniform statement
without this extra hypothesis is false already for `padeR 0 0 = 1`, so the
nonzero unit-level exclusion must remain explicit at the no-escape seam. -/
structure PadeRUnitLevelExclusionInput (n d : ℕ) where
  no_nonzero_unit_points_on_orderWeb :
    ∀ z : ℂ, z ≠ 0 → z ∈ orderWeb (padeR n d) →
      ‖padeR n d z * exp (-z)‖ = 1 → False

/-- Honest Padé-local far-field sign input. These large-radius sign controls
are separate analytic feeders and are not forced by the realized-branch germ
interface alone. -/
structure PadeRFarFieldSignInput (n d : ℕ) where
  far_plus_on_orderWeb :
    ∃ radius > 0, ∀ z : ℂ, z ∈ orderWeb (padeR n d) → radius ≤ ‖z‖ →
      1 < ‖padeR n d z * exp (-z)‖
  far_minus_on_orderWeb :
    ∃ radius > 0, ∀ z : ℂ, z ∈ orderWeb (padeR n d) → radius ≤ ‖z‖ →
      ‖padeR n d z * exp (-z)‖ < 1

/-- Minimal Padé-local boundary for the live no-escape seam.
This exposes the exact remaining input below `ConcreteRationalApproxToExp`
without changing the `OrderStars` interface: two realized infinity witness
families together with the explicit small Padé-local analytic bundles that
rule them out and the honest explicit-sign local feeders currently available
in the live Padé file. The remaining zero-cosine exact-ray exclusions stay
theorem-local downstream. -/
structure PadeRConcreteNoEscapeInput
    (n d : ℕ) (data : OrderArrowTerminationData) where
  downArrowInfinityWitnesses : PadeRRealizedDownArrowInfinityWitnessFamily n d data
  upArrowInfinityWitnesses : PadeRRealizedUpArrowInfinityWitnessFamily n d data
  cont_orderWeb :
    ContinuousOn (fun z => ‖padeR n d z * exp (-z)‖)
      (orderWeb (padeR n d))
  zeroSupportExclusion : PadeRZeroSupportExclusionInput n d
  unitLevelExclusion : PadeRUnitLevelExclusionInput n d
  local_minus_near_of_sign :
    ∀ θ : ℝ,
      0 < padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) →
      ∃ aperture > 0, ∃ radius > 0,
        ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
          ‖padeR n d z * exp (-z)‖ < 1
  local_plus_near_of_sign :
    ∀ θ : ℝ,
      padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) < 0 →
      ∃ aperture > 0, ∃ radius > 0,
        ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
          1 < ‖padeR n d z * exp (-z)‖
  farFieldSign : PadeRFarFieldSignInput n d

def PadeRConcreteNoEscapeInput.realizesInfinityBranchGerms
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeRConcreteNoEscapeInput n d data) :
    RealizesInfinityBranchGerms (padeR n d) data := by
  exact realizesInfinityBranchGerms_of_padeR
    h.downArrowInfinityWitnesses h.upArrowInfinityWitnesses

theorem PadeRConcreteNoEscapeInput.concrete
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeRConcreteNoEscapeInput n d data)
    (hdown_zeroCosExclusion : PadeRDownArrowZeroCosExclusion n d)
    (hup_zeroCosExclusion : PadeRUpArrowZeroCosExclusion n d) :
    ConcreteRationalApproxToExp (padeR n d) data := by
  exact concreteRationalApproxToExp_of_padeR
    h.cont_orderWeb
    h.zeroSupportExclusion.zero_not_mem_down_support
    h.zeroSupportExclusion.zero_not_mem_up_support
    h.unitLevelExclusion.no_nonzero_unit_points_on_orderWeb
    h.local_minus_near_of_sign
    h.local_plus_near_of_sign
    hdown_zeroCosExclusion
    hup_zeroCosExclusion
    h.farFieldSign.far_plus_on_orderWeb
    h.farFieldSign.far_minus_on_orderWeb

theorem PadeRConcreteNoEscapeInput.no_nonzero_eq_exp
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeRConcreteNoEscapeInput n d data) :
    ∀ z : ℂ, z ≠ 0 → z ∈ orderWeb (padeR n d) →
      padeR n d z = exp z → False := by
  exact
    (no_nonzero_unit_points_on_orderWeb_iff_no_nonzero_eq_exp
      (R := padeR n d)).1 h.unitLevelExclusion.no_nonzero_unit_points_on_orderWeb

def padeRConcreteNoEscapeInput_of_realizesInfinityBranchGerms_of_inputs
    {n d : ℕ} {data : OrderArrowTerminationData}
    (hreal : RealizesInfinityBranchGerms (padeR n d) data)
    (hcont_orderWeb :
      ContinuousOn (fun z => ‖padeR n d z * exp (-z)‖)
        (orderWeb (padeR n d)))
    (hzero : PadeRZeroSupportExclusionInput n d)
    (hunit : PadeRUnitLevelExclusionInput n d)
    (hfar : PadeRFarFieldSignInput n d) :
    PadeRConcreteNoEscapeInput n d data := by
  exact
    { downArrowInfinityWitnesses := hreal.downArrowInfinityWitnesses
      upArrowInfinityWitnesses := hreal.upArrowInfinityWitnesses
      cont_orderWeb := hcont_orderWeb
      zeroSupportExclusion := hzero
      unitLevelExclusion := hunit
      local_minus_near_of_sign := padeR_local_minus_near_of_errorConst_cos_pos n d
      local_plus_near_of_sign := padeR_local_plus_near_of_errorConst_cos_neg n d
      farFieldSign := hfar }

def padeRConcreteNoEscapeInput_of_realizesInfinityBranchGerms
    {n d : ℕ} {data : OrderArrowTerminationData}
    (hreal : RealizesInfinityBranchGerms (padeR n d) data)
    (hcont_orderWeb :
      ContinuousOn (fun z => ‖padeR n d z * exp (-z)‖)
        (orderWeb (padeR n d)))
    (hzero : PadeRZeroSupportExclusionInput n d)
    (hunit : PadeRUnitLevelExclusionInput n d)
    (hfar : PadeRFarFieldSignInput n d) :
    PadeRConcreteNoEscapeInput n d data := by
  exact padeRConcreteNoEscapeInput_of_realizesInfinityBranchGerms_of_inputs
    hreal
    hcont_orderWeb
    hzero
    hunit
    hfar

/-- Honest Padé-local boundary for the repaired Ehle barrier seam.
This bundles exactly the concrete hypotheses currently needed to apply the
Padé-side no-escape seam together with `ehle_barrier_nat`, while leaving the
remaining zero-cosine exact-ray exclusions for the 355D/355E' endpoint
wrappers as separate theorem-local inputs. This still avoids pretending that
the explicit endpoint counts already supply the separate 355G correction-term
witnesses. -/
structure PadeREhleBarrierInput
    (n d : ℕ) (data : OrderArrowTerminationData) where
  numeratorDegree_eq : data.numeratorDegree = n
  denominatorDegree_eq : data.denominatorDegree = d
  pade : IsPadeApproxToExp data
  noEscape : PadeRConcreteNoEscapeInput n d data
  ehle : EhleBarrierInput data

def padeREhleBarrierInput_of_padeR
    {n d : ℕ} {data : OrderArrowTerminationData}
    (hnum : data.numeratorDegree = n)
    (hden : data.denominatorDegree = d)
    (hpade : IsPadeApproxToExp data)
    (hreal : RealizesInfinityBranchGerms (padeR n d) data)
    (hcont_orderWeb :
      ContinuousOn (fun z => ‖padeR n d z * exp (-z)‖)
        (orderWeb (padeR n d)))
    (hzero : PadeRZeroSupportExclusionInput n d)
    (hunit : PadeRUnitLevelExclusionInput n d)
    (hfar : PadeRFarFieldSignInput n d)
    (hehle : EhleBarrierInput data) :
    PadeREhleBarrierInput n d data := by
  refine ⟨hnum, hden, hpade, ?_, hehle⟩
  exact padeRConcreteNoEscapeInput_of_realizesInfinityBranchGerms
    hreal
    hcont_orderWeb
    hzero
    hunit
    hfar

def PadeREhleBarrierInput.realizesInfinityBranchGerms
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeREhleBarrierInput n d data) :
    RealizesInfinityBranchGerms (padeR n d) data := by
  exact h.noEscape.realizesInfinityBranchGerms

theorem PadeREhleBarrierInput.concrete
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeREhleBarrierInput n d data)
    (hdown_zeroCosExclusion : PadeRDownArrowZeroCosExclusion n d)
    (hup_zeroCosExclusion : PadeRUpArrowZeroCosExclusion n d) :
    ConcreteRationalApproxToExp (padeR n d) data := by
  exact h.noEscape.concrete hdown_zeroCosExclusion hup_zeroCosExclusion

theorem PadeREhleBarrierInput.thm_355D
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeREhleBarrierInput n d data)
    (hdown_zeroCosExclusion : PadeRDownArrowZeroCosExclusion n d)
    (hup_zeroCosExclusion : PadeRUpArrowZeroCosExclusion n d) :
    SatisfiesArrowCountInequality data.toOrderArrowCountData := by
  exact thm_355D_of_padeR n d data h.pade.toIsRationalApproxToExp
    h.realizesInfinityBranchGerms
    (h.concrete hdown_zeroCosExclusion hup_zeroCosExclusion)

theorem PadeREhleBarrierInput.thm_355E'
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeREhleBarrierInput n d data)
    (hdown_zeroCosExclusion : PadeRDownArrowZeroCosExclusion n d)
    (hup_zeroCosExclusion : PadeRUpArrowZeroCosExclusion n d) :
    data.downArrowsAtZeros = data.numeratorDegree ∧
    data.upArrowsAtPoles = data.denominatorDegree := by
  exact thm_355E'_of_padeR n d data h.pade h.realizesInfinityBranchGerms
    (h.concrete hdown_zeroCosExclusion hup_zeroCosExclusion)

/-- Minimal Padé-local input actually used by `ehle_barrier_nat_of_padeR`.
The branch-realization and concrete no-infinity data are needed for the sibling
355D/355E' wrappers, but the Ehle-barrier conclusion itself only depends on the
degree bookkeeping together with `EhleBarrierInput data`. -/
structure PadeREhleBarrierNatInput
    (n d : ℕ) (data : OrderArrowTerminationData) : Prop where
  numeratorDegree_eq : data.numeratorDegree = n
  denominatorDegree_eq : data.denominatorDegree = d
  ehle : EhleBarrierInput data

/-- Forget the extra 355D/355E' Padé-side fields when the only downstream goal
is the Ehle-barrier wedge conclusion. -/
theorem PadeREhleBarrierInput.toNatInput
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeREhleBarrierInput n d data) :
    PadeREhleBarrierNatInput n d data := by
  exact ⟨h.numeratorDegree_eq, h.denominatorDegree_eq, h.ehle⟩

/-- Honest theorem-local Padé boundary for the repaired Ehle barrier:
`ehle_barrier_nat` needs only the degree equalities and the separate 355G
correction-term package. -/
theorem PadeREhleBarrierNatInput.ehle_barrier_nat
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeREhleBarrierNatInput n d data) :
    InEhleWedge n d := by
  exact _root_.ehle_barrier_nat n d
    ⟨data, h.numeratorDegree_eq, h.denominatorDegree_eq, h.ehle⟩

theorem PadeREhleBarrierInput.ehle_barrier_nat
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeREhleBarrierInput n d data) :
    InEhleWedge n d := by
  exact h.toNatInput.ehle_barrier_nat

/-- Concrete zero-side 355G correction witness for the Padé/Ehle seam.
This is the repaired 355G zero-side field specialized to the existing
`IsAStablePadeApprox` bookkeeping: the sector-count inequality is already live,
and A-stability kills the correction term by forcing it to be `0`. -/
theorem padeR_zero_side_correction_of_aStable
    {n d : ℕ} {data : OrderArrowTerminationData}
    (_hnum : data.numeratorDegree = n)
    (_hden : data.denominatorDegree = d)
    (hA : IsAStablePadeApprox data) :
    ∃ zeroCorrection : ℕ,
      data.numeratorDegree ≤ data.denominatorDegree + zeroCorrection ∧
      zeroCorrection = 0 := by
  refine ⟨0, ?_, rfl⟩
  simpa [hA.arrows_zero] using hA.sector_bound_n

/-- Concrete pole-side 355G correction witness for the Padé/Ehle seam. -/
theorem padeR_pole_side_correction_of_aStable
    {n d : ℕ} {data : OrderArrowTerminationData}
    (_hnum : data.numeratorDegree = n)
    (_hden : data.denominatorDegree = d)
    (hA : IsAStablePadeApprox data) :
    ∃ poleCorrection : ℕ,
      data.denominatorDegree ≤ data.numeratorDegree + 2 + poleCorrection ∧
      poleCorrection = 0 := by
  refine ⟨0, ?_, rfl⟩
  simpa [hA.arrows_poles, Nat.add_assoc] using hA.sector_bound_d

/-- Package the repaired 355G-side correction witnesses into the honest
`EhleBarrierInput` consumed by the Ehle barrier. -/
theorem ehleBarrierInput_of_padeR_aStable
    {n d : ℕ} {data : OrderArrowTerminationData}
    (hnum : data.numeratorDegree = n)
    (hden : data.denominatorDegree = d)
    (hA : IsAStablePadeApprox data) :
    EhleBarrierInput data := by
  refine ⟨hA.pade, ?_, ?_⟩
  · exact padeR_zero_side_correction_of_aStable hnum hden hA
  · exact padeR_pole_side_correction_of_aStable hnum hden hA

/-- Direct Padé-side constructor for the minimal theorem-local Ehle seam. -/
theorem padeREhleBarrierNatInput_of_padeR_aStable
    {n d : ℕ} {data : OrderArrowTerminationData}
    (hnum : data.numeratorDegree = n)
    (hden : data.denominatorDegree = d)
    (hA : IsAStablePadeApprox data) :
    PadeREhleBarrierNatInput n d data := by
  exact ⟨hnum, hden, ehleBarrierInput_of_padeR_aStable hnum hden hA⟩

/-- The explicit theorem-local hypothesis still blocking a concrete Padé
application of the Ehle barrier is the repaired 355G input itself. The heavier
Padé bundle remains available for the sibling 355D/355E' consumers. -/
theorem ehle_barrier_nat_of_padeR_of_natInput
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeREhleBarrierNatInput n d data) :
    InEhleWedge n d := by
  exact h.ehle_barrier_nat

/-- The original full Padé-local bundle still yields the Ehle wedge by forgetting
its theorem-local extra fields and using the minimal seam. -/
theorem ehle_barrier_nat_of_padeR_of_input
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeREhleBarrierInput n d data) :
    InEhleWedge n d := by
  exact ehle_barrier_nat_of_padeR_of_natInput h.toNatInput

/-- First concrete Padé-side consumer of the repaired Ehle barrier boundary.
For the wedge conclusion, the no-infinity and realized-branch data are not
theorem-local inputs; the honest seam is just the degree bookkeeping together
with the repaired 355G correction-term package built from
`IsAStablePadeApprox`. -/
theorem ehle_barrier_nat_of_padeR
    {n d : ℕ} {data : OrderArrowTerminationData}
    (hnum : data.numeratorDegree = n)
    (hden : data.denominatorDegree = d)
    (hA : IsAStablePadeApprox data) :
    InEhleWedge n d := by
  exact ehle_barrier_nat_of_padeR_of_natInput
    (padeREhleBarrierNatInput_of_padeR_aStable hnum hden hA)

/-- For Padé order webs, the exact coincidence exclusion is an honest consequence
of the unit-level exclusion already exposed by `OrderStars`. The fully uniform
statement without this extra hypothesis is false already for `padeR 0 0 = 1`. -/
theorem padeR_no_nonzero_eq_exp_on_orderWeb
    (n d : ℕ)
    (hno_nonzero_unit_points_on_orderWeb :
      ∀ z : ℂ, z ≠ 0 → z ∈ orderWeb (padeR n d) →
        ‖padeR n d z * exp (-z)‖ = 1 → False) :
    ∀ z : ℂ, z ≠ 0 → z ∈ orderWeb (padeR n d) →
      padeR n d z = exp z → False := by
  intro z hz_ne hz_web hz_eq
  apply hno_nonzero_unit_points_on_orderWeb z hz_ne hz_web
  calc
    ‖padeR n d z * exp (-z)‖ = ‖exp z * exp (-z)‖ := by simp [hz_eq]
    _ = ‖(1 : ℂ)‖ := by rw [← Complex.exp_add]; simp
    _ = 1 := by simp
