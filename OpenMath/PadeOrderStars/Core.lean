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

theorem padePhiErrorConst_pos_of_even
    (n d : ℕ) (hd : Even d) :
    0 < padePhiErrorConst n d := by
  rcases hd with ⟨k, rfl⟩
  have hpow : ((-1 : ℝ) ^ (k + k)) = 1 := by
    rw [← two_mul, pow_mul]
    norm_num
  rw [padePhiErrorConst, hpow]
  positivity

theorem padePhiErrorConst_neg_of_odd
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

/-- Up-arrow companion to `PadeRTrackedDownArrowBranch`: a concrete global
up-arrow branch that already carries the local ray-tracking datum near the
origin. -/
abbrev PadeRTrackedUpArrowBranch (n d : ℕ) :=
  { branch : GlobalUpArrowBranch (padeR n d) //
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
theorem mem_orderWeb_of_im_zero_of_re_pos
    {R : ℂ → ℂ} {z : ℂ}
    (hre : 0 < (R z * exp (-z)).re)
    (him : (R z * exp (-z)).im = 0) :
    z ∈ orderWeb R := by
  refine ⟨(R z * exp (-z)).re, hre, ?_⟩
  apply Complex.ext <;> simp [him]

/-- The Padé order-star amplitude is continuous along a short exact angle arc once
the Padé denominator is known to stay nonzero there. -/
theorem padeR_exp_neg_continuousOn_angleArc
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

theorem abs_im_sub_le_norm_sub (a b : ℂ) :
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

theorem im_main_term_odd_down_left
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

theorem im_main_term_odd_down_right
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

private theorem padeR_odd_downArrowUniformRadiusPhaseStrip_of_neg_errorConst
    (n d : ℕ) {η : ℝ}
    (hC : padePhiErrorConst n d < 0)
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
        0 < Complex.im (padeR n d w * exp (-w))) ∧
      (∀ r ∈ Set.Ioo (0 : ℝ) δ,
        let w : ℂ :=
          (↑r : ℂ) * exp (↑(Real.pi / ((↑(n + d) + 1) : ℝ) + η) * I)
        Complex.im (padeR n d w * exp (-w)) < 0) := by
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
  let δ : ℝ := min δre (min δ₀ δsign)
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min hδre (lt_min hδ hδsign)
  refine ⟨δ, hδpos, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro r hr s hs
    apply hre_small
    have hrδre : r < δre := by
      exact lt_of_lt_of_le hr.2 (min_le_left _ _)
    exact (norm_ofReal_mul_exp_I r (θ0 + s) hr.1.le).trans_lt hrδre
  · intro r hr
    have hr_delta : r < δ₀ := by
      exact lt_of_lt_of_le hr.2 (le_trans (min_le_right _ _) (min_le_left _ _))
    have hr_sign : r < δsign := by
      exact lt_of_lt_of_le hr.2 (le_trans (min_le_right _ _) (min_le_right _ _))
    have hKt : K * r < (-padePhiErrorConst n d) * Real.sin α / 2 := by
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
        0 < (-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin α -
          K * r ^ (n + d + 2) := by
      have hpow_pos : 0 < r ^ (n + d + 1) := pow_pos hr.1 _
      have hlin : 0 < (-padePhiErrorConst n d) * Real.sin α - K * r := by
        nlinarith [hKt, hnegC, hsin]
      have hrewrite :
          (-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin α - K * r ^ (n + d + 2) =
            r ^ (n + d + 1) * ((-padePhiErrorConst n d) * Real.sin α - K * r) := by
        ring
      rw [hrewrite]
      exact mul_pos hpow_pos hlin
    have hleft_bound :
        (-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin α - K * r ^ (n + d + 2) ≤
          Complex.im (padeR n d zL * exp (-zL)) := by
      have h' := abs_le.mp himdiffL
      linarith [hmainL]
    exact lt_of_lt_of_le hleft_core hleft_bound
  · intro r hr
    have hr_delta : r < δ₀ := by
      exact lt_of_lt_of_le hr.2 (le_trans (min_le_right _ _) (min_le_left _ _))
    have hr_sign : r < δsign := by
      exact lt_of_lt_of_le hr.2 (le_trans (min_le_right _ _) (min_le_right _ _))
    have hKt : K * r < (-padePhiErrorConst n d) * Real.sin α / 2 := by
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
        -((-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin α) +
          K * r ^ (n + d + 2) < 0 := by
      have hpow_pos : 0 < r ^ (n + d + 1) := pow_pos hr.1 _
      have hlin : K * r - (-padePhiErrorConst n d) * Real.sin α < 0 := by
        nlinarith [hKt, hnegC, hsin]
      have hrewrite :
          -((-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin α) + K * r ^ (n + d + 2) =
            r ^ (n + d + 1) * (K * r - (-padePhiErrorConst n d) * Real.sin α) := by
        ring
      rw [hrewrite]
      exact mul_neg_of_pos_of_neg hpow_pos hlin
    have hright_bound :
        Complex.im (padeR n d zR * exp (-zR)) ≤
          -((-padePhiErrorConst n d) * r ^ (n + d + 1) * Real.sin α) +
            K * r ^ (n + d + 2) := by
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
  obtain ⟨δ, hδ, _hre, hleft, hright⟩ :=
    padeR_odd_downArrowUniformRadiusPhaseStrip_of_neg_errorConst n d hC hη hηpi
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
  constructor
  · simpa using hleft t ht_δ
  · simpa using hright t ht_δ

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

/-- Up-arrow companion to `PadeRRayTrackingOrderWebSupport.toTrackedDownArrowBranch`. -/
def PadeRRayTrackingOrderWebSupport.toTrackedUpArrowBranch
    {n d : ℕ} {θ : ℝ}
    (h : PadeRRayTrackingOrderWebSupport n d θ)
    (hθ : IsUpArrowDir (padeR n d) θ) :
    PadeRTrackedUpArrowBranch n d :=
  ⟨{ support := h.support
     support_connected := h.support_connected
     support_subset_orderWeb := h.support_subset_orderWeb
     origin_mem_closure := h.origin_mem_closure
     tangentAngle := θ
     tangentUp := hθ }, h.branchTracksRayNearOrigin⟩

def PadeRTrackedDownArrowBranch.toRayTrackingOrderWebSupport
    {n d : ℕ} (branch : PadeRTrackedDownArrowBranch n d) :
    PadeRRayTrackingOrderWebSupport n d branch.1.tangentAngle :=
  { support := branch.1.support
    support_connected := branch.1.support_connected
    support_subset_orderWeb := branch.1.support_subset_orderWeb
    origin_mem_closure := branch.1.origin_mem_closure
    meets_rayConeNearOrigin := branch.2 }

/-- Up-arrow companion to
`PadeRTrackedDownArrowBranch.toRayTrackingOrderWebSupport`. -/
def PadeRTrackedUpArrowBranch.toRayTrackingOrderWebSupport
    {n d : ℕ} (branch : PadeRTrackedUpArrowBranch n d) :
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

/-- Up-arrow companion to
`nonempty_padeR_trackedDownArrowBranch_iff_exists_rayTrackingSupport`. -/
theorem nonempty_padeR_trackedUpArrowBranch_iff_exists_rayTrackingSupport
    (n d : ℕ) :
    Nonempty (PadeRTrackedUpArrowBranch n d) ↔
      ∃ θ : ℝ, IsUpArrowDir (padeR n d) θ ∧
        Nonempty (PadeRRayTrackingOrderWebSupport n d θ) := by
  constructor
  · rintro ⟨branch⟩
    exact ⟨branch.1.tangentAngle, branch.1.tangentUp,
      ⟨branch.toRayTrackingOrderWebSupport⟩⟩
  · rintro ⟨θ, hθ, ⟨support⟩⟩
    exact ⟨support.toTrackedUpArrowBranch hθ⟩

/-- Count-indexed family of down-arrow branches that already satisfy the local
ray-tracking half of the realized-branch interface. -/
abbrev PadeRTrackedDownArrowInfinityWitnessFamily
    (n d : ℕ) (data : OrderArrowTerminationData) :=
  ∀ _ : Fin data.downArrowsAtInfinity, PadeRTrackedDownArrowBranch n d

/-- Up-arrow companion to `PadeRTrackedDownArrowInfinityWitnessFamily`. -/
abbrev PadeRTrackedUpArrowInfinityWitnessFamily
    (n d : ℕ) (data : OrderArrowTerminationData) :=
  ∀ _ : Fin data.upArrowsAtInfinity, PadeRTrackedUpArrowBranch n d

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

theorem nonempty_padeR_trackedUpArrowInfinityWitnessFamily_iff
    (n d : ℕ) (data : OrderArrowTerminationData) :
    Nonempty (PadeRTrackedUpArrowInfinityWitnessFamily n d data) ↔
      data.upArrowsAtInfinity = 0 ∨
        Nonempty (PadeRTrackedUpArrowBranch n d) := by
  simpa [PadeRTrackedUpArrowInfinityWitnessFamily] using
    (nonempty_finFunction_iff_zero_or_nonempty
      (α := PadeRTrackedUpArrowBranch n d)
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

/-- Honest theorem-local compatibility seam below the up-arrow wrapper chain: a
concrete up-arrow ray whose small-cone order-web witnesses all lie in one
connected component. -/
structure PadeRUpArrowOrderWebConnectedComponentMeetInput
    (n d : ℕ) (data : OrderArrowTerminationData) where
  upOrderWebMeetsRayConeInConnectedComponent_of_upArrowsAtInfinity_pos :
    0 < data.upArrowsAtInfinity →
      ∃ θ : ℝ, IsUpArrowDir (padeR n d) θ ∧
        PadeROrderWebMeetsRayConeNearOriginInConnectedComponent n d θ

/-- Intermediate honest seam between raw cone intersections and the current
up-arrow ray-tracking support input. -/
structure PadeRUpArrowConnectedRayConeSupportInput
    (n d : ℕ) (data : OrderArrowTerminationData) where
  upConnectedRayConeSupport_of_upArrowsAtInfinity_pos :
    0 < data.upArrowsAtInfinity →
      ∃ θ : ℝ, IsUpArrowDir (padeR n d) θ ∧
        Nonempty (PadeRConnectedRayConeOrderWebSupport n d θ)

def PadeRUpArrowOrderWebConnectedComponentMeetInput.toConnectedRayConeSupportInput
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeRUpArrowOrderWebConnectedComponentMeetInput n d data) :
    PadeRUpArrowConnectedRayConeSupportInput n d data := by
  refine ⟨?_⟩
  intro hpos
  rcases h.upOrderWebMeetsRayConeInConnectedComponent_of_upArrowsAtInfinity_pos hpos with
    ⟨θ, hθ, hcomp⟩
  exact ⟨θ, hθ,
    nonempty_connectedRayConeSupport_of_meetsRayConeNearOriginInConnectedComponent hcomp⟩

/-- Honest one-level-lower seam beneath `PadeRUpArrowBranchTrackingInput`. -/
structure PadeRUpArrowRayTrackingSupportInput
    (n d : ℕ) (data : OrderArrowTerminationData) where
  upRayTrackingSupport_of_upArrowsAtInfinity_pos :
    0 < data.upArrowsAtInfinity →
      ∃ θ : ℝ, IsUpArrowDir (padeR n d) θ ∧
        Nonempty (PadeRRayTrackingOrderWebSupport n d θ)

def PadeRUpArrowConnectedRayConeSupportInput.toRayTrackingSupportInput
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeRUpArrowConnectedRayConeSupportInput n d data) :
    PadeRUpArrowRayTrackingSupportInput n d data := by
  refine ⟨?_⟩
  intro hpos
  rcases h.upConnectedRayConeSupport_of_upArrowsAtInfinity_pos hpos with
    ⟨θ, hθ, ⟨support⟩⟩
  exact ⟨θ, hθ, ⟨support.toRayTrackingOrderWebSupport⟩⟩

theorem padeR_exists_trackedUpArrowBranch_of_exists_rayTrackingSupport
    {n d : ℕ}
    (hexists :
      ∃ θ : ℝ, IsUpArrowDir (padeR n d) θ ∧
        Nonempty (PadeRRayTrackingOrderWebSupport n d θ)) :
    Nonempty (PadeRTrackedUpArrowBranch n d) := by
  rcases hexists with ⟨θ, hθ, hsupport⟩
  rcases hsupport with ⟨support⟩
  exact ⟨support.toTrackedUpArrowBranch hθ⟩

/-- Up-arrow companion to `PadeRDownArrowBranchTrackingInput`. -/
structure PadeRUpArrowBranchTrackingInput
    (n d : ℕ) (data : OrderArrowTerminationData) where
  upTrackedBranch_of_upArrowsAtInfinity_pos :
    0 < data.upArrowsAtInfinity →
      Nonempty (PadeRTrackedUpArrowBranch n d)

def PadeRUpArrowRayTrackingSupportInput.toTrackingInput
    {n d : ℕ} {data : OrderArrowTerminationData}
    (h : PadeRUpArrowRayTrackingSupportInput n d data) :
    PadeRUpArrowBranchTrackingInput n d data :=
  ⟨fun hpos =>
    padeR_exists_trackedUpArrowBranch_of_exists_rayTrackingSupport
      (h.upRayTrackingSupport_of_upArrowsAtInfinity_pos hpos)⟩

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

theorem padeR_mem_orderWeb_zero (n d : ℕ) :
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

theorem exact_ray_mem_rayConeNearOrigin
    (θ aperture radius t : ℝ)
    (haperture : 0 < aperture)
    (ht : t ∈ Set.Ioo (0 : ℝ) radius) :
    ((↑t : ℂ) * exp (↑θ * I)) ∈ rayConeNearOrigin θ aperture radius := by
  refine ⟨t, ht, ?_⟩
  have hclose : 0 < aperture * t := mul_pos haperture ht.1
  simpa using hclose

theorem exact_angle_arc_mem_rayConeNearOrigin
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

theorem padeR_exp_neg_re_pos_of_small_norm
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

private theorem padeR_exp_neg_im_zero_on_real_axis
    (n d : ℕ) (t : ℝ) :
    Complex.im (padeR n d (↑t : ℂ) * exp (-((↑t : ℂ)))) = 0 := by
  apply (Complex.conj_eq_iff_im).mp
  rw [map_mul]
  have hExp : (starRingEnd ℂ) (exp (-((↑t : ℂ)))) = exp (-((↑t : ℂ))) := by
    simpa using (Complex.exp_conj (-((↑t : ℂ)))).symm
  rw [hExp]
  have hP : (starRingEnd ℂ) (padeP n d (↑t : ℂ)) = padeP n d (↑t : ℂ) := by
    simp [padeP]
  have hQ : (starRingEnd ℂ) (padeQ n d (↑t : ℂ)) = padeQ n d (↑t : ℂ) := by
    simp [padeQ]
  simp [padeR, map_div₀, hP, hQ]

theorem padeR_mem_orderWeb_on_posRealAxis_of_small_radius
    (n d : ℕ) :
    ∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ, ((↑t : ℂ) ∈ orderWeb (padeR n d)) := by
  obtain ⟨δ, hδpos, hre_small⟩ := padeR_exp_neg_re_pos_of_small_norm n d
  refine ⟨δ, hδpos, ?_⟩
  intro t ht
  have hre : 0 < Complex.re (padeR n d (↑t : ℂ) * exp (-((↑t : ℂ)))) := by
    apply hre_small
    simpa [Real.norm_eq_abs, abs_of_pos ht.1] using ht.2
  have him : Complex.im (padeR n d (↑t : ℂ) * exp (-((↑t : ℂ)))) = 0 :=
    padeR_exp_neg_im_zero_on_real_axis n d t
  exact mem_orderWeb_of_im_zero_of_re_pos hre him

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

/-- The even-ray continuation no longer needs the abstract bridge/selector
scaffold: the exact positive real ray itself lies in the order web for all
sufficiently small radii, so one connected component already meets every small
cone around `θ = 0`. -/
theorem padeR_even_downArrowOrderWebSameComponentContinuation_of_pos_errorConst
    (n d : ℕ) (_hC : 0 < padePhiErrorConst n d) :
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
    have hhalf : radius / 2 < radius := by linarith
    exact lt_of_le_of_lt (min_le_left _ _) hhalf
  have hr_le_r0 : r ≤ r0 := by
    have hhalf : r0 / 2 ≤ r0 := by linarith
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
    rcases hz with ⟨x, hx, rfl⟩
    exact hreal_web x ⟨lt_of_lt_of_le hr_pos hx.1, lt_of_le_of_lt hx.2 hr0_lt_δ⟩
  have hsubset_comp :
      support ⊆ connectedComponentIn (orderWeb (padeR n d)) (↑r0 : ℂ) :=
    hsupport_conn.2.subset_connectedComponentIn hz0support hsupport_web
  exact ⟨(↑r : ℂ), hsubset_comp hzsupport, hzcone⟩
