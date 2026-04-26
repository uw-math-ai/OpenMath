import OpenMath.MultistepMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMAB4Convergence

/-! ## BDF4 Vector Quantitative Truncation Chain (Iserles §4.5)

Finite-dimensional vector-valued analogue of the scalar BDF4 truncation chain
in `OpenMath/LMMBDF4Convergence.lean`.

The Lyapunov/global BDF4 theorem is deliberately not included here; see
`.prover-state/issues/bdf4_lyapunov_gap.md`.
-/

namespace LMM

/-- BDF4 vector trajectory predicate:
`y_{n+4} = (48/25)y_{n+3} - (36/25)y_{n+2} + (16/25)y_{n+1} - (3/25)y_n
  + h • ((12/25) • f(t_{n+4}, y_{n+4}))`.
The new value appears inside `f`, so existence of such a trajectory is a
separate fixed-point problem. -/
structure IsBDF4TrajectoryVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y : ℕ → E) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 4)
      = (48 / 25 : ℝ) • y (n + 3) - (36 / 25 : ℝ) • y (n + 2)
        + (16 / 25 : ℝ) • y (n + 1) - (3 / 25 : ℝ) • y n
        + h • ((12 / 25 : ℝ) •
            f (t₀ + ((n : ℝ) + 4) * h) (y (n + 4)))

/-- Textbook BDF4 vector residual:
`y(t+4h) - (48/25)y(t+3h) + (36/25)y(t+2h) - (16/25)y(t+h) + (3/25)y(t)
  - h • ((12/25) • y'(t+4h))`. -/
noncomputable def bdf4VecResidual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) : E :=
  y (t + 4 * h) - (48 / 25 : ℝ) • y (t + 3 * h)
    + (36 / 25 : ℝ) • y (t + 2 * h) - (16 / 25 : ℝ) • y (t + h)
    + (3 / 25 : ℝ) • y t - h • ((12 / 25 : ℝ) • deriv y (t + 4 * h))

/-- The vector BDF4 residual unfolds to the textbook four-step form. -/
theorem bdf4Vec_localTruncationError_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) :
    bdf4VecResidual h t y
      = y (t + 4 * h) - (48 / 25 : ℝ) • y (t + 3 * h)
        + (36 / 25 : ℝ) • y (t + 2 * h) - (16 / 25 : ℝ) • y (t + h)
        + (3 / 25 : ℝ) • y t
        - h • ((12 / 25 : ℝ) • deriv y (t + 4 * h)) := by
  rfl

/-- Forcing decomposition of the BDF4 vector error recurrence. -/
theorem bdf4Vec_one_step_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsBDF4TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    ‖(yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h))
      - (48 / 25 : ℝ) •
          (yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h))
      + (36 / 25 : ℝ) •
          (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))
      - (16 / 25 : ℝ) •
          (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
      + (3 / 25 : ℝ) • (yseq n - y (t₀ + (n : ℝ) * h))‖
    ≤ (12 / 25 : ℝ) * h * L
        * ‖yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)‖
      + ‖bdf4VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set yn : E := yseq n with hyn_def
  set yn1 : E := yseq (n + 1) with hyn1_def
  set yn2 : E := yseq (n + 2) with hyn2_def
  set yn3 : E := yseq (n + 3) with hyn3_def
  set yn4 : E := yseq (n + 4) with hyn4_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set tn3 : ℝ := t₀ + ((n : ℝ) + 3) * h with htn3_def
  set tn4 : ℝ := t₀ + ((n : ℝ) + 4) * h with htn4_def
  set zn : E := y tn with hzn_def
  set zn1 : E := y tn1 with hzn1_def
  set zn2 : E := y tn2 with hzn2_def
  set zn3 : E := y tn3 with hzn3_def
  set zn4 : E := y tn4 with hzn4_def
  set τ : E := bdf4VecResidual h tn y with hτ_def
  have hstep : yn4
      = (48 / 25 : ℝ) • yn3 - (36 / 25 : ℝ) • yn2
        + (16 / 25 : ℝ) • yn1 - (3 / 25 : ℝ) • yn
        + h • ((12 / 25 : ℝ) • f tn4 yn4) := by
    simpa [hyn4_def, hyn3_def, hyn2_def, hyn1_def, hyn_def, htn4_def]
      using hy.recurrence n
  have htn_h : tn + h = tn1 := by
    simp [htn_def, htn1_def]
    ring
  have htn_2h : tn + 2 * h = tn2 := by
    simp [htn_def, htn2_def]
    ring
  have htn_3h : tn + 3 * h = tn3 := by
    simp [htn_def, htn3_def]
    ring
  have htn_4h : tn + 4 * h = tn4 := by
    simp [htn_def, htn4_def]
    ring
  have hτ_eq : τ = zn4 - (48 / 25 : ℝ) • zn3
        + (36 / 25 : ℝ) • zn2 - (16 / 25 : ℝ) • zn1
        + (3 / 25 : ℝ) • zn
        - h • ((12 / 25 : ℝ) • f tn4 zn4) := by
    show bdf4VecResidual h tn y = _
    unfold bdf4VecResidual
    rw [htn_h, htn_2h, htn_3h, htn_4h, hyf tn4]
  have halg : (yn4 - zn4) - (48 / 25 : ℝ) • (yn3 - zn3)
        + (36 / 25 : ℝ) • (yn2 - zn2) - (16 / 25 : ℝ) • (yn1 - zn1)
        + (3 / 25 : ℝ) • (yn - zn)
      = h • ((12 / 25 : ℝ) • (f tn4 yn4 - f tn4 zn4)) - τ := by
    conv_lhs => rw [hstep]
    rw [hτ_eq]
    simp only [smul_sub, smul_smul]
    module
  have hLip : ‖f tn4 yn4 - f tn4 zn4‖ ≤ L * ‖yn4 - zn4‖ := hf tn4 yn4 zn4
  have h1225_nn : (0 : ℝ) ≤ (12 / 25 : ℝ) := by norm_num
  have h_term :
      ‖h • ((12 / 25 : ℝ) • (f tn4 yn4 - f tn4 zn4))‖
        ≤ (12 / 25 : ℝ) * h * L * ‖yn4 - zn4‖ := by
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hh,
      Real.norm_of_nonneg h1225_nn]
    calc h * ((12 / 25 : ℝ) * ‖f tn4 yn4 - f tn4 zn4‖)
        ≤ h * ((12 / 25 : ℝ) * (L * ‖yn4 - zn4‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ hh
          exact mul_le_mul_of_nonneg_left hLip h1225_nn
      _ = (12 / 25 : ℝ) * h * L * ‖yn4 - zn4‖ := by ring
  have htri :
      ‖h • ((12 / 25 : ℝ) • (f tn4 yn4 - f tn4 zn4)) - τ‖
        ≤ ‖h • ((12 / 25 : ℝ) • (f tn4 yn4 - f tn4 zn4))‖ + ‖τ‖ :=
    norm_sub_le _ _
  calc
    ‖(yn4 - zn4) - (48 / 25 : ℝ) • (yn3 - zn3)
        + (36 / 25 : ℝ) • (yn2 - zn2) - (16 / 25 : ℝ) • (yn1 - zn1)
        + (3 / 25 : ℝ) • (yn - zn)‖
        = ‖h • ((12 / 25 : ℝ) • (f tn4 yn4 - f tn4 zn4)) - τ‖ := by rw [halg]
    _ ≤ ‖h • ((12 / 25 : ℝ) • (f tn4 yn4 - f tn4 zn4))‖ + ‖τ‖ := htri
    _ ≤ (12 / 25 : ℝ) * h * L * ‖yn4 - zn4‖ + ‖τ‖ := by
      linarith [h_term]

private lemma bdf4Vec_pointwise_residual_alg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h M : ℝ} (hh : 0 ≤ h) (hMnn : 0 ≤ M)
    (A B C D R : E)
    (hA_bd : ‖A‖ ≤ M / 120 * (4 * h) ^ 5)
    (hB_bd : ‖B‖ ≤ M / 120 * (3 * h) ^ 5)
    (hC_bd : ‖C‖ ≤ M / 120 * (2 * h) ^ 5)
    (hD_bd : ‖D‖ ≤ M / 120 * h ^ 5)
    (hR_bd : ‖R‖ ≤ M / 24 * (4 * h) ^ 4) :
    ‖A - (48 / 25 : ℝ) • B + (36 / 25 : ℝ) • C
        - (16 / 25 : ℝ) • D - ((12 / 25 : ℝ) * h) • R‖
      ≤ 18 * M * h ^ 5 := by
  have h1225h_nn : 0 ≤ (12 / 25 : ℝ) * h := mul_nonneg (by norm_num) hh
  have htri :
      ‖A - (48 / 25 : ℝ) • B + (36 / 25 : ℝ) • C
          - (16 / 25 : ℝ) • D - ((12 / 25 : ℝ) * h) • R‖
      ≤ ‖A‖ + (48 / 25 : ℝ) * ‖B‖ + (36 / 25 : ℝ) * ‖C‖
          + (16 / 25 : ℝ) * ‖D‖ + (12 / 25 : ℝ) * h * ‖R‖ := by
    have h1 : ‖A - (48 / 25 : ℝ) • B + (36 / 25 : ℝ) • C
                  - (16 / 25 : ℝ) • D - ((12 / 25 : ℝ) * h) • R‖
        ≤ ‖A - (48 / 25 : ℝ) • B + (36 / 25 : ℝ) • C
              - (16 / 25 : ℝ) • D‖
            + ‖((12 / 25 : ℝ) * h) • R‖ := norm_sub_le _ _
    have h2 : ‖A - (48 / 25 : ℝ) • B + (36 / 25 : ℝ) • C
                  - (16 / 25 : ℝ) • D‖
        ≤ ‖A - (48 / 25 : ℝ) • B + (36 / 25 : ℝ) • C‖
            + ‖(16 / 25 : ℝ) • D‖ := norm_sub_le _ _
    have h3 : ‖A - (48 / 25 : ℝ) • B + (36 / 25 : ℝ) • C‖
        ≤ ‖A - (48 / 25 : ℝ) • B‖ + ‖(36 / 25 : ℝ) • C‖ :=
      norm_add_le _ _
    have h4 : ‖A - (48 / 25 : ℝ) • B‖
        ≤ ‖A‖ + ‖(48 / 25 : ℝ) • B‖ := norm_sub_le _ _
    have e48 : ‖(48 / 25 : ℝ) • B‖ = (48 / 25 : ℝ) * ‖B‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 48 / 25)]
    have e36 : ‖(36 / 25 : ℝ) • C‖ = (36 / 25 : ℝ) * ‖C‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 36 / 25)]
    have e16 : ‖(16 / 25 : ℝ) • D‖ = (16 / 25 : ℝ) * ‖D‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 16 / 25)]
    have e12 : ‖((12 / 25 : ℝ) * h) • R‖ = (12 / 25 : ℝ) * h * ‖R‖ := by
      rw [norm_smul, Real.norm_of_nonneg h1225h_nn]
    linarith [h1, h2, h3, h4, e48.le, e48.ge, e36.le, e36.ge,
      e16.le, e16.ge, e12.le, e12.ge]
  have h48B_bd : (48 / 25 : ℝ) * ‖B‖
      ≤ (48 / 25 : ℝ) * (M / 120 * (3 * h) ^ 5) :=
    mul_le_mul_of_nonneg_left hB_bd (by norm_num)
  have h36C_bd : (36 / 25 : ℝ) * ‖C‖
      ≤ (36 / 25 : ℝ) * (M / 120 * (2 * h) ^ 5) :=
    mul_le_mul_of_nonneg_left hC_bd (by norm_num)
  have h16D_bd : (16 / 25 : ℝ) * ‖D‖
      ≤ (16 / 25 : ℝ) * (M / 120 * h ^ 5) :=
    mul_le_mul_of_nonneg_left hD_bd (by norm_num)
  have h1225R_bd : (12 / 25 : ℝ) * h * ‖R‖
      ≤ (12 / 25 : ℝ) * h * (M / 24 * (4 * h) ^ 4) :=
    mul_le_mul_of_nonneg_left hR_bd h1225h_nn
  have hbound_alg :
      M / 120 * (4 * h) ^ 5
        + (48 / 25 : ℝ) * (M / 120 * (3 * h) ^ 5)
        + (36 / 25 : ℝ) * (M / 120 * (2 * h) ^ 5)
        + (16 / 25 : ℝ) * (M / 120 * h ^ 5)
        + (12 / 25 : ℝ) * h * (M / 24 * (4 * h) ^ 4)
        = (6724 / 375 : ℝ) * M * h ^ 5 := by
    ring
  have hh5_nn : 0 ≤ h ^ 5 := by positivity
  have hMh5_nn : 0 ≤ M * h ^ 5 := mul_nonneg hMnn hh5_nn
  have hslack : (6724 / 375 : ℝ) * M * h ^ 5 ≤ 18 * M * h ^ 5 := by
    have hcoef : (6724 / 375 : ℝ) ≤ 18 := by norm_num
    have := mul_le_mul_of_nonneg_right hcoef hMh5_nn
    linarith
  linarith [htri, hA_bd, h48B_bd, h36C_bd, h16D_bd, h1225R_bd,
    hbound_alg.le, hbound_alg.ge, hslack]

/-- Pointwise BDF4 vector truncation residual bound. -/
theorem bdf4Vec_pointwise_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 5 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 5 y t‖ ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (ht4h : t + 4 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    ‖y (t + 4 * h) - (48 / 25 : ℝ) • y (t + 3 * h)
        + (36 / 25 : ℝ) • y (t + 2 * h) - (16 / 25 : ℝ) • y (t + h)
        + (3 / 25 : ℝ) • y t
        - h • ((12 / 25 : ℝ) • deriv y (t + 4 * h))‖
      ≤ (18 : ℝ) * M * h ^ 5 := by
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have hRy1 := y_fifth_order_taylor_remainder_vec hy hbnd ht hth hh
  have hRy2 := y_fifth_order_taylor_remainder_vec hy hbnd ht ht2h h2h
  have hRy3 := y_fifth_order_taylor_remainder_vec hy hbnd ht ht3h h3h
  have hRy4 := y_fifth_order_taylor_remainder_vec hy hbnd ht ht4h h4h
  have hRyp4 := derivY_fourth_order_taylor_remainder_vec hy hbnd ht ht4h h4h
  set y0 : E := y t with hy0_def
  set y1 : E := y (t + h) with hy1_def
  set y2 : E := y (t + 2 * h) with hy2_def
  set y3 : E := y (t + 3 * h) with hy3_def
  set y4 : E := y (t + 4 * h) with hy4_def
  set d0 : E := deriv y t with hd0_def
  set d4 : E := deriv y (t + 4 * h) with hd4_def
  set dd : E := iteratedDeriv 2 y t with hdd_def
  set ddd : E := iteratedDeriv 3 y t with hddd_def
  set dddd : E := iteratedDeriv 4 y t with hdddd_def
  have hLTE_eq :
      y4 - (48 / 25 : ℝ) • y3 + (36 / 25 : ℝ) • y2
          - (16 / 25 : ℝ) • y1 + (3 / 25 : ℝ) • y0
          - h • ((12 / 25 : ℝ) • d4)
        = (y4 - y0 - (4 * h) • d0
              - (((4 * h) ^ 2) / 2) • dd - (((4 * h) ^ 3) / 6) • ddd
              - (((4 * h) ^ 4) / 24) • dddd)
          - (48 / 25 : ℝ)
              • (y3 - y0 - (3 * h) • d0
                  - (((3 * h) ^ 2) / 2) • dd - (((3 * h) ^ 3) / 6) • ddd
                  - (((3 * h) ^ 4) / 24) • dddd)
          + (36 / 25 : ℝ)
              • (y2 - y0 - (2 * h) • d0
                  - (((2 * h) ^ 2) / 2) • dd - (((2 * h) ^ 3) / 6) • ddd
                  - (((2 * h) ^ 4) / 24) • dddd)
          - (16 / 25 : ℝ)
              • (y1 - y0 - h • d0 - (h ^ 2 / 2) • dd - (h ^ 3 / 6) • ddd
                  - (h ^ 4 / 24) • dddd)
          - ((12 / 25 : ℝ) * h)
              • (d4 - d0 - (4 * h) • dd - (((4 * h) ^ 2) / 2) • ddd
                  - (((4 * h) ^ 3) / 6) • dddd) := by
    simp only [smul_sub, smul_smul]
    module
  rw [hLTE_eq]
  set A : E := y4 - y0 - (4 * h) • d0
            - (((4 * h) ^ 2) / 2) • dd - (((4 * h) ^ 3) / 6) • ddd
            - (((4 * h) ^ 4) / 24) • dddd with hA_def
  set B : E := y3 - y0 - (3 * h) • d0
            - (((3 * h) ^ 2) / 2) • dd - (((3 * h) ^ 3) / 6) • ddd
            - (((3 * h) ^ 4) / 24) • dddd with hB_def
  set C : E := y2 - y0 - (2 * h) • d0
            - (((2 * h) ^ 2) / 2) • dd - (((2 * h) ^ 3) / 6) • ddd
            - (((2 * h) ^ 4) / 24) • dddd with hC_def
  set D : E := y1 - y0 - h • d0 - (h ^ 2 / 2) • dd - (h ^ 3 / 6) • ddd
            - (h ^ 4 / 24) • dddd with hD_def
  set R : E := d4 - d0 - (4 * h) • dd - (((4 * h) ^ 2) / 2) • ddd
            - (((4 * h) ^ 3) / 6) • dddd with hR_def
  clear_value A B C D R
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (norm_nonneg _).trans this
  exact bdf4Vec_pointwise_residual_alg hh hMnn A B C D R hRy4 hRy3 hRy2 hRy1 hRyp4

/-- Uniform bound on the BDF4 vector one-step truncation residual on a finite
horizon, given a `C^5` exact solution. -/
theorem bdf4Vec_local_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 5 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 4) * h ≤ T →
        ‖bdf4VecResidual h
            (t₀ + (n : ℝ) * h) y‖
          ≤ C * h ^ 5 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_five_bounded_on_Icc_vec hy t₀ (t₀ + T + 1)
  refine ⟨(18 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by nlinarith [hn_nn, hh.le], ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 4) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by nlinarith [hn_nn, hh.le], ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 4) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by nlinarith [hn_nn, hh.le], ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 4) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by nlinarith [hn_nn, hh.le], ?_⟩
    have h1 : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 4) * h := by nlinarith
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by nlinarith [hn_nn, hh.le], ?_⟩
    have h1 : (n : ℝ) * h + 4 * h = ((n : ℝ) + 4) * h := by ring
    linarith
  show ‖bdf4VecResidual h t y‖ ≤ 18 * M * h ^ 5
  unfold bdf4VecResidual
  exact bdf4Vec_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem ht3h_mem
    ht4h_mem hh.le

end LMM
