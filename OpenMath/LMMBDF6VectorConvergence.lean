import Mathlib
import OpenMath.MultistepMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMAB6VectorConvergence

/-! ## BDF6 Vector Quantitative Truncation Chain (Iserles §4.5)

Finite-dimensional vector-valued analogue of the scalar BDF6 truncation chain
in `OpenMath/LMMBDF6Convergence.lean`.

The Lyapunov/global BDF6 theorem is deliberately not included here; see
`.prover-state/issues/bdf4_lyapunov_gap.md`.
-/

namespace LMM

/-- BDF6 vector trajectory predicate:
`y_{n+6} = (360/147)y_{n+5} − (450/147)y_{n+4} + (400/147)y_{n+3}
  − (225/147)y_{n+2} + (72/147)y_{n+1} − (10/147)y_n
  + h • ((60/147) • f(t_{n+6}, y_{n+6}))`.
The new value appears inside `f`, so existence of such a trajectory is a
separate fixed-point problem. -/
structure IsBDF6TrajectoryVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y : ℕ → E) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 6)
      = (360 / 147 : ℝ) • y (n + 5) - (450 / 147 : ℝ) • y (n + 4)
        + (400 / 147 : ℝ) • y (n + 3) - (225 / 147 : ℝ) • y (n + 2)
        + (72 / 147 : ℝ) • y (n + 1) - (10 / 147 : ℝ) • y n
        + h • ((60 / 147 : ℝ) •
            f (t₀ + ((n : ℝ) + 6) * h) (y (n + 6)))

/-- Textbook BDF6 vector residual:
`y(t+6h) - (360/147)y(t+5h) + (450/147)y(t+4h) - (400/147)y(t+3h)
  + (225/147)y(t+2h) - (72/147)y(t+h) + (10/147)y(t)
  - h • ((60/147) • y'(t+6h))`. -/
noncomputable def bdf6VecResidual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) : E :=
  y (t + 6 * h) - (360 / 147 : ℝ) • y (t + 5 * h)
    + (450 / 147 : ℝ) • y (t + 4 * h)
    - (400 / 147 : ℝ) • y (t + 3 * h)
    + (225 / 147 : ℝ) • y (t + 2 * h)
    - (72 / 147 : ℝ) • y (t + h)
    + (10 / 147 : ℝ) • y t
    - h • ((60 / 147 : ℝ) • deriv y (t + 6 * h))

/-- The vector BDF6 residual unfolds to the textbook six-step form. -/
theorem bdf6Vec_localTruncationError_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) :
    bdf6VecResidual h t y
      = y (t + 6 * h) - (360 / 147 : ℝ) • y (t + 5 * h)
        + (450 / 147 : ℝ) • y (t + 4 * h)
        - (400 / 147 : ℝ) • y (t + 3 * h)
        + (225 / 147 : ℝ) • y (t + 2 * h)
        - (72 / 147 : ℝ) • y (t + h)
        + (10 / 147 : ℝ) • y t
        - h • ((60 / 147 : ℝ) • deriv y (t + 6 * h)) := by
  rfl

/-- Forcing decomposition of the BDF6 vector error recurrence. -/
theorem bdf6Vec_one_step_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsBDF6TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    ‖(yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h))
      - (360 / 147 : ℝ) •
          (yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h))
      + (450 / 147 : ℝ) •
          (yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h))
      - (400 / 147 : ℝ) •
          (yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h))
      + (225 / 147 : ℝ) •
          (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))
      - (72 / 147 : ℝ) •
          (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
      + (10 / 147 : ℝ) • (yseq n - y (t₀ + (n : ℝ) * h))‖
    ≤ (60 / 147 : ℝ) * h * L
        * ‖yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)‖
      + ‖bdf6VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set yn : E := yseq n with hyn_def
  set yn1 : E := yseq (n + 1) with hyn1_def
  set yn2 : E := yseq (n + 2) with hyn2_def
  set yn3 : E := yseq (n + 3) with hyn3_def
  set yn4 : E := yseq (n + 4) with hyn4_def
  set yn5 : E := yseq (n + 5) with hyn5_def
  set yn6 : E := yseq (n + 6) with hyn6_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set tn3 : ℝ := t₀ + ((n : ℝ) + 3) * h with htn3_def
  set tn4 : ℝ := t₀ + ((n : ℝ) + 4) * h with htn4_def
  set tn5 : ℝ := t₀ + ((n : ℝ) + 5) * h with htn5_def
  set tn6 : ℝ := t₀ + ((n : ℝ) + 6) * h with htn6_def
  set zn : E := y tn with hzn_def
  set zn1 : E := y tn1 with hzn1_def
  set zn2 : E := y tn2 with hzn2_def
  set zn3 : E := y tn3 with hzn3_def
  set zn4 : E := y tn4 with hzn4_def
  set zn5 : E := y tn5 with hzn5_def
  set zn6 : E := y tn6 with hzn6_def
  set τ : E := bdf6VecResidual h tn y with hτ_def
  have hstep : yn6
      = (360 / 147 : ℝ) • yn5 - (450 / 147 : ℝ) • yn4
        + (400 / 147 : ℝ) • yn3 - (225 / 147 : ℝ) • yn2
        + (72 / 147 : ℝ) • yn1 - (10 / 147 : ℝ) • yn
        + h • ((60 / 147 : ℝ) • f tn6 yn6) := by
    simpa [hyn6_def, hyn5_def, hyn4_def, hyn3_def, hyn2_def, hyn1_def,
      hyn_def, htn6_def] using hy.recurrence n
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
  have htn_5h : tn + 5 * h = tn5 := by
    simp [htn_def, htn5_def]
    ring
  have htn_6h : tn + 6 * h = tn6 := by
    simp [htn_def, htn6_def]
    ring
  have hτ_eq : τ = zn6 - (360 / 147 : ℝ) • zn5
        + (450 / 147 : ℝ) • zn4 - (400 / 147 : ℝ) • zn3
        + (225 / 147 : ℝ) • zn2 - (72 / 147 : ℝ) • zn1
        + (10 / 147 : ℝ) • zn
        - h • ((60 / 147 : ℝ) • f tn6 zn6) := by
    show bdf6VecResidual h tn y = _
    unfold bdf6VecResidual
    rw [htn_h, htn_2h, htn_3h, htn_4h, htn_5h, htn_6h, hyf tn6]
  have halg : (yn6 - zn6) - (360 / 147 : ℝ) • (yn5 - zn5)
        + (450 / 147 : ℝ) • (yn4 - zn4)
        - (400 / 147 : ℝ) • (yn3 - zn3)
        + (225 / 147 : ℝ) • (yn2 - zn2)
        - (72 / 147 : ℝ) • (yn1 - zn1)
        + (10 / 147 : ℝ) • (yn - zn)
      = h • ((60 / 147 : ℝ) • (f tn6 yn6 - f tn6 zn6)) - τ := by
    conv_lhs => rw [hstep]
    rw [hτ_eq]
    simp only [smul_sub, smul_smul]
    module
  have hLip : ‖f tn6 yn6 - f tn6 zn6‖ ≤ L * ‖yn6 - zn6‖ := hf tn6 yn6 zn6
  have h60147_nn : (0 : ℝ) ≤ (60 / 147 : ℝ) := by norm_num
  have h_term :
      ‖h • ((60 / 147 : ℝ) • (f tn6 yn6 - f tn6 zn6))‖
        ≤ (60 / 147 : ℝ) * h * L * ‖yn6 - zn6‖ := by
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hh,
      Real.norm_of_nonneg h60147_nn]
    calc h * ((60 / 147 : ℝ) * ‖f tn6 yn6 - f tn6 zn6‖)
        ≤ h * ((60 / 147 : ℝ) * (L * ‖yn6 - zn6‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ hh
          exact mul_le_mul_of_nonneg_left hLip h60147_nn
      _ = (60 / 147 : ℝ) * h * L * ‖yn6 - zn6‖ := by ring
  have htri :
      ‖h • ((60 / 147 : ℝ) • (f tn6 yn6 - f tn6 zn6)) - τ‖
        ≤ ‖h • ((60 / 147 : ℝ) • (f tn6 yn6 - f tn6 zn6))‖ + ‖τ‖ :=
    norm_sub_le _ _
  calc
    ‖(yn6 - zn6) - (360 / 147 : ℝ) • (yn5 - zn5)
        + (450 / 147 : ℝ) • (yn4 - zn4)
        - (400 / 147 : ℝ) • (yn3 - zn3)
        + (225 / 147 : ℝ) • (yn2 - zn2)
        - (72 / 147 : ℝ) • (yn1 - zn1)
        + (10 / 147 : ℝ) • (yn - zn)‖
        = ‖h • ((60 / 147 : ℝ) • (f tn6 yn6 - f tn6 zn6)) - τ‖ := by
          rw [halg]
    _ ≤ ‖h • ((60 / 147 : ℝ) • (f tn6 yn6 - f tn6 zn6))‖ + ‖τ‖ := htri
    _ ≤ (60 / 147 : ℝ) * h * L * ‖yn6 - zn6‖ + ‖τ‖ := by
      linarith [h_term]

private lemma bdf6Vec_pointwise_residual_alg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h M : ℝ) (A B C D E' F G : E)
    (hA : ‖A‖ ≤ M * (6 * h) ^ 7 / 5040)
    (hB : ‖B‖ ≤ M * (5 * h) ^ 7 / 5040)
    (hC : ‖C‖ ≤ M * (4 * h) ^ 7 / 5040)
    (hD : ‖D‖ ≤ M * (3 * h) ^ 7 / 5040)
    (hE : ‖E'‖ ≤ M * (2 * h) ^ 7 / 5040)
    (hF : ‖F‖ ≤ M * h ^ 7 / 5040)
    (hG : ‖G‖ ≤ M * (6 * h) ^ 6 / 720)
    (hh : 0 ≤ h) (hMnn : 0 ≤ M) :
    ‖A - (360 / 147 : ℝ) • B + (450 / 147 : ℝ) • C
        - (400 / 147 : ℝ) • D + (225 / 147 : ℝ) • E'
        - (72 / 147 : ℝ) • F
        - ((60 / 147 : ℝ) * h) • G‖
      ≤ 132 * M * h ^ 7 := by
  have h60147h_nn : 0 ≤ (60 / 147 : ℝ) * h := mul_nonneg (by norm_num) hh
  have htri :
      ‖A - (360 / 147 : ℝ) • B + (450 / 147 : ℝ) • C
          - (400 / 147 : ℝ) • D + (225 / 147 : ℝ) • E'
          - (72 / 147 : ℝ) • F
          - ((60 / 147 : ℝ) * h) • G‖
      ≤ ‖A‖ + (360 / 147 : ℝ) * ‖B‖ + (450 / 147 : ℝ) * ‖C‖
          + (400 / 147 : ℝ) * ‖D‖ + (225 / 147 : ℝ) * ‖E'‖
          + (72 / 147 : ℝ) * ‖F‖
          + (60 / 147 : ℝ) * h * ‖G‖ := by
    have h1 :
        ‖A - (360 / 147 : ℝ) • B + (450 / 147 : ℝ) • C
            - (400 / 147 : ℝ) • D + (225 / 147 : ℝ) • E'
            - (72 / 147 : ℝ) • F
            - ((60 / 147 : ℝ) * h) • G‖
        ≤ ‖A - (360 / 147 : ℝ) • B + (450 / 147 : ℝ) • C
              - (400 / 147 : ℝ) • D + (225 / 147 : ℝ) • E'
              - (72 / 147 : ℝ) • F‖
            + ‖((60 / 147 : ℝ) * h) • G‖ := norm_sub_le _ _
    have h2 :
        ‖A - (360 / 147 : ℝ) • B + (450 / 147 : ℝ) • C
            - (400 / 147 : ℝ) • D + (225 / 147 : ℝ) • E'
            - (72 / 147 : ℝ) • F‖
        ≤ ‖A - (360 / 147 : ℝ) • B + (450 / 147 : ℝ) • C
              - (400 / 147 : ℝ) • D + (225 / 147 : ℝ) • E'‖
            + ‖(72 / 147 : ℝ) • F‖ := norm_sub_le _ _
    have h3 :
        ‖A - (360 / 147 : ℝ) • B + (450 / 147 : ℝ) • C
            - (400 / 147 : ℝ) • D + (225 / 147 : ℝ) • E'‖
        ≤ ‖A - (360 / 147 : ℝ) • B + (450 / 147 : ℝ) • C
              - (400 / 147 : ℝ) • D‖
            + ‖(225 / 147 : ℝ) • E'‖ := norm_add_le _ _
    have h4 :
        ‖A - (360 / 147 : ℝ) • B + (450 / 147 : ℝ) • C
            - (400 / 147 : ℝ) • D‖
        ≤ ‖A - (360 / 147 : ℝ) • B + (450 / 147 : ℝ) • C‖
            + ‖(400 / 147 : ℝ) • D‖ := norm_sub_le _ _
    have h5 :
        ‖A - (360 / 147 : ℝ) • B + (450 / 147 : ℝ) • C‖
        ≤ ‖A - (360 / 147 : ℝ) • B‖ + ‖(450 / 147 : ℝ) • C‖ :=
      norm_add_le _ _
    have h6 :
        ‖A - (360 / 147 : ℝ) • B‖
        ≤ ‖A‖ + ‖(360 / 147 : ℝ) • B‖ := norm_sub_le _ _
    have e360 : ‖(360 / 147 : ℝ) • B‖ = (360 / 147 : ℝ) * ‖B‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 360 / 147)]
    have e450 : ‖(450 / 147 : ℝ) • C‖ = (450 / 147 : ℝ) * ‖C‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 450 / 147)]
    have e400 : ‖(400 / 147 : ℝ) • D‖ = (400 / 147 : ℝ) * ‖D‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 400 / 147)]
    have e225 : ‖(225 / 147 : ℝ) • E'‖ = (225 / 147 : ℝ) * ‖E'‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 225 / 147)]
    have e72 : ‖(72 / 147 : ℝ) • F‖ = (72 / 147 : ℝ) * ‖F‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 72 / 147)]
    have e60 : ‖((60 / 147 : ℝ) * h) • G‖ = (60 / 147 : ℝ) * h * ‖G‖ := by
      rw [norm_smul, Real.norm_of_nonneg h60147h_nn]
    linarith [h1, h2, h3, h4, h5, h6, e360.le, e360.ge,
      e450.le, e450.ge, e400.le, e400.ge, e225.le, e225.ge,
      e72.le, e72.ge, e60.le, e60.ge]
  have h360B_bd : (360 / 147 : ℝ) * ‖B‖
      ≤ (360 / 147 : ℝ) * (M * (5 * h) ^ 7 / 5040) :=
    mul_le_mul_of_nonneg_left hB (by norm_num)
  have h450C_bd : (450 / 147 : ℝ) * ‖C‖
      ≤ (450 / 147 : ℝ) * (M * (4 * h) ^ 7 / 5040) :=
    mul_le_mul_of_nonneg_left hC (by norm_num)
  have h400D_bd : (400 / 147 : ℝ) * ‖D‖
      ≤ (400 / 147 : ℝ) * (M * (3 * h) ^ 7 / 5040) :=
    mul_le_mul_of_nonneg_left hD (by norm_num)
  have h225E_bd : (225 / 147 : ℝ) * ‖E'‖
      ≤ (225 / 147 : ℝ) * (M * (2 * h) ^ 7 / 5040) :=
    mul_le_mul_of_nonneg_left hE (by norm_num)
  have h72F_bd : (72 / 147 : ℝ) * ‖F‖
      ≤ (72 / 147 : ℝ) * (M * h ^ 7 / 5040) :=
    mul_le_mul_of_nonneg_left hF (by norm_num)
  have h60147G_bd : (60 / 147 : ℝ) * h * ‖G‖
      ≤ (60 / 147 : ℝ) * h * (M * (6 * h) ^ 6 / 720) :=
    mul_le_mul_of_nonneg_left hG h60147h_nn
  have hbound_alg :
      M * (6 * h) ^ 7 / 5040
        + (360 / 147 : ℝ) * (M * (5 * h) ^ 7 / 5040)
        + (450 / 147 : ℝ) * (M * (4 * h) ^ 7 / 5040)
        + (400 / 147 : ℝ) * (M * (3 * h) ^ 7 / 5040)
        + (225 / 147 : ℝ) * (M * (2 * h) ^ 7 / 5040)
        + (72 / 147 : ℝ) * (M * h ^ 7 / 5040)
        + (60 / 147 : ℝ) * h * (M * (6 * h) ^ 6 / 720)
        = (674636 / 5145 : ℝ) * M * h ^ 7 := by
    ring
  have hh7_nn : 0 ≤ h ^ 7 := by positivity
  have hMh7_nn : 0 ≤ M * h ^ 7 := mul_nonneg hMnn hh7_nn
  have hslack : (674636 / 5145 : ℝ) * M * h ^ 7 ≤ 132 * M * h ^ 7 := by
    have hcoef : (674636 / 5145 : ℝ) ≤ 132 := by norm_num
    have := mul_le_mul_of_nonneg_right hcoef hMh7_nn
    linarith [this]
  linarith [htri, hA, h360B_bd, h450C_bd, h400D_bd, h225E_bd, h72F_bd,
    h60147G_bd, hbound_alg.le, hbound_alg.ge, hslack]

/-- Pointwise BDF6 vector truncation residual bound. -/
theorem bdf6Vec_pointwise_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 7 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 7 y t‖ ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (ht4h : t + 4 * h ∈ Set.Icc a b)
    (ht5h : t + 5 * h ∈ Set.Icc a b)
    (ht6h : t + 6 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    ‖y (t + 6 * h) - (360 / 147 : ℝ) • y (t + 5 * h)
        + (450 / 147 : ℝ) • y (t + 4 * h)
        - (400 / 147 : ℝ) • y (t + 3 * h)
        + (225 / 147 : ℝ) • y (t + 2 * h)
        - (72 / 147 : ℝ) • y (t + h)
        + (10 / 147 : ℝ) • y t
        - h • ((60 / 147 : ℝ) • deriv y (t + 6 * h))‖
      ≤ (132 : ℝ) * M * h ^ 7 := by
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have h5h : 0 ≤ 5 * h := by linarith
  have h6h : 0 ≤ 6 * h := by linarith
  have hRy1 := y_seventh_order_taylor_remainder_vec hy hbnd ht hth hh
  have hRy2 := y_seventh_order_taylor_remainder_vec hy hbnd ht ht2h h2h
  have hRy3 := y_seventh_order_taylor_remainder_vec hy hbnd ht ht3h h3h
  have hRy4 := y_seventh_order_taylor_remainder_vec hy hbnd ht ht4h h4h
  have hRy5 := y_seventh_order_taylor_remainder_vec hy hbnd ht ht5h h5h
  have hRy6 := y_seventh_order_taylor_remainder_vec hy hbnd ht ht6h h6h
  have hRyp6 := derivY_sixth_order_taylor_remainder_vec hy hbnd ht ht6h h6h
  set y0 : E := y t with hy0_def
  set y1 : E := y (t + h) with hy1_def
  set y2 : E := y (t + 2 * h) with hy2_def
  set y3 : E := y (t + 3 * h) with hy3_def
  set y4 : E := y (t + 4 * h) with hy4_def
  set y5 : E := y (t + 5 * h) with hy5_def
  set y6 : E := y (t + 6 * h) with hy6_def
  set d0 : E := deriv y t with hd0_def
  set d6 : E := deriv y (t + 6 * h) with hd6_def
  set dd : E := iteratedDeriv 2 y t with hdd_def
  set ddd : E := iteratedDeriv 3 y t with hddd_def
  set dddd : E := iteratedDeriv 4 y t with hdddd_def
  set ddddd : E := iteratedDeriv 5 y t with hddddd_def
  set dddddd : E := iteratedDeriv 6 y t with hdddddd_def
  have hLTE_eq :
      y6 - (360 / 147 : ℝ) • y5 + (450 / 147 : ℝ) • y4
          - (400 / 147 : ℝ) • y3 + (225 / 147 : ℝ) • y2
          - (72 / 147 : ℝ) • y1
          + (10 / 147 : ℝ) • y0
          - h • ((60 / 147 : ℝ) • d6)
        = (y6 - y0 - (6 * h) • d0
              - (((6 * h) ^ 2) / 2) • dd
              - (((6 * h) ^ 3) / 6) • ddd
              - (((6 * h) ^ 4) / 24) • dddd
              - (((6 * h) ^ 5) / 120) • ddddd
              - (((6 * h) ^ 6) / 720) • dddddd)
          - (360 / 147 : ℝ)
              • (y5 - y0 - (5 * h) • d0
                  - (((5 * h) ^ 2) / 2) • dd
                  - (((5 * h) ^ 3) / 6) • ddd
                  - (((5 * h) ^ 4) / 24) • dddd
                  - (((5 * h) ^ 5) / 120) • ddddd
                  - (((5 * h) ^ 6) / 720) • dddddd)
          + (450 / 147 : ℝ)
              • (y4 - y0 - (4 * h) • d0
                  - (((4 * h) ^ 2) / 2) • dd
                  - (((4 * h) ^ 3) / 6) • ddd
                  - (((4 * h) ^ 4) / 24) • dddd
                  - (((4 * h) ^ 5) / 120) • ddddd
                  - (((4 * h) ^ 6) / 720) • dddddd)
          - (400 / 147 : ℝ)
              • (y3 - y0 - (3 * h) • d0
                  - (((3 * h) ^ 2) / 2) • dd
                  - (((3 * h) ^ 3) / 6) • ddd
                  - (((3 * h) ^ 4) / 24) • dddd
                  - (((3 * h) ^ 5) / 120) • ddddd
                  - (((3 * h) ^ 6) / 720) • dddddd)
          + (225 / 147 : ℝ)
              • (y2 - y0 - (2 * h) • d0
                  - (((2 * h) ^ 2) / 2) • dd
                  - (((2 * h) ^ 3) / 6) • ddd
                  - (((2 * h) ^ 4) / 24) • dddd
                  - (((2 * h) ^ 5) / 120) • ddddd
                  - (((2 * h) ^ 6) / 720) • dddddd)
          - (72 / 147 : ℝ)
              • (y1 - y0 - h • d0 - (h ^ 2 / 2) • dd
                  - (h ^ 3 / 6) • ddd - (h ^ 4 / 24) • dddd
                  - (h ^ 5 / 120) • ddddd - (h ^ 6 / 720) • dddddd)
          - ((60 / 147 : ℝ) * h)
              • (d6 - d0 - (6 * h) • dd
                  - (((6 * h) ^ 2) / 2) • ddd
                  - (((6 * h) ^ 3) / 6) • dddd
                  - (((6 * h) ^ 4) / 24) • ddddd
                  - (((6 * h) ^ 5) / 120) • dddddd) := by
    simp only [smul_sub, smul_smul]
    module
  rw [hLTE_eq]
  set A : E := y6 - y0 - (6 * h) • d0
            - (((6 * h) ^ 2) / 2) • dd
            - (((6 * h) ^ 3) / 6) • ddd
            - (((6 * h) ^ 4) / 24) • dddd
            - (((6 * h) ^ 5) / 120) • ddddd
            - (((6 * h) ^ 6) / 720) • dddddd with hA_def
  set B : E := y5 - y0 - (5 * h) • d0
            - (((5 * h) ^ 2) / 2) • dd
            - (((5 * h) ^ 3) / 6) • ddd
            - (((5 * h) ^ 4) / 24) • dddd
            - (((5 * h) ^ 5) / 120) • ddddd
            - (((5 * h) ^ 6) / 720) • dddddd with hB_def
  set C : E := y4 - y0 - (4 * h) • d0
            - (((4 * h) ^ 2) / 2) • dd
            - (((4 * h) ^ 3) / 6) • ddd
            - (((4 * h) ^ 4) / 24) • dddd
            - (((4 * h) ^ 5) / 120) • ddddd
            - (((4 * h) ^ 6) / 720) • dddddd with hC_def
  set D : E := y3 - y0 - (3 * h) • d0
            - (((3 * h) ^ 2) / 2) • dd
            - (((3 * h) ^ 3) / 6) • ddd
            - (((3 * h) ^ 4) / 24) • dddd
            - (((3 * h) ^ 5) / 120) • ddddd
            - (((3 * h) ^ 6) / 720) • dddddd with hD_def
  set E2 : E := y2 - y0 - (2 * h) • d0
            - (((2 * h) ^ 2) / 2) • dd
            - (((2 * h) ^ 3) / 6) • ddd
            - (((2 * h) ^ 4) / 24) • dddd
            - (((2 * h) ^ 5) / 120) • ddddd
            - (((2 * h) ^ 6) / 720) • dddddd with hE2_def
  set F : E := y1 - y0 - h • d0 - (h ^ 2 / 2) • dd
            - (h ^ 3 / 6) • ddd - (h ^ 4 / 24) • dddd
            - (h ^ 5 / 120) • ddddd - (h ^ 6 / 720) • dddddd with hF_def
  set G : E := d6 - d0 - (6 * h) • dd
            - (((6 * h) ^ 2) / 2) • ddd
            - (((6 * h) ^ 3) / 6) • dddd
            - (((6 * h) ^ 4) / 24) • ddddd
            - (((6 * h) ^ 5) / 120) • dddddd with hG_def
  clear_value A B C D E2 F G
  have hA_bd : ‖A‖ ≤ M * (6 * h) ^ 7 / 5040 := by
    have htmp : ‖A‖ ≤ M / 5040 * (6 * h) ^ 7 := by
      simpa [hA_def, hy6_def, hy0_def, hd0_def, hdd_def, hddd_def,
        hdddd_def, hddddd_def, hdddddd_def] using hRy6
    have hconv : M / 5040 * (6 * h) ^ 7 = M * (6 * h) ^ 7 / 5040 := by ring
    linarith
  have hB_bd : ‖B‖ ≤ M * (5 * h) ^ 7 / 5040 := by
    have htmp : ‖B‖ ≤ M / 5040 * (5 * h) ^ 7 := by
      simpa [hB_def, hy5_def, hy0_def, hd0_def, hdd_def, hddd_def,
        hdddd_def, hddddd_def, hdddddd_def] using hRy5
    have hconv : M / 5040 * (5 * h) ^ 7 = M * (5 * h) ^ 7 / 5040 := by ring
    linarith
  have hC_bd : ‖C‖ ≤ M * (4 * h) ^ 7 / 5040 := by
    have htmp : ‖C‖ ≤ M / 5040 * (4 * h) ^ 7 := by
      simpa [hC_def, hy4_def, hy0_def, hd0_def, hdd_def, hddd_def,
        hdddd_def, hddddd_def, hdddddd_def] using hRy4
    have hconv : M / 5040 * (4 * h) ^ 7 = M * (4 * h) ^ 7 / 5040 := by ring
    linarith
  have hD_bd : ‖D‖ ≤ M * (3 * h) ^ 7 / 5040 := by
    have htmp : ‖D‖ ≤ M / 5040 * (3 * h) ^ 7 := by
      simpa [hD_def, hy3_def, hy0_def, hd0_def, hdd_def, hddd_def,
        hdddd_def, hddddd_def, hdddddd_def] using hRy3
    have hconv : M / 5040 * (3 * h) ^ 7 = M * (3 * h) ^ 7 / 5040 := by ring
    linarith
  have hE_bd : ‖E2‖ ≤ M * (2 * h) ^ 7 / 5040 := by
    have htmp : ‖E2‖ ≤ M / 5040 * (2 * h) ^ 7 := by
      simpa [hE2_def, hy2_def, hy0_def, hd0_def, hdd_def, hddd_def,
        hdddd_def, hddddd_def, hdddddd_def] using hRy2
    have hconv : M / 5040 * (2 * h) ^ 7 = M * (2 * h) ^ 7 / 5040 := by ring
    linarith
  have hF_bd : ‖F‖ ≤ M * h ^ 7 / 5040 := by
    have htmp : ‖F‖ ≤ M / 5040 * h ^ 7 := by
      simpa [hF_def, hy1_def, hy0_def, hd0_def, hdd_def, hddd_def,
        hdddd_def, hddddd_def, hdddddd_def] using hRy1
    have hconv : M / 5040 * h ^ 7 = M * h ^ 7 / 5040 := by ring
    linarith
  have hG_bd : ‖G‖ ≤ M * (6 * h) ^ 6 / 720 := by
    have htmp : ‖G‖ ≤ M / 720 * (6 * h) ^ 6 := by
      simpa [hG_def, hd6_def, hd0_def, hdd_def, hddd_def, hdddd_def,
        hddddd_def, hdddddd_def] using hRyp6
    have hconv : M / 720 * (6 * h) ^ 6 = M * (6 * h) ^ 6 / 720 := by ring
    linarith
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (norm_nonneg _).trans this
  exact bdf6Vec_pointwise_residual_alg h M A B C D E2 F G
    hA_bd hB_bd hC_bd hD_bd hE_bd hF_bd hG_bd hh hMnn

/-- Uniform bound on the BDF6 vector one-step truncation residual on a finite
horizon, given a `C^7` exact solution. -/
theorem bdf6Vec_local_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 7 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 6) * h ≤ T →
        ‖bdf6VecResidual h
            (t₀ + (n : ℝ) * h) y‖
          ≤ C * h ^ 7 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_seven_bounded_on_Icc_vec hy t₀ (t₀ + T + 1)
  refine ⟨(132 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh _hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 6) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 6) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 6) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 6) * h := by nlinarith
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 4 * h ≤ ((n : ℝ) + 6) * h := by nlinarith
    linarith
  have ht5h_mem : t + 5 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 5 * h ≤ ((n : ℝ) + 6) * h := by nlinarith
    linarith
  have ht6h_mem : t + 6 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 6 * h = ((n : ℝ) + 6) * h := by ring
    linarith
  show ‖bdf6VecResidual h t y‖ ≤ 132 * M * h ^ 7
  unfold bdf6VecResidual
  exact bdf6Vec_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem ht3h_mem
    ht4h_mem ht5h_mem ht6h_mem hh.le

end LMM
