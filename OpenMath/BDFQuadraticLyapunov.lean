import OpenMath.LMMBDF4Convergence
import OpenMath.LMMTruncationOp

/-!
# BDF quadratic Lyapunov infrastructure

Concrete rational Lyapunov certificate for the stable cubic factor of BDF4.
The unit-root coordinate is separated from the three stable coordinates, and
the stable companion block is equipped with an explicit quadratic form.
-/

namespace LMM

/-- Homogeneous BDF4 recurrence defect for an arbitrary scalar sequence. -/
noncomputable def bdf4RecDefect (e : ℕ → ℝ) (n : ℕ) : ℝ :=
  e (n + 4)
    - (48 / 25 : ℝ) * e (n + 3)
    + (36 / 25 : ℝ) * e (n + 2)
    - (16 / 25 : ℝ) * e (n + 1)
    + (3 / 25 : ℝ) * e n

/-- Unnormalized coordinate along the BDF4 unit-root direction. -/
noncomputable def bdf4LyapU (e : ℕ → ℝ) (n : ℕ) : ℝ :=
  -3 * e n + 13 * e (n + 1) - 23 * e (n + 2) + 25 * e (n + 3)

lemma bdf4LyapU_succ_eq (e : ℕ → ℝ) (n : ℕ) :
    bdf4LyapU e (n + 1)
      = bdf4LyapU e n + 25 * bdf4RecDefect e n := by
  unfold bdf4LyapU bdf4RecDefect
  ring

/-- First stable BDF4 coordinate after subtracting the normalized unit part. -/
noncomputable def bdf4StableX0 (e : ℕ → ℝ) (n : ℕ) : ℝ :=
  e n - bdf4LyapU e n / 12

/-- Second stable BDF4 coordinate after subtracting the normalized unit part. -/
noncomputable def bdf4StableX1 (e : ℕ → ℝ) (n : ℕ) : ℝ :=
  e (n + 1) - bdf4LyapU e n / 12

/-- Third stable BDF4 coordinate after subtracting the normalized unit part. -/
noncomputable def bdf4StableX2 (e : ℕ → ℝ) (n : ℕ) : ℝ :=
  e (n + 2) - bdf4LyapU e n / 12

lemma bdf4StableX0_succ_eq (e : ℕ → ℝ) (n : ℕ) :
    bdf4StableX0 e (n + 1)
      = bdf4StableX1 e n - (25 / 12 : ℝ) * bdf4RecDefect e n := by
  unfold bdf4StableX0 bdf4StableX1 bdf4LyapU bdf4RecDefect
  ring

lemma bdf4StableX1_succ_eq (e : ℕ → ℝ) (n : ℕ) :
    bdf4StableX1 e (n + 1)
      = bdf4StableX2 e n - (25 / 12 : ℝ) * bdf4RecDefect e n := by
  unfold bdf4StableX1 bdf4StableX2 bdf4LyapU bdf4RecDefect
  ring

lemma bdf4StableX2_succ_eq (e : ℕ → ℝ) (n : ℕ) :
    bdf4StableX2 e (n + 1)
      = (3 / 25 : ℝ) * bdf4StableX0 e n
        - (13 / 25 : ℝ) * bdf4StableX1 e n
        + (23 / 25 : ℝ) * bdf4StableX2 e n
        - (25 / 12 : ℝ) * bdf4RecDefect e n := by
  unfold bdf4StableX2 bdf4StableX0 bdf4StableX1 bdf4LyapU bdf4RecDefect
  ring

noncomputable def bdf4CubicStep0 (_x0 x1 _x2 : ℝ) : ℝ := x1

noncomputable def bdf4CubicStep1 (_x0 _x1 x2 : ℝ) : ℝ := x2

noncomputable def bdf4CubicStep2 (x0 x1 x2 : ℝ) : ℝ :=
  (3 / 25 : ℝ) * x0 - (13 / 25 : ℝ) * x1 + (23 / 25 : ℝ) * x2

/-- Explicit rational quadratic form satisfying `Aᵀ P A - P = -I` for the
BDF4 stable cubic companion block. -/
noncomputable def bdf4CubicQuad (x0 x1 x2 : ℝ) : ℝ :=
  (1389 / 1280 : ℝ) * x0 ^ 2
    + 2 * (-19 / 60 : ℝ) * x0 * x1
    + 2 * (335 / 768 : ℝ) * x0 * x2
    + (1163 / 360 : ℝ) * x1 ^ 2
    + 2 * (-65 / 36 : ℝ) * x1 * x2
    + (13625 / 2304 : ℝ) * x2 ^ 2

lemma bdf4CubicQuad_step_identity (x0 x1 x2 : ℝ) :
    bdf4CubicQuad
        (bdf4CubicStep0 x0 x1 x2)
        (bdf4CubicStep1 x0 x1 x2)
        (bdf4CubicStep2 x0 x1 x2)
      = bdf4CubicQuad x0 x1 x2 - (x0 ^ 2 + x1 ^ 2 + x2 ^ 2) := by
  unfold bdf4CubicQuad bdf4CubicStep0 bdf4CubicStep1 bdf4CubicStep2
  ring

private lemma two_mul_abs_mul_le_sq_add_sq (a b : ℝ) :
    2 * |a * b| ≤ a ^ 2 + b ^ 2 := by
  cases abs_cases (a * b) <;>
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

private lemma neg_cross_lower_bound (c a b : ℝ) :
    -2 * c * a * b ≤ 2 * |c| * |a * b| := by
  cases abs_cases c <;> cases abs_cases (a * b) <;> nlinarith

private lemma cross_upper_bound (c a b : ℝ) :
    2 * c * a * b ≤ 2 * |c| * |a * b| := by
  cases abs_cases c <;> cases abs_cases (a * b) <;> nlinarith

lemma bdf4CubicQuad_lower (x0 x1 x2 : ℝ) :
    (1 / 4 : ℝ) * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2)
      ≤ bdf4CubicQuad x0 x1 x2 := by
  unfold bdf4CubicQuad
  nlinarith [sq_nonneg (x0 - 2 * x1), sq_nonneg (x0 - 2 * x2),
    sq_nonneg (x1 - 2 * x2), sq_nonneg (x1 - x2),
    sq_nonneg (x0 + x1 + x2)]

lemma bdf4CubicQuad_upper (x0 x1 x2 : ℝ) :
    bdf4CubicQuad x0 x1 x2
      ≤ 9 * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2) := by
  unfold bdf4CubicQuad
  nlinarith [sq_nonneg (x0 - x1), sq_nonneg (x0 - x2),
    sq_nonneg (x1 - x2), sq_nonneg (x0 + x1),
    sq_nonneg (x0 + x2), sq_nonneg (x1 + x2)]

lemma bdf4StableQuad_homogeneous_step_identity
    (e : ℕ → ℝ) (n : ℕ) (hψ : bdf4RecDefect e n = 0) :
    bdf4CubicQuad
        (bdf4StableX0 e (n + 1))
        (bdf4StableX1 e (n + 1))
        (bdf4StableX2 e (n + 1))
      =
    bdf4CubicQuad
        (bdf4StableX0 e n)
        (bdf4StableX1 e n)
        (bdf4StableX2 e n)
      - (bdf4StableX0 e n ^ 2
          + bdf4StableX1 e n ^ 2
          + bdf4StableX2 e n ^ 2) := by
  rw [bdf4StableX0_succ_eq, bdf4StableX1_succ_eq, bdf4StableX2_succ_eq, hψ]
  simpa [bdf4CubicStep0, bdf4CubicStep1, bdf4CubicStep2] using
    (bdf4CubicQuad_step_identity
      (bdf4StableX0 e n) (bdf4StableX1 e n) (bdf4StableX2 e n))

/-- Square-root energy associated to the stable BDF4 block. -/
noncomputable def bdf4StableEnergy (e : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (bdf4CubicQuad
    (bdf4StableX0 e n) (bdf4StableX1 e n) (bdf4StableX2 e n))

/-- BDF4 Lyapunov weight combining the unit-root coordinate and the stable energy. -/
noncomputable def bdf4LyapW (e : ℕ → ℝ) (n : ℕ) : ℝ :=
  |bdf4LyapU e n| + 6 * bdf4StableEnergy e n

lemma bdf4StableEnergy_nonneg (e : ℕ → ℝ) (n : ℕ) :
    0 ≤ bdf4StableEnergy e n := by
  unfold bdf4StableEnergy
  exact Real.sqrt_nonneg _

lemma bdf4LyapW_nonneg (e : ℕ → ℝ) (n : ℕ) :
    0 ≤ bdf4LyapW e n := by
  unfold bdf4LyapW
  nlinarith [abs_nonneg (bdf4LyapU e n), bdf4StableEnergy_nonneg e n]

/-- Symmetric bilinear form polarizing `bdf4CubicQuad`, written in coordinates. -/
noncomputable def bdf4CubicBil
    (x0 x1 x2 y0 y1 y2 : ℝ) : ℝ :=
  (1389 / 1280 : ℝ) * x0 * y0
    + (-19 / 60 : ℝ) * (x0 * y1 + x1 * y0)
    + (335 / 768 : ℝ) * (x0 * y2 + x2 * y0)
    + (1163 / 360 : ℝ) * x1 * y1
    + (-65 / 36 : ℝ) * (x1 * y2 + x2 * y1)
    + (13625 / 2304 : ℝ) * x2 * y2

lemma bdf4CubicBil_self (x0 x1 x2 : ℝ) :
    bdf4CubicBil x0 x1 x2 x0 x1 x2 = bdf4CubicQuad x0 x1 x2 := by
  unfold bdf4CubicBil bdf4CubicQuad
  ring

lemma bdf4CubicBil_step_ones_sq_le
    (x0 x1 x2 : ℝ) :
    (bdf4CubicBil
        (bdf4CubicStep0 x0 x1 x2)
        (bdf4CubicStep1 x0 x1 x2)
        (bdf4CubicStep2 x0 x1 x2)
        1 1 1) ^ 2
      ≤ bdf4CubicQuad
          (bdf4CubicStep0 x0 x1 x2)
          (bdf4CubicStep1 x0 x1 x2)
          (bdf4CubicStep2 x0 x1 x2)
        * (6583 / 960 : ℝ) := by
  unfold bdf4CubicBil bdf4CubicQuad bdf4CubicStep0 bdf4CubicStep1 bdf4CubicStep2
  nlinarith [sq_nonneg (x1 - x2),
    sq_nonneg (x1 - ((3 / 25 : ℝ) * x0 - (13 / 25 : ℝ) * x1 + (23 / 25 : ℝ) * x2)),
    sq_nonneg (x2 - ((3 / 25 : ℝ) * x0 - (13 / 25 : ℝ) * x1 + (23 / 25 : ℝ) * x2))]

private lemma bdf4CubicBil_step_ones_abs_le
    (x0 x1 x2 : ℝ) :
    |(25 / 12 : ℝ) *
      bdf4CubicBil
        (bdf4CubicStep0 x0 x1 x2)
        (bdf4CubicStep1 x0 x1 x2)
        (bdf4CubicStep2 x0 x1 x2)
        1 1 1|
      ≤ 6 * Real.sqrt (bdf4CubicQuad x0 x1 x2) := by
  set q : ℝ := bdf4CubicQuad x0 x1 x2 with hq
  set qstep : ℝ :=
    bdf4CubicQuad
      (bdf4CubicStep0 x0 x1 x2)
      (bdf4CubicStep1 x0 x1 x2)
      (bdf4CubicStep2 x0 x1 x2) with hqstep
  set b : ℝ :=
    bdf4CubicBil
      (bdf4CubicStep0 x0 x1 x2)
      (bdf4CubicStep1 x0 x1 x2)
      (bdf4CubicStep2 x0 x1 x2)
      1 1 1 with hb
  have hq_nonneg : 0 ≤ q := by
    rw [hq]
    have hlow := bdf4CubicQuad_lower x0 x1 x2
    nlinarith [sq_nonneg x0, sq_nonneg x1, sq_nonneg x2]
  have hqstep_nonneg : 0 ≤ qstep := by
    rw [hqstep]
    have hlow := bdf4CubicQuad_lower
      (bdf4CubicStep0 x0 x1 x2)
      (bdf4CubicStep1 x0 x1 x2)
      (bdf4CubicStep2 x0 x1 x2)
    nlinarith [sq_nonneg (bdf4CubicStep0 x0 x1 x2),
      sq_nonneg (bdf4CubicStep1 x0 x1 x2),
      sq_nonneg (bdf4CubicStep2 x0 x1 x2)]
  have hqstep_le_q : qstep ≤ q := by
    rw [hqstep, hq, bdf4CubicQuad_step_identity]
    nlinarith [sq_nonneg x0, sq_nonneg x1, sq_nonneg x2]
  have hb_sq : b ^ 2 ≤ qstep * (6583 / 960 : ℝ) := by
    rw [hb, hqstep]
    exact bdf4CubicBil_step_ones_sq_le x0 x1 x2
  have hsq :
      ((25 / 12 : ℝ) * b) ^ 2 ≤ (6 * Real.sqrt q) ^ 2 := by
    have hconst : ((25 / 12 : ℝ) ^ 2) * (6583 / 960 : ℝ) ≤ 36 := by
      norm_num
    have h1 : ((25 / 12 : ℝ) ^ 2) * b ^ 2
        ≤ ((25 / 12 : ℝ) ^ 2) * (qstep * (6583 / 960 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hb_sq (by positivity)
    have h2 : ((25 / 12 : ℝ) ^ 2) * (qstep * (6583 / 960 : ℝ))
        ≤ ((25 / 12 : ℝ) ^ 2) * (q * (6583 / 960 : ℝ)) := by
      nlinarith [hqstep_le_q]
    have h3 : ((25 / 12 : ℝ) ^ 2) * (q * (6583 / 960 : ℝ)) ≤ 36 * q := by
      nlinarith [hconst, hq_nonneg]
    have hsqrt_sq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq_nonneg
    nlinarith
  exact abs_le_of_sq_le_sq hsq (by positivity)

private lemma bdf4CubicQuad_forced_step_le
    (x0 x1 x2 ψ : ℝ) :
    bdf4CubicQuad
        (bdf4CubicStep0 x0 x1 x2 - (25 / 12 : ℝ) * ψ)
        (bdf4CubicStep1 x0 x1 x2 - (25 / 12 : ℝ) * ψ)
        (bdf4CubicStep2 x0 x1 x2 - (25 / 12 : ℝ) * ψ)
      ≤ (Real.sqrt (bdf4CubicQuad x0 x1 x2) + 6 * |ψ|) ^ 2 := by
  set q : ℝ := bdf4CubicQuad x0 x1 x2 with hq
  set qstep : ℝ :=
    bdf4CubicQuad
      (bdf4CubicStep0 x0 x1 x2)
      (bdf4CubicStep1 x0 x1 x2)
      (bdf4CubicStep2 x0 x1 x2) with hqstep
  set b : ℝ :=
    bdf4CubicBil
      (bdf4CubicStep0 x0 x1 x2)
      (bdf4CubicStep1 x0 x1 x2)
      (bdf4CubicStep2 x0 x1 x2)
      1 1 1 with hb
  have hq_nonneg : 0 ≤ q := by
    rw [hq]
    have hlow := bdf4CubicQuad_lower x0 x1 x2
    nlinarith [sq_nonneg x0, sq_nonneg x1, sq_nonneg x2]
  have hqstep_le_q : qstep ≤ q := by
    rw [hqstep, hq, bdf4CubicQuad_step_identity]
    nlinarith [sq_nonneg x0, sq_nonneg x1, sq_nonneg x2]
  have hcross_abs :
      |(25 / 12 : ℝ) * b| ≤ 6 * Real.sqrt q := by
    rw [hb, hq]
    exact bdf4CubicBil_step_ones_abs_le x0 x1 x2
  have hcross :
      -2 * ((25 / 12 : ℝ) * ψ) * b ≤ 12 * |ψ| * Real.sqrt q := by
    have hbasic : -2 * ψ * ((25 / 12 : ℝ) * b)
        ≤ 2 * |ψ| * |(25 / 12 : ℝ) * b| := by
      cases abs_cases ψ <;> cases abs_cases ((25 / 12 : ℝ) * b) <;> nlinarith
    have hmul := mul_le_mul_of_nonneg_left hcross_abs (by positivity : 0 ≤ 2 * |ψ|)
    nlinarith [hbasic, hmul]
  have hquad :
      (((25 / 12 : ℝ) * ψ) ^ 2) * (6583 / 960 : ℝ) ≤ 36 * |ψ| ^ 2 := by
    have hconst : ((25 / 12 : ℝ) ^ 2) * (6583 / 960 : ℝ) ≤ 36 := by
      norm_num
    have hψsq : 0 ≤ ψ ^ 2 := sq_nonneg ψ
    have habs_sq : |ψ| ^ 2 = ψ ^ 2 := by rw [sq_abs]
    nlinarith
  have hexpand :
      bdf4CubicQuad
          (bdf4CubicStep0 x0 x1 x2 - (25 / 12 : ℝ) * ψ)
          (bdf4CubicStep1 x0 x1 x2 - (25 / 12 : ℝ) * ψ)
          (bdf4CubicStep2 x0 x1 x2 - (25 / 12 : ℝ) * ψ)
        = qstep - 2 * ((25 / 12 : ℝ) * ψ) * b
            + (((25 / 12 : ℝ) * ψ) ^ 2) * (6583 / 960 : ℝ) := by
    rw [hqstep, hb]
    unfold bdf4CubicQuad bdf4CubicBil
    ring
  have hsqrt_sq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq_nonneg
  rw [hexpand]
  nlinarith [hqstep_le_q, hcross, hquad, hsqrt_sq]

lemma bdf4StableEnergy_forced_step_bound (e : ℕ → ℝ) (n : ℕ) :
    bdf4StableEnergy e (n + 1)
      ≤ bdf4StableEnergy e n + 6 * |bdf4RecDefect e n| := by
  set x0 : ℝ := bdf4StableX0 e n with hx0
  set x1 : ℝ := bdf4StableX1 e n with hx1
  set x2 : ℝ := bdf4StableX2 e n with hx2
  set ψ : ℝ := bdf4RecDefect e n with hψ
  have hq_forced := bdf4CubicQuad_forced_step_le x0 x1 x2 ψ
  have hsucc :
      bdf4CubicQuad
          (bdf4StableX0 e (n + 1))
          (bdf4StableX1 e (n + 1))
          (bdf4StableX2 e (n + 1))
        =
      bdf4CubicQuad
          (bdf4CubicStep0 x0 x1 x2 - (25 / 12 : ℝ) * ψ)
          (bdf4CubicStep1 x0 x1 x2 - (25 / 12 : ℝ) * ψ)
          (bdf4CubicStep2 x0 x1 x2 - (25 / 12 : ℝ) * ψ) := by
    rw [bdf4StableX0_succ_eq, bdf4StableX1_succ_eq, bdf4StableX2_succ_eq]
    simp [hx0, hx1, hx2, hψ, bdf4CubicStep0, bdf4CubicStep1, bdf4CubicStep2]
  have hq_nonneg :
      0 ≤ bdf4CubicQuad
        (bdf4StableX0 e n) (bdf4StableX1 e n) (bdf4StableX2 e n) := by
    have hlow := bdf4CubicQuad_lower
      (bdf4StableX0 e n) (bdf4StableX1 e n) (bdf4StableX2 e n)
    nlinarith [sq_nonneg (bdf4StableX0 e n),
      sq_nonneg (bdf4StableX1 e n), sq_nonneg (bdf4StableX2 e n)]
  have hforced_nonneg :
      0 ≤ bdf4CubicQuad
          (bdf4StableX0 e (n + 1))
          (bdf4StableX1 e (n + 1))
          (bdf4StableX2 e (n + 1)) := by
    have hlow := bdf4CubicQuad_lower
      (bdf4StableX0 e (n + 1))
      (bdf4StableX1 e (n + 1))
      (bdf4StableX2 e (n + 1))
    nlinarith [sq_nonneg (bdf4StableX0 e (n + 1)),
      sq_nonneg (bdf4StableX1 e (n + 1)), sq_nonneg (bdf4StableX2 e (n + 1))]
  have htarget_sq :
      bdf4CubicQuad
          (bdf4StableX0 e (n + 1))
          (bdf4StableX1 e (n + 1))
          (bdf4StableX2 e (n + 1))
      ≤ (bdf4StableEnergy e n + 6 * |bdf4RecDefect e n|) ^ 2 := by
    rw [hsucc]
    simpa [bdf4StableEnergy, hx0, hx1, hx2, hψ] using hq_forced
  have hrhs_nonneg : 0 ≤ bdf4StableEnergy e n + 6 * |bdf4RecDefect e n| := by
    nlinarith [bdf4StableEnergy_nonneg e n, abs_nonneg (bdf4RecDefect e n)]
  calc
    bdf4StableEnergy e (n + 1)
        = Real.sqrt
          (bdf4CubicQuad
            (bdf4StableX0 e (n + 1))
            (bdf4StableX1 e (n + 1))
            (bdf4StableX2 e (n + 1))) := rfl
    _ ≤ Real.sqrt ((bdf4StableEnergy e n + 6 * |bdf4RecDefect e n|) ^ 2) :=
      Real.sqrt_le_sqrt htarget_sq
    _ = bdf4StableEnergy e n + 6 * |bdf4RecDefect e n| := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hrhs_nonneg]

lemma bdf4LyapW_succ_le_of_defect (e : ℕ → ℝ) (n : ℕ) :
    bdf4LyapW e (n + 1)
      ≤ bdf4LyapW e n + 61 * |bdf4RecDefect e n| := by
  unfold bdf4LyapW
  have hU := bdf4LyapU_succ_eq e n
  have hE := bdf4StableEnergy_forced_step_bound e n
  rw [hU]
  have hU_abs := abs_add_le (bdf4LyapU e n) (25 * bdf4RecDefect e n)
  have h25 : |25 * bdf4RecDefect e n| = 25 * |bdf4RecDefect e n| := by
    rw [abs_mul, abs_of_pos (by norm_num : (25 : ℝ) > 0)]
  linarith

private lemma bdf4_eIdx4_decomposition (e : ℕ → ℝ) (n : ℕ) :
    e (n + 4)
      = bdf4LyapU e n / 12
        + ((69 / 625 : ℝ) * bdf4StableX0 e n
            - (224 / 625 : ℝ) * bdf4StableX1 e n
            + (204 / 625 : ℝ) * bdf4StableX2 e n)
        + bdf4RecDefect e n := by
  unfold bdf4LyapU bdf4StableX0 bdf4StableX1 bdf4StableX2 bdf4RecDefect
  unfold bdf4LyapU
  ring_nf

private lemma bdf4_stable_linear_le_energy (x0 x1 x2 : ℝ) :
    |(69 / 625 : ℝ) * x0 - (224 / 625 : ℝ) * x1 + (204 / 625 : ℝ) * x2|
      ≤ 6 * Real.sqrt (bdf4CubicQuad x0 x1 x2) := by
  rw [← Real.sqrt_sq_eq_abs, mul_comm]
  rw [Real.sqrt_le_left] <;> ring_nf <;> norm_num
  · rw [Real.sq_sqrt]
    · unfold bdf4CubicQuad
      nlinarith [sq_nonneg (x0 - x1), sq_nonneg (x0 - x2),
        sq_nonneg (x1 - x2), sq_nonneg (x0 + x1 + x2)]
    · exact le_trans (by positivity) (bdf4CubicQuad_lower x0 x1 x2)

lemma bdf4_eIdx4_le_W_add_defect (e : ℕ → ℝ) (n : ℕ) :
    |e (n + 4)| ≤ bdf4LyapW e n + |bdf4RecDefect e n| := by
  have hdecomp := bdf4_eIdx4_decomposition e n
  have htri :
      |e (n + 4)|
        ≤ |bdf4LyapU e n / 12|
          + |(69 / 625 : ℝ) * bdf4StableX0 e n
              - (224 / 625 : ℝ) * bdf4StableX1 e n
              + (204 / 625 : ℝ) * bdf4StableX2 e n|
          + |bdf4RecDefect e n| := by
    rw [hdecomp]
    exact abs_add_three _ _ _
  have hU_div : |bdf4LyapU e n / 12| ≤ |bdf4LyapU e n| := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 12)]
    exact div_le_self (abs_nonneg _) (by norm_num)
  have hstable := bdf4_stable_linear_le_energy
    (bdf4StableX0 e n) (bdf4StableX1 e n) (bdf4StableX2 e n)
  unfold bdf4LyapW bdf4StableEnergy
  linarith

private lemma bdf4_abs_defect_solve
    {a W τ ψ : ℝ} (ha_nonneg : 0 ≤ a) (hsmall : a ≤ 1 / 2)
    (hW : 0 ≤ W) (_hτ : 0 ≤ τ)
    (hψ_nonneg : 0 ≤ ψ)
    (hψ : ψ ≤ a * (W + ψ) + τ) :
    ψ ≤ (25 / 12 : ℝ) * a * W + 2 * τ := by
  nlinarith [mul_nonneg ha_nonneg hW, mul_nonneg ha_nonneg hψ_nonneg]

theorem bdf4LyapW_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (12 / 25 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsBDF4Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    bdf4LyapW (fun k => yseq k - y (t₀ + (k : ℝ) * h)) (n + 1)
      ≤ (1 + h * (61 * L))
          * bdf4LyapW (fun k => yseq k - y (t₀ + (k : ℝ) * h)) n
        + 122 * |bdf4.localTruncationError h (t₀ + (n : ℝ) * h) y| := by
  let e : ℕ → ℝ := fun k => yseq k - y (t₀ + (k : ℝ) * h)
  set τ : ℝ := |bdf4.localTruncationError h (t₀ + (n : ℝ) * h) y| with hτ_def
  have hτ_nonneg : 0 ≤ τ := by
    rw [hτ_def]
    exact abs_nonneg _
  have hdefect :
      |bdf4RecDefect e n|
        ≤ (12 / 25 : ℝ) * h * L * |e (n + 4)| + τ := by
    have h := bdf4_one_step_lipschitz hh hf t₀ hy y hyf n
    rw [hτ_def]
    simpa [bdf4RecDefect, e, Nat.cast_add, Nat.cast_ofNat, add_mul,
      add_assoc, add_comm, add_left_comm] using h
  have ha_nonneg : 0 ≤ (12 / 25 : ℝ) * h * L := by
    positivity
  have hW_nonneg : 0 ≤ bdf4LyapW e n := bdf4LyapW_nonneg e n
  have hψ_nonneg : 0 ≤ |bdf4RecDefect e n| := abs_nonneg _
  have he4 := bdf4_eIdx4_le_W_add_defect e n
  have hψ_implicit :
      |bdf4RecDefect e n|
        ≤ (12 / 25 : ℝ) * h * L
            * (bdf4LyapW e n + |bdf4RecDefect e n|) + τ := by
    have hmul := mul_le_mul_of_nonneg_left he4 ha_nonneg
    nlinarith [hdefect, hmul]
  have hψ_solved :
      |bdf4RecDefect e n|
        ≤ h * L * bdf4LyapW e n + 2 * τ := by
    have hsolve := bdf4_abs_defect_solve
      ha_nonneg hsmall hW_nonneg hτ_nonneg hψ_nonneg hψ_implicit
    nlinarith
  have hstep := bdf4LyapW_succ_le_of_defect e n
  change bdf4LyapW e (n + 1)
      ≤ (1 + h * (61 * L)) * bdf4LyapW e n + 122 * τ
  nlinarith

/-- Bound the BDF4 stable-block energy by `6·M` when each stable coordinate
is bounded in absolute value by `M`. Uses the upper coercive estimate
`Q ≤ 9·(x₀² + x₁² + x₂²)` and `√(36·M²) = 6·M`. -/
private lemma bdf4StableEnergy_le_of_max
    (e : ℕ → ℝ) (n : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (h0 : |bdf4StableX0 e n| ≤ M)
    (h1 : |bdf4StableX1 e n| ≤ M)
    (h2 : |bdf4StableX2 e n| ≤ M) :
    bdf4StableEnergy e n ≤ 6 * M := by
  unfold bdf4StableEnergy
  set x0 := bdf4StableX0 e n
  set x1 := bdf4StableX1 e n
  set x2 := bdf4StableX2 e n
  have hsq0 : x0 ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs x0]; exact pow_le_pow_left₀ (abs_nonneg _) h0 2
  have hsq1 : x1 ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs x1]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hsq2 : x2 ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs x2]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have hupper := bdf4CubicQuad_upper x0 x1 x2
  have hQ_le : bdf4CubicQuad x0 x1 x2 ≤ (6 * M) ^ 2 := by
    nlinarith [hupper, hsq0, hsq1, hsq2]
  have h6M_nn : 0 ≤ 6 * M := by linarith
  calc Real.sqrt (bdf4CubicQuad x0 x1 x2)
      ≤ Real.sqrt ((6 * M) ^ 2) := Real.sqrt_le_sqrt hQ_le
    _ = 6 * M := Real.sqrt_sq h6M_nn

/-- Initial Lyapunov bound: if the first four BDF4 errors are bounded by
`ε₀`, then the BDF4 quadratic Lyapunov weight at index 0 is at most
`292·ε₀`. -/
lemma bdf4LyapW_initial_bound
    {e : ℕ → ℝ} {ε₀ : ℝ}
    (h0 : |e 0| ≤ ε₀) (h1 : |e 1| ≤ ε₀)
    (h2 : |e 2| ≤ ε₀) (h3 : |e 3| ≤ ε₀) :
    bdf4LyapW e 0 ≤ 292 * ε₀ := by
  obtain ⟨h0a, h0b⟩ := abs_le.mp h0
  obtain ⟨h1a, h1b⟩ := abs_le.mp h1
  obtain ⟨h2a, h2b⟩ := abs_le.mp h2
  obtain ⟨h3a, h3b⟩ := abs_le.mp h3
  have hε_nn : 0 ≤ ε₀ := le_trans (abs_nonneg _) h0
  -- |U| ≤ (3+13+23+25)·ε₀ = 64·ε₀
  have hU_bd : |bdf4LyapU e 0| ≤ 64 * ε₀ := by
    unfold bdf4LyapU
    rw [abs_le]
    refine ⟨?_, ?_⟩ <;> linarith
  -- |Xi| ≤ ε₀ + |U|/12 ≤ (12 + 64)/12 · ε₀ = 76/12 · ε₀
  set M : ℝ := (76 / 12 : ℝ) * ε₀ with hM_def
  have hM_nn : 0 ≤ M := by rw [hM_def]; positivity
  have hX0_bd : |bdf4StableX0 e 0| ≤ M := by
    unfold bdf4StableX0 bdf4LyapU
    rw [hM_def, abs_le]
    refine ⟨?_, ?_⟩ <;> linarith
  have hX1_bd : |bdf4StableX1 e 0| ≤ M := by
    unfold bdf4StableX1 bdf4LyapU
    rw [hM_def, abs_le]
    refine ⟨?_, ?_⟩ <;> linarith
  have hX2_bd : |bdf4StableX2 e 0| ≤ M := by
    unfold bdf4StableX2 bdf4LyapU
    rw [hM_def, abs_le]
    refine ⟨?_, ?_⟩ <;> linarith
  have hE_bd : bdf4StableEnergy e 0 ≤ 6 * M :=
    bdf4StableEnergy_le_of_max e 0 hM_nn hX0_bd hX1_bd hX2_bd
  -- |U| + 6 E ≤ 64 ε₀ + 36 · (76/12) · ε₀ = 64 ε₀ + 228 ε₀ = 292 ε₀
  unfold bdf4LyapW
  have h36M : 36 * M = 228 * ε₀ := by rw [hM_def]; ring
  linarith

/-- Coercive lower bound: `|Xᵢ| ≤ 2·E` for each stable coordinate. -/
private lemma bdf4_abs_X0_le_2E (e : ℕ → ℝ) (n : ℕ) :
    |bdf4StableX0 e n| ≤ 2 * bdf4StableEnergy e n := by
  unfold bdf4StableEnergy
  set x0 := bdf4StableX0 e n
  set x1 := bdf4StableX1 e n
  set x2 := bdf4StableX2 e n
  have hlow := bdf4CubicQuad_lower x0 x1 x2
  have hX0sq_le : x0 ^ 2 ≤ 4 * bdf4CubicQuad x0 x1 x2 := by
    nlinarith [sq_nonneg x1, sq_nonneg x2, hlow]
  have h2sqrtQ : 2 * Real.sqrt (bdf4CubicQuad x0 x1 x2)
      = Real.sqrt (4 * bdf4CubicQuad x0 x1 x2) := by
    rw [show (4 : ℝ) * bdf4CubicQuad x0 x1 x2
          = 2 ^ 2 * bdf4CubicQuad x0 x1 x2 from by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h2sqrtQ, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hX0sq_le

private lemma bdf4_abs_X1_le_2E (e : ℕ → ℝ) (n : ℕ) :
    |bdf4StableX1 e n| ≤ 2 * bdf4StableEnergy e n := by
  unfold bdf4StableEnergy
  set x0 := bdf4StableX0 e n
  set x1 := bdf4StableX1 e n
  set x2 := bdf4StableX2 e n
  have hlow := bdf4CubicQuad_lower x0 x1 x2
  have hX1sq_le : x1 ^ 2 ≤ 4 * bdf4CubicQuad x0 x1 x2 := by
    nlinarith [sq_nonneg x0, sq_nonneg x2, hlow]
  have h2sqrtQ : 2 * Real.sqrt (bdf4CubicQuad x0 x1 x2)
      = Real.sqrt (4 * bdf4CubicQuad x0 x1 x2) := by
    rw [show (4 : ℝ) * bdf4CubicQuad x0 x1 x2
          = 2 ^ 2 * bdf4CubicQuad x0 x1 x2 from by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h2sqrtQ, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hX1sq_le

private lemma bdf4_abs_X2_le_2E (e : ℕ → ℝ) (n : ℕ) :
    |bdf4StableX2 e n| ≤ 2 * bdf4StableEnergy e n := by
  unfold bdf4StableEnergy
  set x0 := bdf4StableX0 e n
  set x1 := bdf4StableX1 e n
  set x2 := bdf4StableX2 e n
  have hlow := bdf4CubicQuad_lower x0 x1 x2
  have hX2sq_le : x2 ^ 2 ≤ 4 * bdf4CubicQuad x0 x1 x2 := by
    nlinarith [sq_nonneg x0, sq_nonneg x1, hlow]
  have h2sqrtQ : 2 * Real.sqrt (bdf4CubicQuad x0 x1 x2)
      = Real.sqrt (4 * bdf4CubicQuad x0 x1 x2) := by
    rw [show (4 : ℝ) * bdf4CubicQuad x0 x1 x2
          = 2 ^ 2 * bdf4CubicQuad x0 x1 x2 from by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h2sqrtQ, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hX2sq_le

/-- Readout at index `n`: `|e_n| ≤ W_n`. -/
lemma bdf4_eIdx0_le_W (e : ℕ → ℝ) (n : ℕ) :
    |e n| ≤ bdf4LyapW e n := by
  have hd : e n = bdf4StableX0 e n + bdf4LyapU e n / 12 := by
    unfold bdf4StableX0; ring
  rw [hd]
  have htri : |bdf4StableX0 e n + bdf4LyapU e n / 12|
      ≤ |bdf4StableX0 e n| + |bdf4LyapU e n / 12| := abs_add_le _ _
  have hX0_le := bdf4_abs_X0_le_2E e n
  have hU_div : |bdf4LyapU e n / 12| = |bdf4LyapU e n| / 12 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 12)]
  unfold bdf4LyapW
  have hE_nn := bdf4StableEnergy_nonneg e n
  have hU_nn := abs_nonneg (bdf4LyapU e n)
  linarith

/-- Readout at index `n+1`: `|e_{n+1}| ≤ W_n`. -/
lemma bdf4_eIdx1_le_W (e : ℕ → ℝ) (n : ℕ) :
    |e (n + 1)| ≤ bdf4LyapW e n := by
  have hd : e (n + 1) = bdf4StableX1 e n + bdf4LyapU e n / 12 := by
    unfold bdf4StableX1; ring
  rw [hd]
  have htri : |bdf4StableX1 e n + bdf4LyapU e n / 12|
      ≤ |bdf4StableX1 e n| + |bdf4LyapU e n / 12| := abs_add_le _ _
  have hX1_le := bdf4_abs_X1_le_2E e n
  have hU_div : |bdf4LyapU e n / 12| = |bdf4LyapU e n| / 12 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 12)]
  unfold bdf4LyapW
  have hE_nn := bdf4StableEnergy_nonneg e n
  have hU_nn := abs_nonneg (bdf4LyapU e n)
  linarith

/-- Readout at index `n+2`: `|e_{n+2}| ≤ W_n`. -/
lemma bdf4_eIdx2_le_W (e : ℕ → ℝ) (n : ℕ) :
    |e (n + 2)| ≤ bdf4LyapW e n := by
  have hd : e (n + 2) = bdf4StableX2 e n + bdf4LyapU e n / 12 := by
    unfold bdf4StableX2; ring
  rw [hd]
  have htri : |bdf4StableX2 e n + bdf4LyapU e n / 12|
      ≤ |bdf4StableX2 e n| + |bdf4LyapU e n / 12| := abs_add_le _ _
  have hX2_le := bdf4_abs_X2_le_2E e n
  have hU_div : |bdf4LyapU e n / 12| = |bdf4LyapU e n| / 12 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 12)]
  unfold bdf4LyapW
  have hE_nn := bdf4StableEnergy_nonneg e n
  have hU_nn := abs_nonneg (bdf4LyapU e n)
  linarith

/-- Headline BDF4 global error bound. Mirrors `bdf3_global_error_bound`,
extended by one starting index and with constants `K₁ = 292`, growth
rate `61·L`, and residual coefficient `122·C` from
`bdf4LyapW_one_step_error_bound` and `bdf4_local_residual_bound`. -/
theorem bdf4_global_error_bound
    {y : ℝ → ℝ} (hy_smooth : ContDiff ℝ 5 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      (12 / 25 : ℝ) * h * L ≤ 1 / 2 →
      ∀ {yseq : ℕ → ℝ} {ε₀ : ℝ},
      IsBDF4Trajectory h f t₀ yseq →
      0 ≤ ε₀ →
      |yseq 0 - y t₀| ≤ ε₀ →
      |yseq 1 - y (t₀ + h)| ≤ ε₀ →
      |yseq 2 - y (t₀ + 2 * h)| ≤ ε₀ →
      |yseq 3 - y (t₀ + 3 * h)| ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 1) * h ≤ T →
      |yseq N - y (t₀ + (N : ℝ) * h)|
        ≤ 292 * Real.exp ((61 * L) * T) * ε₀ + K * h ^ 4 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    bdf4_local_residual_bound hy_smooth t₀ T hT
  refine ⟨122 * T * Real.exp ((61 * L) * T) * C, δ, ?_, hδ_pos, ?_⟩
  · have hT_nn : (0 : ℝ) ≤ T := hT.le
    have hexp_nn : (0 : ℝ) ≤ Real.exp ((61 * L) * T) := Real.exp_nonneg _
    have h1 : (0 : ℝ) ≤ 122 * T := by positivity
    have h2 : (0 : ℝ) ≤ 122 * T * Real.exp ((61 * L) * T) := mul_nonneg h1 hexp_nn
    exact mul_nonneg h2 hC_nn
  intro h hh hδ_le hsmall yseq ε₀ hy_traj hε₀ he0_bd he1_bd he2_bd he3_bd N hNh
  set e : ℕ → ℝ := fun k => yseq k - y (t₀ + (k : ℝ) * h) with he_def
  set W : ℕ → ℝ := fun k => bdf4LyapW e k with hW_def
  have hW_nn : ∀ k, 0 ≤ W k := fun k => bdf4LyapW_nonneg e k
  have h61L_nn : (0 : ℝ) ≤ 61 * L := by linarith
  -- Initial bound: W 0 ≤ 292 ε₀.
  have he0' : |e 0| ≤ ε₀ := by
    show |yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)| ≤ ε₀
    have : t₀ + ((0 : ℕ) : ℝ) * h = t₀ := by push_cast; ring
    rw [this]; exact he0_bd
  have he1' : |e 1| ≤ ε₀ := by
    show |yseq 1 - y (t₀ + ((1 : ℕ) : ℝ) * h)| ≤ ε₀
    have : t₀ + ((1 : ℕ) : ℝ) * h = t₀ + h := by push_cast; ring
    rw [this]; exact he1_bd
  have he2' : |e 2| ≤ ε₀ := by
    show |yseq 2 - y (t₀ + ((2 : ℕ) : ℝ) * h)| ≤ ε₀
    have : t₀ + ((2 : ℕ) : ℝ) * h = t₀ + 2 * h := by push_cast; ring
    rw [this]; exact he2_bd
  have he3' : |e 3| ≤ ε₀ := by
    show |yseq 3 - y (t₀ + ((3 : ℕ) : ℝ) * h)| ≤ ε₀
    have : t₀ + ((3 : ℕ) : ℝ) * h = t₀ + 3 * h := by push_cast; ring
    rw [this]; exact he3_bd
  have hW0_le : W 0 ≤ 292 * ε₀ := bdf4LyapW_initial_bound he0' he1' he2' he3'
  -- Step bound for the W iteration.
  have hstep_general : ∀ n : ℕ, ((n : ℝ) + 4) * h ≤ T →
      W (n + 1) ≤ (1 + h * (61 * L)) * W n + (122 * C) * h ^ (4 + 1) := by
    intro n hnh_le
    have honestep := bdf4LyapW_one_step_error_bound
      (h := h) (L := L) hh.le hL hsmall hf t₀ hy_traj y hyf n
    have hres := hresidual hh hδ_le n hnh_le
    have h122_nn : (0 : ℝ) ≤ 122 := by norm_num
    have h122τ : 122 * |bdf4.localTruncationError h
        (t₀ + (n : ℝ) * h) y| ≤ (122 * C) * h ^ (4 + 1) := by
      have := mul_le_mul_of_nonneg_left hres h122_nn
      have hpow : (h : ℝ) ^ (4 + 1) = h ^ 5 := by norm_num
      rw [hpow]; linarith
    show bdf4LyapW e (n + 1)
        ≤ (1 + h * (61 * L)) * bdf4LyapW e n + (122 * C) * h ^ (4 + 1)
    linarith [honestep, h122τ]
  have hexp_ge_one : (1 : ℝ) ≤ Real.exp ((61 * L) * T) :=
    Real.one_le_exp_iff.mpr (mul_nonneg h61L_nn hT.le)
  have hexp_nn : 0 ≤ Real.exp ((61 * L) * T) := Real.exp_nonneg _
  have hKnn : 0 ≤ 122 * T * Real.exp ((61 * L) * T) * C := by
    have h1 : (0 : ℝ) ≤ 122 * T := by positivity
    have h2 : (0 : ℝ) ≤ 122 * T * Real.exp ((61 * L) * T) := mul_nonneg h1 hexp_nn
    exact mul_nonneg h2 hC_nn
  have hh4_nn : 0 ≤ h ^ 4 := by positivity
  match N, hNh with
  | 0, _ =>
    show |yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)|
        ≤ 292 * Real.exp ((61 * L) * T) * ε₀
            + 122 * T * Real.exp ((61 * L) * T) * C * h ^ 4
    have hbd : |yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)| ≤ ε₀ := he0'
    nlinarith [hbd, hexp_ge_one, hKnn, hh4_nn, hε₀]
  | 1, _ =>
    show |yseq 1 - y (t₀ + ((1 : ℕ) : ℝ) * h)|
        ≤ 292 * Real.exp ((61 * L) * T) * ε₀
            + 122 * T * Real.exp ((61 * L) * T) * C * h ^ 4
    have hbd : |yseq 1 - y (t₀ + ((1 : ℕ) : ℝ) * h)| ≤ ε₀ := he1'
    nlinarith [hbd, hexp_ge_one, hKnn, hh4_nn, hε₀]
  | 2, _ =>
    show |yseq 2 - y (t₀ + ((2 : ℕ) : ℝ) * h)|
        ≤ 292 * Real.exp ((61 * L) * T) * ε₀
            + 122 * T * Real.exp ((61 * L) * T) * C * h ^ 4
    have hbd : |yseq 2 - y (t₀ + ((2 : ℕ) : ℝ) * h)| ≤ ε₀ := he2'
    nlinarith [hbd, hexp_ge_one, hKnn, hh4_nn, hε₀]
  | 3, _ =>
    show |yseq 3 - y (t₀ + ((3 : ℕ) : ℝ) * h)|
        ≤ 292 * Real.exp ((61 * L) * T) * ε₀
            + 122 * T * Real.exp ((61 * L) * T) * C * h ^ 4
    have hbd : |yseq 3 - y (t₀ + ((3 : ℕ) : ℝ) * h)| ≤ ε₀ := he3'
    nlinarith [hbd, hexp_ge_one, hKnn, hh4_nn, hε₀]
  | (N'' + 4), hNh' =>
    -- Reduction: write N = N''+4 = (N''+2)+2; use |e_{(N''+2)+2}| ≤ W_{N''+2}.
    -- Apply Gronwall up to index N''+2; need (N''+2)·h ≤ T and step bound
    -- for n < N''+2, i.e., n ≤ N''+1, requiring (N''+5)·h ≤ T.
    have hcastN : ((N'' + 4 : ℕ) : ℝ) = (N'' : ℝ) + 4 := by push_cast; ring
    have hN_le : ((N'' : ℝ) + 5) * h ≤ T := by
      have hcastNh : (((N'' + 4 : ℕ) : ℝ) + 1) * h ≤ T := hNh'
      have heq : ((N'' + 4 : ℕ) : ℝ) + 1 = (N'' : ℝ) + 5 := by push_cast; ring
      rw [heq] at hcastNh
      exact hcastNh
    -- Step bound for the Gronwall driver up to N''+2.
    have hgronwall_step : ∀ n, n < N'' + 2 →
        W (n + 1) ≤ (1 + h * (61 * L)) * W n + (122 * C) * h ^ (4 + 1) := by
      intro n hn_lt
      apply hstep_general
      have hn1_le : (n : ℝ) ≤ ((N'' : ℝ) + 1) := by
        exact_mod_cast Nat.lt_succ_iff.mp hn_lt
      have hle : (n : ℝ) + 4 ≤ (N'' : ℝ) + 5 := by linarith
      have hmul : ((n : ℝ) + 4) * h ≤ ((N'' : ℝ) + 5) * h :=
        mul_le_mul_of_nonneg_right hle hh.le
      linarith
    have hN2h_le_T : ((N'' + 2 : ℕ) : ℝ) * h ≤ T := by
      have hcast : ((N'' + 2 : ℕ) : ℝ) = (N'' : ℝ) + 2 := by push_cast; ring
      rw [hcast]
      have hle : (N'' : ℝ) + 2 ≤ (N'' : ℝ) + 5 := by linarith
      have := mul_le_mul_of_nonneg_right hle hh.le
      linarith
    have hgronwall :=
      lmm_error_bound_from_local_truncation
        (h := h) (L := 61 * L) (C := 122 * C) (T := T) (p := 4) (e := W)
        (N := N'' + 2)
        hh.le h61L_nn (by positivity) (hW_nn 0) hgronwall_step
        (N'' + 2) le_rfl hN2h_le_T
    -- W_{N''+2} ≤ exp((61L)·T) W_0 + T·exp((61L)·T)·(122 C)·h^4.
    -- |e_{(N''+2)+2}| ≤ W_{N''+2}.
    have hek2 := bdf4_eIdx2_le_W e (N'' + 2)
    have hidx : ((N'' + 2 + 2 : ℕ) : ℝ) = (N'' : ℝ) + 4 := by push_cast; ring
    have h_chain :
        Real.exp ((61 * L) * T) * W 0
          ≤ Real.exp ((61 * L) * T) * (292 * ε₀) :=
      mul_le_mul_of_nonneg_left hW0_le hexp_nn
    show |yseq (N'' + 4) - y (t₀ + ((N'' + 4 : ℕ) : ℝ) * h)|
        ≤ 292 * Real.exp ((61 * L) * T) * ε₀
            + 122 * T * Real.exp ((61 * L) * T) * C * h ^ 4
    have hcastN4 : ((N'' + 4 : ℕ) : ℝ) = (N'' : ℝ) + 4 := by push_cast; ring
    rw [hcastN4]
    have he_eq : e (N'' + 2 + 2)
        = yseq (N'' + 4) - y (t₀ + ((N'' : ℝ) + 4) * h) := by
      show yseq (N'' + 2 + 2) - y (t₀ + ((N'' + 2 + 2 : ℕ) : ℝ) * h)
          = yseq (N'' + 4) - y (t₀ + ((N'' : ℝ) + 4) * h)
      have h_idx_eq : (N'' + 2 + 2 : ℕ) = N'' + 4 := by ring
      rw [h_idx_eq, hidx]
    have hek2' : |yseq (N'' + 4) - y (t₀ + ((N'' : ℝ) + 4) * h)|
        ≤ W (N'' + 2) := by
      have := hek2
      rw [he_eq] at this
      exact this
    linarith [hek2', hgronwall, h_chain]

end LMM
