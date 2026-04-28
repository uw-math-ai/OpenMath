import OpenMath.LMMBDF4Convergence

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

end LMM
