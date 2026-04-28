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

end LMM
