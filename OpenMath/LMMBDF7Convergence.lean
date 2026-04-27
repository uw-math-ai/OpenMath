import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMAM6Convergence

/-! ## BDF7 Quantitative Truncation Chain (Iserles §4.5)

Truncation chain for the scalar 7-step backward differentiation formula.
This module lands the supplied-trajectory predicate, the textbook local
truncation residual unfolding, the Lipschitz defect estimate, the
pointwise eighth-order Taylor residual bound, and the uniform local
residual bound on a finite horizon.

BDF7 is zero-unstable (Dahlquist barrier), so a global error theorem is
not available — the local truncation chain is the entire story. The
public 8th-order scalar Taylor helpers from `LMMAM6Convergence` are
reused here (`iteratedDeriv_eight_bounded_on_Icc`,
`y_eighth_order_taylor_remainder`,
`derivY_seventh_order_taylor_remainder`).
-/

namespace LMM

/-- BDF7 trajectory predicate:
`y_{n+7} = (2940/1089)y_{n+6} − (4410/1089)y_{n+5} + (4900/1089)y_{n+4}
  − (3675/1089)y_{n+3} + (1764/1089)y_{n+2} − (490/1089)y_{n+1}
  + (60/1089)y_n + (420/1089)h·f(t_{n+7}, y_{n+7})`.
The new value appears inside `f`, so existence of such a trajectory is a
separate fixed-point problem. -/
structure IsBDF7Trajectory (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ : ℝ)
    (y : ℕ → ℝ) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 7)
      = (2940 / 1089 : ℝ) * y (n + 6) - (4410 / 1089 : ℝ) * y (n + 5)
        + (4900 / 1089 : ℝ) * y (n + 4) - (3675 / 1089 : ℝ) * y (n + 3)
        + (1764 / 1089 : ℝ) * y (n + 2) - (490 / 1089 : ℝ) * y (n + 1)
        + (60 / 1089 : ℝ) * y n
        + (420 / 1089 : ℝ) * h * f (t₀ + ((n : ℝ) + 7) * h) (y (n + 7))

/-- BDF7 local truncation operator reduces to the textbook 7-step residual
`y(t+7h) − (2940/1089)y(t+6h) + (4410/1089)y(t+5h) − (4900/1089)y(t+4h)
  + (3675/1089)y(t+3h) − (1764/1089)y(t+2h) + (490/1089)y(t+h) − (60/1089)y(t)
  − (420/1089)h y'(t+7h)`. -/
theorem bdf7_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    bdf7.localTruncationError h t y
      = y (t + 7 * h) - (2940 / 1089 : ℝ) * y (t + 6 * h)
        + (4410 / 1089 : ℝ) * y (t + 5 * h)
        - (4900 / 1089 : ℝ) * y (t + 4 * h)
        + (3675 / 1089 : ℝ) * y (t + 3 * h)
        - (1764 / 1089 : ℝ) * y (t + 2 * h)
        + (490 / 1089 : ℝ) * y (t + h)
        - (60 / 1089 : ℝ) * y t
        - (420 / 1089 : ℝ) * h * deriv y (t + 7 * h) := by
  unfold localTruncationError truncationOp
  simp [bdf7, Fin.sum_univ_eight, iteratedDeriv_one, iteratedDeriv_zero]
  ring

/-- Forcing decomposition of the BDF7 error recurrence: the homogeneous
defect is bounded by `(420/1089) h L · |e_{n+7}| + |τ_n|`. -/
theorem bdf7_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsBDF7Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    |(yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h))
      - (2940 / 1089 : ℝ) * (yseq (n + 6) - y (t₀ + ((n : ℝ) + 6) * h))
      + (4410 / 1089 : ℝ) * (yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h))
      - (4900 / 1089 : ℝ) * (yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h))
      + (3675 / 1089 : ℝ) * (yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h))
      - (1764 / 1089 : ℝ) * (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))
      + (490 / 1089 : ℝ) * (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
      - (60 / 1089 : ℝ) * (yseq n - y (t₀ + (n : ℝ) * h))|
    ≤ (420 / 1089 : ℝ) * h * L
        * |yseq (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)|
      + |bdf7.localTruncationError h (t₀ + (n : ℝ) * h) y| := by
  set yn : ℝ := yseq n with hyn_def
  set yn1 : ℝ := yseq (n + 1) with hyn1_def
  set yn2 : ℝ := yseq (n + 2) with hyn2_def
  set yn3 : ℝ := yseq (n + 3) with hyn3_def
  set yn4 : ℝ := yseq (n + 4) with hyn4_def
  set yn5 : ℝ := yseq (n + 5) with hyn5_def
  set yn6 : ℝ := yseq (n + 6) with hyn6_def
  set yn7 : ℝ := yseq (n + 7) with hyn7_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set tn3 : ℝ := t₀ + ((n : ℝ) + 3) * h with htn3_def
  set tn4 : ℝ := t₀ + ((n : ℝ) + 4) * h with htn4_def
  set tn5 : ℝ := t₀ + ((n : ℝ) + 5) * h with htn5_def
  set tn6 : ℝ := t₀ + ((n : ℝ) + 6) * h with htn6_def
  set tn7 : ℝ := t₀ + ((n : ℝ) + 7) * h with htn7_def
  set zn : ℝ := y tn with hzn_def
  set zn1 : ℝ := y tn1 with hzn1_def
  set zn2 : ℝ := y tn2 with hzn2_def
  set zn3 : ℝ := y tn3 with hzn3_def
  set zn4 : ℝ := y tn4 with hzn4_def
  set zn5 : ℝ := y tn5 with hzn5_def
  set zn6 : ℝ := y tn6 with hzn6_def
  set zn7 : ℝ := y tn7 with hzn7_def
  set τ : ℝ := bdf7.localTruncationError h tn y with hτ_def
  have hstep : yn7
      = (2940 / 1089 : ℝ) * yn6 - (4410 / 1089 : ℝ) * yn5
        + (4900 / 1089 : ℝ) * yn4 - (3675 / 1089 : ℝ) * yn3
        + (1764 / 1089 : ℝ) * yn2 - (490 / 1089 : ℝ) * yn1
        + (60 / 1089 : ℝ) * yn
        + (420 / 1089 : ℝ) * h * f tn7 yn7 := by
    simpa [hyn7_def, hyn6_def, hyn5_def, hyn4_def, hyn3_def, hyn2_def,
      hyn1_def, hyn_def, htn7_def] using hy.recurrence n
  have htn_h : tn + h = tn1 := by simp [htn_def, htn1_def]; ring
  have htn_2h : tn + 2 * h = tn2 := by simp [htn_def, htn2_def]; ring
  have htn_3h : tn + 3 * h = tn3 := by simp [htn_def, htn3_def]; ring
  have htn_4h : tn + 4 * h = tn4 := by simp [htn_def, htn4_def]; ring
  have htn_5h : tn + 5 * h = tn5 := by simp [htn_def, htn5_def]; ring
  have htn_6h : tn + 6 * h = tn6 := by simp [htn_def, htn6_def]; ring
  have htn_7h : tn + 7 * h = tn7 := by simp [htn_def, htn7_def]; ring
  have hτ_eq : τ = zn7 - (2940 / 1089 : ℝ) * zn6
        + (4410 / 1089 : ℝ) * zn5 - (4900 / 1089 : ℝ) * zn4
        + (3675 / 1089 : ℝ) * zn3 - (1764 / 1089 : ℝ) * zn2
        + (490 / 1089 : ℝ) * zn1 - (60 / 1089 : ℝ) * zn
        - (420 / 1089 : ℝ) * h * f tn7 zn7 := by
    show bdf7.localTruncationError h tn y = _
    rw [bdf7_localTruncationError_eq, htn_h, htn_2h, htn_3h, htn_4h,
      htn_5h, htn_6h, htn_7h, hyf tn7]
  have halg : (yn7 - zn7) - (2940 / 1089 : ℝ) * (yn6 - zn6)
        + (4410 / 1089 : ℝ) * (yn5 - zn5)
        - (4900 / 1089 : ℝ) * (yn4 - zn4)
        + (3675 / 1089 : ℝ) * (yn3 - zn3)
        - (1764 / 1089 : ℝ) * (yn2 - zn2)
        + (490 / 1089 : ℝ) * (yn1 - zn1)
        - (60 / 1089 : ℝ) * (yn - zn)
      = (420 / 1089 : ℝ) * h * (f tn7 yn7 - f tn7 zn7) - τ := by
    conv_lhs => rw [hstep]
    rw [hτ_eq]; ring
  have hLip : |f tn7 yn7 - f tn7 zn7| ≤ L * |yn7 - zn7| := hf tn7 yn7 zn7
  have h420_nn : (0 : ℝ) ≤ (420 / 1089 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h420_abs :
      |(420 / 1089 : ℝ) * h * (f tn7 yn7 - f tn7 zn7)|
        ≤ (420 / 1089 : ℝ) * h * L * |yn7 - zn7| := by
    rw [abs_mul, abs_of_nonneg h420_nn]
    calc (420 / 1089 : ℝ) * h * |f tn7 yn7 - f tn7 zn7|
        ≤ (420 / 1089 : ℝ) * h * (L * |yn7 - zn7|) :=
          mul_le_mul_of_nonneg_left hLip h420_nn
      _ = (420 / 1089 : ℝ) * h * L * |yn7 - zn7| := by ring
  have htri :
      |(420 / 1089 : ℝ) * h * (f tn7 yn7 - f tn7 zn7) - τ|
      ≤ |(420 / 1089 : ℝ) * h * (f tn7 yn7 - f tn7 zn7)| + |τ| := abs_sub _ _
  calc |(yn7 - zn7) - (2940 / 1089 : ℝ) * (yn6 - zn6)
            + (4410 / 1089 : ℝ) * (yn5 - zn5)
            - (4900 / 1089 : ℝ) * (yn4 - zn4)
            + (3675 / 1089 : ℝ) * (yn3 - zn3)
            - (1764 / 1089 : ℝ) * (yn2 - zn2)
            + (490 / 1089 : ℝ) * (yn1 - zn1)
            - (60 / 1089 : ℝ) * (yn - zn)|
      = |(420 / 1089 : ℝ) * h * (f tn7 yn7 - f tn7 zn7) - τ| := by rw [halg]
    _ ≤ |(420 / 1089 : ℝ) * h * (f tn7 yn7 - f tn7 zn7)| + |τ| := htri
    _ ≤ (420 / 1089 : ℝ) * h * L * |yn7 - zn7| + |τ| := by linarith [h420_abs]

/-- Pure-algebra core of the BDF7 pointwise residual bound. Given the eight
Taylor-remainder magnitude bounds, the BDF7 residual combination is bounded
by `366 · M · h⁸`. The exact coefficient is `17914498/49005 ≈ 365.565`,
slackened to `366`. Extracted as a private lemma to keep the kernel out of
the heavy ambient Taylor context. -/
private lemma bdf7_pointwise_residual_alg
    (h M : ℝ) (A B C D E F G H : ℝ)
    (hA : |A| ≤ M * (7 * h) ^ 8 / 40320)
    (hB : |B| ≤ M * (6 * h) ^ 8 / 40320)
    (hC : |C| ≤ M * (5 * h) ^ 8 / 40320)
    (hD : |D| ≤ M * (4 * h) ^ 8 / 40320)
    (hE : |E| ≤ M * (3 * h) ^ 8 / 40320)
    (hF : |F| ≤ M * (2 * h) ^ 8 / 40320)
    (hG : |G| ≤ M * h ^ 8 / 40320)
    (hH : |H| ≤ M * (7 * h) ^ 7 / 5040)
    (hh : 0 ≤ h) (hMnn : 0 ≤ M) :
    |A - (2940 / 1089 : ℝ) * B + (4410 / 1089 : ℝ) * C
        - (4900 / 1089 : ℝ) * D + (3675 / 1089 : ℝ) * E
        - (1764 / 1089 : ℝ) * F + (490 / 1089 : ℝ) * G
        - (420 / 1089 : ℝ) * h * H|
      ≤ 366 * M * h ^ 8 := by
  have h420h_nn : 0 ≤ (420 / 1089 : ℝ) * h := mul_nonneg (by norm_num) hh
  have habs2940B : |(2940 / 1089 : ℝ) * B| = (2940 / 1089 : ℝ) * |B| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2940 / 1089)]
  have habs4410C : |(4410 / 1089 : ℝ) * C| = (4410 / 1089 : ℝ) * |C| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4410 / 1089)]
  have habs4900D : |(4900 / 1089 : ℝ) * D| = (4900 / 1089 : ℝ) * |D| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4900 / 1089)]
  have habs3675E : |(3675 / 1089 : ℝ) * E| = (3675 / 1089 : ℝ) * |E| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3675 / 1089)]
  have habs1764F : |(1764 / 1089 : ℝ) * F| = (1764 / 1089 : ℝ) * |F| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1764 / 1089)]
  have habs490G : |(490 / 1089 : ℝ) * G| = (490 / 1089 : ℝ) * |G| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 490 / 1089)]
  have habs420H : |(420 / 1089 : ℝ) * h * H| = (420 / 1089 : ℝ) * h * |H| := by
    rw [abs_mul, abs_of_nonneg h420h_nn]
  have htri :
      |A - (2940 / 1089 : ℝ) * B + (4410 / 1089 : ℝ) * C
          - (4900 / 1089 : ℝ) * D + (3675 / 1089 : ℝ) * E
          - (1764 / 1089 : ℝ) * F + (490 / 1089 : ℝ) * G
          - (420 / 1089 : ℝ) * h * H|
      ≤ |A| + (2940 / 1089 : ℝ) * |B| + (4410 / 1089 : ℝ) * |C|
          + (4900 / 1089 : ℝ) * |D| + (3675 / 1089 : ℝ) * |E|
          + (1764 / 1089 : ℝ) * |F| + (490 / 1089 : ℝ) * |G|
          + (420 / 1089 : ℝ) * h * |H| := by
    have h1 :
        |A - (2940 / 1089 : ℝ) * B + (4410 / 1089 : ℝ) * C
            - (4900 / 1089 : ℝ) * D + (3675 / 1089 : ℝ) * E
            - (1764 / 1089 : ℝ) * F + (490 / 1089 : ℝ) * G
            - (420 / 1089 : ℝ) * h * H|
        ≤ |A - (2940 / 1089 : ℝ) * B + (4410 / 1089 : ℝ) * C
              - (4900 / 1089 : ℝ) * D + (3675 / 1089 : ℝ) * E
              - (1764 / 1089 : ℝ) * F + (490 / 1089 : ℝ) * G|
            + |(420 / 1089 : ℝ) * h * H| := abs_sub _ _
    have h2 :
        |A - (2940 / 1089 : ℝ) * B + (4410 / 1089 : ℝ) * C
            - (4900 / 1089 : ℝ) * D + (3675 / 1089 : ℝ) * E
            - (1764 / 1089 : ℝ) * F + (490 / 1089 : ℝ) * G|
        ≤ |A - (2940 / 1089 : ℝ) * B + (4410 / 1089 : ℝ) * C
              - (4900 / 1089 : ℝ) * D + (3675 / 1089 : ℝ) * E
              - (1764 / 1089 : ℝ) * F|
            + |(490 / 1089 : ℝ) * G| := abs_add_le _ _
    have h3 :
        |A - (2940 / 1089 : ℝ) * B + (4410 / 1089 : ℝ) * C
            - (4900 / 1089 : ℝ) * D + (3675 / 1089 : ℝ) * E
            - (1764 / 1089 : ℝ) * F|
        ≤ |A - (2940 / 1089 : ℝ) * B + (4410 / 1089 : ℝ) * C
              - (4900 / 1089 : ℝ) * D + (3675 / 1089 : ℝ) * E|
            + |(1764 / 1089 : ℝ) * F| := abs_sub _ _
    have h4 :
        |A - (2940 / 1089 : ℝ) * B + (4410 / 1089 : ℝ) * C
            - (4900 / 1089 : ℝ) * D + (3675 / 1089 : ℝ) * E|
        ≤ |A - (2940 / 1089 : ℝ) * B + (4410 / 1089 : ℝ) * C
              - (4900 / 1089 : ℝ) * D|
            + |(3675 / 1089 : ℝ) * E| := abs_add_le _ _
    have h5 :
        |A - (2940 / 1089 : ℝ) * B + (4410 / 1089 : ℝ) * C
            - (4900 / 1089 : ℝ) * D|
        ≤ |A - (2940 / 1089 : ℝ) * B + (4410 / 1089 : ℝ) * C|
            + |(4900 / 1089 : ℝ) * D| := abs_sub _ _
    have h6 :
        |A - (2940 / 1089 : ℝ) * B + (4410 / 1089 : ℝ) * C|
        ≤ |A - (2940 / 1089 : ℝ) * B| + |(4410 / 1089 : ℝ) * C| :=
      abs_add_le _ _
    have h7 :
        |A - (2940 / 1089 : ℝ) * B|
        ≤ |A| + |(2940 / 1089 : ℝ) * B| := abs_sub _ _
    linarith [h1, h2, h3, h4, h5, h6, h7,
      habs2940B.le, habs2940B.ge, habs4410C.le, habs4410C.ge,
      habs4900D.le, habs4900D.ge, habs3675E.le, habs3675E.ge,
      habs1764F.le, habs1764F.ge, habs490G.le, habs490G.ge,
      habs420H.le, habs420H.ge]
  have h2940B_bd : (2940 / 1089 : ℝ) * |B|
      ≤ (2940 / 1089 : ℝ) * (M * (6 * h) ^ 8 / 40320) :=
    mul_le_mul_of_nonneg_left hB (by norm_num)
  have h4410C_bd : (4410 / 1089 : ℝ) * |C|
      ≤ (4410 / 1089 : ℝ) * (M * (5 * h) ^ 8 / 40320) :=
    mul_le_mul_of_nonneg_left hC (by norm_num)
  have h4900D_bd : (4900 / 1089 : ℝ) * |D|
      ≤ (4900 / 1089 : ℝ) * (M * (4 * h) ^ 8 / 40320) :=
    mul_le_mul_of_nonneg_left hD (by norm_num)
  have h3675E_bd : (3675 / 1089 : ℝ) * |E|
      ≤ (3675 / 1089 : ℝ) * (M * (3 * h) ^ 8 / 40320) :=
    mul_le_mul_of_nonneg_left hE (by norm_num)
  have h1764F_bd : (1764 / 1089 : ℝ) * |F|
      ≤ (1764 / 1089 : ℝ) * (M * (2 * h) ^ 8 / 40320) :=
    mul_le_mul_of_nonneg_left hF (by norm_num)
  have h490G_bd : (490 / 1089 : ℝ) * |G|
      ≤ (490 / 1089 : ℝ) * (M * h ^ 8 / 40320) :=
    mul_le_mul_of_nonneg_left hG (by norm_num)
  have h420H_bd : (420 / 1089 : ℝ) * h * |H|
      ≤ (420 / 1089 : ℝ) * h * (M * (7 * h) ^ 7 / 5040) :=
    mul_le_mul_of_nonneg_left hH h420h_nn
  have hbound_alg :
      M * (7 * h) ^ 8 / 40320
        + (2940 / 1089 : ℝ) * (M * (6 * h) ^ 8 / 40320)
        + (4410 / 1089 : ℝ) * (M * (5 * h) ^ 8 / 40320)
        + (4900 / 1089 : ℝ) * (M * (4 * h) ^ 8 / 40320)
        + (3675 / 1089 : ℝ) * (M * (3 * h) ^ 8 / 40320)
        + (1764 / 1089 : ℝ) * (M * (2 * h) ^ 8 / 40320)
        + (490 / 1089 : ℝ) * (M * h ^ 8 / 40320)
        + (420 / 1089 : ℝ) * h * (M * (7 * h) ^ 7 / 5040)
        = (17914498 / 49005 : ℝ) * M * h ^ 8 := by
    ring
  have hh8_nn : 0 ≤ h ^ 8 := by positivity
  have hMh8_nn : 0 ≤ M * h ^ 8 := mul_nonneg hMnn hh8_nn
  have hslack : (17914498 / 49005 : ℝ) * M * h ^ 8 ≤ 366 * M * h ^ 8 := by
    have hcoef : (17914498 / 49005 : ℝ) ≤ 366 := by norm_num
    have := mul_le_mul_of_nonneg_right hcoef hMh8_nn
    linarith [this]
  linarith [htri, hA, h2940B_bd, h4410C_bd, h4900D_bd, h3675E_bd,
    h1764F_bd, h490G_bd, h420H_bd, hbound_alg.le, hbound_alg.ge, hslack]

/-- Pointwise BDF7 truncation residual bound. Algebraic identity
`τ = R_y(7) − (2940/1089)R_y(6) + (4410/1089)R_y(5) − (4900/1089)R_y(4)
   + (3675/1089)R_y(3) − (1764/1089)R_y(2) + (490/1089)R_y(1)
   − (420h/1089)R_y'(7)`, with eighth-order Taylor remainders for `y` and a
seventh-order Taylor remainder for `y'`. The `R_y(0)` contribution
vanishes identically. -/
theorem bdf7_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 8 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 8 y t| ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (ht4h : t + 4 * h ∈ Set.Icc a b)
    (ht5h : t + 5 * h ∈ Set.Icc a b)
    (ht6h : t + 6 * h ∈ Set.Icc a b)
    (ht7h : t + 7 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    |y (t + 7 * h) - (2940 / 1089 : ℝ) * y (t + 6 * h)
        + (4410 / 1089 : ℝ) * y (t + 5 * h)
        - (4900 / 1089 : ℝ) * y (t + 4 * h)
        + (3675 / 1089 : ℝ) * y (t + 3 * h)
        - (1764 / 1089 : ℝ) * y (t + 2 * h)
        + (490 / 1089 : ℝ) * y (t + h)
        - (60 / 1089 : ℝ) * y t
        - (420 / 1089 : ℝ) * h * deriv y (t + 7 * h)|
      ≤ (366 : ℝ) * M * h ^ 8 := by
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have h5h : 0 ≤ 5 * h := by linarith
  have h6h : 0 ≤ 6 * h := by linarith
  have h7h : 0 ≤ 7 * h := by linarith
  have hRy1 := y_eighth_order_taylor_remainder hy hbnd ht hth hh
  have hRy2 := y_eighth_order_taylor_remainder hy hbnd ht ht2h h2h
  have hRy3 := y_eighth_order_taylor_remainder hy hbnd ht ht3h h3h
  have hRy4 := y_eighth_order_taylor_remainder hy hbnd ht ht4h h4h
  have hRy5 := y_eighth_order_taylor_remainder hy hbnd ht ht5h h5h
  have hRy6 := y_eighth_order_taylor_remainder hy hbnd ht ht6h h6h
  have hRy7 := y_eighth_order_taylor_remainder hy hbnd ht ht7h h7h
  have hRyp7 := derivY_seventh_order_taylor_remainder hy hbnd ht ht7h h7h
  set y0 := y t with hy0_def
  set y1 := y (t + h) with hy1_def
  set y2 := y (t + 2 * h) with hy2_def
  set y3 := y (t + 3 * h) with hy3_def
  set y4 := y (t + 4 * h) with hy4_def
  set y5 := y (t + 5 * h) with hy5_def
  set y6 := y (t + 6 * h) with hy6_def
  set y7 := y (t + 7 * h) with hy7_def
  set d0 := deriv y t with hd0_def
  set d7 := deriv y (t + 7 * h) with hd7_def
  set dd := iteratedDeriv 2 y t with hdd_def
  set ddd := iteratedDeriv 3 y t with hddd_def
  set dddd := iteratedDeriv 4 y t with hdddd_def
  set ddddd := iteratedDeriv 5 y t with hddddd_def
  set dddddd := iteratedDeriv 6 y t with hdddddd_def
  set ddddddd := iteratedDeriv 7 y t with hddddddd_def
  -- LTE = R_y(7) − (2940/1089) R_y(6) + (4410/1089) R_y(5)
  --   − (4900/1089) R_y(4) + (3675/1089) R_y(3) − (1764/1089) R_y(2)
  --   + (490/1089) R_y(1) − (420h/1089) R_y'(7).
  have hLTE_eq :
      y7 - (2940 / 1089 : ℝ) * y6 + (4410 / 1089 : ℝ) * y5
          - (4900 / 1089 : ℝ) * y4 + (3675 / 1089 : ℝ) * y3
          - (1764 / 1089 : ℝ) * y2 + (490 / 1089 : ℝ) * y1
          - (60 / 1089 : ℝ) * y0
          - (420 / 1089 : ℝ) * h * d7
        = (y7 - y0 - (7 * h) * d0
              - (7 * h) ^ 2 / 2 * dd
              - (7 * h) ^ 3 / 6 * ddd
              - (7 * h) ^ 4 / 24 * dddd
              - (7 * h) ^ 5 / 120 * ddddd
              - (7 * h) ^ 6 / 720 * dddddd
              - (7 * h) ^ 7 / 5040 * ddddddd)
          - (2940 / 1089 : ℝ)
              * (y6 - y0 - (6 * h) * d0
                  - (6 * h) ^ 2 / 2 * dd
                  - (6 * h) ^ 3 / 6 * ddd
                  - (6 * h) ^ 4 / 24 * dddd
                  - (6 * h) ^ 5 / 120 * ddddd
                  - (6 * h) ^ 6 / 720 * dddddd
                  - (6 * h) ^ 7 / 5040 * ddddddd)
          + (4410 / 1089 : ℝ)
              * (y5 - y0 - (5 * h) * d0
                  - (5 * h) ^ 2 / 2 * dd
                  - (5 * h) ^ 3 / 6 * ddd
                  - (5 * h) ^ 4 / 24 * dddd
                  - (5 * h) ^ 5 / 120 * ddddd
                  - (5 * h) ^ 6 / 720 * dddddd
                  - (5 * h) ^ 7 / 5040 * ddddddd)
          - (4900 / 1089 : ℝ)
              * (y4 - y0 - (4 * h) * d0
                  - (4 * h) ^ 2 / 2 * dd
                  - (4 * h) ^ 3 / 6 * ddd
                  - (4 * h) ^ 4 / 24 * dddd
                  - (4 * h) ^ 5 / 120 * ddddd
                  - (4 * h) ^ 6 / 720 * dddddd
                  - (4 * h) ^ 7 / 5040 * ddddddd)
          + (3675 / 1089 : ℝ)
              * (y3 - y0 - (3 * h) * d0
                  - (3 * h) ^ 2 / 2 * dd
                  - (3 * h) ^ 3 / 6 * ddd
                  - (3 * h) ^ 4 / 24 * dddd
                  - (3 * h) ^ 5 / 120 * ddddd
                  - (3 * h) ^ 6 / 720 * dddddd
                  - (3 * h) ^ 7 / 5040 * ddddddd)
          - (1764 / 1089 : ℝ)
              * (y2 - y0 - (2 * h) * d0
                  - (2 * h) ^ 2 / 2 * dd
                  - (2 * h) ^ 3 / 6 * ddd
                  - (2 * h) ^ 4 / 24 * dddd
                  - (2 * h) ^ 5 / 120 * ddddd
                  - (2 * h) ^ 6 / 720 * dddddd
                  - (2 * h) ^ 7 / 5040 * ddddddd)
          + (490 / 1089 : ℝ)
              * (y1 - y0 - h * d0 - h ^ 2 / 2 * dd
                  - h ^ 3 / 6 * ddd - h ^ 4 / 24 * dddd
                  - h ^ 5 / 120 * ddddd - h ^ 6 / 720 * dddddd
                  - h ^ 7 / 5040 * ddddddd)
          - (420 / 1089 : ℝ) * h
              * (d7 - d0 - (7 * h) * dd
                  - (7 * h) ^ 2 / 2 * ddd
                  - (7 * h) ^ 3 / 6 * dddd
                  - (7 * h) ^ 4 / 24 * ddddd
                  - (7 * h) ^ 5 / 120 * dddddd
                  - (7 * h) ^ 6 / 720 * ddddddd) := by
    ring
  rw [hLTE_eq]
  set A := y7 - y0 - (7 * h) * d0
            - (7 * h) ^ 2 / 2 * dd - (7 * h) ^ 3 / 6 * ddd
            - (7 * h) ^ 4 / 24 * dddd
            - (7 * h) ^ 5 / 120 * ddddd
            - (7 * h) ^ 6 / 720 * dddddd
            - (7 * h) ^ 7 / 5040 * ddddddd with hA_def
  set B := y6 - y0 - (6 * h) * d0
            - (6 * h) ^ 2 / 2 * dd - (6 * h) ^ 3 / 6 * ddd
            - (6 * h) ^ 4 / 24 * dddd
            - (6 * h) ^ 5 / 120 * ddddd
            - (6 * h) ^ 6 / 720 * dddddd
            - (6 * h) ^ 7 / 5040 * ddddddd with hB_def
  set C := y5 - y0 - (5 * h) * d0
            - (5 * h) ^ 2 / 2 * dd - (5 * h) ^ 3 / 6 * ddd
            - (5 * h) ^ 4 / 24 * dddd
            - (5 * h) ^ 5 / 120 * ddddd
            - (5 * h) ^ 6 / 720 * dddddd
            - (5 * h) ^ 7 / 5040 * ddddddd with hC_def
  set D := y4 - y0 - (4 * h) * d0
            - (4 * h) ^ 2 / 2 * dd - (4 * h) ^ 3 / 6 * ddd
            - (4 * h) ^ 4 / 24 * dddd
            - (4 * h) ^ 5 / 120 * ddddd
            - (4 * h) ^ 6 / 720 * dddddd
            - (4 * h) ^ 7 / 5040 * ddddddd with hD_def
  set E := y3 - y0 - (3 * h) * d0
            - (3 * h) ^ 2 / 2 * dd - (3 * h) ^ 3 / 6 * ddd
            - (3 * h) ^ 4 / 24 * dddd
            - (3 * h) ^ 5 / 120 * ddddd
            - (3 * h) ^ 6 / 720 * dddddd
            - (3 * h) ^ 7 / 5040 * ddddddd with hE_def
  set F := y2 - y0 - (2 * h) * d0
            - (2 * h) ^ 2 / 2 * dd - (2 * h) ^ 3 / 6 * ddd
            - (2 * h) ^ 4 / 24 * dddd
            - (2 * h) ^ 5 / 120 * ddddd
            - (2 * h) ^ 6 / 720 * dddddd
            - (2 * h) ^ 7 / 5040 * ddddddd with hF_def
  set G := y1 - y0 - h * d0 - h ^ 2 / 2 * dd - h ^ 3 / 6 * ddd
            - h ^ 4 / 24 * dddd - h ^ 5 / 120 * ddddd
            - h ^ 6 / 720 * dddddd
            - h ^ 7 / 5040 * ddddddd with hG_def
  set H := d7 - d0 - (7 * h) * dd - (7 * h) ^ 2 / 2 * ddd
            - (7 * h) ^ 3 / 6 * dddd
            - (7 * h) ^ 4 / 24 * ddddd
            - (7 * h) ^ 5 / 120 * dddddd
            - (7 * h) ^ 6 / 720 * ddddddd with hH_def
  clear_value A B C D E F G H
  have hA_bd : |A| ≤ M * (7 * h) ^ 8 / 40320 := by
    have htmp : |A| ≤ M / 40320 * (7 * h) ^ 8 := by
      simpa [hA_def, hy7_def, hy0_def, hd0_def, hdd_def, hddd_def,
        hdddd_def, hddddd_def, hdddddd_def, hddddddd_def] using hRy7
    have hconv : M / 40320 * (7 * h) ^ 8 = M * (7 * h) ^ 8 / 40320 := by ring
    linarith
  have hB_bd : |B| ≤ M * (6 * h) ^ 8 / 40320 := by
    have htmp : |B| ≤ M / 40320 * (6 * h) ^ 8 := by
      simpa [hB_def, hy6_def, hy0_def, hd0_def, hdd_def, hddd_def,
        hdddd_def, hddddd_def, hdddddd_def, hddddddd_def] using hRy6
    have hconv : M / 40320 * (6 * h) ^ 8 = M * (6 * h) ^ 8 / 40320 := by ring
    linarith
  have hC_bd : |C| ≤ M * (5 * h) ^ 8 / 40320 := by
    have htmp : |C| ≤ M / 40320 * (5 * h) ^ 8 := by
      simpa [hC_def, hy5_def, hy0_def, hd0_def, hdd_def, hddd_def,
        hdddd_def, hddddd_def, hdddddd_def, hddddddd_def] using hRy5
    have hconv : M / 40320 * (5 * h) ^ 8 = M * (5 * h) ^ 8 / 40320 := by ring
    linarith
  have hD_bd : |D| ≤ M * (4 * h) ^ 8 / 40320 := by
    have htmp : |D| ≤ M / 40320 * (4 * h) ^ 8 := by
      simpa [hD_def, hy4_def, hy0_def, hd0_def, hdd_def, hddd_def,
        hdddd_def, hddddd_def, hdddddd_def, hddddddd_def] using hRy4
    have hconv : M / 40320 * (4 * h) ^ 8 = M * (4 * h) ^ 8 / 40320 := by ring
    linarith
  have hE_bd : |E| ≤ M * (3 * h) ^ 8 / 40320 := by
    have htmp : |E| ≤ M / 40320 * (3 * h) ^ 8 := by
      simpa [hE_def, hy3_def, hy0_def, hd0_def, hdd_def, hddd_def,
        hdddd_def, hddddd_def, hdddddd_def, hddddddd_def] using hRy3
    have hconv : M / 40320 * (3 * h) ^ 8 = M * (3 * h) ^ 8 / 40320 := by ring
    linarith
  have hF_bd : |F| ≤ M * (2 * h) ^ 8 / 40320 := by
    have htmp : |F| ≤ M / 40320 * (2 * h) ^ 8 := by
      simpa [hF_def, hy2_def, hy0_def, hd0_def, hdd_def, hddd_def,
        hdddd_def, hddddd_def, hdddddd_def, hddddddd_def] using hRy2
    have hconv : M / 40320 * (2 * h) ^ 8 = M * (2 * h) ^ 8 / 40320 := by ring
    linarith
  have hG_bd : |G| ≤ M * h ^ 8 / 40320 := by
    have htmp : |G| ≤ M / 40320 * h ^ 8 := by
      simpa [hG_def, hy1_def, hy0_def, hd0_def, hdd_def, hddd_def,
        hdddd_def, hddddd_def, hdddddd_def, hddddddd_def] using hRy1
    have hconv : M / 40320 * h ^ 8 = M * h ^ 8 / 40320 := by ring
    linarith
  have hH_bd : |H| ≤ M * (7 * h) ^ 7 / 5040 := by
    have htmp : |H| ≤ M / 5040 * (7 * h) ^ 7 := by
      simpa [hH_def, hd7_def, hd0_def, hdd_def, hddd_def, hdddd_def,
        hddddd_def, hdddddd_def, hddddddd_def] using hRyp7
    have hconv : M / 5040 * (7 * h) ^ 7 = M * (7 * h) ^ 7 / 5040 := by ring
    linarith
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (abs_nonneg _).trans this
  exact bdf7_pointwise_residual_alg h M A B C D E F G H
    hA_bd hB_bd hC_bd hD_bd hE_bd hF_bd hG_bd hH_bd hh hMnn

/-- Uniform bound on the BDF7 one-step truncation residual on a finite
horizon, given a `C^8` exact solution. -/
theorem bdf7_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 8 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 7) * h ≤ T →
        |bdf7.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 8 := by
  obtain ⟨M, _hM_nn, hM⟩ :=
    iteratedDeriv_eight_bounded_on_Icc hy t₀ (t₀ + T + 1)
  refine ⟨(366 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 7) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 7) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 7) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 7) * h := by nlinarith
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 4 * h ≤ ((n : ℝ) + 7) * h := by nlinarith
    linarith
  have ht5h_mem : t + 5 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 5 * h ≤ ((n : ℝ) + 7) * h := by nlinarith
    linarith
  have ht6h_mem : t + 6 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 6 * h ≤ ((n : ℝ) + 7) * h := by nlinarith
    linarith
  have ht7h_mem : t + 7 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 7 * h = ((n : ℝ) + 7) * h := by ring
    linarith
  rw [bdf7_localTruncationError_eq]
  exact bdf7_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem ht3h_mem
    ht4h_mem ht5h_mem ht6h_mem ht7h_mem hh.le

end LMM
