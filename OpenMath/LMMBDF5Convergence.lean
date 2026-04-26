import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMAB5Convergence

/-! ## BDF5 Quantitative Truncation Chain (Iserles §4.5)

Truncation chain for the scalar 5-step backward differentiation formula.
This module lands the supplied-trajectory predicate, the textbook local
truncation residual unfolding, the Lipschitz defect estimate, the
pointwise sixth-order Taylor residual bound, and the uniform local
residual bound on a finite horizon.

The BDF5 Lyapunov coordinates and global error theorem are deferred to a
follow-up cycle. The same obstruction documented for BDF4 in
`.prover-state/issues/bdf4_lyapunov_gap.md` applies here: irreducible
degree-at-least-three factors obstruct the rational eigenbasis transplant,
and the abs-value companion matrix has Perron radius greater than one, so
a direct weighted-ℓ¹ kernel is not available.
-/

namespace LMM

/-- BDF5 trajectory predicate:
`y_{n+5} = (300/137)y_{n+4} − (300/137)y_{n+3} + (200/137)y_{n+2}
  − (75/137)y_{n+1} + (12/137)y_n + (60/137)h·f(t_{n+5}, y_{n+5})`.
The new value appears inside `f`, so existence of such a trajectory is a
separate fixed-point problem. -/
structure IsBDF5Trajectory (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ : ℝ)
    (y : ℕ → ℝ) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 5)
      = (300 / 137 : ℝ) * y (n + 4) - (300 / 137 : ℝ) * y (n + 3)
        + (200 / 137 : ℝ) * y (n + 2) - (75 / 137 : ℝ) * y (n + 1)
        + (12 / 137 : ℝ) * y n
        + (60 / 137 : ℝ) * h * f (t₀ + ((n : ℝ) + 5) * h) (y (n + 5))

/-- BDF5 local truncation operator reduces to the textbook 5-step residual
`y(t+5h) − (300/137)y(t+4h) + (300/137)y(t+3h) − (200/137)y(t+2h)
  + (75/137)y(t+h) − (12/137)y(t) − (60/137)h y'(t+5h)`. -/
theorem bdf5_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    bdf5.localTruncationError h t y
      = y (t + 5 * h) - (300 / 137 : ℝ) * y (t + 4 * h)
        + (300 / 137 : ℝ) * y (t + 3 * h)
        - (200 / 137 : ℝ) * y (t + 2 * h)
        + (75 / 137 : ℝ) * y (t + h)
        - (12 / 137 : ℝ) * y t
        - (60 / 137 : ℝ) * h * deriv y (t + 5 * h) := by
  unfold localTruncationError truncationOp
  simp [bdf5, Fin.sum_univ_six, iteratedDeriv_one, iteratedDeriv_zero]
  ring

/-- Forcing decomposition of the BDF5 error recurrence: the homogeneous
defect is bounded by `(60/137) h L · |e_{n+5}| + |τ_n|`. -/
theorem bdf5_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsBDF5Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    |(yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h))
      - (300 / 137 : ℝ) * (yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h))
      + (300 / 137 : ℝ) * (yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h))
      - (200 / 137 : ℝ) * (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))
      + (75 / 137 : ℝ) * (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
      - (12 / 137 : ℝ) * (yseq n - y (t₀ + (n : ℝ) * h))|
    ≤ (60 / 137 : ℝ) * h * L
        * |yseq (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|
      + |bdf5.localTruncationError h (t₀ + (n : ℝ) * h) y| := by
  set yn : ℝ := yseq n with hyn_def
  set yn1 : ℝ := yseq (n + 1) with hyn1_def
  set yn2 : ℝ := yseq (n + 2) with hyn2_def
  set yn3 : ℝ := yseq (n + 3) with hyn3_def
  set yn4 : ℝ := yseq (n + 4) with hyn4_def
  set yn5 : ℝ := yseq (n + 5) with hyn5_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set tn3 : ℝ := t₀ + ((n : ℝ) + 3) * h with htn3_def
  set tn4 : ℝ := t₀ + ((n : ℝ) + 4) * h with htn4_def
  set tn5 : ℝ := t₀ + ((n : ℝ) + 5) * h with htn5_def
  set zn : ℝ := y tn with hzn_def
  set zn1 : ℝ := y tn1 with hzn1_def
  set zn2 : ℝ := y tn2 with hzn2_def
  set zn3 : ℝ := y tn3 with hzn3_def
  set zn4 : ℝ := y tn4 with hzn4_def
  set zn5 : ℝ := y tn5 with hzn5_def
  set τ : ℝ := bdf5.localTruncationError h tn y with hτ_def
  have hstep : yn5
      = (300 / 137 : ℝ) * yn4 - (300 / 137 : ℝ) * yn3
        + (200 / 137 : ℝ) * yn2 - (75 / 137 : ℝ) * yn1
        + (12 / 137 : ℝ) * yn
        + (60 / 137 : ℝ) * h * f tn5 yn5 := by
    simpa [hyn5_def, hyn4_def, hyn3_def, hyn2_def, hyn1_def, hyn_def, htn5_def]
      using hy.recurrence n
  have htn_h : tn + h = tn1 := by simp [htn_def, htn1_def]; ring
  have htn_2h : tn + 2 * h = tn2 := by simp [htn_def, htn2_def]; ring
  have htn_3h : tn + 3 * h = tn3 := by simp [htn_def, htn3_def]; ring
  have htn_4h : tn + 4 * h = tn4 := by simp [htn_def, htn4_def]; ring
  have htn_5h : tn + 5 * h = tn5 := by simp [htn_def, htn5_def]; ring
  have hτ_eq : τ = zn5 - (300 / 137 : ℝ) * zn4
        + (300 / 137 : ℝ) * zn3 - (200 / 137 : ℝ) * zn2
        + (75 / 137 : ℝ) * zn1 - (12 / 137 : ℝ) * zn
        - (60 / 137 : ℝ) * h * f tn5 zn5 := by
    show bdf5.localTruncationError h tn y = _
    rw [bdf5_localTruncationError_eq, htn_h, htn_2h, htn_3h, htn_4h,
      htn_5h, hyf tn5]
  have halg : (yn5 - zn5) - (300 / 137 : ℝ) * (yn4 - zn4)
        + (300 / 137 : ℝ) * (yn3 - zn3)
        - (200 / 137 : ℝ) * (yn2 - zn2)
        + (75 / 137 : ℝ) * (yn1 - zn1)
        - (12 / 137 : ℝ) * (yn - zn)
      = (60 / 137 : ℝ) * h * (f tn5 yn5 - f tn5 zn5) - τ := by
    conv_lhs => rw [hstep]
    rw [hτ_eq]; ring
  have hLip : |f tn5 yn5 - f tn5 zn5| ≤ L * |yn5 - zn5| := hf tn5 yn5 zn5
  have h60137_nn : (0 : ℝ) ≤ (60 / 137 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h60137_abs :
      |(60 / 137 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)|
        ≤ (60 / 137 : ℝ) * h * L * |yn5 - zn5| := by
    rw [abs_mul, abs_of_nonneg h60137_nn]
    calc (60 / 137 : ℝ) * h * |f tn5 yn5 - f tn5 zn5|
        ≤ (60 / 137 : ℝ) * h * (L * |yn5 - zn5|) :=
          mul_le_mul_of_nonneg_left hLip h60137_nn
      _ = (60 / 137 : ℝ) * h * L * |yn5 - zn5| := by ring
  have htri :
      |(60 / 137 : ℝ) * h * (f tn5 yn5 - f tn5 zn5) - τ|
      ≤ |(60 / 137 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)| + |τ| := abs_sub _ _
  calc |(yn5 - zn5) - (300 / 137 : ℝ) * (yn4 - zn4)
            + (300 / 137 : ℝ) * (yn3 - zn3)
            - (200 / 137 : ℝ) * (yn2 - zn2)
            + (75 / 137 : ℝ) * (yn1 - zn1)
            - (12 / 137 : ℝ) * (yn - zn)|
      = |(60 / 137 : ℝ) * h * (f tn5 yn5 - f tn5 zn5) - τ| := by rw [halg]
    _ ≤ |(60 / 137 : ℝ) * h * (f tn5 yn5 - f tn5 zn5)| + |τ| := htri
    _ ≤ (60 / 137 : ℝ) * h * L * |yn5 - zn5| + |τ| := by linarith [h60137_abs]

/-- Pure-algebra core of the BDF5 pointwise residual bound. Given the six
Taylor-remainder magnitude bounds, the BDF5 residual combination is
bounded by `48 · M · h⁶`. The exact coefficient is `59075/1233 ≈ 47.91`,
slackened to `48`. Extracted as a private lemma to keep the kernel out of
the heavy ambient Taylor context. -/
private lemma bdf5_pointwise_residual_alg
    (h M : ℝ) (A B C D E F : ℝ)
    (hA : |A| ≤ M * (5 * h) ^ 6 / 720)
    (hB : |B| ≤ M * (4 * h) ^ 6 / 720)
    (hC : |C| ≤ M * (3 * h) ^ 6 / 720)
    (hD : |D| ≤ M * (2 * h) ^ 6 / 720)
    (hE : |E| ≤ M * h ^ 6 / 720)
    (hF : |F| ≤ M * (5 * h) ^ 5 / 120)
    (hh : 0 ≤ h) (hMnn : 0 ≤ M) :
    |A - (300 / 137 : ℝ) * B + (300 / 137 : ℝ) * C
        - (200 / 137 : ℝ) * D + (75 / 137 : ℝ) * E
        - (60 / 137 : ℝ) * h * F|
      ≤ 48 * M * h ^ 6 := by
  have h60137h_nn : 0 ≤ (60 / 137 : ℝ) * h := mul_nonneg (by norm_num) hh
  have habs300B : |(300 / 137 : ℝ) * B| = (300 / 137 : ℝ) * |B| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 300 / 137)]
  have habs300C : |(300 / 137 : ℝ) * C| = (300 / 137 : ℝ) * |C| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 300 / 137)]
  have habs200D : |(200 / 137 : ℝ) * D| = (200 / 137 : ℝ) * |D| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 200 / 137)]
  have habs75E : |(75 / 137 : ℝ) * E| = (75 / 137 : ℝ) * |E| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 75 / 137)]
  have habs60137h : |(60 / 137 : ℝ) * h * F| = (60 / 137 : ℝ) * h * |F| := by
    rw [abs_mul, abs_of_nonneg h60137h_nn]
  have htri :
      |A - (300 / 137 : ℝ) * B + (300 / 137 : ℝ) * C
          - (200 / 137 : ℝ) * D + (75 / 137 : ℝ) * E
          - (60 / 137 : ℝ) * h * F|
      ≤ |A| + (300 / 137 : ℝ) * |B| + (300 / 137 : ℝ) * |C|
          + (200 / 137 : ℝ) * |D| + (75 / 137 : ℝ) * |E|
          + (60 / 137 : ℝ) * h * |F| := by
    have h1 :
        |A - (300 / 137 : ℝ) * B + (300 / 137 : ℝ) * C
            - (200 / 137 : ℝ) * D + (75 / 137 : ℝ) * E
            - (60 / 137 : ℝ) * h * F|
        ≤ |A - (300 / 137 : ℝ) * B + (300 / 137 : ℝ) * C
              - (200 / 137 : ℝ) * D + (75 / 137 : ℝ) * E|
            + |(60 / 137 : ℝ) * h * F| := abs_sub _ _
    have h2 :
        |A - (300 / 137 : ℝ) * B + (300 / 137 : ℝ) * C
            - (200 / 137 : ℝ) * D + (75 / 137 : ℝ) * E|
        ≤ |A - (300 / 137 : ℝ) * B + (300 / 137 : ℝ) * C
              - (200 / 137 : ℝ) * D|
            + |(75 / 137 : ℝ) * E| := abs_add_le _ _
    have h3 :
        |A - (300 / 137 : ℝ) * B + (300 / 137 : ℝ) * C
            - (200 / 137 : ℝ) * D|
        ≤ |A - (300 / 137 : ℝ) * B + (300 / 137 : ℝ) * C|
            + |(200 / 137 : ℝ) * D| := abs_sub _ _
    have h4 :
        |A - (300 / 137 : ℝ) * B + (300 / 137 : ℝ) * C|
        ≤ |A - (300 / 137 : ℝ) * B| + |(300 / 137 : ℝ) * C| :=
      abs_add_le _ _
    have h5 :
        |A - (300 / 137 : ℝ) * B|
        ≤ |A| + |(300 / 137 : ℝ) * B| := abs_sub _ _
    linarith [h1, h2, h3, h4, h5, habs300B.le, habs300B.ge,
      habs300C.le, habs300C.ge, habs200D.le, habs200D.ge,
      habs75E.le, habs75E.ge, habs60137h.le, habs60137h.ge]
  have h300B_bd : (300 / 137 : ℝ) * |B|
      ≤ (300 / 137 : ℝ) * (M * (4 * h) ^ 6 / 720) :=
    mul_le_mul_of_nonneg_left hB (by norm_num)
  have h300C_bd : (300 / 137 : ℝ) * |C|
      ≤ (300 / 137 : ℝ) * (M * (3 * h) ^ 6 / 720) :=
    mul_le_mul_of_nonneg_left hC (by norm_num)
  have h200D_bd : (200 / 137 : ℝ) * |D|
      ≤ (200 / 137 : ℝ) * (M * (2 * h) ^ 6 / 720) :=
    mul_le_mul_of_nonneg_left hD (by norm_num)
  have h75E_bd : (75 / 137 : ℝ) * |E|
      ≤ (75 / 137 : ℝ) * (M * h ^ 6 / 720) :=
    mul_le_mul_of_nonneg_left hE (by norm_num)
  have h60137F_bd : (60 / 137 : ℝ) * h * |F|
      ≤ (60 / 137 : ℝ) * h * (M * (5 * h) ^ 5 / 120) :=
    mul_le_mul_of_nonneg_left hF h60137h_nn
  have hbound_alg :
      M * (5 * h) ^ 6 / 720
        + (300 / 137 : ℝ) * (M * (4 * h) ^ 6 / 720)
        + (300 / 137 : ℝ) * (M * (3 * h) ^ 6 / 720)
        + (200 / 137 : ℝ) * (M * (2 * h) ^ 6 / 720)
        + (75 / 137 : ℝ) * (M * h ^ 6 / 720)
        + (60 / 137 : ℝ) * h * (M * (5 * h) ^ 5 / 120)
        = (59075 / 1233 : ℝ) * M * h ^ 6 := by
    ring
  have hh6_nn : 0 ≤ h ^ 6 := by positivity
  have hMh6_nn : 0 ≤ M * h ^ 6 := mul_nonneg hMnn hh6_nn
  have hslack : (59075 / 1233 : ℝ) * M * h ^ 6 ≤ 48 * M * h ^ 6 := by
    have hcoef : (59075 / 1233 : ℝ) ≤ 48 := by norm_num
    have := mul_le_mul_of_nonneg_right hcoef hMh6_nn
    linarith [this]
  linarith [htri, hA, h300B_bd, h300C_bd, h200D_bd, h75E_bd,
    h60137F_bd, hbound_alg.le, hbound_alg.ge, hslack]

/-- Pointwise BDF5 truncation residual bound. Algebraic identity
`τ = R_y(5) − (300/137)R_y(4) + (300/137)R_y(3) − (200/137)R_y(2)
   + (75/137)R_y(1) − (60h/137)R_y'(5)`, with sixth-order Taylor
remainders for `y` and a fifth-order Taylor remainder for `y'`. -/
theorem bdf5_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 6 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 6 y t| ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (ht4h : t + 4 * h ∈ Set.Icc a b)
    (ht5h : t + 5 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    |y (t + 5 * h) - (300 / 137 : ℝ) * y (t + 4 * h)
        + (300 / 137 : ℝ) * y (t + 3 * h)
        - (200 / 137 : ℝ) * y (t + 2 * h)
        + (75 / 137 : ℝ) * y (t + h)
        - (12 / 137 : ℝ) * y t
        - (60 / 137 : ℝ) * h * deriv y (t + 5 * h)|
      ≤ (48 : ℝ) * M * h ^ 6 := by
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have h5h : 0 ≤ 5 * h := by linarith
  have hRy1 := y_sixth_order_taylor_remainder hy hbnd ht hth hh
  have hRy2 := y_sixth_order_taylor_remainder hy hbnd ht ht2h h2h
  have hRy3 := y_sixth_order_taylor_remainder hy hbnd ht ht3h h3h
  have hRy4 := y_sixth_order_taylor_remainder hy hbnd ht ht4h h4h
  have hRy5 := y_sixth_order_taylor_remainder hy hbnd ht ht5h h5h
  have hRyp5 := derivY_fifth_order_taylor_remainder hy hbnd ht ht5h h5h
  set y0 := y t with hy0_def
  set y1 := y (t + h) with hy1_def
  set y2 := y (t + 2 * h) with hy2_def
  set y3 := y (t + 3 * h) with hy3_def
  set y4 := y (t + 4 * h) with hy4_def
  set y5 := y (t + 5 * h) with hy5_def
  set d0 := deriv y t with hd0_def
  set d5 := deriv y (t + 5 * h) with hd5_def
  set dd := iteratedDeriv 2 y t with hdd_def
  set ddd := iteratedDeriv 3 y t with hddd_def
  set dddd := iteratedDeriv 4 y t with hdddd_def
  set ddddd := iteratedDeriv 5 y t with hddddd_def
  -- LTE = R_y(5) − (300/137) R_y(4) + (300/137) R_y(3)
  --   − (200/137) R_y(2) + (75/137) R_y(1) − (60h/137) R_y'(5).
  have hLTE_eq :
      y5 - (300 / 137 : ℝ) * y4 + (300 / 137 : ℝ) * y3
          - (200 / 137 : ℝ) * y2 + (75 / 137 : ℝ) * y1
          - (12 / 137 : ℝ) * y0
          - (60 / 137 : ℝ) * h * d5
        = (y5 - y0 - (5 * h) * d0
              - (5 * h) ^ 2 / 2 * dd
              - (5 * h) ^ 3 / 6 * ddd
              - (5 * h) ^ 4 / 24 * dddd
              - (5 * h) ^ 5 / 120 * ddddd)
          - (300 / 137 : ℝ)
              * (y4 - y0 - (4 * h) * d0
                  - (4 * h) ^ 2 / 2 * dd
                  - (4 * h) ^ 3 / 6 * ddd
                  - (4 * h) ^ 4 / 24 * dddd
                  - (4 * h) ^ 5 / 120 * ddddd)
          + (300 / 137 : ℝ)
              * (y3 - y0 - (3 * h) * d0
                  - (3 * h) ^ 2 / 2 * dd
                  - (3 * h) ^ 3 / 6 * ddd
                  - (3 * h) ^ 4 / 24 * dddd
                  - (3 * h) ^ 5 / 120 * ddddd)
          - (200 / 137 : ℝ)
              * (y2 - y0 - (2 * h) * d0
                  - (2 * h) ^ 2 / 2 * dd
                  - (2 * h) ^ 3 / 6 * ddd
                  - (2 * h) ^ 4 / 24 * dddd
                  - (2 * h) ^ 5 / 120 * ddddd)
          + (75 / 137 : ℝ)
              * (y1 - y0 - h * d0 - h ^ 2 / 2 * dd
                  - h ^ 3 / 6 * ddd - h ^ 4 / 24 * dddd
                  - h ^ 5 / 120 * ddddd)
          - (60 / 137 : ℝ) * h
              * (d5 - d0 - (5 * h) * dd
                  - (5 * h) ^ 2 / 2 * ddd
                  - (5 * h) ^ 3 / 6 * dddd
                  - (5 * h) ^ 4 / 24 * ddddd) := by
    ring
  rw [hLTE_eq]
  set A := y5 - y0 - (5 * h) * d0
            - (5 * h) ^ 2 / 2 * dd - (5 * h) ^ 3 / 6 * ddd
            - (5 * h) ^ 4 / 24 * dddd
            - (5 * h) ^ 5 / 120 * ddddd with hA_def
  set B := y4 - y0 - (4 * h) * d0
            - (4 * h) ^ 2 / 2 * dd - (4 * h) ^ 3 / 6 * ddd
            - (4 * h) ^ 4 / 24 * dddd
            - (4 * h) ^ 5 / 120 * ddddd with hB_def
  set C := y3 - y0 - (3 * h) * d0
            - (3 * h) ^ 2 / 2 * dd - (3 * h) ^ 3 / 6 * ddd
            - (3 * h) ^ 4 / 24 * dddd
            - (3 * h) ^ 5 / 120 * ddddd with hC_def
  set D := y2 - y0 - (2 * h) * d0
            - (2 * h) ^ 2 / 2 * dd - (2 * h) ^ 3 / 6 * ddd
            - (2 * h) ^ 4 / 24 * dddd
            - (2 * h) ^ 5 / 120 * ddddd with hD_def
  set E := y1 - y0 - h * d0 - h ^ 2 / 2 * dd - h ^ 3 / 6 * ddd
            - h ^ 4 / 24 * dddd - h ^ 5 / 120 * ddddd with hE_def
  set F := d5 - d0 - (5 * h) * dd - (5 * h) ^ 2 / 2 * ddd
            - (5 * h) ^ 3 / 6 * dddd
            - (5 * h) ^ 4 / 24 * ddddd with hF_def
  clear_value A B C D E F
  have hA_bd : |A| ≤ M * (5 * h) ^ 6 / 720 := by
    have htmp : |A| ≤ M / 720 * (5 * h) ^ 6 := by
      simpa [hA_def, hy5_def, hy0_def, hd0_def, hdd_def, hddd_def,
        hdddd_def, hddddd_def] using hRy5
    have hconv : M / 720 * (5 * h) ^ 6 = M * (5 * h) ^ 6 / 720 := by ring
    linarith
  have hB_bd : |B| ≤ M * (4 * h) ^ 6 / 720 := by
    have htmp : |B| ≤ M / 720 * (4 * h) ^ 6 := by
      simpa [hB_def, hy4_def, hy0_def, hd0_def, hdd_def, hddd_def,
        hdddd_def, hddddd_def] using hRy4
    have hconv : M / 720 * (4 * h) ^ 6 = M * (4 * h) ^ 6 / 720 := by ring
    linarith
  have hC_bd : |C| ≤ M * (3 * h) ^ 6 / 720 := by
    have htmp : |C| ≤ M / 720 * (3 * h) ^ 6 := by
      simpa [hC_def, hy3_def, hy0_def, hd0_def, hdd_def, hddd_def,
        hdddd_def, hddddd_def] using hRy3
    have hconv : M / 720 * (3 * h) ^ 6 = M * (3 * h) ^ 6 / 720 := by ring
    linarith
  have hD_bd : |D| ≤ M * (2 * h) ^ 6 / 720 := by
    have htmp : |D| ≤ M / 720 * (2 * h) ^ 6 := by
      simpa [hD_def, hy2_def, hy0_def, hd0_def, hdd_def, hddd_def,
        hdddd_def, hddddd_def] using hRy2
    have hconv : M / 720 * (2 * h) ^ 6 = M * (2 * h) ^ 6 / 720 := by ring
    linarith
  have hE_bd : |E| ≤ M * h ^ 6 / 720 := by
    have htmp : |E| ≤ M / 720 * h ^ 6 := by
      simpa [hE_def, hy1_def, hy0_def, hd0_def, hdd_def, hddd_def,
        hdddd_def, hddddd_def] using hRy1
    have hconv : M / 720 * h ^ 6 = M * h ^ 6 / 720 := by ring
    linarith
  have hF_bd : |F| ≤ M * (5 * h) ^ 5 / 120 := by
    have htmp : |F| ≤ M / 120 * (5 * h) ^ 5 := by
      simpa [hF_def, hd5_def, hd0_def, hdd_def, hddd_def, hdddd_def,
        hddddd_def] using hRyp5
    have hconv : M / 120 * (5 * h) ^ 5 = M * (5 * h) ^ 5 / 120 := by ring
    linarith
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (abs_nonneg _).trans this
  exact bdf5_pointwise_residual_alg h M A B C D E F
    hA_bd hB_bd hC_bd hD_bd hE_bd hF_bd hh hMnn

/-- Uniform bound on the BDF5 one-step truncation residual on a finite
horizon, given a `C^6` exact solution. -/
theorem bdf5_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 6 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 5) * h ≤ T →
        |bdf5.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 6 := by
  obtain ⟨M, _hM_nn, hM⟩ :=
    iteratedDeriv_six_bounded_on_Icc hy t₀ (t₀ + T + 1)
  refine ⟨(48 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 5) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 5) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 5) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 5) * h := by nlinarith
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 4 * h ≤ ((n : ℝ) + 5) * h := by nlinarith
    linarith
  have ht5h_mem : t + 5 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 5 * h = ((n : ℝ) + 5) * h := by ring
    linarith
  rw [bdf5_localTruncationError_eq]
  exact bdf5_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem ht3h_mem
    ht4h_mem ht5h_mem hh.le

end LMM
