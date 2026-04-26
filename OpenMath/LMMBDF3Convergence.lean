import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMAB3Convergence

/-! ## BDF3 Quantitative Convergence Chain (Iserles §4.5)

Fallback-start module for the scalar 3-step backward differentiation formula.
This cycle lands the supplied-trajectory predicate, the textbook local
truncation residual unfolding, the Lipschitz defect estimate, and the local
residual bound; the Lyapunov-sum convergence recurrence is the next piece.
-/

namespace LMM

/-- BDF3 trajectory predicate:
`y_{n+3} = (18/11)y_{n+2} - (9/11)y_{n+1} + (2/11)y_n
  + (6/11)h f(t_{n+3}, y_{n+3})`.
The new value appears inside `f`, so existence of such a trajectory is a
separate fixed-point problem. -/
structure IsBDF3Trajectory (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ : ℝ)
    (y : ℕ → ℝ) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 3)
      = (18 / 11 : ℝ) * y (n + 2) - (9 / 11 : ℝ) * y (n + 1)
        + (2 / 11 : ℝ) * y n
        + (6 / 11 : ℝ) * h * f (t₀ + ((n : ℝ) + 3) * h) (y (n + 3))

/-- BDF3 local truncation operator reduces to the textbook 3-step residual
`y(t+3h) − (18/11)y(t+2h) + (9/11)y(t+h) − (2/11)y(t)
  − (6/11)h y'(t+3h)`. -/
theorem bdf3_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    bdf3.localTruncationError h t y
      = y (t + 3 * h) - (18 / 11 : ℝ) * y (t + 2 * h)
        + (9 / 11 : ℝ) * y (t + h) - (2 / 11 : ℝ) * y t
        - (6 / 11 : ℝ) * h * deriv y (t + 3 * h) := by
  unfold localTruncationError truncationOp
  simp [bdf3, Fin.sum_univ_four, iteratedDeriv_one, iteratedDeriv_zero]
  ring

/-- Forcing decomposition of the BDF3 error recurrence: the homogeneous
defect `e_{n+3} − (18/11)e_{n+2} + (9/11)e_{n+1} − (2/11)e_n` is bounded by
`(6/11) h L · |e_{n+3}| + |τ_n|`.  The remaining BDF3 work is to convert this
defect estimate into a stable Lyapunov-window recurrence. -/
theorem bdf3_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsBDF3Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    |(yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h))
      - (18 / 11 : ℝ) * (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))
      + (9 / 11 : ℝ) * (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
      - (2 / 11 : ℝ) * (yseq n - y (t₀ + (n : ℝ) * h))|
    ≤ (6 / 11 : ℝ) * h * L
        * |yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|
      + |bdf3.localTruncationError h (t₀ + (n : ℝ) * h) y| := by
  set yn : ℝ := yseq n with hyn_def
  set yn1 : ℝ := yseq (n + 1) with hyn1_def
  set yn2 : ℝ := yseq (n + 2) with hyn2_def
  set yn3 : ℝ := yseq (n + 3) with hyn3_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set tn3 : ℝ := t₀ + ((n : ℝ) + 3) * h with htn3_def
  set zn : ℝ := y tn with hzn_def
  set zn1 : ℝ := y tn1 with hzn1_def
  set zn2 : ℝ := y tn2 with hzn2_def
  set zn3 : ℝ := y tn3 with hzn3_def
  set τ : ℝ := bdf3.localTruncationError h tn y with hτ_def
  have hstep : yn3
      = (18 / 11 : ℝ) * yn2 - (9 / 11 : ℝ) * yn1 + (2 / 11 : ℝ) * yn
        + (6 / 11 : ℝ) * h * f tn3 yn3 := by
    simpa [hyn3_def, hyn2_def, hyn1_def, hyn_def, htn3_def] using hy.recurrence n
  have htn_h : tn + h = tn1 := by simp [htn_def, htn1_def]; ring
  have htn_2h : tn + 2 * h = tn2 := by simp [htn_def, htn2_def]; ring
  have htn_3h : tn + 3 * h = tn3 := by simp [htn_def, htn3_def]; ring
  have hτ_eq : τ = zn3 - (18 / 11 : ℝ) * zn2 + (9 / 11 : ℝ) * zn1
        - (2 / 11 : ℝ) * zn - (6 / 11 : ℝ) * h * f tn3 zn3 := by
    show bdf3.localTruncationError h tn y = _
    rw [bdf3_localTruncationError_eq, htn_h, htn_2h, htn_3h, hyf tn3]
  have halg : (yn3 - zn3) - (18 / 11 : ℝ) * (yn2 - zn2)
        + (9 / 11 : ℝ) * (yn1 - zn1) - (2 / 11 : ℝ) * (yn - zn)
      = (6 / 11 : ℝ) * h * (f tn3 yn3 - f tn3 zn3) - τ := by
    conv_lhs => rw [hstep]
    rw [hτ_eq]; ring
  have hLip : |f tn3 yn3 - f tn3 zn3| ≤ L * |yn3 - zn3| := hf tn3 yn3 zn3
  have h611_nn : (0 : ℝ) ≤ (6 / 11 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h611_abs :
      |(6 / 11 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)|
        ≤ (6 / 11 : ℝ) * h * L * |yn3 - zn3| := by
    rw [abs_mul, abs_of_nonneg h611_nn]
    calc (6 / 11 : ℝ) * h * |f tn3 yn3 - f tn3 zn3|
        ≤ (6 / 11 : ℝ) * h * (L * |yn3 - zn3|) :=
          mul_le_mul_of_nonneg_left hLip h611_nn
      _ = (6 / 11 : ℝ) * h * L * |yn3 - zn3| := by ring
  have htri :
      |(6 / 11 : ℝ) * h * (f tn3 yn3 - f tn3 zn3) - τ|
      ≤ |(6 / 11 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)| + |τ| := abs_sub _ _
  calc |(yn3 - zn3) - (18 / 11 : ℝ) * (yn2 - zn2)
            + (9 / 11 : ℝ) * (yn1 - zn1) - (2 / 11 : ℝ) * (yn - zn)|
      = |(6 / 11 : ℝ) * h * (f tn3 yn3 - f tn3 zn3) - τ| := by rw [halg]
    _ ≤ |(6 / 11 : ℝ) * h * (f tn3 yn3 - f tn3 zn3)| + |τ| := htri
    _ ≤ (6 / 11 : ℝ) * h * L * |yn3 - zn3| + |τ| := by linarith [h611_abs]

/-- Pointwise BDF3 truncation residual bound.  Algebraic identity
`tau = R_y(3) - (18/11) R_y(2) + (9/11) R_y(1)
  - (6h/11) R_y'(3)`, with fourth-order Taylor remainders for `y` and a
third-order Taylor remainder for `y'`.  The exact coefficient
`153/22 ~= 6.96` is slackened to `7`. -/
theorem bdf3_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 4 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 4 y t| ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    |y (t + 3 * h) - (18 / 11 : ℝ) * y (t + 2 * h)
        + (9 / 11 : ℝ) * y (t + h) - (2 / 11 : ℝ) * y t
        - (6 / 11 : ℝ) * h * deriv y (t + 3 * h)|
      ≤ (7 : ℝ) * M * h ^ 4 := by
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have hRy1 := y_fourth_order_taylor_remainder hy hbnd ht hth hh
  have hRy2 := y_fourth_order_taylor_remainder hy hbnd ht ht2h h2h
  have hRy3 := y_fourth_order_taylor_remainder hy hbnd ht ht3h h3h
  have hRyp3 := derivY_third_order_taylor_remainder hy hbnd ht ht3h h3h
  set y0 := y t with hy0_def
  set y1 := y (t + h) with hy1_def
  set y2 := y (t + 2 * h) with hy2_def
  set y3 := y (t + 3 * h) with hy3_def
  set d0 := deriv y t with hd0_def
  set d3 := deriv y (t + 3 * h) with hd3_def
  set dd := iteratedDeriv 2 y t with hdd_def
  set ddd := iteratedDeriv 3 y t with hddd_def
  have hLTE_eq :
      y3 - (18 / 11 : ℝ) * y2 + (9 / 11 : ℝ) * y1
          - (2 / 11 : ℝ) * y0 - (6 / 11 : ℝ) * h * d3
        = (y3 - y0 - (3 * h) * d0
              - (3 * h) ^ 2 / 2 * dd - (3 * h) ^ 3 / 6 * ddd)
          - (18 / 11 : ℝ)
              * (y2 - y0 - (2 * h) * d0
                  - (2 * h) ^ 2 / 2 * dd - (2 * h) ^ 3 / 6 * ddd)
          + (9 / 11 : ℝ)
              * (y1 - y0 - h * d0 - h ^ 2 / 2 * dd - h ^ 3 / 6 * ddd)
          - ((6 / 11 : ℝ) * h)
              * (d3 - d0 - (3 * h) * dd - (3 * h) ^ 2 / 2 * ddd) := by
    ring
  rw [hLTE_eq]
  set A := y3 - y0 - (3 * h) * d0
            - (3 * h) ^ 2 / 2 * dd - (3 * h) ^ 3 / 6 * ddd with hA_def
  set B := y2 - y0 - (2 * h) * d0
            - (2 * h) ^ 2 / 2 * dd - (2 * h) ^ 3 / 6 * ddd with hB_def
  set C := y1 - y0 - h * d0 - h ^ 2 / 2 * dd - h ^ 3 / 6 * ddd with hC_def
  set D := d3 - d0 - (3 * h) * dd - (3 * h) ^ 2 / 2 * ddd with hD_def
  have h611h_nn : 0 ≤ (6 / 11 : ℝ) * h := mul_nonneg (by norm_num) hh
  have habs18 : |(18 / 11 : ℝ) * B| = (18 / 11 : ℝ) * |B| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 18 / 11)]
  have habs9 : |(9 / 11 : ℝ) * C| = (9 / 11 : ℝ) * |C| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 11)]
  have habs611h : |((6 / 11 : ℝ) * h) * D|
      = (6 / 11 : ℝ) * h * |D| := by
    rw [abs_mul, abs_of_nonneg h611h_nn]
  have htri :
      |A - (18 / 11 : ℝ) * B + (9 / 11 : ℝ) * C
          - ((6 / 11 : ℝ) * h) * D|
      ≤ |A| + (18 / 11 : ℝ) * |B| + (9 / 11 : ℝ) * |C|
          + (6 / 11 : ℝ) * h * |D| := by
    have h1 : |A - (18 / 11 : ℝ) * B + (9 / 11 : ℝ) * C
          - ((6 / 11 : ℝ) * h) * D|
        ≤ |A - (18 / 11 : ℝ) * B + (9 / 11 : ℝ) * C|
            + |((6 / 11 : ℝ) * h) * D| := abs_sub _ _
    have h2 : |A - (18 / 11 : ℝ) * B + (9 / 11 : ℝ) * C|
        ≤ |A - (18 / 11 : ℝ) * B| + |(9 / 11 : ℝ) * C| :=
      abs_add_le _ _
    have h3 : |A - (18 / 11 : ℝ) * B|
        ≤ |A| + |(18 / 11 : ℝ) * B| := abs_sub _ _
    linarith [habs18.le, habs18.ge, habs9.le, habs9.ge,
      habs611h.le, habs611h.ge]
  have hA_bd : |A| ≤ M / 24 * (3 * h) ^ 4 := hRy3
  have hB_bd : |B| ≤ M / 24 * (2 * h) ^ 4 := hRy2
  have hC_bd : |C| ≤ M / 24 * h ^ 4 := hRy1
  have hD_bd : |D| ≤ M / 6 * (3 * h) ^ 3 := hRyp3
  have h18B_bd : (18 / 11 : ℝ) * |B|
      ≤ (18 / 11 : ℝ) * (M / 24 * (2 * h) ^ 4) :=
    mul_le_mul_of_nonneg_left hB_bd (by norm_num)
  have h9C_bd : (9 / 11 : ℝ) * |C|
      ≤ (9 / 11 : ℝ) * (M / 24 * h ^ 4) :=
    mul_le_mul_of_nonneg_left hC_bd (by norm_num)
  have h611D_bd : (6 / 11 : ℝ) * h * |D|
      ≤ (6 / 11 : ℝ) * h * (M / 6 * (3 * h) ^ 3) :=
    mul_le_mul_of_nonneg_left hD_bd h611h_nn
  have hbound_alg :
      M / 24 * (3 * h) ^ 4
        + (18 / 11 : ℝ) * (M / 24 * (2 * h) ^ 4)
        + (9 / 11 : ℝ) * (M / 24 * h ^ 4)
        + (6 / 11 : ℝ) * h * (M / 6 * (3 * h) ^ 3)
        = (153 / 22 : ℝ) * M * h ^ 4 := by
    ring
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (abs_nonneg _).trans this
  have hh4_nn : 0 ≤ h ^ 4 := by positivity
  have hslack : (153 / 22 : ℝ) * M * h ^ 4 ≤ 7 * M * h ^ 4 := by
    have hcoef : (153 / 22 : ℝ) ≤ 7 := by norm_num
    nlinarith [hMnn, hh4_nn]
  linarith [htri, hA_bd, h18B_bd, h9C_bd, h611D_bd, hbound_alg.le,
    hbound_alg.ge, hslack]

/-- Uniform bound on the BDF3 one-step truncation residual on a finite
horizon, given a `C^4` exact solution. -/
theorem bdf3_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 4 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 3) * h ≤ T →
        |bdf3.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 4 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_four_bounded_on_Icc hy t₀ (t₀ + T + 1)
  refine ⟨(7 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by nlinarith [hn_nn, hh.le], ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 3) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by nlinarith [hn_nn, hh.le], ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 3) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by nlinarith [hn_nn, hh.le], ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 3) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by nlinarith [hn_nn, hh.le], ?_⟩
    have h1 : (n : ℝ) * h + 3 * h = ((n : ℝ) + 3) * h := by ring
    linarith
  rw [bdf3_localTruncationError_eq]
  exact bdf3_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem ht3h_mem hh.le

end LMM
