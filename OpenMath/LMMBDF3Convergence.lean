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

/-! ### Lyapunov coordinates for the BDF3 error system

The companion matrix of `ρ(ζ) = ζ³ − (18/11)ζ² + (9/11)ζ − (2/11)
  = (ζ − 1)(ζ² − (7/11)ζ + 2/11)` has principal root `1` and a complex pair
with `|λ|² = 2/11`.  We split the error window `(e_n, e_{n+1}, e_{n+2})` along
this decomposition:

* `bdf3LyapU e n := (2/11) e n − (7/11) e (n+1) + e (n+2)` is the left
  eigenvector for `λ = 1`; it satisfies `u_{n+1} = u_n + ψ_n` exactly.
* `bdf3LyapSigma e n := (1/6)(4 e n + 7 e (n+1) − 11 e (n+2))` and
  `bdf3LyapTau e n := (1/6)(−2 e n + 13 e (n+1) − 11 e (n+2))` are the two
  complementary `V`-coordinates (`σ_n = e_n − c_n`, `τ_n = e_{n+1} − c_n`
  with `c_n = (11/6) u_n`); they satisfy
  `σ_{n+1} = τ_n − (11/6) ψ_n`, `τ_{n+1} = −(2/11) σ_n + (7/11) τ_n − (11/6) ψ_n`.

The Lyapunov sum `W_n := |u_n| + (1/11) (|σ_n| + 5 |τ_n|)` satisfies the
clean recurrence `W_{n+1} ≤ (1 + h·(6 L)) W_n + 4 |τ_n|` under the small-step
regime `(6/11) h L ≤ 1/4`. -/

/-- Principal-eigenvector projection of a 3-window BDF3 error sample. -/
noncomputable def bdf3LyapU (e : ℕ → ℝ) (n : ℕ) : ℝ :=
  (2 / 11 : ℝ) * e n - (7 / 11 : ℝ) * e (n + 1) + e (n + 2)

/-- First complementary `V`-coordinate of a 3-window BDF3 error sample. -/
noncomputable def bdf3LyapSigma (e : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 / 6 : ℝ) * (4 * e n + 7 * e (n + 1) - 11 * e (n + 2))

/-- Second complementary `V`-coordinate of a 3-window BDF3 error sample. -/
noncomputable def bdf3LyapTau (e : ℕ → ℝ) (n : ℕ) : ℝ :=
  (1 / 6 : ℝ) * (-2 * e n + 13 * e (n + 1) - 11 * e (n + 2))

/-- BDF3 Lyapunov sum. -/
noncomputable def bdf3LyapW (e : ℕ → ℝ) (n : ℕ) : ℝ :=
  |bdf3LyapU e n|
    + (1 / 11 : ℝ) * (|bdf3LyapSigma e n| + 5 * |bdf3LyapTau e n|)

lemma bdf3LyapW_nonneg (e : ℕ → ℝ) (n : ℕ) : 0 ≤ bdf3LyapW e n := by
  unfold bdf3LyapW
  have h1 : 0 ≤ |bdf3LyapU e n| := abs_nonneg _
  have h2 : 0 ≤ |bdf3LyapSigma e n| := abs_nonneg _
  have h3 : 0 ≤ |bdf3LyapTau e n| := abs_nonneg _
  have hsum : 0 ≤ |bdf3LyapSigma e n| + 5 * |bdf3LyapTau e n| := by
    have h5 : 0 ≤ 5 * |bdf3LyapTau e n| := by positivity
    linarith
  have h11 : 0 ≤ (1 / 11 : ℝ) * (|bdf3LyapSigma e n| + 5 * |bdf3LyapTau e n|) :=
    mul_nonneg (by norm_num) hsum
  linarith

/-- Principal Lyapunov recurrence: `u_{n+1} = u_n + ψ_n` where `ψ_n` is the
BDF3 defect. -/
lemma bdf3LyapU_succ_eq
    {h : ℝ} {f : ℝ → ℝ → ℝ} (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsBDF3Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    bdf3LyapU (fun k => yseq k - y (t₀ + (k : ℝ) * h)) (n + 1)
      = bdf3LyapU (fun k => yseq k - y (t₀ + (k : ℝ) * h)) n
        + ((yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h))
            - (18 / 11 : ℝ) * (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))
            + (9 / 11 : ℝ) * (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
            - (2 / 11 : ℝ) * (yseq n - y (t₀ + (n : ℝ) * h))) := by
  unfold bdf3LyapU
  have hcast0 : ((n + 0 : ℕ) : ℝ) = (n : ℝ) := by push_cast; ring
  have hcast1 : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
  have hcast2 : (((n + 2 : ℕ) : ℝ)) = (n : ℝ) + 2 := by push_cast; ring
  have hcast3 : (((n + 3 : ℕ) : ℝ)) = (n : ℝ) + 3 := by push_cast; ring
  show (2 / 11 : ℝ) * (yseq (n + 1) - y (t₀ + ((n + 1 : ℕ) : ℝ) * h))
        - (7 / 11 : ℝ) * (yseq (n + 1 + 1) - y (t₀ + ((n + 1 + 1 : ℕ) : ℝ) * h))
        + (yseq (n + 1 + 2) - y (t₀ + ((n + 1 + 2 : ℕ) : ℝ) * h))
      = ((2 / 11 : ℝ) * (yseq n - y (t₀ + (n : ℝ) * h))
          - (7 / 11 : ℝ) * (yseq (n + 1) - y (t₀ + ((n + 1 : ℕ) : ℝ) * h))
          + (yseq (n + 2) - y (t₀ + ((n + 2 : ℕ) : ℝ) * h)))
        + ((yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h))
            - (18 / 11 : ℝ) * (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))
            + (9 / 11 : ℝ) * (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
            - (2 / 11 : ℝ) * (yseq n - y (t₀ + (n : ℝ) * h)))
  have e1 : n + 1 + 1 = n + 2 := by omega
  have e2 : n + 1 + 2 = n + 3 := by omega
  rw [e1, e2, hcast1, hcast2, hcast3]
  ring

/-- First complementary recurrence: `σ_{n+1} = τ_n − (11/6) ψ_n`. -/
lemma bdf3LyapSigma_succ_eq
    (h : ℝ) (yseq : ℕ → ℝ) (t₀ : ℝ) (y : ℝ → ℝ) (n : ℕ) :
    bdf3LyapSigma (fun k => yseq k - y (t₀ + (k : ℝ) * h)) (n + 1)
      = bdf3LyapTau (fun k => yseq k - y (t₀ + (k : ℝ) * h)) n
        - (11 / 6 : ℝ) * ((yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h))
            - (18 / 11 : ℝ) * (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))
            + (9 / 11 : ℝ) * (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
            - (2 / 11 : ℝ) * (yseq n - y (t₀ + (n : ℝ) * h))) := by
  unfold bdf3LyapSigma bdf3LyapTau
  have hcast1 : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
  have hcast2 : (((n + 2 : ℕ) : ℝ)) = (n : ℝ) + 2 := by push_cast; ring
  have hcast3 : (((n + 3 : ℕ) : ℝ)) = (n : ℝ) + 3 := by push_cast; ring
  have e1 : n + 1 + 1 = n + 2 := by omega
  have e2 : n + 1 + 2 = n + 3 := by omega
  show (1 / 6 : ℝ) * (4 * (yseq (n + 1) - y (t₀ + ((n + 1 : ℕ) : ℝ) * h))
        + 7 * (yseq (n + 1 + 1) - y (t₀ + ((n + 1 + 1 : ℕ) : ℝ) * h))
        - 11 * (yseq (n + 1 + 2) - y (t₀ + ((n + 1 + 2 : ℕ) : ℝ) * h)))
      = (1 / 6 : ℝ) * (-2 * (yseq n - y (t₀ + (n : ℝ) * h))
          + 13 * (yseq (n + 1) - y (t₀ + ((n + 1 : ℕ) : ℝ) * h))
          - 11 * (yseq (n + 2) - y (t₀ + ((n + 2 : ℕ) : ℝ) * h)))
        - (11 / 6 : ℝ) * ((yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h))
            - (18 / 11 : ℝ) * (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))
            + (9 / 11 : ℝ) * (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
            - (2 / 11 : ℝ) * (yseq n - y (t₀ + (n : ℝ) * h)))
  rw [e1, e2, hcast1, hcast2, hcast3]
  ring

/-- Second complementary recurrence:
`τ_{n+1} = −(2/11) σ_n + (7/11) τ_n − (11/6) ψ_n`. -/
lemma bdf3LyapTau_succ_eq
    (h : ℝ) (yseq : ℕ → ℝ) (t₀ : ℝ) (y : ℝ → ℝ) (n : ℕ) :
    bdf3LyapTau (fun k => yseq k - y (t₀ + (k : ℝ) * h)) (n + 1)
      = -(2 / 11 : ℝ) * bdf3LyapSigma (fun k => yseq k - y (t₀ + (k : ℝ) * h)) n
        + (7 / 11 : ℝ) * bdf3LyapTau (fun k => yseq k - y (t₀ + (k : ℝ) * h)) n
        - (11 / 6 : ℝ) * ((yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h))
            - (18 / 11 : ℝ) * (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))
            + (9 / 11 : ℝ) * (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
            - (2 / 11 : ℝ) * (yseq n - y (t₀ + (n : ℝ) * h))) := by
  unfold bdf3LyapTau bdf3LyapSigma
  have hcast1 : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
  have hcast2 : (((n + 2 : ℕ) : ℝ)) = (n : ℝ) + 2 := by push_cast; ring
  have hcast3 : (((n + 3 : ℕ) : ℝ)) = (n : ℝ) + 3 := by push_cast; ring
  have e1 : n + 1 + 1 = n + 2 := by omega
  have e2 : n + 1 + 2 = n + 3 := by omega
  show (1 / 6 : ℝ) * (-2 * (yseq (n + 1) - y (t₀ + ((n + 1 : ℕ) : ℝ) * h))
        + 13 * (yseq (n + 1 + 1) - y (t₀ + ((n + 1 + 1 : ℕ) : ℝ) * h))
        - 11 * (yseq (n + 1 + 2) - y (t₀ + ((n + 1 + 2 : ℕ) : ℝ) * h)))
      = -(2 / 11 : ℝ) * ((1 / 6 : ℝ) * (4 * (yseq n - y (t₀ + (n : ℝ) * h))
            + 7 * (yseq (n + 1) - y (t₀ + ((n + 1 : ℕ) : ℝ) * h))
            - 11 * (yseq (n + 2) - y (t₀ + ((n + 2 : ℕ) : ℝ) * h))))
        + (7 / 11 : ℝ) * ((1 / 6 : ℝ) * (-2 * (yseq n - y (t₀ + (n : ℝ) * h))
            + 13 * (yseq (n + 1) - y (t₀ + ((n + 1 : ℕ) : ℝ) * h))
            - 11 * (yseq (n + 2) - y (t₀ + ((n + 2 : ℕ) : ℝ) * h))))
        - (11 / 6 : ℝ) * ((yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h))
            - (18 / 11 : ℝ) * (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))
            + (9 / 11 : ℝ) * (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
            - (2 / 11 : ℝ) * (yseq n - y (t₀ + (n : ℝ) * h)))
  rw [e1, e2, hcast1, hcast2, hcast3]
  ring

/-- Pure-algebra core of the BDF3 Lyapunov-window recurrence.  Given a defect
`ψ` controlled by `(6/11) h L · |en3| + τabs` and the Lyapunov decomposition
`en3 = (11/6) u − (14/121) σ + (27/121) τc + ψ`, the next Lyapunov coordinates
satisfy
`|u + ψ| + (1/11)(|τc − (11/6) ψ| + 5 |−(2/11) σ + (7/11) τc − (11/6) ψ|)
  ≤ (1 + h·(6 L))·(|u| + (1/11)(|σ| + 5 |τc|)) + 4 τabs`.
Extracted as a separate lemma to keep the kernel out of the heavy ambient
trajectory context (cycle 442/444/450 pattern). -/
private lemma bdf3_one_step_lyapunov_alg
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (6 / 11 : ℝ) * h * L ≤ 1 / 4)
    (u σ τc ψ en3 τabs : ℝ)
    (hτabs_nn : 0 ≤ τabs)
    (hen3_uv : en3 = (11 / 6 : ℝ) * u
        - (14 / 121 : ℝ) * σ + (27 / 121 : ℝ) * τc + ψ)
    (hψ_bd : |ψ| ≤ (6 / 11 : ℝ) * h * L * |en3| + τabs) :
    |u + ψ|
        + (1 / 11 : ℝ) * (|τc - (11 / 6 : ℝ) * ψ|
            + 5 * |-(2 / 11 : ℝ) * σ + (7 / 11 : ℝ) * τc
                  - (11 / 6 : ℝ) * ψ|)
      ≤ (1 + h * (6 * L)) * (|u| + (1 / 11 : ℝ) * (|σ| + 5 * |τc|))
        + 4 * τabs := by
  have hu_nn : 0 ≤ |u| := abs_nonneg _
  have hσ_nn : 0 ≤ |σ| := abs_nonneg _
  have hτc_nn : 0 ≤ |τc| := abs_nonneg _
  have hψ_nn : 0 ≤ |ψ| := abs_nonneg _
  have hen3_nn : 0 ≤ |en3| := abs_nonneg _
  have hhL_nn : 0 ≤ h * L := mul_nonneg hh hL
  have h611hL_nn : 0 ≤ (6 / 11 : ℝ) * h * L := by positivity
  -- |en3| ≤ (11/6)|u| + (14/121)|σ| + (27/121)|τc| + |ψ|.
  have hen3_bd_components : |en3| ≤ (11 / 6 : ℝ) * |u|
        + (14 / 121 : ℝ) * |σ| + (27 / 121 : ℝ) * |τc| + |ψ| := by
    rw [hen3_uv]
    have a1 : |(11 / 6 : ℝ) * u
                - (14 / 121 : ℝ) * σ + (27 / 121 : ℝ) * τc + ψ|
        ≤ |(11 / 6 : ℝ) * u
            - (14 / 121 : ℝ) * σ + (27 / 121 : ℝ) * τc| + |ψ| := abs_add_le _ _
    have a2 : |(11 / 6 : ℝ) * u
                - (14 / 121 : ℝ) * σ + (27 / 121 : ℝ) * τc|
        ≤ |(11 / 6 : ℝ) * u - (14 / 121 : ℝ) * σ| + |(27 / 121 : ℝ) * τc| :=
      abs_add_le _ _
    have a3 : |(11 / 6 : ℝ) * u - (14 / 121 : ℝ) * σ|
        ≤ |(11 / 6 : ℝ) * u| + |(14 / 121 : ℝ) * σ| := abs_sub _ _
    have e1 : |(11 / 6 : ℝ) * u| = (11 / 6 : ℝ) * |u| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 11 / 6)]
    have e2 : |(14 / 121 : ℝ) * σ| = (14 / 121 : ℝ) * |σ| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 14 / 121)]
    have e3 : |(27 / 121 : ℝ) * τc| = (27 / 121 : ℝ) * |τc| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 27 / 121)]
    linarith
  -- Set W := |u| + (1/11)(|σ| + 5|τc|).
  set W : ℝ := |u| + (1 / 11 : ℝ) * (|σ| + 5 * |τc|) with hW_def
  clear_value W
  have hW_nn : 0 ≤ W := by
    rw [hW_def]
    have h1 : 0 ≤ (1 / 11 : ℝ) * (|σ| + 5 * |τc|) := by positivity
    linarith
  -- Slack |en3| ≤ 4 W + |ψ|.
  have hen3_bd : |en3| ≤ 4 * W + |ψ| := by
    rw [hW_def]
    have hcoef_u : (11 / 6 : ℝ) ≤ 4 := by norm_num
    have hcoef_σ : (14 / 121 : ℝ) ≤ 4 * (1 / 11 : ℝ) := by norm_num
    have hcoef_τ : (27 / 121 : ℝ) ≤ 4 * ((1 / 11 : ℝ) * 5) := by norm_num
    have hu_bd' : (11 / 6 : ℝ) * |u| ≤ 4 * |u| :=
      mul_le_mul_of_nonneg_right hcoef_u hu_nn
    have hσ_bd' : (14 / 121 : ℝ) * |σ| ≤ 4 * (1 / 11 : ℝ) * |σ| :=
      mul_le_mul_of_nonneg_right hcoef_σ hσ_nn
    have hτ_bd' : (27 / 121 : ℝ) * |τc| ≤ 4 * ((1 / 11 : ℝ) * 5) * |τc| :=
      mul_le_mul_of_nonneg_right hcoef_τ hτc_nn
    have hexp : 4 * (|u| + (1 / 11 : ℝ) * (|σ| + 5 * |τc|))
        = 4 * |u| + 4 * (1 / 11 : ℝ) * |σ| + 4 * ((1 / 11 : ℝ) * 5) * |τc| := by
      ring
    linarith [hen3_bd_components, hu_bd', hσ_bd', hτ_bd', hexp.le, hexp.ge]
  -- |ψ| ≤ (6/11) h L · (4 W + |ψ|) + τabs.
  have hψ_step : |ψ| ≤ (6 / 11 : ℝ) * h * L * (4 * W + |ψ|) + τabs := by
    have := mul_le_mul_of_nonneg_left hen3_bd h611hL_nn
    linarith [hψ_bd]
  -- 1 - (6/11) h L ≥ 3/4.
  have h_one_minus_ge : (3 / 4 : ℝ) ≤ 1 - (6 / 11 : ℝ) * h * L := by
    linarith [hsmall]
  -- (1 - (6/11) h L)·|ψ| ≤ (24/11) h L W + τabs.
  have hψ_solved :
      (1 - (6 / 11 : ℝ) * h * L) * |ψ|
        ≤ (24 / 11 : ℝ) * h * L * W + τabs := by
    have hexp : (6 / 11 : ℝ) * h * L * (4 * W + |ψ|)
        = (24 / 11 : ℝ) * h * L * W + (6 / 11 : ℝ) * h * L * |ψ| := by ring
    have hexp2 : (1 - (6 / 11 : ℝ) * h * L) * |ψ|
        = |ψ| - (6 / 11 : ℝ) * h * L * |ψ| := by ring
    linarith [hψ_step, hexp.le, hexp.ge, hexp2.le, hexp2.ge]
  -- |ψ| ≤ 3 h L W + 2 τabs.
  have hψ_final : |ψ| ≤ 3 * h * L * W + 2 * τabs := by
    have hkey := mul_le_mul_of_nonneg_right h_one_minus_ge hψ_nn
    have hcomb := le_trans hkey hψ_solved
    have hmul := mul_le_mul_of_nonneg_left hcomb
      (by norm_num : (0 : ℝ) ≤ 4 / 3)
    have hLHS : (4 / 3 : ℝ) * ((3 / 4 : ℝ) * |ψ|) = |ψ| := by ring
    have hRHS : (4 / 3 : ℝ) * ((24 / 11 : ℝ) * h * L * W + τabs)
        = (32 / 11 : ℝ) * h * L * W + (4 / 3 : ℝ) * τabs := by ring
    have hhLW : 0 ≤ h * L * W := mul_nonneg hhL_nn hW_nn
    have hslack_W : (32 / 11 : ℝ) * h * L * W ≤ 3 * h * L * W := by
      have hdiff : 3 * h * L * W - (32 / 11 : ℝ) * h * L * W
          = (1 / 11 : ℝ) * (h * L * W) := by ring
      have hpos : 0 ≤ (1 / 11 : ℝ) * (h * L * W) :=
        mul_nonneg (by norm_num) hhLW
      linarith [hdiff.le, hdiff.ge, hpos]
    have hslack_τ : (4 / 3 : ℝ) * τabs ≤ 2 * τabs := by
      have hdiff : 2 * τabs - (4 / 3 : ℝ) * τabs
          = (2 / 3 : ℝ) * τabs := by ring
      have hpos : 0 ≤ (2 / 3 : ℝ) * τabs :=
        mul_nonneg (by norm_num) hτabs_nn
      linarith [hdiff.le, hdiff.ge, hpos]
    linarith [hmul, hLHS.le, hLHS.ge, hRHS.le, hRHS.ge, hslack_W, hslack_τ]
  -- |u + ψ| ≤ |u| + |ψ|.
  have hu'_bd : |u + ψ| ≤ |u| + |ψ| := abs_add_le u ψ
  -- |τc - (11/6) ψ| ≤ |τc| + (11/6) |ψ|.
  have hσ'_bd : |τc - (11 / 6 : ℝ) * ψ| ≤ |τc| + (11 / 6 : ℝ) * |ψ| := by
    calc |τc - (11 / 6 : ℝ) * ψ|
        ≤ |τc| + |(11 / 6 : ℝ) * ψ| := abs_sub _ _
      _ = |τc| + (11 / 6 : ℝ) * |ψ| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 11 / 6)]
  -- |-(2/11)σ + (7/11)τc - (11/6)ψ| ≤ (2/11)|σ| + (7/11)|τc| + (11/6)|ψ|.
  have hτc'_bd : |-(2 / 11 : ℝ) * σ + (7 / 11 : ℝ) * τc
        - (11 / 6 : ℝ) * ψ|
      ≤ (2 / 11 : ℝ) * |σ| + (7 / 11 : ℝ) * |τc| + (11 / 6 : ℝ) * |ψ| := by
    calc |-(2 / 11 : ℝ) * σ + (7 / 11 : ℝ) * τc - (11 / 6 : ℝ) * ψ|
        ≤ |-(2 / 11 : ℝ) * σ + (7 / 11 : ℝ) * τc|
            + |(11 / 6 : ℝ) * ψ| := abs_sub _ _
      _ ≤ |-(2 / 11 : ℝ) * σ| + |(7 / 11 : ℝ) * τc|
            + |(11 / 6 : ℝ) * ψ| := by
            linarith [abs_add_le (-(2 / 11 : ℝ) * σ) ((7 / 11 : ℝ) * τc)]
      _ = (2 / 11 : ℝ) * |σ| + (7 / 11 : ℝ) * |τc|
            + (11 / 6 : ℝ) * |ψ| := by
            have a1 : |-(2 / 11 : ℝ) * σ| = (2 / 11 : ℝ) * |σ| := by
              rw [show (-(2 / 11 : ℝ) * σ) = -((2 / 11 : ℝ) * σ) from by ring,
                  abs_neg, abs_mul,
                  abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 11)]
            have a2 : |(7 / 11 : ℝ) * τc| = (7 / 11 : ℝ) * |τc| := by
              rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 11)]
            have a3 : |(11 / 6 : ℝ) * ψ| = (11 / 6 : ℝ) * |ψ| := by
              rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 11 / 6)]
            linarith [a1.le, a1.ge, a2.le, a2.ge, a3.le, a3.ge]
  -- Combine: W' ≤ |u| + (10/121)|σ| + (46/121)|τc| + 2|ψ|.
  have hW'_bd : |u + ψ|
        + (1 / 11 : ℝ) * (|τc - (11 / 6 : ℝ) * ψ|
            + 5 * |-(2 / 11 : ℝ) * σ + (7 / 11 : ℝ) * τc
                  - (11 / 6 : ℝ) * ψ|)
      ≤ |u| + (10 / 121 : ℝ) * |σ| + (46 / 121 : ℝ) * |τc| + 2 * |ψ| := by
    have h1_11 : 0 ≤ (1 / 11 : ℝ) := by norm_num
    have h5_11 : 0 ≤ (5 / 11 : ℝ) := by norm_num
    have hbd1 := mul_le_mul_of_nonneg_left hσ'_bd h1_11
    have hbd2 := mul_le_mul_of_nonneg_left hτc'_bd h5_11
    have hsplit : (1 / 11 : ℝ) * (|τc - (11 / 6 : ℝ) * ψ|
              + 5 * |-(2 / 11 : ℝ) * σ + (7 / 11 : ℝ) * τc
                    - (11 / 6 : ℝ) * ψ|)
        = (1 / 11 : ℝ) * |τc - (11 / 6 : ℝ) * ψ|
          + (5 / 11 : ℝ) * |-(2 / 11 : ℝ) * σ + (7 / 11 : ℝ) * τc
                  - (11 / 6 : ℝ) * ψ| := by ring
    have htarget :
        |u| + (1 / 11 : ℝ) * (|τc| + (11 / 6 : ℝ) * |ψ|)
        + (5 / 11 : ℝ)
            * ((2 / 11 : ℝ) * |σ| + (7 / 11 : ℝ) * |τc|
                + (11 / 6 : ℝ) * |ψ|)
        + |ψ|
        = |u| + (10 / 121 : ℝ) * |σ| + (46 / 121 : ℝ) * |τc|
          + 2 * |ψ| := by ring
    linarith [hu'_bd, hbd1, hbd2, hsplit.le, hsplit.ge, htarget.le, htarget.ge]
  -- Goal: W' ≤ (1+h*(6L)) W + 4 τabs.
  have h2ψ_bd : 2 * |ψ| ≤ 6 * h * L * W + 4 * τabs := by
    have := mul_le_mul_of_nonneg_left hψ_final (by norm_num : (0 : ℝ) ≤ 2)
    have hexp : (2 : ℝ) * (3 * h * L * W + 2 * τabs)
        = 6 * h * L * W + 4 * τabs := by ring
    linarith [this, hexp.le, hexp.ge]
  have hsplit_W : (1 + h * (6 * L)) * W
      = (|u| + (1 / 11 : ℝ) * |σ| + (5 / 11 : ℝ) * |τc|)
        + h * (6 * L) * W := by
    rw [hW_def]; ring
  have hsig_slack : (10 / 121 : ℝ) * |σ| ≤ (1 / 11 : ℝ) * |σ| := by
    have hcoef : (10 / 121 : ℝ) ≤ (1 / 11 : ℝ) := by norm_num
    exact mul_le_mul_of_nonneg_right hcoef hσ_nn
  have htau_slack : (46 / 121 : ℝ) * |τc| ≤ (5 / 11 : ℝ) * |τc| := by
    have hcoef : (46 / 121 : ℝ) ≤ (5 / 11 : ℝ) := by norm_num
    exact mul_le_mul_of_nonneg_right hcoef hτc_nn
  have h6hLW_eq : 6 * h * L * W = h * (6 * L) * W := by ring
  linarith [hW'_bd, h2ψ_bd, hsig_slack, htau_slack, hsplit_W.le, hsplit_W.ge,
    h6hLW_eq.le, h6hLW_eq.ge]

/-- BDF3 one-step Lyapunov-window recurrence:
`W_{n+1} ≤ (1 + h·(6 L)) W_n + 4 |τ_n|` under `(6/11) h L ≤ 1/4`.
This is the analogue of `bdf2_one_step_error_pair_bound` in the BDF3 setting,
with the 2D contractive complementary block of the companion matrix
absorbed into the second-eigenvalue subspace. -/
theorem bdf3_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (6 / 11 : ℝ) * h * L ≤ 1 / 4)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsBDF3Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    bdf3LyapW (fun k => yseq k - y (t₀ + (k : ℝ) * h)) (n + 1)
      ≤ (1 + h * (6 * L))
          * bdf3LyapW (fun k => yseq k - y (t₀ + (k : ℝ) * h)) n
        + 4 * |bdf3.localTruncationError h (t₀ + (n : ℝ) * h) y| := by
  -- Define error sequence and Lyapunov coordinates at index n.
  set e : ℕ → ℝ := fun k => yseq k - y (t₀ + (k : ℝ) * h) with he_def
  set u : ℝ := bdf3LyapU e n with hu_def
  set σ : ℝ := bdf3LyapSigma e n with hσ_def
  set τc : ℝ := bdf3LyapTau e n with hτc_def
  set τabs : ℝ := |bdf3.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  -- Defect ψ in terms of yseq, y (matching `bdf3_one_step_lipschitz`).
  set ψ : ℝ := (yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h))
        - (18 / 11 : ℝ) * (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))
        + (9 / 11 : ℝ) * (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
        - (2 / 11 : ℝ) * (yseq n - y (t₀ + (n : ℝ) * h)) with hψ_def
  set en3 : ℝ := yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h) with hen3_def
  -- Lipschitz defect bound: |ψ| ≤ (6/11) h L · |en3| + τabs.
  have hlip := bdf3_one_step_lipschitz (h := h) (L := L) hh hf t₀ hy y hyf n
  have hψ_bd : |ψ| ≤ (6 / 11 : ℝ) * h * L * |en3| + τabs := hlip
  -- en3 = (11/6) u − (14/121) σ + (27/121) τc + ψ.
  have hen3_uv : en3 = (11 / 6 : ℝ) * u - (14 / 121 : ℝ) * σ
        + (27 / 121 : ℝ) * τc + ψ := by
    show en3
        = (11 / 6 : ℝ) * bdf3LyapU e n
          - (14 / 121 : ℝ) * bdf3LyapSigma e n
          + (27 / 121 : ℝ) * bdf3LyapTau e n + ψ
    unfold bdf3LyapU bdf3LyapSigma bdf3LyapTau
    have hcast1 : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
    have hcast2 : (((n + 2 : ℕ) : ℝ)) = (n : ℝ) + 2 := by push_cast; ring
    show (yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h))
        = (11 / 6 : ℝ) * ((2 / 11 : ℝ) * (yseq n - y (t₀ + (n : ℝ) * h))
            - (7 / 11 : ℝ) * (yseq (n + 1) - y (t₀ + ((n + 1 : ℕ) : ℝ) * h))
            + (yseq (n + 2) - y (t₀ + ((n + 2 : ℕ) : ℝ) * h)))
          - (14 / 121 : ℝ) * ((1 / 6 : ℝ)
              * (4 * (yseq n - y (t₀ + (n : ℝ) * h))
                  + 7 * (yseq (n + 1) - y (t₀ + ((n + 1 : ℕ) : ℝ) * h))
                  - 11 * (yseq (n + 2) - y (t₀ + ((n + 2 : ℕ) : ℝ) * h))))
          + (27 / 121 : ℝ) * ((1 / 6 : ℝ)
              * (-2 * (yseq n - y (t₀ + (n : ℝ) * h))
                  + 13 * (yseq (n + 1) - y (t₀ + ((n + 1 : ℕ) : ℝ) * h))
                  - 11 * (yseq (n + 2) - y (t₀ + ((n + 2 : ℕ) : ℝ) * h))))
          + ((yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h))
              - (18 / 11 : ℝ) * (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))
              + (9 / 11 : ℝ) * (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
              - (2 / 11 : ℝ) * (yseq n - y (t₀ + (n : ℝ) * h)))
    rw [hcast1, hcast2]
    ring
  have hτabs_nn : 0 ≤ τabs := abs_nonneg _
  -- Apply the pure-algebra helper.
  have halg := bdf3_one_step_lyapunov_alg hh hL hsmall u σ τc ψ en3 τabs
                hτabs_nn hen3_uv hψ_bd
  -- Bridge bdf3LyapU/Σ/Τ at index n+1 to (u + ψ), (τc − (11/6) ψ), …
  have hu' : bdf3LyapU e (n + 1) = u + ψ := by
    have hsucc := bdf3LyapU_succ_eq (h := h) (f := f) t₀ hy y hyf n
    rw [hsucc]
  have hσ' : bdf3LyapSigma e (n + 1) = τc - (11 / 6 : ℝ) * ψ := by
    have hsucc := bdf3LyapSigma_succ_eq h yseq t₀ y n
    rw [hsucc]
  have hτc' : bdf3LyapTau e (n + 1)
      = -(2 / 11 : ℝ) * σ + (7 / 11 : ℝ) * τc - (11 / 6 : ℝ) * ψ := by
    have hsucc := bdf3LyapTau_succ_eq h yseq t₀ y n
    rw [hsucc]
  -- Rewrite the goal in u, σ, τc, ψ, τabs form.
  show |bdf3LyapU e (n + 1)|
        + (1 / 11 : ℝ)
            * (|bdf3LyapSigma e (n + 1)| + 5 * |bdf3LyapTau e (n + 1)|)
      ≤ (1 + h * (6 * L)) * (|u| + (1 / 11 : ℝ) * (|σ| + 5 * |τc|))
        + 4 * τabs
  rw [hu', hσ', hτc']
  exact halg

/-- Initial Lyapunov-sum bound: if the first three errors are bounded by `ε₀`,
then the BDF3 Lyapunov sum at index 0 is at most `5 ε₀`. -/
lemma bdf3LyapW_initial_bound
    {e : ℕ → ℝ} {ε₀ : ℝ} (h0 : |e 0| ≤ ε₀) (h1 : |e 1| ≤ ε₀)
    (h2 : |e 2| ≤ ε₀) :
    bdf3LyapW e 0 ≤ 5 * ε₀ := by
  unfold bdf3LyapW bdf3LyapU bdf3LyapSigma bdf3LyapTau
  -- Bound |u| = |(2/11) e0 − (7/11) e1 + e2| ≤ 20/11 ε₀.
  have hu_bd : |(2 / 11 : ℝ) * e 0 - (7 / 11 : ℝ) * e 1 + e 2|
      ≤ (20/11 : ℝ) * ε₀ := by
    have hAB : |(2 / 11 : ℝ) * e 0 - (7 / 11 : ℝ) * e 1|
        ≤ (2/11 : ℝ) * ε₀ + (7/11 : ℝ) * ε₀ := by
      calc |(2 / 11 : ℝ) * e 0 - (7 / 11 : ℝ) * e 1|
          ≤ |(2 / 11 : ℝ) * e 0| + |(7 / 11 : ℝ) * e 1| := abs_sub _ _
        _ = (2/11 : ℝ) * |e 0| + (7/11 : ℝ) * |e 1| := by
            rw [abs_mul, abs_mul,
                abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2/11),
                abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 7/11)]
        _ ≤ (2/11 : ℝ) * ε₀ + (7/11 : ℝ) * ε₀ := by linarith
    have hAdd := abs_add_le ((2 / 11 : ℝ) * e 0 - (7 / 11 : ℝ) * e 1) (e 2)
    linarith
  -- Bound |σ_inner| ≤ 22 ε₀ (then ×1/6).
  have hσ_bd : |(1 / 6 : ℝ) * (4 * e 0 + 7 * e 1 - 11 * e 2)|
        ≤ (22/6 : ℝ) * ε₀ := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/6)]
    have he4 : |4 * e 0| ≤ 4 * ε₀ := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]; linarith
    have he7 : |7 * e 1| ≤ 7 * ε₀ := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 7)]; linarith
    have he11 : |11 * e 2| ≤ 11 * ε₀ := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 11)]; linarith
    have h_pre : |4 * e 0 + 7 * e 1| ≤ |4 * e 0| + |7 * e 1| :=
      abs_add_le _ _
    have h_step : |4 * e 0 + 7 * e 1 + -(11 * e 2)|
        ≤ |4 * e 0 + 7 * e 1| + |-(11 * e 2)| :=
      abs_add_le _ _
    have hneg : |-(11 * e 2)| = |11 * e 2| := abs_neg _
    have hsub : 4 * e 0 + 7 * e 1 - 11 * e 2
        = (4 * e 0 + 7 * e 1) + -(11 * e 2) := by ring
    have hgoal : |4 * e 0 + 7 * e 1 - 11 * e 2| ≤ 22 * ε₀ := by
      rw [hsub]
      calc |(4 * e 0 + 7 * e 1) + -(11 * e 2)|
          ≤ |4 * e 0 + 7 * e 1| + |-(11 * e 2)| := h_step
        _ = |4 * e 0 + 7 * e 1| + |11 * e 2| := by rw [hneg]
        _ ≤ |4 * e 0| + |7 * e 1| + |11 * e 2| := by linarith
        _ ≤ 4 * ε₀ + 7 * ε₀ + 11 * ε₀ := by linarith
        _ = 22 * ε₀ := by ring
    linarith
  -- Bound |τ_inner| ≤ 26 ε₀ (then ×1/6).
  have hτ_bd : |(1 / 6 : ℝ) * (-2 * e 0 + 13 * e 1 - 11 * e 2)|
        ≤ (26/6 : ℝ) * ε₀ := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/6)]
    have he2' : |-2 * e 0| ≤ 2 * ε₀ := by
      rw [show (-2 * e 0 : ℝ) = -(2 * e 0) from by ring, abs_neg, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith
    have he13 : |13 * e 1| ≤ 13 * ε₀ := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 13)]; linarith
    have he11 : |11 * e 2| ≤ 11 * ε₀ := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 11)]; linarith
    have h_pre : |-2 * e 0 + 13 * e 1| ≤ |-2 * e 0| + |13 * e 1| :=
      abs_add_le _ _
    have h_step : |(-2 * e 0 + 13 * e 1) + -(11 * e 2)|
        ≤ |-2 * e 0 + 13 * e 1| + |-(11 * e 2)| :=
      abs_add_le _ _
    have hneg : |-(11 * e 2)| = |11 * e 2| := abs_neg _
    have hsub : -2 * e 0 + 13 * e 1 - 11 * e 2
        = (-2 * e 0 + 13 * e 1) + -(11 * e 2) := by ring
    have hgoal : |-2 * e 0 + 13 * e 1 - 11 * e 2| ≤ 26 * ε₀ := by
      rw [hsub]
      calc |(-2 * e 0 + 13 * e 1) + -(11 * e 2)|
          ≤ |-2 * e 0 + 13 * e 1| + |-(11 * e 2)| := h_step
        _ = |-2 * e 0 + 13 * e 1| + |11 * e 2| := by rw [hneg]
        _ ≤ |-2 * e 0| + |13 * e 1| + |11 * e 2| := by linarith
        _ ≤ 2 * ε₀ + 13 * ε₀ + 11 * ε₀ := by linarith
        _ = 26 * ε₀ := by ring
    linarith
  have hε_aux : 0 ≤ ε₀ := by
    have : 0 ≤ |e 0| := abs_nonneg _
    linarith
  nlinarith [hu_bd, hσ_bd, hτ_bd, hε_aux]

/-- Bound for `|e_{n+2}|` in terms of `bdf3LyapW e n`. -/
lemma bdf3_eIdx2_le_W (e : ℕ → ℝ) (n : ℕ) :
    |e (n + 2)| ≤ 2 * bdf3LyapW e n := by
  -- e (n + 2) = (11/6) u + (-2/11) σ + (7/11) τc.
  -- Verify: (11/6)·((2/11) e 0 - (7/11) e 1 + e 2)
  --       + (-2/11)·((1/6)(4 e 0 + 7 e 1 - 11 e 2))
  --       + (7/11)·((1/6)(-2 e 0 + 13 e 1 - 11 e 2))
  -- Coeff of e 0: 11/6 · 2/11 + (-2/11) · 4/6 + (7/11) · (-2/6)
  --             = 2/6 - 8/66 - 14/66 = 22/66 - 22/66 = 0
  -- Coeff of e 1: 11/6 · (-7/11) + (-2/11) · 7/6 + (7/11) · 13/6
  --             = -7/6 - 14/66 + 91/66 = -77/66 + 77/66 = 0
  -- Coeff of e 2: 11/6 + (-2/11)(-11/6) + (7/11)(-11/6)
  --             = 11/6 + 2/6 - 7/6 = 6/6 = 1 ✓
  unfold bdf3LyapW bdf3LyapU bdf3LyapSigma bdf3LyapTau
  set Uval : ℝ := (2 / 11 : ℝ) * e n - (7 / 11 : ℝ) * e (n + 1) + e (n + 2)
    with hUval_def
  set Sval : ℝ := (1 / 6 : ℝ) * (4 * e n + 7 * e (n + 1) - 11 * e (n + 2))
    with hSval_def
  set Tval : ℝ := (1 / 6 : ℝ) * (-2 * e n + 13 * e (n + 1) - 11 * e (n + 2))
    with hTval_def
  have hid : e (n + 2)
      = (11 / 6 : ℝ) * Uval + (-2 / 11 : ℝ) * Sval + (7 / 11 : ℝ) * Tval := by
    show e (n + 2)
        = (11 / 6 : ℝ) * ((2 / 11 : ℝ) * e n - (7 / 11 : ℝ) * e (n + 1) + e (n + 2))
        + (-2 / 11 : ℝ) * ((1 / 6 : ℝ) * (4 * e n + 7 * e (n + 1) - 11 * e (n + 2)))
        + (7 / 11 : ℝ) * ((1 / 6 : ℝ) * (-2 * e n + 13 * e (n + 1) - 11 * e (n + 2)))
    ring
  rw [hid]
  have habs :
      |(11 / 6 : ℝ) * Uval + (-2 / 11 : ℝ) * Sval + (7 / 11 : ℝ) * Tval|
      ≤ (11/6 : ℝ) * |Uval| + (2/11 : ℝ) * |Sval| + (7/11 : ℝ) * |Tval| := by
    have h1 := abs_add_le
      ((11 / 6 : ℝ) * Uval + (-2 / 11 : ℝ) * Sval) ((7 / 11 : ℝ) * Tval)
    have h2 := abs_add_le ((11 / 6 : ℝ) * Uval) ((-2 / 11 : ℝ) * Sval)
    have e1 : |(11 / 6 : ℝ) * Uval| = (11/6 : ℝ) * |Uval| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 11/6)]
    have e2 : |(-2 / 11 : ℝ) * Sval| = (2/11 : ℝ) * |Sval| := by
      rw [abs_mul, show |(-2/11 : ℝ)| = (2/11 : ℝ) from by
        rw [show (-2/11 : ℝ) = -(2/11 : ℝ) from by ring, abs_neg,
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2/11)]]
    have e3 : |(7 / 11 : ℝ) * Tval| = (7/11 : ℝ) * |Tval| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 7/11)]
    linarith
  have hU_nn : 0 ≤ |Uval| := abs_nonneg _
  have hS_nn : 0 ≤ |Sval| := abs_nonneg _
  have hT_nn : 0 ≤ |Tval| := abs_nonneg _
  nlinarith [habs, hU_nn, hS_nn, hT_nn]

/-- Headline BDF3 global error bound.  Given a supplied BDF3 trajectory and
starting errors bounded by `ε₀`, the scalar global error is `O(ε₀ + h³)` on
a finite horizon. -/
theorem bdf3_global_error_bound
    {y : ℝ → ℝ} (hy_smooth : ContDiff ℝ 4 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      (6 / 11 : ℝ) * h * L ≤ 1 / 4 →
      ∀ {yseq : ℕ → ℝ} {ε₀ : ℝ},
      IsBDF3Trajectory h f t₀ yseq →
      0 ≤ ε₀ →
      |yseq 0 - y t₀| ≤ ε₀ →
      |yseq 1 - y (t₀ + h)| ≤ ε₀ →
      |yseq 2 - y (t₀ + 2 * h)| ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 2) * h ≤ T →
      |yseq N - y (t₀ + (N : ℝ) * h)|
        ≤ 10 * Real.exp ((6 * L) * T) * ε₀ + K * h ^ 3 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    bdf3_local_residual_bound hy_smooth t₀ T hT
  refine ⟨8 * T * Real.exp ((6 * L) * T) * C, δ, ?_, hδ_pos, ?_⟩
  · have h8nn : (0 : ℝ) ≤ 8 := by norm_num
    have hT_nn : (0 : ℝ) ≤ T := hT.le
    have hexp_nn : (0 : ℝ) ≤ Real.exp ((6 * L) * T) := Real.exp_nonneg _
    have h1 : (0 : ℝ) ≤ 8 * T := mul_nonneg h8nn hT_nn
    have h2 : (0 : ℝ) ≤ 8 * T * Real.exp ((6 * L) * T) := mul_nonneg h1 hexp_nn
    exact mul_nonneg h2 hC_nn
  intro h hh hδ_le hsmall yseq ε₀ hy_traj hε₀ he0_bd he1_bd he2_bd N hNh
  -- Error sequence and Lyapunov sum.
  set e : ℕ → ℝ := fun k => yseq k - y (t₀ + (k : ℝ) * h) with he_def
  set W : ℕ → ℝ := fun k => bdf3LyapW e k with hW_def
  have hW_nn : ∀ k, 0 ≤ W k := fun k => bdf3LyapW_nonneg e k
  have h6L_nn : (0 : ℝ) ≤ 6 * L := by linarith
  -- Initial bound: W 0 ≤ 5 ε₀.
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
  have hW0_le : W 0 ≤ 5 * ε₀ := bdf3LyapW_initial_bound he0' he1' he2'
  -- Step bound: when (n + 3) h ≤ T, W (n+1) ≤ (1 + h*(6L)) W n + (4*C) h^(3+1).
  have hstep_general : ∀ n : ℕ, ((n : ℝ) + 3) * h ≤ T →
      W (n + 1) ≤ (1 + h * (6 * L)) * W n + (4 * C) * h ^ (3 + 1) := by
    intro n hnh_le
    have honestep := bdf3_one_step_error_bound
      (h := h) (L := L) hh.le hL hsmall hf t₀ hy_traj y hyf n
    have hres := hresidual hh hδ_le n hnh_le
    have h4nn : (0 : ℝ) ≤ 4 := by norm_num
    have h4τ : 4 * |bdf3.localTruncationError h
        (t₀ + (n : ℝ) * h) y| ≤ (4 * C) * h ^ (3 + 1) := by
      have := mul_le_mul_of_nonneg_left hres h4nn
      have hpow : (h : ℝ) ^ (3 + 1) = h ^ 4 := by norm_num
      rw [hpow]; linarith
    show bdf3LyapW e (n + 1)
        ≤ (1 + h * (6 * L)) * bdf3LyapW e n + (4 * C) * h ^ (3 + 1)
    linarith [honestep, h4τ]
  -- Case-split on N = 0, 1, 2 (ε₀ direct) vs N ≥ 3 (Grönwall + |e_{n+2}| ≤ 2 W).
  have hexp_ge_one : (1 : ℝ) ≤ Real.exp ((6 * L) * T) :=
    Real.one_le_exp_iff.mpr (mul_nonneg h6L_nn hT.le)
  have hexp_nn : 0 ≤ Real.exp ((6 * L) * T) := Real.exp_nonneg _
  have hKnn : 0 ≤ 8 * T * Real.exp ((6 * L) * T) * C := by
    have h8 : (0 : ℝ) ≤ 8 := by norm_num
    have h1 : (0 : ℝ) ≤ 8 * T := mul_nonneg h8 hT.le
    have h2 : (0 : ℝ) ≤ 8 * T * Real.exp ((6 * L) * T) := mul_nonneg h1 hexp_nn
    exact mul_nonneg h2 hC_nn
  have hh3_nn : 0 ≤ h ^ 3 := by positivity
  match N, hNh with
  | 0, _ =>
    show |yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)|
        ≤ 10 * Real.exp ((6 * L) * T) * ε₀
            + 8 * T * Real.exp ((6 * L) * T) * C * h ^ 3
    have hbd : |yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)| ≤ ε₀ := he0' -- since e 0 = yseq 0 - y(t₀+0·h)
    nlinarith [hbd, hexp_ge_one, hKnn, hh3_nn, hε₀]
  | 1, _ =>
    show |yseq 1 - y (t₀ + ((1 : ℕ) : ℝ) * h)|
        ≤ 10 * Real.exp ((6 * L) * T) * ε₀
            + 8 * T * Real.exp ((6 * L) * T) * C * h ^ 3
    have hbd : |yseq 1 - y (t₀ + ((1 : ℕ) : ℝ) * h)| ≤ ε₀ := he1'
    nlinarith [hbd, hexp_ge_one, hKnn, hh3_nn, hε₀]
  | 2, _ =>
    show |yseq 2 - y (t₀ + ((2 : ℕ) : ℝ) * h)|
        ≤ 10 * Real.exp ((6 * L) * T) * ε₀
            + 8 * T * Real.exp ((6 * L) * T) * C * h ^ 3
    have hbd : |yseq 2 - y (t₀ + ((2 : ℕ) : ℝ) * h)| ≤ ε₀ := he2'
    nlinarith [hbd, hexp_ge_one, hKnn, hh3_nn, hε₀]
  | (N'' + 3), hNh' =>
    -- Reduction: write N = N''+3 = (N''+1)+2; use |e_{(N''+1)+2}| ≤ 2 W_{N''+1}.
    -- Apply Grönwall up to index N''+1; need (N''+1) h ≤ T and step
    -- bound for n < N''+1, i.e., n ≤ N''.
    have hcastN : ((N'' + 3 : ℕ) : ℝ) = (N'' : ℝ) + 3 := by push_cast; ring
    have hN_le : ((N'' : ℝ) + 3) * h ≤ T := by
      have : ((N'' + 3 : ℕ) : ℝ) + 2 = (N'' : ℝ) + 5 := by push_cast; ring
      have hcastNh : (((N'' + 3 : ℕ) : ℝ) + 2) * h ≤ T := hNh'
      rw [this] at hcastNh
      have hle : (N'' : ℝ) + 3 ≤ (N'' : ℝ) + 5 := by linarith
      have := mul_le_mul_of_nonneg_right hle hh.le
      linarith
    -- Step bound for the Grönwall driver up to N''+1.
    have hgronwall_step : ∀ n, n < N'' + 1 →
        W (n + 1) ≤ (1 + h * (6 * L)) * W n + (4 * C) * h ^ (3 + 1) := by
      intro n hn_lt
      apply hstep_general
      have hn1_le_N''1 : (n : ℝ) + 1 ≤ ((N'' : ℝ) + 1) := by
        have : (n : ℝ) ≤ (N'' : ℝ) := by
          exact_mod_cast Nat.lt_succ_iff.mp hn_lt
        linarith
      -- (n+3) h ≤ (N''+3) h ≤ T.
      have hle : (n : ℝ) + 3 ≤ (N'' : ℝ) + 3 := by linarith
      have hmul : ((n : ℝ) + 3) * h ≤ ((N'' : ℝ) + 3) * h :=
        mul_le_mul_of_nonneg_right hle hh.le
      linarith
    -- Need (N''+1) h ≤ T.
    have hN1h_le_T : ((N'' + 1 : ℕ) : ℝ) * h ≤ T := by
      have hcast : ((N'' + 1 : ℕ) : ℝ) = (N'' : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have hle : (N'' : ℝ) + 1 ≤ (N'' : ℝ) + 3 := by linarith
      have := mul_le_mul_of_nonneg_right hle hh.le
      linarith
    have hgronwall :=
      lmm_error_bound_from_local_truncation
        (h := h) (L := 6 * L) (C := 4 * C) (T := T) (p := 3) (e := W)
        (N := N'' + 1)
        hh.le h6L_nn (by linarith) (hW_nn 0) hgronwall_step
        (N'' + 1) le_rfl hN1h_le_T
    -- W_{N''+1} ≤ exp((6L)T) W_0 + T exp((6L)T) (4C) h^3.
    -- |e_{(N''+1)+2}| ≤ 2 W_{N''+1}.
    have hek2 := bdf3_eIdx2_le_W e (N'' + 1)
    -- Index alignment: yseq (N''+3) - y(t₀ + (N''+3) h) = e (N''+1+2) = e (N''+3).
    have hidx : ((N'' + 1 + 2 : ℕ) : ℝ) = (N'' : ℝ) + 3 := by push_cast; ring
    have hidx2 : (N'' + 1 + 2 : ℕ) = (N'' + 3 : ℕ) := by ring
    have h_chain :
        Real.exp ((6 * L) * T) * W 0
          ≤ Real.exp ((6 * L) * T) * (5 * ε₀) :=
      mul_le_mul_of_nonneg_left hW0_le hexp_nn
    -- Final assembly.
    show |yseq (N'' + 3) - y (t₀ + ((N'' + 3 : ℕ) : ℝ) * h)|
        ≤ 10 * Real.exp ((6 * L) * T) * ε₀
            + 8 * T * Real.exp ((6 * L) * T) * C * h ^ 3
    have hcastN3 : ((N'' + 3 : ℕ) : ℝ) = (N'' : ℝ) + 3 := by push_cast; ring
    rw [hcastN3]
    have he_eq : e (N'' + 1 + 2)
        = yseq (N'' + 3) - y (t₀ + ((N'' : ℝ) + 3) * h) := by
      show yseq (N'' + 1 + 2) - y (t₀ + ((N'' + 1 + 2 : ℕ) : ℝ) * h)
          = yseq (N'' + 3) - y (t₀ + ((N'' : ℝ) + 3) * h)
      have h_idx_eq : (N'' + 1 + 2 : ℕ) = N'' + 3 := by ring
      rw [h_idx_eq, hidx]
    have hek2' : |yseq (N'' + 3) - y (t₀ + ((N'' : ℝ) + 3) * h)|
        ≤ 2 * W (N'' + 1) := by
      have := hek2
      rw [he_eq] at this
      exact this
    linarith [hek2', hgronwall, h_chain]

end LMM
