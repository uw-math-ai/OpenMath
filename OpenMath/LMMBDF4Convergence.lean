import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMAB4Convergence

/-! ## BDF4 Quantitative Convergence Chain (Iserles §4.5)

Truncation chain for the scalar 4-step backward differentiation formula.
This module lands the supplied-trajectory predicate, the textbook local
truncation residual unfolding, the Lipschitz defect estimate, the
pointwise fifth-order Taylor residual bound, and the uniform local
residual bound on a finite horizon.

The BDF4 Lyapunov coordinates and global error theorem are deferred to a
follow-up cycle: the cubic factor `25ζ³ − 23ζ² + 13ζ − 3` of `ρ(ζ)` after
removing the unit root is irreducible over ℚ, so the BDF3-style rational
eigenvector decomposition has no transplant, and the abs-value companion
matrix has Perron radius `≈ 2.58`, ruling out a direct weighted-ℓ¹ kernel
with growth `1 + h·G·L`. See `.prover-state/issues/bdf4_lyapunov_gap.md`.
-/

namespace LMM

/-- BDF4 trajectory predicate:
`y_{n+4} = (48/25) y_{n+3} − (36/25) y_{n+2} + (16/25) y_{n+1} − (3/25) y_n
  + (12/25) h · f(t_{n+4}, y_{n+4})`.
The new value appears inside `f`, so existence of such a trajectory is a
separate fixed-point problem. -/
structure IsBDF4Trajectory (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ : ℝ)
    (y : ℕ → ℝ) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 4)
      = (48 / 25 : ℝ) * y (n + 3) - (36 / 25 : ℝ) * y (n + 2)
        + (16 / 25 : ℝ) * y (n + 1) - (3 / 25 : ℝ) * y n
        + (12 / 25 : ℝ) * h * f (t₀ + ((n : ℝ) + 4) * h) (y (n + 4))

/-- BDF4 local truncation operator reduces to the textbook 4-step residual
`y(t+4h) − (48/25)y(t+3h) + (36/25)y(t+2h) − (16/25)y(t+h) + (3/25)y(t)
  − (12/25)h y'(t+4h)`. -/
theorem bdf4_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    bdf4.localTruncationError h t y
      = y (t + 4 * h) - (48 / 25 : ℝ) * y (t + 3 * h)
        + (36 / 25 : ℝ) * y (t + 2 * h) - (16 / 25 : ℝ) * y (t + h)
        + (3 / 25 : ℝ) * y t
        - (12 / 25 : ℝ) * h * deriv y (t + 4 * h) := by
  unfold localTruncationError truncationOp
  simp [bdf4, Fin.sum_univ_five, iteratedDeriv_one, iteratedDeriv_zero]
  ring

/-- Forcing decomposition of the BDF4 error recurrence: the homogeneous
defect `e_{n+4} − (48/25)e_{n+3} + (36/25)e_{n+2} − (16/25)e_{n+1} + (3/25)e_n`
is bounded by `(12/25) h L · |e_{n+4}| + |τ_n|`. -/
theorem bdf4_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsBDF4Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    |(yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h))
      - (48 / 25 : ℝ) * (yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h))
      + (36 / 25 : ℝ) * (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))
      - (16 / 25 : ℝ) * (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
      + (3 / 25 : ℝ) * (yseq n - y (t₀ + (n : ℝ) * h))|
    ≤ (12 / 25 : ℝ) * h * L
        * |yseq (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|
      + |bdf4.localTruncationError h (t₀ + (n : ℝ) * h) y| := by
  set yn : ℝ := yseq n with hyn_def
  set yn1 : ℝ := yseq (n + 1) with hyn1_def
  set yn2 : ℝ := yseq (n + 2) with hyn2_def
  set yn3 : ℝ := yseq (n + 3) with hyn3_def
  set yn4 : ℝ := yseq (n + 4) with hyn4_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set tn3 : ℝ := t₀ + ((n : ℝ) + 3) * h with htn3_def
  set tn4 : ℝ := t₀ + ((n : ℝ) + 4) * h with htn4_def
  set zn : ℝ := y tn with hzn_def
  set zn1 : ℝ := y tn1 with hzn1_def
  set zn2 : ℝ := y tn2 with hzn2_def
  set zn3 : ℝ := y tn3 with hzn3_def
  set zn4 : ℝ := y tn4 with hzn4_def
  set τ : ℝ := bdf4.localTruncationError h tn y with hτ_def
  have hstep : yn4
      = (48 / 25 : ℝ) * yn3 - (36 / 25 : ℝ) * yn2
        + (16 / 25 : ℝ) * yn1 - (3 / 25 : ℝ) * yn
        + (12 / 25 : ℝ) * h * f tn4 yn4 := by
    simpa [hyn4_def, hyn3_def, hyn2_def, hyn1_def, hyn_def, htn4_def]
      using hy.recurrence n
  have htn_h : tn + h = tn1 := by simp [htn_def, htn1_def]; ring
  have htn_2h : tn + 2 * h = tn2 := by simp [htn_def, htn2_def]; ring
  have htn_3h : tn + 3 * h = tn3 := by simp [htn_def, htn3_def]; ring
  have htn_4h : tn + 4 * h = tn4 := by simp [htn_def, htn4_def]; ring
  have hτ_eq : τ = zn4 - (48 / 25 : ℝ) * zn3 + (36 / 25 : ℝ) * zn2
        - (16 / 25 : ℝ) * zn1 + (3 / 25 : ℝ) * zn
        - (12 / 25 : ℝ) * h * f tn4 zn4 := by
    show bdf4.localTruncationError h tn y = _
    rw [bdf4_localTruncationError_eq, htn_h, htn_2h, htn_3h, htn_4h, hyf tn4]
  have halg : (yn4 - zn4) - (48 / 25 : ℝ) * (yn3 - zn3)
        + (36 / 25 : ℝ) * (yn2 - zn2) - (16 / 25 : ℝ) * (yn1 - zn1)
        + (3 / 25 : ℝ) * (yn - zn)
      = (12 / 25 : ℝ) * h * (f tn4 yn4 - f tn4 zn4) - τ := by
    conv_lhs => rw [hstep]
    rw [hτ_eq]; ring
  have hLip : |f tn4 yn4 - f tn4 zn4| ≤ L * |yn4 - zn4| := hf tn4 yn4 zn4
  have h1225_nn : (0 : ℝ) ≤ (12 / 25 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h1225_abs :
      |(12 / 25 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)|
        ≤ (12 / 25 : ℝ) * h * L * |yn4 - zn4| := by
    rw [abs_mul, abs_of_nonneg h1225_nn]
    calc (12 / 25 : ℝ) * h * |f tn4 yn4 - f tn4 zn4|
        ≤ (12 / 25 : ℝ) * h * (L * |yn4 - zn4|) :=
          mul_le_mul_of_nonneg_left hLip h1225_nn
      _ = (12 / 25 : ℝ) * h * L * |yn4 - zn4| := by ring
  have htri :
      |(12 / 25 : ℝ) * h * (f tn4 yn4 - f tn4 zn4) - τ|
      ≤ |(12 / 25 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)| + |τ| := abs_sub _ _
  calc |(yn4 - zn4) - (48 / 25 : ℝ) * (yn3 - zn3)
            + (36 / 25 : ℝ) * (yn2 - zn2) - (16 / 25 : ℝ) * (yn1 - zn1)
            + (3 / 25 : ℝ) * (yn - zn)|
      = |(12 / 25 : ℝ) * h * (f tn4 yn4 - f tn4 zn4) - τ| := by rw [halg]
    _ ≤ |(12 / 25 : ℝ) * h * (f tn4 yn4 - f tn4 zn4)| + |τ| := htri
    _ ≤ (12 / 25 : ℝ) * h * L * |yn4 - zn4| + |τ| := by linarith [h1225_abs]

/-- Pure-algebra core of the BDF4 pointwise residual bound. Given the
five Taylor-remainder magnitude bounds, the BDF4 linear combination
`A − (48/25) B + (36/25) C − (16/25) D − (12h/25) E` is bounded by
`18 · M · h⁵`. The exact coefficient is `6724/375 ≈ 17.93`, slackened
to `18` for `linarith` cleanliness. Extracted as a private lemma to
keep the kernel out of the heavy ambient Taylor context. -/
private lemma bdf4_pointwise_residual_alg
    {h M : ℝ} (hh : 0 ≤ h) (hMnn : 0 ≤ M)
    (A B C D E : ℝ)
    (hA_bd : |A| ≤ M / 120 * (4 * h) ^ 5)
    (hB_bd : |B| ≤ M / 120 * (3 * h) ^ 5)
    (hC_bd : |C| ≤ M / 120 * (2 * h) ^ 5)
    (hD_bd : |D| ≤ M / 120 * h ^ 5)
    (hE_bd : |E| ≤ M / 24 * (4 * h) ^ 4) :
    |A - (48 / 25 : ℝ) * B + (36 / 25 : ℝ) * C
        - (16 / 25 : ℝ) * D - ((12 / 25 : ℝ) * h) * E|
      ≤ 18 * M * h ^ 5 := by
  have h1225h_nn : 0 ≤ (12 / 25 : ℝ) * h := mul_nonneg (by norm_num) hh
  have habs48 : |(48 / 25 : ℝ) * B| = (48 / 25 : ℝ) * |B| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 48 / 25)]
  have habs36 : |(36 / 25 : ℝ) * C| = (36 / 25 : ℝ) * |C| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 36 / 25)]
  have habs16 : |(16 / 25 : ℝ) * D| = (16 / 25 : ℝ) * |D| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 16 / 25)]
  have habs1225h : |((12 / 25 : ℝ) * h) * E|
      = (12 / 25 : ℝ) * h * |E| := by
    rw [abs_mul, abs_of_nonneg h1225h_nn]
  have htri :
      |A - (48 / 25 : ℝ) * B + (36 / 25 : ℝ) * C
          - (16 / 25 : ℝ) * D - ((12 / 25 : ℝ) * h) * E|
      ≤ |A| + (48 / 25 : ℝ) * |B| + (36 / 25 : ℝ) * |C|
          + (16 / 25 : ℝ) * |D| + (12 / 25 : ℝ) * h * |E| := by
    have h1 : |A - (48 / 25 : ℝ) * B + (36 / 25 : ℝ) * C
                  - (16 / 25 : ℝ) * D - ((12 / 25 : ℝ) * h) * E|
        ≤ |A - (48 / 25 : ℝ) * B + (36 / 25 : ℝ) * C
              - (16 / 25 : ℝ) * D|
            + |((12 / 25 : ℝ) * h) * E| := abs_sub _ _
    have h2 : |A - (48 / 25 : ℝ) * B + (36 / 25 : ℝ) * C
                  - (16 / 25 : ℝ) * D|
        ≤ |A - (48 / 25 : ℝ) * B + (36 / 25 : ℝ) * C|
            + |(16 / 25 : ℝ) * D| := abs_sub _ _
    have h3 : |A - (48 / 25 : ℝ) * B + (36 / 25 : ℝ) * C|
        ≤ |A - (48 / 25 : ℝ) * B| + |(36 / 25 : ℝ) * C| :=
      abs_add_le _ _
    have h4 : |A - (48 / 25 : ℝ) * B|
        ≤ |A| + |(48 / 25 : ℝ) * B| := abs_sub _ _
    linarith [habs48.le, habs48.ge, habs36.le, habs36.ge,
      habs16.le, habs16.ge, habs1225h.le, habs1225h.ge]
  have h48B_bd : (48 / 25 : ℝ) * |B|
      ≤ (48 / 25 : ℝ) * (M / 120 * (3 * h) ^ 5) :=
    mul_le_mul_of_nonneg_left hB_bd (by norm_num)
  have h36C_bd : (36 / 25 : ℝ) * |C|
      ≤ (36 / 25 : ℝ) * (M / 120 * (2 * h) ^ 5) :=
    mul_le_mul_of_nonneg_left hC_bd (by norm_num)
  have h16D_bd : (16 / 25 : ℝ) * |D|
      ≤ (16 / 25 : ℝ) * (M / 120 * h ^ 5) :=
    mul_le_mul_of_nonneg_left hD_bd (by norm_num)
  have h1225E_bd : (12 / 25 : ℝ) * h * |E|
      ≤ (12 / 25 : ℝ) * h * (M / 24 * (4 * h) ^ 4) :=
    mul_le_mul_of_nonneg_left hE_bd h1225h_nn
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
  linarith [htri, hA_bd, h48B_bd, h36C_bd, h16D_bd, h1225E_bd,
    hbound_alg.le, hbound_alg.ge, hslack]

/-- Pointwise BDF4 truncation residual bound. Algebraic identity
`τ = R_y(4) − (48/25) R_y(3) + (36/25) R_y(2) − (16/25) R_y(1)
   − (12h/25) R_y'(4)`, with fifth-order Taylor remainders for `y` and a
fourth-order Taylor remainder for `y'`. The exact rational coefficient
`6724/375 ≈ 17.93` is slackened to `18`. -/
theorem bdf4_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 5 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 5 y t| ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (ht4h : t + 4 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    |y (t + 4 * h) - (48 / 25 : ℝ) * y (t + 3 * h)
        + (36 / 25 : ℝ) * y (t + 2 * h) - (16 / 25 : ℝ) * y (t + h)
        + (3 / 25 : ℝ) * y t
        - (12 / 25 : ℝ) * h * deriv y (t + 4 * h)|
      ≤ (18 : ℝ) * M * h ^ 5 := by
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have hRy1 := y_fifth_order_taylor_remainder hy hbnd ht hth hh
  have hRy2 := y_fifth_order_taylor_remainder hy hbnd ht ht2h h2h
  have hRy3 := y_fifth_order_taylor_remainder hy hbnd ht ht3h h3h
  have hRy4 := y_fifth_order_taylor_remainder hy hbnd ht ht4h h4h
  have hRyp4 := derivY_fourth_order_taylor_remainder hy hbnd ht ht4h h4h
  set y0 := y t with hy0_def
  set y1 := y (t + h) with hy1_def
  set y2 := y (t + 2 * h) with hy2_def
  set y3 := y (t + 3 * h) with hy3_def
  set y4 := y (t + 4 * h) with hy4_def
  set d0 := deriv y t with hd0_def
  set d4 := deriv y (t + 4 * h) with hd4_def
  set dd := iteratedDeriv 2 y t with hdd_def
  set ddd := iteratedDeriv 3 y t with hddd_def
  set dddd := iteratedDeriv 4 y t with hdddd_def
  -- LTE = R_y(4) − (48/25) R_y(3) + (36/25) R_y(2) − (16/25) R_y(1) − (12h/25) R_y'(4).
  have hLTE_eq :
      y4 - (48 / 25 : ℝ) * y3 + (36 / 25 : ℝ) * y2
          - (16 / 25 : ℝ) * y1 + (3 / 25 : ℝ) * y0
          - (12 / 25 : ℝ) * h * d4
        = (y4 - y0 - (4 * h) * d0
              - (4 * h) ^ 2 / 2 * dd - (4 * h) ^ 3 / 6 * ddd
              - (4 * h) ^ 4 / 24 * dddd)
          - (48 / 25 : ℝ)
              * (y3 - y0 - (3 * h) * d0
                  - (3 * h) ^ 2 / 2 * dd - (3 * h) ^ 3 / 6 * ddd
                  - (3 * h) ^ 4 / 24 * dddd)
          + (36 / 25 : ℝ)
              * (y2 - y0 - (2 * h) * d0
                  - (2 * h) ^ 2 / 2 * dd - (2 * h) ^ 3 / 6 * ddd
                  - (2 * h) ^ 4 / 24 * dddd)
          - (16 / 25 : ℝ)
              * (y1 - y0 - h * d0 - h ^ 2 / 2 * dd - h ^ 3 / 6 * ddd
                  - h ^ 4 / 24 * dddd)
          - ((12 / 25 : ℝ) * h)
              * (d4 - d0 - (4 * h) * dd - (4 * h) ^ 2 / 2 * ddd
                  - (4 * h) ^ 3 / 6 * dddd) := by
    ring
  rw [hLTE_eq]
  set A := y4 - y0 - (4 * h) * d0
            - (4 * h) ^ 2 / 2 * dd - (4 * h) ^ 3 / 6 * ddd
            - (4 * h) ^ 4 / 24 * dddd with hA_def
  set B := y3 - y0 - (3 * h) * d0
            - (3 * h) ^ 2 / 2 * dd - (3 * h) ^ 3 / 6 * ddd
            - (3 * h) ^ 4 / 24 * dddd with hB_def
  set C := y2 - y0 - (2 * h) * d0
            - (2 * h) ^ 2 / 2 * dd - (2 * h) ^ 3 / 6 * ddd
            - (2 * h) ^ 4 / 24 * dddd with hC_def
  set D := y1 - y0 - h * d0 - h ^ 2 / 2 * dd - h ^ 3 / 6 * ddd
            - h ^ 4 / 24 * dddd with hD_def
  set E := d4 - d0 - (4 * h) * dd - (4 * h) ^ 2 / 2 * ddd
            - (4 * h) ^ 3 / 6 * dddd with hE_def
  clear_value A B C D E
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (abs_nonneg _).trans this
  exact bdf4_pointwise_residual_alg hh hMnn A B C D E hRy4 hRy3 hRy2 hRy1 hRyp4

/-- Uniform bound on the BDF4 one-step truncation residual on a finite
horizon, given a `C^5` exact solution. -/
theorem bdf4_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 5 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 4) * h ≤ T →
        |bdf4.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 5 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_five_bounded_on_Icc hy t₀ (t₀ + T + 1)
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
  rw [bdf4_localTruncationError_eq]
  exact bdf4_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem ht3h_mem
    ht4h_mem hh.le

end LMM
