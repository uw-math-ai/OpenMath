import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMAB2Convergence

/-! ## BDF2 Quantitative Convergence Chain (Iserles §1.2)

Quantitative scalar convergence chain for the implicit 2-step BDF2 method
`y_{n+2} = (4/3) y_{n+1} − (1/3) y_n + (2/3) h · f(t_{n+2}, y_{n+2})`.

Unlike the Adams family, BDF2's homogeneous polynomial
`ρ(ξ) = ξ² − (4/3)ξ + 1/3 = (ξ − 1)(ξ − 1/3)` has |α₀| + |α₁| = 5/3 > 1, so
the trivial max-norm error bound has growth `5/3 > 1` even at `h = 0`. We
sidestep this via the Lyapunov sum

  W_n := |3/2·e_{n+1} − 1/2·e_n| + |3/2·(e_n − e_{n+1})|

(absolute values of the eigen-coordinates `u, v` for the eigenvalues `1, 1/3`
of the companion matrix). Under the small-step regime `(2/3)·h·L ≤ 1/4`, this
satisfies the clean recurrence `W_{n+1} ≤ (1 + 4·h·L)·W_n + 6·|τ_n|`, which is
the standard form consumed by `lmm_error_bound_from_local_truncation`. -/

namespace LMM

/-- BDF2 trajectory predicate:
`y_{n+2} = (4/3) y_{n+1} − (1/3) y_n + (2/3) h · f(t_{n+2}, y_{n+2})`.
The new value appears inside `f`, so existence of such a trajectory is a
separate fixed-point problem. -/
structure IsBDF2Trajectory (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ : ℝ)
    (y : ℕ → ℝ) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 2)
      = (4 / 3 : ℝ) * y (n + 1) - (1 / 3 : ℝ) * y n
        + (2 / 3 : ℝ) * h * f (t₀ + ((n : ℝ) + 2) * h) (y (n + 2))

/-- BDF2 local truncation operator reduces to the textbook 2-step residual
`y(t+2h) − (4/3) y(t+h) + (1/3) y(t) − (2/3) h · y'(t+2h)`. -/
theorem bdf2_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    bdf2.localTruncationError h t y
      = y (t + 2 * h) - (4 / 3 : ℝ) * y (t + h) + (1 / 3 : ℝ) * y t
        - (2 / 3 : ℝ) * h * deriv y (t + 2 * h) := by
  unfold localTruncationError truncationOp
  simp [bdf2, Fin.sum_univ_three, iteratedDeriv_one, iteratedDeriv_zero]
  ring

/-- Forcing decomposition of the BDF2 error recurrence: the homogeneous
defect `e_{n+2} − (4/3) e_{n+1} + (1/3) e_n` is bounded by
`(2/3) h L · |e_{n+2}| + |τ_n|`. This is the BDF2 analogue of
`am2_one_step_lipschitz` but with the past-coefficient algebra coming from
α (homogeneous part) rather than from β·h. -/
theorem bdf2_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsBDF2Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    |(yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))
      - (4 / 3 : ℝ) * (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
      + (1 / 3 : ℝ) * (yseq n - y (t₀ + (n : ℝ) * h))|
    ≤ (2 / 3 : ℝ) * h * L
        * |yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|
      + |bdf2.localTruncationError h (t₀ + (n : ℝ) * h) y| := by
  set yn : ℝ := yseq n with hyn_def
  set yn1 : ℝ := yseq (n + 1) with hyn1_def
  set yn2 : ℝ := yseq (n + 2) with hyn2_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set zn : ℝ := y tn with hzn_def
  set zn1 : ℝ := y tn1 with hzn1_def
  set zn2 : ℝ := y tn2 with hzn2_def
  set τ : ℝ := bdf2.localTruncationError h tn y with hτ_def
  -- BDF2 step formula for the supplied implicit trajectory.
  have hstep : yn2
      = (4 / 3 : ℝ) * yn1 - (1 / 3 : ℝ) * yn
        + (2 / 3 : ℝ) * h * f tn2 yn2 := by
    simpa [hyn2_def, hyn1_def, hyn_def, htn2_def] using hy.recurrence n
  -- LTE in textbook form along the trajectory.
  have htn_2h : tn + 2 * h = tn2 := by simp [htn_def, htn2_def]; ring
  have htn_h : tn + h = tn1 := by simp [htn_def, htn1_def]; ring
  have hτ_eq : τ = zn2 - (4 / 3 : ℝ) * zn1 + (1 / 3 : ℝ) * zn
        - (2 / 3 : ℝ) * h * f tn2 zn2 := by
    show bdf2.localTruncationError h tn y = _
    rw [bdf2_localTruncationError_eq, htn_2h, htn_h, hyf tn2]
  -- Algebraic decomposition of the error defect.
  have halg : (yn2 - zn2) - (4 / 3 : ℝ) * (yn1 - zn1)
        + (1 / 3 : ℝ) * (yn - zn)
      = (2 / 3 : ℝ) * h * (f tn2 yn2 - f tn2 zn2) - τ := by
    conv_lhs => rw [hstep]
    rw [hτ_eq]; ring
  have hLip : |f tn2 yn2 - f tn2 zn2| ≤ L * |yn2 - zn2| := hf tn2 yn2 zn2
  have h23_nn : (0 : ℝ) ≤ (2 / 3 : ℝ) * h := mul_nonneg (by norm_num) hh
  have h23_abs :
      |(2 / 3 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)|
        ≤ (2 / 3 : ℝ) * h * L * |yn2 - zn2| := by
    rw [abs_mul, abs_of_nonneg h23_nn]
    calc (2 / 3 : ℝ) * h * |f tn2 yn2 - f tn2 zn2|
        ≤ (2 / 3 : ℝ) * h * (L * |yn2 - zn2|) :=
          mul_le_mul_of_nonneg_left hLip h23_nn
      _ = (2 / 3 : ℝ) * h * L * |yn2 - zn2| := by ring
  have htri :
      |(2 / 3 : ℝ) * h * (f tn2 yn2 - f tn2 zn2) - τ|
      ≤ |(2 / 3 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)| + |τ| := abs_sub _ _
  calc |(yn2 - zn2) - (4 / 3 : ℝ) * (yn1 - zn1)
            + (1 / 3 : ℝ) * (yn - zn)|
      = |(2 / 3 : ℝ) * h * (f tn2 yn2 - f tn2 zn2) - τ| := by rw [halg]
    _ ≤ |(2 / 3 : ℝ) * h * (f tn2 yn2 - f tn2 zn2)| + |τ| := htri
    _ ≤ (2 / 3 : ℝ) * h * L * |yn2 - zn2| + |τ| := by linarith [h23_abs]

/-- Pointwise BDF2 truncation residual bound.  Algebraic identity
`τ = R_y(2) − (4/3)·R_y(1) − (2h/3)·R_y'(2)` where `R_y(r), R_y'(r)` are
the second-order Taylor remainders at `t` for `y, y'`.  Sum of the three
bounds `(4/3 + 2/9 + 4/3)·M·h³ = (26/9)·M·h³`, slackened to `3·M·h³`. -/
theorem bdf2_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 3 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 3 y t| ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    |y (t + 2 * h) - (4 / 3 : ℝ) * y (t + h) + (1 / 3 : ℝ) * y t
        - (2 / 3 : ℝ) * h * deriv y (t + 2 * h)|
      ≤ (3 : ℝ) * M * h ^ 3 := by
  have h2h : 0 ≤ 2 * h := by linarith
  -- R_y(1) : |y(t+h) - y(t) - h·y'(t) - h²/2·y''(t)| ≤ M/6 · h³.
  have hR1 := y_third_order_taylor_remainder hy hbnd ht hth hh
  -- R_y(2) : |y(t+2h) - y(t) - 2h·y'(t) - 2h²·y''(t)| ≤ M/6 · (2h)³.
  have hR2 := y_third_order_taylor_remainder hy hbnd ht ht2h h2h
  -- R_y'(2) : |y'(t+2h) - y'(t) - 2h·y''(t)| ≤ M/2 · (2h)².
  have hR3 := derivY_second_order_taylor_remainder hy hbnd ht ht2h h2h
  set y0 := y t with hy0_def
  set y1 := y (t + h) with hy1_def
  set y2 := y (t + 2 * h) with hy2_def
  set d0 := deriv y t with hd0_def
  set d2 := deriv y (t + 2 * h) with hd2_def
  set dd := iteratedDeriv 2 y t with hdd_def
  -- Algebraic identity: BDF2 LTE = R_y(2) − (4/3)·R_y(1) − (2h/3)·R_y'(2).
  -- Verified by ring after expanding remainders to polynomial parts.
  have hLTE_eq :
      y2 - (4 / 3 : ℝ) * y1 + (1 / 3 : ℝ) * y0
          - (2 / 3 : ℝ) * h * d2
        = (y2 - y0 - (2 * h) * d0 - (2 * h) ^ 2 / 2 * dd)
          - (4 / 3 : ℝ) * (y1 - y0 - h * d0 - h ^ 2 / 2 * dd)
          - (2 * h / 3 : ℝ) * (d2 - d0 - (2 * h) * dd) := by ring
  rw [hLTE_eq]
  set A := y2 - y0 - (2 * h) * d0 - (2 * h) ^ 2 / 2 * dd with hA_def
  set B := y1 - y0 - h * d0 - h ^ 2 / 2 * dd with hB_def
  set C := d2 - d0 - (2 * h) * dd with hC_def
  have h2h3_nn : (0 : ℝ) ≤ 2 * h / 3 := by linarith
  have habs2h3 : |(2 * h / 3 : ℝ) * C| = (2 * h / 3 : ℝ) * |C| := by
    rw [abs_mul, abs_of_nonneg h2h3_nn]
  have habs43 : |(4 / 3 : ℝ) * B| = (4 / 3 : ℝ) * |B| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3)]
  have htri : |A - (4 / 3 : ℝ) * B - (2 * h / 3 : ℝ) * C|
      ≤ |A| + (4 / 3 : ℝ) * |B| + (2 * h / 3 : ℝ) * |C| := by
    have h1 : |A - (4 / 3 : ℝ) * B - (2 * h / 3 : ℝ) * C|
        ≤ |A - (4 / 3 : ℝ) * B| + |(2 * h / 3 : ℝ) * C| := abs_sub _ _
    have h2 : |A - (4 / 3 : ℝ) * B| ≤ |A| + |(4 / 3 : ℝ) * B| := abs_sub _ _
    linarith [habs2h3.le, habs2h3.ge, habs43.le, habs43.ge]
  -- Apply the three remainder bounds.
  have hA_bd : |A| ≤ M / 6 * (2 * h) ^ 3 := hR2
  have hB_bd : |B| ≤ M / 6 * h ^ 3 := hR1
  have hC_bd : |C| ≤ M / 2 * (2 * h) ^ 2 := hR3
  -- (4/3) · M/6 · h^3 ≤ (4/3) · |B|-bound; etc.
  have h43B_bd : (4 / 3 : ℝ) * |B| ≤ (4 / 3 : ℝ) * (M / 6 * h ^ 3) :=
    mul_le_mul_of_nonneg_left hB_bd (by norm_num)
  have h2h3C_bd : (2 * h / 3 : ℝ) * |C|
      ≤ (2 * h / 3 : ℝ) * (M / 2 * (2 * h) ^ 2) :=
    mul_le_mul_of_nonneg_left hC_bd h2h3_nn
  -- Sum of upper bounds: (8/6)·M·h³ + (4/3)·M·h³/6 + (2h/3)·M/2·(2h)²
  --                  = (4/3)·M·h³ + (2/9)·M·h³ + (4/3)·M·h³ = (26/9)·M·h³
  have hbound_alg :
      M / 6 * (2 * h) ^ 3 + (4 / 3 : ℝ) * (M / 6 * h ^ 3)
        + (2 * h / 3 : ℝ) * (M / 2 * (2 * h) ^ 2)
        = (26 / 9 : ℝ) * M * h ^ 3 := by ring
  have hMnn : 0 ≤ M := (abs_nonneg _).trans (hbnd t ht)
  have hh3_nn : 0 ≤ h ^ 3 := by positivity
  have hslack : (26 / 9 : ℝ) * M * h ^ 3 ≤ (3 : ℝ) * M * h ^ 3 := by
    have hcoef : (26 / 9 : ℝ) ≤ 3 := by norm_num
    nlinarith [hMnn, hh3_nn]
  linarith [htri, hA_bd, h43B_bd, h2h3C_bd, hbound_alg.le, hbound_alg.ge,
    hslack]

/-- Uniform bound on the BDF2 one-step truncation residual on a finite
horizon, given a `C^3` exact solution. -/
theorem bdf2_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 3 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 2) * h ≤ T →
        |bdf2.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 3 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_three_bounded_on_Icc hy t₀ (t₀ + T + 1)
  refine ⟨(3 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 2) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 2) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h = ((n : ℝ) + 2) * h := by ring
    linarith
  rw [bdf2_localTruncationError_eq]
  exact bdf2_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem hh.le

/-- The Lyapunov-sum recurrence for BDF2.  Defining
`u := (3/2)·e_{n+1} − (1/2)·e_n` and `v := (3/2)·(e_n − e_{n+1})`
(eigenvector coordinates for ρ's roots `1` and `1/3`), the sum
`W_n := |u_n| + |v_n|` satisfies the clean (1 + h·(4L)) growth bound.
This is the analogue of the `_one_step_error_pair_bound` recurrence used by
the Adams chains, but in the eigen-norm rather than the trivial max-norm. -/
theorem bdf2_one_step_error_pair_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (2 / 3 : ℝ) * h * L ≤ 1 / 4)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ : ℝ) {yseq : ℕ → ℝ}
    (hy : IsBDF2Trajectory h f t₀ yseq)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    |(3 / 2 : ℝ) * (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))
        - (1 / 2 : ℝ) * (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))|
      + |(3 / 2 : ℝ) * (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
          - (3 / 2 : ℝ) * (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))|
      ≤ (1 + h * (4 * L))
          * (|(3 / 2 : ℝ) * (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
                - (1 / 2 : ℝ) * (yseq n - y (t₀ + (n : ℝ) * h))|
            + |(3 / 2 : ℝ) * (yseq n - y (t₀ + (n : ℝ) * h))
                - (3 / 2 : ℝ) * (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))|)
        + 6 * |bdf2.localTruncationError h (t₀ + (n : ℝ) * h) y| := by
  set en : ℝ := yseq n - y (t₀ + (n : ℝ) * h) with hen_def
  set en1 : ℝ := yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h) with hen1_def
  set en2 : ℝ := yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h) with hen2_def
  set τabs : ℝ := |bdf2.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  -- Forcing decomposition: |e_{n+2} - (4/3)e_{n+1} + (1/3)e_n|
  -- ≤ (2/3)·h·L·|e_{n+2}| + |τ|.
  have hlip := bdf2_one_step_lipschitz (h := h) (L := L)
    hh hf t₀ hy y hyf n
  -- Translate `hlip` to abbreviations.
  have hlip' :
      |en2 - (4 / 3 : ℝ) * en1 + (1 / 3 : ℝ) * en|
        ≤ (2 / 3 : ℝ) * h * L * |en2| + τabs := by
    simpa [hen_def, hen1_def, hen2_def, hτabs_def] using hlip
  -- Set up u, v, W.
  set u := (3 / 2 : ℝ) * en1 - (1 / 2 : ℝ) * en with hu_def
  set v := (3 / 2 : ℝ) * en - (3 / 2 : ℝ) * en1 with hv_def
  set u' := (3 / 2 : ℝ) * en2 - (1 / 2 : ℝ) * en1 with hu'_def
  set v' := (3 / 2 : ℝ) * en1 - (3 / 2 : ℝ) * en2 with hv'_def
  -- Identities expressing u', v' as decoupled u-, v-recurrences plus forcing.
  -- Setting ψ := en2 - (4/3) en1 + (1/3) en (so |ψ| ≤ (2/3)hL|en2| + τabs):
  --   u' = u + (3/2) ψ
  --   v' = (1/3) v - (3/2) ψ
  set ψ : ℝ := en2 - (4 / 3 : ℝ) * en1 + (1 / 3 : ℝ) * en with hψ_def
  have hu_rec : u' = u + (3 / 2 : ℝ) * ψ := by
    show (3 / 2 : ℝ) * en2 - (1 / 2 : ℝ) * en1
        = ((3 / 2 : ℝ) * en1 - (1 / 2 : ℝ) * en)
          + (3 / 2 : ℝ) * (en2 - (4 / 3 : ℝ) * en1 + (1 / 3 : ℝ) * en)
    ring
  have hv_rec : v' = (1 / 3 : ℝ) * v - (3 / 2 : ℝ) * ψ := by
    show (3 / 2 : ℝ) * en1 - (3 / 2 : ℝ) * en2
        = (1 / 3 : ℝ) * ((3 / 2 : ℝ) * en - (3 / 2 : ℝ) * en1)
          - (3 / 2 : ℝ) * (en2 - (4 / 3 : ℝ) * en1 + (1 / 3 : ℝ) * en)
    ring
  -- |ψ| bound
  have hψ_bd : |ψ| ≤ (2 / 3 : ℝ) * h * L * |en2| + τabs := hlip'
  -- |en2| relates to |u| + |v| + |ψ|.
  -- en2 = u' + (1/3) v' = (u + (3/2)ψ) + (1/3)((1/3) v - (3/2) ψ)
  --     = u + (1/9) v + 2 ψ - (1/2) ψ ... let me recompute.
  -- u' + (1/3) v' = u + (3/2)ψ + (1/3)((1/3)v - (3/2)ψ)
  --              = u + (1/9)v + (3/2)ψ - (1/2)ψ
  --              = u + (1/9)v + ψ.
  -- And en2 = u' + (1/3) v' (since en_k = u_k + v_k for original mapping, but
  -- in our convention u_{n} := (3/2)en1 - (1/2)en represents the value at
  -- "index n+1"-ish; verify by direct algebra:
  --   u + (1/3) v = (3/2)en1 - (1/2)en + (1/3)((3/2)en - (3/2)en1)
  --              = (3/2)en1 - (1/2)en + (1/2)en - (1/2)en1
  --              = en1.
  -- So u_k + (1/3) v_k = e_{k+1}. Hence en2 = u' + (1/3) v'.
  have hen2_uv : en2 = u' + (1 / 3 : ℝ) * v' := by
    show en2
        = ((3 / 2 : ℝ) * en2 - (1 / 2 : ℝ) * en1)
          + (1 / 3 : ℝ) * ((3 / 2 : ℝ) * en1 - (3 / 2 : ℝ) * en2)
    ring
  -- en2 = u + (1/9) v + ψ.
  have hen2_recombined :
      en2 = u + (1 / 9 : ℝ) * v + ψ := by
    rw [hen2_uv, hu_rec, hv_rec]; ring
  -- |en2| ≤ |u| + (1/9)|v| + |ψ|
  have hen2_bd1 : |en2| ≤ |u| + (1 / 9 : ℝ) * |v| + |ψ| := by
    rw [hen2_recombined]
    calc |u + (1 / 9 : ℝ) * v + ψ|
        ≤ |u + (1 / 9 : ℝ) * v| + |ψ| := abs_add_le _ _
      _ ≤ |u| + |(1 / 9 : ℝ) * v| + |ψ| := by linarith [abs_add_le u ((1 / 9 : ℝ) * v)]
      _ = |u| + (1 / 9 : ℝ) * |v| + |ψ| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 9)]
  -- Combine to bound |ψ| above by (4/3)hL|u| + (4/27)hL|v| + 2 τabs.
  have hu_nn : 0 ≤ |u| := abs_nonneg _
  have hv_nn : 0 ≤ |v| := abs_nonneg _
  have hψ_nn : 0 ≤ |ψ| := abs_nonneg _
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  have hen2_nn : 0 ≤ |en2| := abs_nonneg _
  have hhL_nn : 0 ≤ h * L := mul_nonneg hh hL
  have h23hL_nn : 0 ≤ (2 / 3 : ℝ) * h * L := by positivity
  -- |ψ| ≤ (2/3)hL · (|u| + (1/9)|v| + |ψ|) + τabs
  have hψ_step : |ψ|
      ≤ (2 / 3 : ℝ) * h * L * (|u| + (1 / 9 : ℝ) * |v| + |ψ|) + τabs := by
    have := mul_le_mul_of_nonneg_left hen2_bd1 h23hL_nn
    linarith [hψ_bd]
  -- (2/3)hL ≤ 1/4, so (1 - (2/3)hL) ≥ 3/4 > 0.
  have h_one_minus_pos : 0 < 1 - (2 / 3 : ℝ) * h * L := by linarith [hsmall]
  have h_one_minus_ge : (3 / 4 : ℝ) ≤ 1 - (2 / 3 : ℝ) * h * L := by
    linarith [hsmall]
  -- Solve hψ_step for |ψ|:
  -- (1 - (2/3)hL) |ψ| ≤ (2/3)hL · (|u| + (1/9)|v|) + τabs.
  have hψ_solved :
      (1 - (2 / 3 : ℝ) * h * L) * |ψ|
        ≤ (2 / 3 : ℝ) * h * L * (|u| + (1 / 9 : ℝ) * |v|) + τabs := by
    have : (1 - (2 / 3 : ℝ) * h * L) * |ψ|
        = |ψ| - (2 / 3 : ℝ) * h * L * |ψ| := by ring
    linarith [hψ_step]
  -- Therefore |ψ| ≤ (4/3) ((2/3)hL |u| + (2/27)hL|v|) + (4/3) τabs (using
  -- 1/(1-x) ≤ 4/3 when x ≤ 1/4, i.e., (1-x) ≥ 3/4).
  have hψ_final :
      |ψ| ≤ (8 / 9 : ℝ) * h * L * |u|
            + (8 / 81 : ℝ) * h * L * |v| + (4 / 3 : ℝ) * τabs := by
    have h_lhs : (3 / 4 : ℝ) * |ψ| ≤ (1 - (2 / 3 : ℝ) * h * L) * |ψ| :=
      mul_le_mul_of_nonneg_right h_one_minus_ge hψ_nn
    have hcomb := le_trans h_lhs hψ_solved
    have hexp : (2 / 3 : ℝ) * h * L * (|u| + (1 / 9 : ℝ) * |v|)
        = (2 / 3 : ℝ) * h * L * |u|
            + (2 / 3 : ℝ) * h * L * (1 / 9 : ℝ) * |v| := by ring
    have hbase : (3 / 4 : ℝ) * |ψ|
        ≤ (2 / 3 : ℝ) * h * L * |u|
          + (2 / 3 : ℝ) * h * L * (1 / 9 : ℝ) * |v| + τabs := by
      linarith [hcomb, hexp.le, hexp.ge]
    -- Multiply by 4/3.
    have hmul := mul_le_mul_of_nonneg_left hbase
      (by norm_num : (0 : ℝ) ≤ 4 / 3)
    have hLHS : (4 / 3 : ℝ) * ((3 / 4 : ℝ) * |ψ|) = |ψ| := by ring
    have hRHS : (4 / 3 : ℝ) * ((2 / 3 : ℝ) * h * L * |u|
          + (2 / 3 : ℝ) * h * L * (1 / 9 : ℝ) * |v| + τabs)
        = (8 / 9 : ℝ) * h * L * |u|
          + (8 / 81 : ℝ) * h * L * |v| + (4 / 3 : ℝ) * τabs := by ring
    linarith [hmul, hLHS.le, hLHS.ge, hRHS.le, hRHS.ge]
  -- Now bound |u'| ≤ |u| + (3/2) |ψ|, |v'| ≤ (1/3)|v| + (3/2) |ψ|.
  have hu'_bd : |u'| ≤ |u| + (3 / 2 : ℝ) * |ψ| := by
    rw [hu_rec]
    calc |u + (3 / 2 : ℝ) * ψ|
        ≤ |u| + |(3 / 2 : ℝ) * ψ| := abs_add_le _ _
      _ = |u| + (3 / 2 : ℝ) * |ψ| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  have hv'_bd : |v'| ≤ (1 / 3 : ℝ) * |v| + (3 / 2 : ℝ) * |ψ| := by
    rw [hv_rec]
    calc |(1 / 3 : ℝ) * v - (3 / 2 : ℝ) * ψ|
        ≤ |(1 / 3 : ℝ) * v| + |(3 / 2 : ℝ) * ψ| := abs_sub _ _
      _ = (1 / 3 : ℝ) * |v| + (3 / 2 : ℝ) * |ψ| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3),
              abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  -- Combine:
  --   |u'| + |v'| ≤ |u| + (1/3)|v| + 3 |ψ|
  --             ≤ |u| + (1/3)|v| + 3 ((8/9)hL|u| + (8/81)hL|v| + (4/3)τabs)
  --             = (1 + (8/3)hL) |u| + ((1/3) + (8/27)hL) |v| + 4 τabs.
  -- We want ≤ (1 + 4hL) (|u| + |v|) + 6 τabs.
  -- (1 + (8/3)hL) ≤ (1 + 4hL) ✓.  (1/3 + (8/27)hL) ≤ (1 + 4hL) ✓ when hL ≥ 0.
  -- 4 ≤ 6 ✓.
  have h_show : |u'| + |v'|
      ≤ (1 + h * (4 * L)) * (|u| + |v|) + 6 * τabs := by
    have hsum : |u'| + |v'|
        ≤ |u| + (1 / 3 : ℝ) * |v| + 3 * |ψ| := by
      linarith [hu'_bd, hv'_bd]
    have hψ3 : 3 * |ψ|
        ≤ (8 / 3 : ℝ) * h * L * |u|
          + (8 / 27 : ℝ) * h * L * |v| + 4 * τabs := by
      have := mul_le_mul_of_nonneg_left hψ_final (by norm_num : (0 : ℝ) ≤ 3)
      linarith [this]
    -- The remaining inequality is purely numeric in |u|, |v|, hL, τabs.
    have hgrowth_u : |u| + (8 / 3 : ℝ) * h * L * |u|
        ≤ (1 + h * (4 * L)) * |u| := by
      have hdiff_eq : (1 + h * (4 * L)) * |u| - (|u| + (8 / 3 : ℝ) * h * L * |u|)
          = (4 / 3 : ℝ) * h * L * |u| := by ring
      have hdiff_nn : 0 ≤ (4 / 3 : ℝ) * h * L * |u| :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hh) hL) hu_nn
      linarith [hdiff_nn, hdiff_eq.le, hdiff_eq.ge]
    have hgrowth_v : (1 / 3 : ℝ) * |v| + (8 / 27 : ℝ) * h * L * |v|
        ≤ (1 + h * (4 * L)) * |v| := by
      have hdiff_eq :
          (1 + h * (4 * L)) * |v| - ((1 / 3 : ℝ) * |v| + (8 / 27 : ℝ) * h * L * |v|)
          = (2 / 3 : ℝ) * |v| + (100 / 27 : ℝ) * h * L * |v| := by ring
      have h1_nn : 0 ≤ (2 / 3 : ℝ) * |v| := mul_nonneg (by norm_num) hv_nn
      have h2_nn : 0 ≤ (100 / 27 : ℝ) * h * L * |v| :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hh) hL) hv_nn
      linarith [h1_nn, h2_nn, hdiff_eq.le, hdiff_eq.ge]
    have h_split :
        (1 + h * (4 * L)) * (|u| + |v|)
          = (1 + h * (4 * L)) * |u| + (1 + h * (4 * L)) * |v| := by ring
    have h_step1 : |u'| + |v'|
        ≤ |u| + (1 / 3 : ℝ) * |v|
          + ((8 / 3 : ℝ) * h * L * |u| + (8 / 27 : ℝ) * h * L * |v| + 4 * τabs) := by
      linarith only [hsum, hψ3]
    have h_step2 : |u| + (1 / 3 : ℝ) * |v|
          + ((8 / 3 : ℝ) * h * L * |u| + (8 / 27 : ℝ) * h * L * |v| + 4 * τabs)
        = (|u| + (8 / 3 : ℝ) * h * L * |u|)
          + ((1 / 3 : ℝ) * |v| + (8 / 27 : ℝ) * h * L * |v|)
          + 4 * τabs := by ring
    have h_step3 : (|u| + (8 / 3 : ℝ) * h * L * |u|)
          + ((1 / 3 : ℝ) * |v| + (8 / 27 : ℝ) * h * L * |v|)
          + 4 * τabs
        ≤ (1 + h * (4 * L)) * |u| + (1 + h * (4 * L)) * |v| + 6 * τabs := by
      linarith only [hgrowth_u, hgrowth_v, hτ_nn]
    linarith only [h_step1, h_step2.le, h_step2.ge, h_step3,
      h_split.le, h_split.ge]
  -- Conclude.
  show |u'| + |v'| ≤ (1 + h * (4 * L)) * (|u| + |v|) + 6 * τabs
  exact h_show

/-- Headline BDF2 global error bound.  Given a supplied BDF2 trajectory and
starting errors bounded by `ε₀`, the scalar global error is `O(ε₀ + h²)` on
a finite horizon. -/
theorem bdf2_global_error_bound
    {y : ℝ → ℝ} (hy_smooth : ContDiff ℝ 3 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      (2 / 3 : ℝ) * h * L ≤ 1 / 4 →
      ∀ {yseq : ℕ → ℝ} {ε₀ : ℝ},
      IsBDF2Trajectory h f t₀ yseq →
      0 ≤ ε₀ →
      |yseq 0 - y t₀| ≤ ε₀ →
      |yseq 1 - y (t₀ + h)| ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 1) * h ≤ T →
      |yseq N - y (t₀ + (N : ℝ) * h)|
        ≤ 5 * Real.exp ((4 * L) * T) * ε₀ + K * h ^ 2 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    bdf2_local_residual_bound hy_smooth t₀ T hT
  refine ⟨T * Real.exp ((4 * L) * T) * (6 * C), δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  intro h hh hδ_le hsmall yseq ε₀ hy_traj hε₀ he0_bd he1_bd N hNh
  -- Define the Lyapunov sum sequence W_n.
  set W : ℕ → ℝ := fun k =>
    |(3 / 2 : ℝ) * (yseq (k + 1) - y (t₀ + ((k : ℝ) + 1) * h))
        - (1 / 2 : ℝ) * (yseq k - y (t₀ + (k : ℝ) * h))|
      + |(3 / 2 : ℝ) * (yseq k - y (t₀ + (k : ℝ) * h))
          - (3 / 2 : ℝ) * (yseq (k + 1) - y (t₀ + ((k : ℝ) + 1) * h))|
    with hW_def
  have hW_nn : ∀ k, 0 ≤ W k := fun k =>
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  -- Initial bound: W 0 ≤ 5 ε₀.
  have hW0_le : W 0 ≤ 5 * ε₀ := by
    have he0 : |yseq 0 - y t₀| ≤ ε₀ := by simpa using he0_bd
    have he1 : |yseq 1 - y (t₀ + h)| ≤ ε₀ := he1_bd
    have hcast0r : t₀ + ((0 : ℕ) : ℝ) * h = t₀ := by push_cast; ring
    have hcast1r : t₀ + (((0 : ℕ) : ℝ) + 1) * h = t₀ + h := by push_cast; ring
    set a : ℝ := yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h) with ha_def
    set b : ℝ := yseq 1 - y (t₀ + (((0 : ℕ) : ℝ) + 1) * h) with hb_def
    have ha_bd : |a| ≤ ε₀ := by
      show |yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hcast0r]; exact he0
    have hb_bd : |b| ≤ ε₀ := by
      show |yseq 1 - y (t₀ + (((0 : ℕ) : ℝ) + 1) * h)| ≤ ε₀
      rw [hcast1r]; exact he1
    show |(3 / 2 : ℝ) * b - (1 / 2 : ℝ) * a|
        + |(3 / 2 : ℝ) * a - (3 / 2 : ℝ) * b| ≤ 5 * ε₀
    have h1_abs : |(3 / 2 : ℝ) * b - (1 / 2 : ℝ) * a| ≤ 2 * ε₀ := by
      calc |(3 / 2 : ℝ) * b - (1 / 2 : ℝ) * a|
          ≤ |(3 / 2 : ℝ) * b| + |(1 / 2 : ℝ) * a| := abs_sub _ _
        _ = (3 / 2 : ℝ) * |b| + (1 / 2 : ℝ) * |a| := by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3/2),
                abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
        _ ≤ (3 / 2 : ℝ) * ε₀ + (1 / 2 : ℝ) * ε₀ := by linarith [ha_bd, hb_bd]
        _ = 2 * ε₀ := by ring
    have h2_abs : |(3 / 2 : ℝ) * a - (3 / 2 : ℝ) * b| ≤ 3 * ε₀ := by
      calc |(3 / 2 : ℝ) * a - (3 / 2 : ℝ) * b|
          ≤ |(3 / 2 : ℝ) * a| + |(3 / 2 : ℝ) * b| := abs_sub _ _
        _ = (3 / 2 : ℝ) * |a| + (3 / 2 : ℝ) * |b| := by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3/2),
                abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3/2)]
        _ ≤ (3 / 2 : ℝ) * ε₀ + (3 / 2 : ℝ) * ε₀ := by linarith [ha_bd, hb_bd]
        _ = 3 * ε₀ := by ring
    linarith [h1_abs, h2_abs]
  have h4L_nn : (0 : ℝ) ≤ 4 * L := by linarith
  -- The general step: when (n + 2) * h ≤ T,
  -- W (n+1) ≤ (1 + h*(4L)) * W n + 6*C * h^3.
  have hstep_general : ∀ n : ℕ, ((n : ℝ) + 2) * h ≤ T →
      W (n + 1) ≤ (1 + h * (4 * L)) * W n + (6 * C) * h ^ 3 := by
    intro n hnh_le
    have honestep := bdf2_one_step_error_pair_bound
      (h := h) (L := L) hh.le hL hsmall hf t₀ hy_traj y hyf n
    have hres := hresidual hh hδ_le n hnh_le
    -- Translate W (n+1) and W n.
    have hcast1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hcast2 : ((n + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    have hcast1' : t₀ + ((n + 1 : ℕ) : ℝ) * h = t₀ + ((n : ℝ) + 1) * h := by
      push_cast; ring
    have hcast2' : t₀ + (((n + 1 : ℕ) : ℝ) + 1) * h
        = t₀ + ((n : ℝ) + 2) * h := by push_cast; ring
    have heq_W_n1 : W (n + 1)
        = |(3 / 2 : ℝ) * (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))
              - (1 / 2 : ℝ) * (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))|
          + |(3 / 2 : ℝ) * (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
              - (3 / 2 : ℝ) * (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))| := by
      show |(3/2 : ℝ) * (yseq (n + 1 + 1) - y (t₀ + (((n + 1 : ℕ) : ℝ) + 1) * h))
            - (1/2 : ℝ) * (yseq (n + 1) - y (t₀ + ((n + 1 : ℕ) : ℝ) * h))|
          + |(3/2 : ℝ) * (yseq (n + 1) - y (t₀ + ((n + 1 : ℕ) : ℝ) * h))
            - (3/2 : ℝ) * (yseq (n + 1 + 1) - y (t₀ + (((n + 1 : ℕ) : ℝ) + 1) * h))| = _
      rw [hcast1', hcast2']
    rw [heq_W_n1]
    have h6τ : 6 * |bdf2.localTruncationError h
        (t₀ + (n : ℝ) * h) y| ≤ (6 * C) * h ^ 3 := by
      have h6nn : (0 : ℝ) ≤ 6 := by norm_num
      have := mul_le_mul_of_nonneg_left hres h6nn
      linarith
    show |(3 / 2 : ℝ) * (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))
            - (1 / 2 : ℝ) * (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))|
          + |(3 / 2 : ℝ) * (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
              - (3 / 2 : ℝ) * (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))|
        ≤ (1 + h * (4 * L)) * W n + 6 * C * h ^ 3
    show _ ≤ _
    have hWn_eq : W n
        = |(3 / 2 : ℝ) * (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
              - (1 / 2 : ℝ) * (yseq n - y (t₀ + (n : ℝ) * h))|
          + |(3 / 2 : ℝ) * (yseq n - y (t₀ + (n : ℝ) * h))
              - (3 / 2 : ℝ) * (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))| := rfl
    rw [hWn_eq]
    linarith [honestep, h6τ]
  -- Apply the discrete Grönwall bridge to W.
  -- Need: e (k+1) ≤ (1 + h*(4L)) * e k + (6C) h^(2+1).
  -- For k < N where (N+1) h ≤ T, we need (k + 2) h ≤ T, i.e., k + 2 ≤ N + 1.
  -- That requires k ≤ N - 1, i.e., k < N. So for the loop k < N (in
  -- `lmm_error_bound_from_local_truncation`), we need (k+2) h ≤ T which is
  -- true since (k+2) ≤ (N+1) when k ≤ N - 1, hence k < N. Need N ≥ 1; the
  -- N = 0 case is handled separately.
  rcases N with _ | N'
  · -- N = 0.
    show |yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)|
        ≤ 5 * Real.exp ((4 * L) * T) * ε₀
            + T * Real.exp ((4 * L) * T) * (6 * C) * h ^ 2
    have hbase : |yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)|
        ≤ ε₀ := by simpa using he0_bd
    have hexp_ge : (1 : ℝ) ≤ Real.exp ((4 * L) * T) :=
      Real.one_le_exp_iff.mpr (by positivity)
    have hKnn : 0 ≤ T * Real.exp ((4 * L) * T) * (6 * C) :=
      mul_nonneg (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
    have hh2_nn : 0 ≤ h ^ 2 := by positivity
    nlinarith [hbase, hexp_ge, hKnn, hh2_nn, hε₀]
  · have hN_hyp : ((N' : ℝ) + 1 + 1) * h ≤ T := by
      have hcast : (((N' + 1 : ℕ) : ℝ) + 1) = (N' : ℝ) + 1 + 1 := by
        push_cast; ring
      linarith [hcast.symm ▸ hNh]
    have hgronwall_step : ∀ n, n < N' →
        W (n + 1) ≤ (1 + h * (4 * L)) * W n + (6 * C) * h ^ (2 + 1) := by
      intro n hn_lt
      have hpow : (6 * C) * h ^ (2 + 1) = (6 * C) * h ^ 3 := by norm_num
      rw [hpow]
      apply hstep_general
      have hn1_le_N' : (n : ℝ) + 1 ≤ (N' : ℝ) := by
        exact_mod_cast Nat.lt_iff_add_one_le.mp hn_lt
      have h_le_chain : (n : ℝ) + 2 ≤ (N' : ℝ) + 1 + 1 := by linarith
      have h_mul : ((n : ℝ) + 2) * h ≤ ((N' : ℝ) + 1 + 1) * h :=
        mul_le_mul_of_nonneg_right h_le_chain hh.le
      linarith
    have hN'h_le_T : (N' : ℝ) * h ≤ T := by
      have hle : (N' : ℝ) ≤ (N' : ℝ) + 1 + 1 := by linarith
      have hmul := mul_le_mul_of_nonneg_right hle hh.le
      linarith
    have hgronwall :=
      lmm_error_bound_from_local_truncation
        (h := h) (L := 4 * L) (C := 6 * C) (T := T) (p := 2) (e := W) (N := N')
        hh.le h4L_nn (by linarith) (hW_nn 0) hgronwall_step N' le_rfl hN'h_le_T
    -- W N' ≤ exp((4L)T) W 0 + T exp((4L)T) (6C) h^2.
    have hexp_nn : 0 ≤ Real.exp ((4 * L) * T) := Real.exp_nonneg _
    have h_chain :
        Real.exp ((4 * L) * T) * W 0
          ≤ Real.exp ((4 * L) * T) * (5 * ε₀) :=
      mul_le_mul_of_nonneg_left hW0_le hexp_nn
    -- Bound |e_{N'+1}| ≤ W N'.
    -- W k = |(3/2)e_{k+1} - (1/2)e_k| + |(3/2)e_k - (3/2)e_{k+1}|.
    -- Lower bound: |e_{k+1}| = |((3/2)e_{k+1} - (1/2)e_k) + (1/3)((3/2)e_k - (3/2)e_{k+1})|
    --             ≤ |(3/2)e_{k+1} - (1/2)e_k| + (1/3)|(3/2)e_k - (3/2)e_{k+1}| ≤ W k.
    have hek1_le_W : ∀ k, |yseq (k + 1) - y (t₀ + ((k : ℝ) + 1) * h)|
        ≤ W k := by
      intro k
      set e0 := yseq k - y (t₀ + (k : ℝ) * h)
      set e1 := yseq (k + 1) - y (t₀ + ((k : ℝ) + 1) * h)
      have hid : e1 = ((3 / 2 : ℝ) * e1 - (1 / 2 : ℝ) * e0)
          + (1 / 3 : ℝ) * ((3 / 2 : ℝ) * e0 - (3 / 2 : ℝ) * e1) := by ring
      calc |e1| = |((3 / 2 : ℝ) * e1 - (1 / 2 : ℝ) * e0)
            + (1 / 3 : ℝ) * ((3 / 2 : ℝ) * e0 - (3 / 2 : ℝ) * e1)| := by
              conv_lhs => rw [hid]
        _ ≤ |(3 / 2 : ℝ) * e1 - (1 / 2 : ℝ) * e0|
            + |(1 / 3 : ℝ) * ((3 / 2 : ℝ) * e0 - (3 / 2 : ℝ) * e1)| := abs_add_le _ _
        _ = |(3 / 2 : ℝ) * e1 - (1 / 2 : ℝ) * e0|
            + (1 / 3 : ℝ) * |(3 / 2 : ℝ) * e0 - (3 / 2 : ℝ) * e1| := by
              rw [show |(1 / 3 : ℝ) * ((3 / 2 : ℝ) * e0 - (3 / 2 : ℝ) * e1)|
                = (1 / 3 : ℝ) * |(3 / 2 : ℝ) * e0 - (3 / 2 : ℝ) * e1| from
                by rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/3)]]
        _ ≤ |(3 / 2 : ℝ) * e1 - (1 / 2 : ℝ) * e0|
            + |(3 / 2 : ℝ) * e0 - (3 / 2 : ℝ) * e1| := by
              have habs_nn : 0 ≤ |(3 / 2 : ℝ) * e0 - (3 / 2 : ℝ) * e1| := abs_nonneg _
              nlinarith [habs_nn]
        _ = W k := rfl
    show |yseq (N' + 1) - y (t₀ + ((N' + 1 : ℕ) : ℝ) * h)|
        ≤ 5 * Real.exp ((4 * L) * T) * ε₀
            + T * Real.exp ((4 * L) * T) * (6 * C) * h ^ 2
    have hN'eq : ((N' + 1 : ℕ) : ℝ) = (N' : ℝ) + 1 := by push_cast; ring
    rw [hN'eq]
    have heN' := hek1_le_W N'
    linarith [heN', hgronwall, h_chain]

end LMM
