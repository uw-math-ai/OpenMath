import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.LMMTruncationOp
import OpenMath.AdamsMethods
import OpenMath.LMMAB2Convergence
import OpenMath.LMMBDF1VectorConvergence

/-! ## BDF2 Vector Quantitative Convergence Chain (Iserles §1.2)

Finite-dimensional vector-valued analogue of the scalar BDF2 quantitative
convergence chain in `OpenMath/LMMBDF2Convergence.lean`.

The residual is method-specific, following the vector files in this
development.  The global theorem uses the same real-valued Lyapunov sum as the
scalar BDF2 proof, so the scalar discrete Grönwall bridge applies directly to
that auxiliary error sequence.
-/

namespace LMM

/-- BDF2 vector trajectory predicate:
`y_{n+2} = (4/3) • y_{n+1} - (1/3) • y_n
  + h • ((2/3) • f(t_{n+2}, y_{n+2}))`.
The new value appears inside `f`, so existence of such a trajectory is a
separate fixed-point problem. -/
structure IsBDF2TrajectoryVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y : ℕ → E) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 2)
      = (4 / 3 : ℝ) • y (n + 1) - (1 / 3 : ℝ) • y n
        + h • ((2 / 3 : ℝ) •
            f (t₀ + ((n : ℝ) + 2) * h) (y (n + 2)))

/-- Textbook BDF2 vector residual:
`y(t+2h) - (4/3) y(t+h) + (1/3)y(t) - (2/3)h y'(t+2h)`. -/
noncomputable def bdf2VecResidual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) : E :=
  y (t + 2 * h) - (4 / 3 : ℝ) • y (t + h)
    + (1 / 3 : ℝ) • y t
    - h • ((2 / 3 : ℝ) • deriv y (t + 2 * h))

/-- The vector BDF2 residual unfolds to the textbook two-step form. -/
theorem bdf2Vec_localTruncationError_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) :
    bdf2VecResidual h t y
      = y (t + 2 * h) - (4 / 3 : ℝ) • y (t + h)
        + (1 / 3 : ℝ) • y t
        - h • ((2 / 3 : ℝ) • deriv y (t + 2 * h)) := rfl

/-- Forcing decomposition of the BDF2 vector error recurrence. -/
theorem bdf2Vec_one_step_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsBDF2TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    ‖(yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))
      - (4 / 3 : ℝ) •
          (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
      + (1 / 3 : ℝ) • (yseq n - y (t₀ + (n : ℝ) * h))‖
    ≤ (2 / 3 : ℝ) * h * L
        * ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖
      + ‖bdf2VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set yn : E := yseq n with hyn_def
  set yn1 : E := yseq (n + 1) with hyn1_def
  set yn2 : E := yseq (n + 2) with hyn2_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set zn : E := y tn with hzn_def
  set zn1 : E := y tn1 with hzn1_def
  set zn2 : E := y tn2 with hzn2_def
  set τ : E := bdf2VecResidual h tn y with hτ_def
  -- BDF2 step formula for the supplied implicit trajectory.
  have hstep : yn2
      = (4 / 3 : ℝ) • yn1 - (1 / 3 : ℝ) • yn
        + h • ((2 / 3 : ℝ) • f tn2 yn2) := by
    simpa [hyn2_def, hyn1_def, hyn_def, htn2_def] using hy.recurrence n
  -- Local residual at `tn`, expressed via `f` along the exact trajectory.
  have htn_2h : tn + 2 * h = tn2 := by
    simp [htn_def, htn2_def]
    ring
  have htn_h : tn + h = tn1 := by
    simp [htn_def, htn1_def]
    ring
  have hτ_eq : τ = zn2 - (4 / 3 : ℝ) • zn1 + (1 / 3 : ℝ) • zn
        - h • ((2 / 3 : ℝ) • f tn2 zn2) := by
    show bdf2VecResidual h tn y = _
    unfold bdf2VecResidual
    rw [htn_2h, htn_h, hyf tn2]
  -- Algebraic decomposition of the error defect.
  have halg : (yn2 - zn2) - (4 / 3 : ℝ) • (yn1 - zn1)
        + (1 / 3 : ℝ) • (yn - zn)
      = h • ((2 / 3 : ℝ) • (f tn2 yn2 - f tn2 zn2)) - τ := by
    conv_lhs => rw [hstep]
    rw [hτ_eq]
    simp only [smul_sub, smul_smul]
    abel
  have hLip : ‖f tn2 yn2 - f tn2 zn2‖ ≤ L * ‖yn2 - zn2‖ := hf tn2 yn2 zn2
  have h23_nn : (0 : ℝ) ≤ (2 / 3 : ℝ) := by norm_num
  have h_term :
      ‖h • ((2 / 3 : ℝ) • (f tn2 yn2 - f tn2 zn2))‖
        ≤ (2 / 3 : ℝ) * h * L * ‖yn2 - zn2‖ := by
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hh,
      Real.norm_of_nonneg h23_nn]
    calc h * ((2 / 3 : ℝ) * ‖f tn2 yn2 - f tn2 zn2‖)
        ≤ h * ((2 / 3 : ℝ) * (L * ‖yn2 - zn2‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ hh
          exact mul_le_mul_of_nonneg_left hLip h23_nn
      _ = (2 / 3 : ℝ) * h * L * ‖yn2 - zn2‖ := by ring
  have htri :
      ‖h • ((2 / 3 : ℝ) • (f tn2 yn2 - f tn2 zn2)) - τ‖
        ≤ ‖h • ((2 / 3 : ℝ) • (f tn2 yn2 - f tn2 zn2))‖ + ‖τ‖ :=
    norm_sub_le _ _
  calc
    ‖(yn2 - zn2) - (4 / 3 : ℝ) • (yn1 - zn1)
        + (1 / 3 : ℝ) • (yn - zn)‖
        = ‖h • ((2 / 3 : ℝ) • (f tn2 yn2 - f tn2 zn2)) - τ‖ := by rw [halg]
    _ ≤ ‖h • ((2 / 3 : ℝ) • (f tn2 yn2 - f tn2 zn2))‖ + ‖τ‖ := htri
    _ ≤ (2 / 3 : ℝ) * h * L * ‖yn2 - zn2‖ + ‖τ‖ := by
      linarith [h_term]

/-- Pointwise BDF2 vector truncation residual bound. -/
theorem bdf2Vec_pointwise_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 3 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 3 y t‖ ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    ‖y (t + 2 * h) - (4 / 3 : ℝ) • y (t + h)
        + (1 / 3 : ℝ) • y t
        - h • ((2 / 3 : ℝ) • deriv y (t + 2 * h))‖
      ≤ (3 : ℝ) * M * h ^ 3 := by
  have h2h : 0 ≤ 2 * h := by linarith
  -- R_y(h).
  have hR1 := y_third_order_taylor_remainder_vec hy hbnd ht hth hh
  -- R_y(2h).
  have hR2 := y_third_order_taylor_remainder_vec hy hbnd ht ht2h h2h
  -- R_y'(2h).
  have hR3 := derivY_second_order_taylor_remainder_vec hy hbnd ht ht2h h2h
  set y0 : E := y t with hy0_def
  set y1 : E := y (t + h) with hy1_def
  set y2 : E := y (t + 2 * h) with hy2_def
  set d0 : E := deriv y t with hd0_def
  set d2 : E := deriv y (t + 2 * h) with hd2_def
  set dd : E := iteratedDeriv 2 y t with hdd_def
  -- Algebraic identity: BDF2 LTE =
  -- R_y(2h) - (4/3) R_y(h) - (2h/3) R_y'(2h).
  have hLTE_eq :
      y2 - (4 / 3 : ℝ) • y1 + (1 / 3 : ℝ) • y0
          - h • ((2 / 3 : ℝ) • d2)
        = (y2 - y0 - (2 * h) • d0 - ((2 * h) ^ 2 / 2) • dd)
          - (4 / 3 : ℝ) • (y1 - y0 - h • d0 - (h ^ 2 / 2) • dd)
          - (2 * h / 3 : ℝ) • (d2 - d0 - (2 * h) • dd) := by
    module
  rw [hLTE_eq]
  set A : E := y2 - y0 - (2 * h) • d0 - ((2 * h) ^ 2 / 2) • dd with hA_def
  set B : E := y1 - y0 - h • d0 - (h ^ 2 / 2) • dd with hB_def
  set C : E := d2 - d0 - (2 * h) • dd with hC_def
  have h2h3_nn : (0 : ℝ) ≤ 2 * h / 3 := by linarith
  have htri : ‖A - (4 / 3 : ℝ) • B - (2 * h / 3 : ℝ) • C‖
      ≤ ‖A‖ + (4 / 3 : ℝ) * ‖B‖ + (2 * h / 3 : ℝ) * ‖C‖ := by
    have h1 :
        ‖A - (4 / 3 : ℝ) • B - (2 * h / 3 : ℝ) • C‖
          ≤ ‖A - (4 / 3 : ℝ) • B‖ + ‖(2 * h / 3 : ℝ) • C‖ :=
      norm_sub_le _ _
    have h2 : ‖A - (4 / 3 : ℝ) • B‖
          ≤ ‖A‖ + ‖(4 / 3 : ℝ) • B‖ :=
      norm_sub_le _ _
    have h2h3_abs : ‖(2 * h / 3 : ℝ) • C‖ = (2 * h / 3 : ℝ) * ‖C‖ := by
      rw [norm_smul, Real.norm_of_nonneg h2h3_nn]
    have h43_abs : ‖(4 / 3 : ℝ) • B‖ = (4 / 3 : ℝ) * ‖B‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3)]
    linarith [h1, h2, h2h3_abs.le, h2h3_abs.ge, h43_abs.le, h43_abs.ge]
  -- Apply the three remainder bounds.
  have hA_bd : ‖A‖ ≤ M / 6 * (2 * h) ^ 3 := hR2
  have hB_bd : ‖B‖ ≤ M / 6 * h ^ 3 := hR1
  have hC_bd : ‖C‖ ≤ M / 2 * (2 * h) ^ 2 := hR3
  have h43B_bd : (4 / 3 : ℝ) * ‖B‖ ≤ (4 / 3 : ℝ) * (M / 6 * h ^ 3) :=
    mul_le_mul_of_nonneg_left hB_bd (by norm_num)
  have h2h3C_bd : (2 * h / 3 : ℝ) * ‖C‖
      ≤ (2 * h / 3 : ℝ) * (M / 2 * (2 * h) ^ 2) :=
    mul_le_mul_of_nonneg_left hC_bd h2h3_nn
  have hbound_alg :
      M / 6 * (2 * h) ^ 3 + (4 / 3 : ℝ) * (M / 6 * h ^ 3)
        + (2 * h / 3 : ℝ) * (M / 2 * (2 * h) ^ 2)
        = (26 / 9 : ℝ) * M * h ^ 3 := by ring
  have hMnn : 0 ≤ M := (norm_nonneg _).trans (hbnd t ht)
  have hh3_nn : 0 ≤ h ^ 3 := by positivity
  have hslack : (26 / 9 : ℝ) * M * h ^ 3 ≤ (3 : ℝ) * M * h ^ 3 := by
    have hcoef : (26 / 9 : ℝ) ≤ 3 := by norm_num
    nlinarith [hMnn, hh3_nn]
  linarith [htri, hA_bd, h43B_bd, h2h3C_bd, hbound_alg.le, hbound_alg.ge,
    hslack]

/-- Uniform bound on the BDF2 vector one-step truncation residual on a finite
horizon, given a `C^3` exact solution. -/
theorem bdf2Vec_local_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 3 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 2) * h ≤ T →
        ‖bdf2VecResidual h (t₀ + (n : ℝ) * h) y‖
          ≤ C * h ^ 3 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_three_bounded_on_Icc_vec hy t₀ (t₀ + T + 1)
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
  show ‖bdf2VecResidual h t y‖ ≤ 3 * M * h ^ 3
  unfold bdf2VecResidual
  exact bdf2Vec_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem hh.le

/-- The Lyapunov-sum one-step recurrence for BDF2 vectors. -/
theorem bdf2Vec_one_step_error_pair_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (2 / 3 : ℝ) * h * L ≤ 1 / 4)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsBDF2TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    ‖(3 / 2 : ℝ) •
          (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))
        - (1 / 2 : ℝ) •
          (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))‖
      + ‖(3 / 2 : ℝ) •
            (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
          - (3 / 2 : ℝ) •
            (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))‖
      ≤ (1 + h * (4 * L))
          * (‖(3 / 2 : ℝ) •
                (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
              - (1 / 2 : ℝ) •
                (yseq n - y (t₀ + (n : ℝ) * h))‖
            + ‖(3 / 2 : ℝ) •
                  (yseq n - y (t₀ + (n : ℝ) * h))
                - (3 / 2 : ℝ) •
                  (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))‖)
        + 6 * ‖bdf2VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set en : E := yseq n - y (t₀ + (n : ℝ) * h) with hen_def
  set en1 : E := yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h) with hen1_def
  set en2 : E := yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h) with hen2_def
  set τabs : ℝ := ‖bdf2VecResidual h (t₀ + (n : ℝ) * h) y‖
    with hτabs_def
  -- Forcing decomposition:
  -- ‖e_{n+2} - (4/3)e_{n+1} + (1/3)e_n‖
  -- ≤ (2/3)·h·L·‖e_{n+2}‖ + ‖τ‖.
  have hlip := bdf2Vec_one_step_lipschitz (E := E) (h := h) (L := L)
    hh hf t₀ hy y hyf n
  have hlip' :
      ‖en2 - (4 / 3 : ℝ) • en1 + (1 / 3 : ℝ) • en‖
        ≤ (2 / 3 : ℝ) * h * L * ‖en2‖ + τabs := by
    simpa [hen_def, hen1_def, hen2_def, hτabs_def] using hlip
  -- Set up u, v, W.
  set u : E := (3 / 2 : ℝ) • en1 - (1 / 2 : ℝ) • en with hu_def
  set v : E := (3 / 2 : ℝ) • en - (3 / 2 : ℝ) • en1 with hv_def
  set u' : E := (3 / 2 : ℝ) • en2 - (1 / 2 : ℝ) • en1 with hu'_def
  set v' : E := (3 / 2 : ℝ) • en1 - (3 / 2 : ℝ) • en2 with hv'_def
  set ψ : E := en2 - (4 / 3 : ℝ) • en1 + (1 / 3 : ℝ) • en with hψ_def
  have hu_rec : u' = u + (3 / 2 : ℝ) • ψ := by
    show (3 / 2 : ℝ) • en2 - (1 / 2 : ℝ) • en1
        = ((3 / 2 : ℝ) • en1 - (1 / 2 : ℝ) • en)
          + (3 / 2 : ℝ) •
              (en2 - (4 / 3 : ℝ) • en1 + (1 / 3 : ℝ) • en)
    module
  have hv_rec : v' = (1 / 3 : ℝ) • v - (3 / 2 : ℝ) • ψ := by
    show (3 / 2 : ℝ) • en1 - (3 / 2 : ℝ) • en2
        = (1 / 3 : ℝ) • ((3 / 2 : ℝ) • en - (3 / 2 : ℝ) • en1)
          - (3 / 2 : ℝ) •
              (en2 - (4 / 3 : ℝ) • en1 + (1 / 3 : ℝ) • en)
    simp only [smul_sub, smul_smul]
    abel_nf
    module
  have hψ_bd : ‖ψ‖ ≤ (2 / 3 : ℝ) * h * L * ‖en2‖ + τabs := hlip'
  have hen2_uv : en2 = u' + (1 / 3 : ℝ) • v' := by
    show en2
        = ((3 / 2 : ℝ) • en2 - (1 / 2 : ℝ) • en1)
          + (1 / 3 : ℝ) • ((3 / 2 : ℝ) • en1 - (3 / 2 : ℝ) • en2)
    simp only [smul_sub, smul_smul]
    abel_nf
    module
  have hen2_recombined :
      en2 = u + (1 / 9 : ℝ) • v + ψ := by
    rw [hen2_uv, hu_rec, hv_rec]
    simp only [smul_sub, smul_smul]
    abel_nf
    module
  have hen2_bd1 : ‖en2‖ ≤ ‖u‖ + (1 / 9 : ℝ) * ‖v‖ + ‖ψ‖ := by
    rw [hen2_recombined]
    calc ‖u + (1 / 9 : ℝ) • v + ψ‖
        ≤ ‖u + (1 / 9 : ℝ) • v‖ + ‖ψ‖ := norm_add_le _ _
      _ ≤ ‖u‖ + ‖(1 / 9 : ℝ) • v‖ + ‖ψ‖ := by
          linarith [norm_add_le u ((1 / 9 : ℝ) • v)]
      _ = ‖u‖ + (1 / 9 : ℝ) * ‖v‖ + ‖ψ‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 9)]
  have hu_nn : 0 ≤ ‖u‖ := norm_nonneg _
  have hv_nn : 0 ≤ ‖v‖ := norm_nonneg _
  have hψ_nn : 0 ≤ ‖ψ‖ := norm_nonneg _
  have hτ_nn : 0 ≤ τabs := norm_nonneg _
  have hhL_nn : 0 ≤ h * L := mul_nonneg hh hL
  have h23hL_nn : 0 ≤ (2 / 3 : ℝ) * h * L := by positivity
  -- ‖ψ‖ ≤ (2/3)hL · (‖u‖ + (1/9)‖v‖ + ‖ψ‖) + τabs.
  have hψ_step : ‖ψ‖
      ≤ (2 / 3 : ℝ) * h * L * (‖u‖ + (1 / 9 : ℝ) * ‖v‖ + ‖ψ‖) + τabs := by
    have := mul_le_mul_of_nonneg_left hen2_bd1 h23hL_nn
    linarith [hψ_bd]
  have h_one_minus_ge : (3 / 4 : ℝ) ≤ 1 - (2 / 3 : ℝ) * h * L := by
    linarith [hsmall]
  have hψ_solved :
      (1 - (2 / 3 : ℝ) * h * L) * ‖ψ‖
        ≤ (2 / 3 : ℝ) * h * L * (‖u‖ + (1 / 9 : ℝ) * ‖v‖) + τabs := by
    have : (1 - (2 / 3 : ℝ) * h * L) * ‖ψ‖
        = ‖ψ‖ - (2 / 3 : ℝ) * h * L * ‖ψ‖ := by ring
    linarith [hψ_step]
  have hψ_final :
      ‖ψ‖ ≤ (8 / 9 : ℝ) * h * L * ‖u‖
            + (8 / 81 : ℝ) * h * L * ‖v‖ + (4 / 3 : ℝ) * τabs := by
    have h_lhs : (3 / 4 : ℝ) * ‖ψ‖
        ≤ (1 - (2 / 3 : ℝ) * h * L) * ‖ψ‖ :=
      mul_le_mul_of_nonneg_right h_one_minus_ge hψ_nn
    have hcomb := le_trans h_lhs hψ_solved
    have hexp : (2 / 3 : ℝ) * h * L * (‖u‖ + (1 / 9 : ℝ) * ‖v‖)
        = (2 / 3 : ℝ) * h * L * ‖u‖
            + (2 / 3 : ℝ) * h * L * (1 / 9 : ℝ) * ‖v‖ := by ring
    have hbase : (3 / 4 : ℝ) * ‖ψ‖
        ≤ (2 / 3 : ℝ) * h * L * ‖u‖
          + (2 / 3 : ℝ) * h * L * (1 / 9 : ℝ) * ‖v‖ + τabs := by
      linarith [hcomb, hexp.le, hexp.ge]
    have hmul := mul_le_mul_of_nonneg_left hbase
      (by norm_num : (0 : ℝ) ≤ 4 / 3)
    have hLHS : (4 / 3 : ℝ) * ((3 / 4 : ℝ) * ‖ψ‖) = ‖ψ‖ := by ring
    have hRHS : (4 / 3 : ℝ) * ((2 / 3 : ℝ) * h * L * ‖u‖
          + (2 / 3 : ℝ) * h * L * (1 / 9 : ℝ) * ‖v‖ + τabs)
        = (8 / 9 : ℝ) * h * L * ‖u‖
          + (8 / 81 : ℝ) * h * L * ‖v‖ + (4 / 3 : ℝ) * τabs := by ring
    linarith [hmul, hLHS.le, hLHS.ge, hRHS.le, hRHS.ge]
  have hu'_bd : ‖u'‖ ≤ ‖u‖ + (3 / 2 : ℝ) * ‖ψ‖ := by
    rw [hu_rec]
    calc ‖u + (3 / 2 : ℝ) • ψ‖
        ≤ ‖u‖ + ‖(3 / 2 : ℝ) • ψ‖ := norm_add_le _ _
      _ = ‖u‖ + (3 / 2 : ℝ) * ‖ψ‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  have hv'_bd : ‖v'‖ ≤ (1 / 3 : ℝ) * ‖v‖ + (3 / 2 : ℝ) * ‖ψ‖ := by
    rw [hv_rec]
    calc ‖(1 / 3 : ℝ) • v - (3 / 2 : ℝ) • ψ‖
        ≤ ‖(1 / 3 : ℝ) • v‖ + ‖(3 / 2 : ℝ) • ψ‖ := norm_sub_le _ _
      _ = (1 / 3 : ℝ) * ‖v‖ + (3 / 2 : ℝ) * ‖ψ‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3),
              norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  have h_show : ‖u'‖ + ‖v'‖
      ≤ (1 + h * (4 * L)) * (‖u‖ + ‖v‖) + 6 * τabs := by
    have hsum : ‖u'‖ + ‖v'‖
        ≤ ‖u‖ + (1 / 3 : ℝ) * ‖v‖ + 3 * ‖ψ‖ := by
      linarith [hu'_bd, hv'_bd]
    have hψ3 : 3 * ‖ψ‖
        ≤ (8 / 3 : ℝ) * h * L * ‖u‖
          + (8 / 27 : ℝ) * h * L * ‖v‖ + 4 * τabs := by
      have := mul_le_mul_of_nonneg_left hψ_final (by norm_num : (0 : ℝ) ≤ 3)
      linarith [this]
    have hgrowth_u : ‖u‖ + (8 / 3 : ℝ) * h * L * ‖u‖
        ≤ (1 + h * (4 * L)) * ‖u‖ := by
      have hdiff_eq : (1 + h * (4 * L)) * ‖u‖
          - (‖u‖ + (8 / 3 : ℝ) * h * L * ‖u‖)
          = (4 / 3 : ℝ) * h * L * ‖u‖ := by ring
      have hdiff_nn : 0 ≤ (4 / 3 : ℝ) * h * L * ‖u‖ :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hh) hL) hu_nn
      linarith [hdiff_nn, hdiff_eq.le, hdiff_eq.ge]
    have hgrowth_v : (1 / 3 : ℝ) * ‖v‖ + (8 / 27 : ℝ) * h * L * ‖v‖
        ≤ (1 + h * (4 * L)) * ‖v‖ := by
      have hdiff_eq :
          (1 + h * (4 * L)) * ‖v‖
            - ((1 / 3 : ℝ) * ‖v‖ + (8 / 27 : ℝ) * h * L * ‖v‖)
          = (2 / 3 : ℝ) * ‖v‖ + (100 / 27 : ℝ) * h * L * ‖v‖ := by ring
      have h1_nn : 0 ≤ (2 / 3 : ℝ) * ‖v‖ := mul_nonneg (by norm_num) hv_nn
      have h2_nn : 0 ≤ (100 / 27 : ℝ) * h * L * ‖v‖ :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hh) hL) hv_nn
      linarith [h1_nn, h2_nn, hdiff_eq.le, hdiff_eq.ge]
    have h_split :
        (1 + h * (4 * L)) * (‖u‖ + ‖v‖)
          = (1 + h * (4 * L)) * ‖u‖
              + (1 + h * (4 * L)) * ‖v‖ := by ring
    have h_step1 : ‖u'‖ + ‖v'‖
        ≤ ‖u‖ + (1 / 3 : ℝ) * ‖v‖
          + ((8 / 3 : ℝ) * h * L * ‖u‖
              + (8 / 27 : ℝ) * h * L * ‖v‖ + 4 * τabs) := by
      linarith only [hsum, hψ3]
    have h_step2 : ‖u‖ + (1 / 3 : ℝ) * ‖v‖
          + ((8 / 3 : ℝ) * h * L * ‖u‖
              + (8 / 27 : ℝ) * h * L * ‖v‖ + 4 * τabs)
        = (‖u‖ + (8 / 3 : ℝ) * h * L * ‖u‖)
          + ((1 / 3 : ℝ) * ‖v‖ + (8 / 27 : ℝ) * h * L * ‖v‖)
          + 4 * τabs := by ring
    have h_step3 : (‖u‖ + (8 / 3 : ℝ) * h * L * ‖u‖)
          + ((1 / 3 : ℝ) * ‖v‖ + (8 / 27 : ℝ) * h * L * ‖v‖)
          + 4 * τabs
        ≤ (1 + h * (4 * L)) * ‖u‖
            + (1 + h * (4 * L)) * ‖v‖ + 6 * τabs := by
      linarith only [hgrowth_u, hgrowth_v, hτ_nn]
    linarith only [h_step1, h_step2.le, h_step2.ge, h_step3,
      h_split.le, h_split.ge]
  show ‖u'‖ + ‖v'‖ ≤ (1 + h * (4 * L)) * (‖u‖ + ‖v‖) + 6 * τabs
  exact h_show

/-- Headline BDF2 vector global error bound. -/
theorem bdf2Vec_global_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy_smooth : ContDiff ℝ 3 y)
    {f : ℝ → E → E} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      (2 / 3 : ℝ) * h * L ≤ 1 / 4 →
      ∀ {yseq : ℕ → E} {ε₀ : ℝ},
      IsBDF2TrajectoryVec h f t₀ yseq →
      0 ≤ ε₀ →
      ‖yseq 0 - y t₀‖ ≤ ε₀ →
      ‖yseq 1 - y (t₀ + h)‖ ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 1) * h ≤ T →
      ‖yseq N - y (t₀ + (N : ℝ) * h)‖
        ≤ 5 * Real.exp ((4 * L) * T) * ε₀ + K * h ^ 2 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    bdf2Vec_local_residual_bound hy_smooth t₀ T hT
  refine ⟨T * Real.exp ((4 * L) * T) * (6 * C), δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  intro h hh hδ_le hsmall yseq ε₀ hy_traj hε₀ he0_bd he1_bd N hNh
  -- Define the Lyapunov sum sequence W_n.
  set W : ℕ → ℝ := fun k =>
    ‖(3 / 2 : ℝ) •
          (yseq (k + 1) - y (t₀ + ((k : ℝ) + 1) * h))
        - (1 / 2 : ℝ) • (yseq k - y (t₀ + (k : ℝ) * h))‖
      + ‖(3 / 2 : ℝ) • (yseq k - y (t₀ + (k : ℝ) * h))
          - (3 / 2 : ℝ) •
            (yseq (k + 1) - y (t₀ + ((k : ℝ) + 1) * h))‖
    with hW_def
  have hW_nn : ∀ k, 0 ≤ W k := fun k =>
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  -- Initial bound: W 0 ≤ 5 ε₀.
  have hW0_le : W 0 ≤ 5 * ε₀ := by
    have he0 : ‖yseq 0 - y t₀‖ ≤ ε₀ := by simpa using he0_bd
    have he1 : ‖yseq 1 - y (t₀ + h)‖ ≤ ε₀ := he1_bd
    have hcast0r : t₀ + ((0 : ℕ) : ℝ) * h = t₀ := by push_cast; ring
    have hcast1r : t₀ + (((0 : ℕ) : ℝ) + 1) * h = t₀ + h := by push_cast; ring
    set a : E := yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h) with ha_def
    set b : E := yseq 1 - y (t₀ + (((0 : ℕ) : ℝ) + 1) * h) with hb_def
    have ha_bd : ‖a‖ ≤ ε₀ := by
      show ‖yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hcast0r]
      exact he0
    have hb_bd : ‖b‖ ≤ ε₀ := by
      show ‖yseq 1 - y (t₀ + (((0 : ℕ) : ℝ) + 1) * h)‖ ≤ ε₀
      rw [hcast1r]
      exact he1
    show ‖(3 / 2 : ℝ) • b - (1 / 2 : ℝ) • a‖
        + ‖(3 / 2 : ℝ) • a - (3 / 2 : ℝ) • b‖ ≤ 5 * ε₀
    have h1_abs : ‖(3 / 2 : ℝ) • b - (1 / 2 : ℝ) • a‖ ≤ 2 * ε₀ := by
      calc ‖(3 / 2 : ℝ) • b - (1 / 2 : ℝ) • a‖
          ≤ ‖(3 / 2 : ℝ) • b‖ + ‖(1 / 2 : ℝ) • a‖ := norm_sub_le _ _
        _ = (3 / 2 : ℝ) * ‖b‖ + (1 / 2 : ℝ) * ‖a‖ := by
            rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2),
                norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        _ ≤ (3 / 2 : ℝ) * ε₀ + (1 / 2 : ℝ) * ε₀ := by
            linarith [ha_bd, hb_bd]
        _ = 2 * ε₀ := by ring
    have h2_abs : ‖(3 / 2 : ℝ) • a - (3 / 2 : ℝ) • b‖ ≤ 3 * ε₀ := by
      calc ‖(3 / 2 : ℝ) • a - (3 / 2 : ℝ) • b‖
          ≤ ‖(3 / 2 : ℝ) • a‖ + ‖(3 / 2 : ℝ) • b‖ := norm_sub_le _ _
        _ = (3 / 2 : ℝ) * ‖a‖ + (3 / 2 : ℝ) * ‖b‖ := by
            rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2),
                norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
        _ ≤ (3 / 2 : ℝ) * ε₀ + (3 / 2 : ℝ) * ε₀ := by
            linarith [ha_bd, hb_bd]
        _ = 3 * ε₀ := by ring
    linarith [h1_abs, h2_abs]
  have h4L_nn : (0 : ℝ) ≤ 4 * L := by linarith
  -- General step:
  -- W (n+1) ≤ (1 + h*(4L)) * W n + 6*C*h^3.
  have hstep_general : ∀ n : ℕ, ((n : ℝ) + 2) * h ≤ T →
      W (n + 1) ≤ (1 + h * (4 * L)) * W n + (6 * C) * h ^ 3 := by
    intro n hnh_le
    have honestep := bdf2Vec_one_step_error_pair_bound
      (E := E) (h := h) (L := L) hh.le hL hsmall hf t₀ hy_traj y hyf n
    have hres := hresidual hh hδ_le n hnh_le
    have hcast1' : t₀ + ((n + 1 : ℕ) : ℝ) * h
        = t₀ + ((n : ℝ) + 1) * h := by push_cast; ring
    have hcast2' : t₀ + (((n + 1 : ℕ) : ℝ) + 1) * h
        = t₀ + ((n : ℝ) + 2) * h := by push_cast; ring
    have heq_W_n1 : W (n + 1)
        = ‖(3 / 2 : ℝ) •
              (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))
              - (1 / 2 : ℝ) •
                (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))‖
          + ‖(3 / 2 : ℝ) •
                (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
              - (3 / 2 : ℝ) •
                (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))‖ := by
      show ‖(3/2 : ℝ) •
              (yseq (n + 1 + 1)
                - y (t₀ + (((n + 1 : ℕ) : ℝ) + 1) * h))
            - (1/2 : ℝ) •
              (yseq (n + 1) - y (t₀ + ((n + 1 : ℕ) : ℝ) * h))‖
          + ‖(3/2 : ℝ) •
              (yseq (n + 1) - y (t₀ + ((n + 1 : ℕ) : ℝ) * h))
            - (3/2 : ℝ) •
              (yseq (n + 1 + 1)
                - y (t₀ + (((n + 1 : ℕ) : ℝ) + 1) * h))‖ = _
      rw [hcast1', hcast2']
    rw [heq_W_n1]
    have h6τ : 6 * ‖bdf2VecResidual h
        (t₀ + (n : ℝ) * h) y‖ ≤ (6 * C) * h ^ 3 := by
      have h6nn : (0 : ℝ) ≤ 6 := by norm_num
      have := mul_le_mul_of_nonneg_left hres h6nn
      linarith
    show ‖(3 / 2 : ℝ) •
            (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))
            - (1 / 2 : ℝ) •
              (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))‖
          + ‖(3 / 2 : ℝ) •
              (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
              - (3 / 2 : ℝ) •
                (yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h))‖
        ≤ (1 + h * (4 * L)) * W n + 6 * C * h ^ 3
    have hWn_eq : W n
        = ‖(3 / 2 : ℝ) •
              (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))
              - (1 / 2 : ℝ) •
                (yseq n - y (t₀ + (n : ℝ) * h))‖
          + ‖(3 / 2 : ℝ) •
                (yseq n - y (t₀ + (n : ℝ) * h))
              - (3 / 2 : ℝ) •
                (yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h))‖ := rfl
    rw [hWn_eq]
    linarith [honestep, h6τ]
  rcases N with _ | N'
  · -- N = 0.
    show ‖yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)‖
        ≤ 5 * Real.exp ((4 * L) * T) * ε₀
            + T * Real.exp ((4 * L) * T) * (6 * C) * h ^ 2
    have hbase : ‖yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)‖
        ≤ ε₀ := by simpa using he0_bd
    have hexp_ge : (1 : ℝ) ≤ Real.exp ((4 * L) * T) :=
      Real.one_le_exp_iff.mpr (by positivity)
    have hKnn : 0 ≤ T * Real.exp ((4 * L) * T) * (6 * C) :=
      mul_nonneg (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
    have hh2_nn : 0 ≤ h ^ 2 := by positivity
    nlinarith [hbase, hexp_ge, hKnn, hh2_nn, hε₀]
  · have hN_hyp : ((N' : ℝ) + 1 + 1) * h ≤ T := by
      have hcast : (((N' + 1 : ℕ) : ℝ) + 1) = (N' : ℝ) + 1 + 1 := by
        push_cast
        ring
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
    have hexp_nn : 0 ≤ Real.exp ((4 * L) * T) := Real.exp_nonneg _
    have h_chain :
        Real.exp ((4 * L) * T) * W 0
          ≤ Real.exp ((4 * L) * T) * (5 * ε₀) :=
      mul_le_mul_of_nonneg_left hW0_le hexp_nn
    -- Bound ‖e_{k+1}‖ by W k.
    have hek1_le_W : ∀ k,
        ‖yseq (k + 1) - y (t₀ + ((k : ℝ) + 1) * h)‖ ≤ W k := by
      intro k
      set e0 : E := yseq k - y (t₀ + (k : ℝ) * h)
      set e1 : E := yseq (k + 1) - y (t₀ + ((k : ℝ) + 1) * h)
      have hid : e1 = ((3 / 2 : ℝ) • e1 - (1 / 2 : ℝ) • e0)
          + (1 / 3 : ℝ) • ((3 / 2 : ℝ) • e0 - (3 / 2 : ℝ) • e1) := by
        simp only [smul_sub, smul_smul]
        abel_nf
        module
      calc ‖e1‖ = ‖((3 / 2 : ℝ) • e1 - (1 / 2 : ℝ) • e0)
            + (1 / 3 : ℝ) • ((3 / 2 : ℝ) • e0 - (3 / 2 : ℝ) • e1)‖ := by
              conv_lhs => rw [hid]
        _ ≤ ‖(3 / 2 : ℝ) • e1 - (1 / 2 : ℝ) • e0‖
            + ‖(1 / 3 : ℝ) • ((3 / 2 : ℝ) • e0 - (3 / 2 : ℝ) • e1)‖ :=
              norm_add_le _ _
        _ = ‖(3 / 2 : ℝ) • e1 - (1 / 2 : ℝ) • e0‖
            + (1 / 3 : ℝ) * ‖(3 / 2 : ℝ) • e0 - (3 / 2 : ℝ) • e1‖ := by
              rw [show ‖(1 / 3 : ℝ) • ((3 / 2 : ℝ) • e0 - (3 / 2 : ℝ) • e1)‖
                = (1 / 3 : ℝ) * ‖(3 / 2 : ℝ) • e0 - (3 / 2 : ℝ) • e1‖ from
                by rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3)]]
        _ ≤ ‖(3 / 2 : ℝ) • e1 - (1 / 2 : ℝ) • e0‖
            + ‖(3 / 2 : ℝ) • e0 - (3 / 2 : ℝ) • e1‖ := by
              have hnorm_nn : 0 ≤ ‖(3 / 2 : ℝ) • e0 - (3 / 2 : ℝ) • e1‖ :=
                norm_nonneg _
              nlinarith [hnorm_nn]
        _ = W k := rfl
    show ‖yseq (N' + 1) - y (t₀ + ((N' + 1 : ℕ) : ℝ) * h)‖
        ≤ 5 * Real.exp ((4 * L) * T) * ε₀
            + T * Real.exp ((4 * L) * T) * (6 * C) * h ^ 2
    have hN'eq : ((N' + 1 : ℕ) : ℝ) = (N' : ℝ) + 1 := by push_cast; ring
    rw [hN'eq]
    have heN' := hek1_le_W N'
    linarith [heN', hgronwall, h_chain]

end LMM
