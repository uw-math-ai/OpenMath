import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMAB4Convergence

/-! ## Adams--Moulton 3-step Vector Quantitative Convergence Chain (Iserles §1.2)

Vector-valued analogue of the AM3 scalar quantitative convergence chain in
`OpenMath/LMMAM3Convergence.lean`. The implicit AM3 update is parameterised
by a supplied trajectory; existence of such a trajectory is a separate
fixed-point problem and is not part of this chain.
-/

namespace LMM

/-- AM3 vector trajectory predicate:
`y_{n+3} = y_{n+2} + h • (9/24 f_{n+3} + 19/24 f_{n+2}
  - 5/24 f_{n+1} + 1/24 f_n)`.

The new value appears inside `f`, so existence of such a trajectory is a
separate fixed-point problem. -/
structure IsAM3TrajectoryVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y : ℕ → E) : Prop where
  recurrence :
    ∀ n : ℕ, y (n + 3)
      = y (n + 2)
        + h • ((9 / 24 : ℝ) • f (t₀ + ((n : ℝ) + 3) * h) (y (n + 3))
             + (19 / 24 : ℝ) • f (t₀ + ((n : ℝ) + 2) * h) (y (n + 2))
             - (5 / 24 : ℝ) • f (t₀ + ((n : ℝ) + 1) * h) (y (n + 1))
             + (1 / 24 : ℝ) • f (t₀ + (n : ℝ) * h) (y n))

/-- Textbook AM3 vector residual: the value of the local truncation error of
the AM3 method on a smooth vector trajectory `(y, deriv y)`. -/
noncomputable def am3VecResidual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) : E :=
  y (t + 3 * h) - y (t + 2 * h)
    - h • ((9 / 24 : ℝ) • deriv y (t + 3 * h)
          + (19 / 24 : ℝ) • deriv y (t + 2 * h)
          - (5 / 24 : ℝ) • deriv y (t + h)
          + (1 / 24 : ℝ) • deriv y t)

/-- The vector AM3 residual unfolds to the textbook form. -/
theorem am3Vec_localTruncationError_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) :
    am3VecResidual h t y
      = y (t + 3 * h) - y (t + 2 * h)
          - h • ((9 / 24 : ℝ) • deriv y (t + 3 * h)
                + (19 / 24 : ℝ) • deriv y (t + 2 * h)
                - (5 / 24 : ℝ) • deriv y (t + h)
                + (1 / 24 : ℝ) • deriv y t) := by
  rfl

/-- One-step AM3 Lipschitz inequality before dividing by the implicit
new-point factor. -/
theorem am3Vec_one_step_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h)
    (hsmall : (9 / 24 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM3TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    (1 - (9 / 24 : ℝ) * h * L)
        * ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖
      ≤ ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖
        + (19 / 24 : ℝ) * h * L
            * ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖
        + (5 / 24 : ℝ) * h * L
            * ‖yseq (n + 1)
                - y (t₀ + ((n : ℝ) + 1) * h)‖
        + (1 / 24 : ℝ) * h * L
            * ‖yseq n - y (t₀ + (n : ℝ) * h)‖
        + ‖am3VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set yn : E := yseq n with hyn_def
  set yn1 : E := yseq (n + 1) with hyn1_def
  set yn2 : E := yseq (n + 2) with hyn2_def
  set yn3 : E := yseq (n + 3) with hyn3_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set tn3 : ℝ := t₀ + ((n : ℝ) + 3) * h with htn3_def
  set zn : E := y tn with hzn_def
  set zn1 : E := y tn1 with hzn1_def
  set zn2 : E := y tn2 with hzn2_def
  set zn3 : E := y tn3 with hzn3_def
  set τ : E := am3VecResidual h tn y with hτ_def
  have _hsmall_record : (9 / 24 : ℝ) * h * L ≤ 1 / 2 := hsmall
  -- AM3 step formula for the supplied implicit trajectory.
  have hstep : yn3
      = yn2
        + h • ((9 / 24 : ℝ) • f tn3 yn3
             + (19 / 24 : ℝ) • f tn2 yn2
             - (5 / 24 : ℝ) • f tn1 yn1
             + (1 / 24 : ℝ) • f tn yn) := by
    simpa [hyn3_def, hyn2_def, hyn1_def, hyn_def, htn3_def, htn2_def,
      htn1_def, htn_def] using hy.recurrence n
  -- Local truncation residual at `tn`, expressed via `f` along the trajectory.
  have htn1_h : tn + h = tn1 := by
    simp [htn_def, htn1_def]
    ring
  have htn_2h : tn + 2 * h = tn2 := by
    simp [htn_def, htn2_def]
    ring
  have htn_3h : tn + 3 * h = tn3 := by
    simp [htn_def, htn3_def]
    ring
  have hτ_eq : τ = zn3 - zn2
      - h • ((9 / 24 : ℝ) • f tn3 zn3
             + (19 / 24 : ℝ) • f tn2 zn2
             - (5 / 24 : ℝ) • f tn1 zn1
             + (1 / 24 : ℝ) • f tn zn) := by
    show am3VecResidual h tn y = _
    unfold am3VecResidual
    rw [htn1_h, htn_2h, htn_3h, hyf tn3, hyf tn2, hyf tn1, hyf tn]
  -- Algebraic decomposition of the implicit global-error increment.
  have halg : yn3 - zn3
      = (yn2 - zn2)
        + h • ((9 / 24 : ℝ) • (f tn3 yn3 - f tn3 zn3))
        + h • ((19 / 24 : ℝ) • (f tn2 yn2 - f tn2 zn2))
        - h • ((5 / 24 : ℝ) • (f tn1 yn1 - f tn1 zn1))
        + h • ((1 / 24 : ℝ) • (f tn yn - f tn zn))
        - τ := by
    conv_lhs => rw [hstep]
    rw [hτ_eq]
    simp only [smul_sub, smul_add]
    abel
  -- Lipschitz bounds.
  have hLip3 : ‖f tn3 yn3 - f tn3 zn3‖ ≤ L * ‖yn3 - zn3‖ := hf tn3 yn3 zn3
  have hLip2 : ‖f tn2 yn2 - f tn2 zn2‖ ≤ L * ‖yn2 - zn2‖ := hf tn2 yn2 zn2
  have hLip1 : ‖f tn1 yn1 - f tn1 zn1‖ ≤ L * ‖yn1 - zn1‖ := hf tn1 yn1 zn1
  have hLip0 : ‖f tn yn - f tn zn‖ ≤ L * ‖yn - zn‖ := hf tn yn zn
  have h9_nn : (0 : ℝ) ≤ 9 / 24 := by norm_num
  have h19_nn : (0 : ℝ) ≤ 19 / 24 := by norm_num
  have h5_nn : (0 : ℝ) ≤ 5 / 24 := by norm_num
  have h1_nn : (0 : ℝ) ≤ 1 / 24 := by norm_num
  set A : E := yn2 - zn2 with hA_def
  set B9 : E := h • ((9 / 24 : ℝ) • (f tn3 yn3 - f tn3 zn3)) with hB9_def
  set B19 : E := h • ((19 / 24 : ℝ) • (f tn2 yn2 - f tn2 zn2)) with hB19_def
  set B5 : E := h • ((5 / 24 : ℝ) • (f tn1 yn1 - f tn1 zn1)) with hB5_def
  set B1 : E := h • ((1 / 24 : ℝ) • (f tn yn - f tn zn)) with hB1_def
  have halg' : yn3 - zn3 = A + B9 + B19 - B5 + B1 - τ := by
    simpa [hA_def, hB9_def, hB19_def, hB5_def, hB1_def] using halg
  -- Norm of each smul term.
  have h9_norm :
      ‖B9‖
        ≤ (9 / 24 : ℝ) * h * L * ‖yn3 - zn3‖ := by
    rw [hB9_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h9_nn]
    have : h * ((9 / 24 : ℝ) * ‖f tn3 yn3 - f tn3 zn3‖)
        ≤ h * ((9 / 24 : ℝ) * (L * ‖yn3 - zn3‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip3 h9_nn
    calc h * ((9 / 24 : ℝ) * ‖f tn3 yn3 - f tn3 zn3‖)
        ≤ h * ((9 / 24 : ℝ) * (L * ‖yn3 - zn3‖)) := this
      _ = (9 / 24 : ℝ) * h * L * ‖yn3 - zn3‖ := by ring
  have h19_norm :
      ‖B19‖
        ≤ (19 / 24 : ℝ) * h * L * ‖yn2 - zn2‖ := by
    rw [hB19_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h19_nn]
    have : h * ((19 / 24 : ℝ) * ‖f tn2 yn2 - f tn2 zn2‖)
        ≤ h * ((19 / 24 : ℝ) * (L * ‖yn2 - zn2‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip2 h19_nn
    calc h * ((19 / 24 : ℝ) * ‖f tn2 yn2 - f tn2 zn2‖)
        ≤ h * ((19 / 24 : ℝ) * (L * ‖yn2 - zn2‖)) := this
      _ = (19 / 24 : ℝ) * h * L * ‖yn2 - zn2‖ := by ring
  have h5_norm :
      ‖B5‖
        ≤ (5 / 24 : ℝ) * h * L * ‖yn1 - zn1‖ := by
    rw [hB5_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h5_nn]
    have : h * ((5 / 24 : ℝ) * ‖f tn1 yn1 - f tn1 zn1‖)
        ≤ h * ((5 / 24 : ℝ) * (L * ‖yn1 - zn1‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip1 h5_nn
    calc h * ((5 / 24 : ℝ) * ‖f tn1 yn1 - f tn1 zn1‖)
        ≤ h * ((5 / 24 : ℝ) * (L * ‖yn1 - zn1‖)) := this
      _ = (5 / 24 : ℝ) * h * L * ‖yn1 - zn1‖ := by ring
  have h1_norm :
      ‖B1‖
        ≤ (1 / 24 : ℝ) * h * L * ‖yn - zn‖ := by
    rw [hB1_def, norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h1_nn]
    have : h * ((1 / 24 : ℝ) * ‖f tn yn - f tn zn‖)
        ≤ h * ((1 / 24 : ℝ) * (L * ‖yn - zn‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip0 h1_nn
    calc h * ((1 / 24 : ℝ) * ‖f tn yn - f tn zn‖)
        ≤ h * ((1 / 24 : ℝ) * (L * ‖yn - zn‖)) := this
      _ = (1 / 24 : ℝ) * h * L * ‖yn - zn‖ := by ring
  -- Triangle inequality.
  have htri :
      ‖A + B9 + B19 - B5 + B1 - τ‖
        ≤ ‖A‖
          + ‖B9‖
          + ‖B19‖
          + ‖B5‖
          + ‖B1‖
          + ‖τ‖ := by
    have h1 :
        ‖A + B9 + B19 - B5 + B1 - τ‖
          ≤ ‖A + B9 + B19 - B5 + B1‖
            + ‖τ‖ := norm_sub_le _ _
    have h2 :
        ‖A + B9 + B19 - B5 + B1‖
          ≤ ‖A + B9 + B19 - B5‖ + ‖B1‖ := norm_add_le _ _
    have h3 :
        ‖A + B9 + B19 - B5‖
          ≤ ‖A + B9 + B19‖ + ‖B5‖ :=
      norm_sub_le _ _
    have h4 :
        ‖A + B9 + B19‖
          ≤ ‖A + B9‖ + ‖B19‖ :=
      norm_add_le _ _
    have h5 :
        ‖A + B9‖ ≤ ‖A‖ + ‖B9‖ :=
      norm_add_le _ _
    linarith
  have hmain :
      ‖yn3 - zn3‖
        ≤ ‖yn2 - zn2‖
          + (9 / 24 : ℝ) * h * L * ‖yn3 - zn3‖
          + (19 / 24 : ℝ) * h * L * ‖yn2 - zn2‖
          + (5 / 24 : ℝ) * h * L * ‖yn1 - zn1‖
          + (1 / 24 : ℝ) * h * L * ‖yn - zn‖
          + ‖τ‖ := by
    calc ‖yn3 - zn3‖
        = ‖A + B9 + B19 - B5 + B1 - τ‖ := by rw [halg']
      _ ≤ ‖A‖ + ‖B9‖ + ‖B19‖ + ‖B5‖ + ‖B1‖ + ‖τ‖ := htri
      _ ≤ ‖yn2 - zn2‖
          + (9 / 24 : ℝ) * h * L * ‖yn3 - zn3‖
          + (19 / 24 : ℝ) * h * L * ‖yn2 - zn2‖
          + (5 / 24 : ℝ) * h * L * ‖yn1 - zn1‖
          + (1 / 24 : ℝ) * h * L * ‖yn - zn‖
          + ‖τ‖ := by
        rw [hA_def]
        linarith [h9_norm, h19_norm, h5_norm, h1_norm]
  linarith [hmain]

/-- Divided one-step AM3 vector error bound. -/
theorem am3Vec_one_step_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (9 / 24 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM3TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖
      ≤ (1 + h * (3 * L))
            * max (max ‖yseq n - y (t₀ + (n : ℝ) * h)‖
                      ‖yseq (n + 1)
                          - y (t₀ + ((n : ℝ) + 1) * h)‖)
                  ‖yseq (n + 2)
                      - y (t₀ + ((n : ℝ) + 2) * h)‖
        + 2 * ‖am3VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set en : ℝ := ‖yseq n - y (t₀ + (n : ℝ) * h)‖ with hen_def
  set en1 : ℝ :=
    ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖ with hen1_def
  set en2 : ℝ :=
    ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖ with hen2_def
  set en3 : ℝ :=
    ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖ with hen3_def
  set τabs : ℝ :=
    ‖am3VecResidual h (t₀ + (n : ℝ) * h) y‖ with hτabs_def
  set Emax : ℝ := max (max en en1) en2 with hE_def
  have hen_nn : 0 ≤ en := norm_nonneg _
  have hen1_nn : 0 ≤ en1 := norm_nonneg _
  have hen2_nn : 0 ≤ en2 := norm_nonneg _
  have hen3_nn : 0 ≤ en3 := norm_nonneg _
  have hτ_nn : 0 ≤ τabs := norm_nonneg _
  have hE_nn : 0 ≤ Emax := le_trans hen_nn (le_trans (le_max_left _ _) (le_max_left _ _))
  have hen_le_E : en ≤ Emax := le_trans (le_max_left _ _) (le_max_left _ _)
  have hen1_le_E : en1 ≤ Emax := le_trans (le_max_right _ _) (le_max_left _ _)
  have hen2_le_E : en2 ≤ Emax := le_max_right _ _
  have hx_nn : 0 ≤ h * L := mul_nonneg hh hL
  have hx_small : h * L ≤ 4 / 3 := by
    nlinarith [hsmall]
  have hA_pos : 0 < 1 - (9 / 24 : ℝ) * h * L := by
    nlinarith [hsmall]
  have hstep :
      (1 - (9 / 24 : ℝ) * h * L) * en3
        ≤ en2
          + (19 / 24 : ℝ) * h * L * en2
          + (5 / 24 : ℝ) * h * L * en1
          + (1 / 24 : ℝ) * h * L * en
          + τabs := by
    simpa [hen_def, hen1_def, hen2_def, hen3_def, hτabs_def] using
      (am3Vec_one_step_lipschitz (E := E) (h := h) (L := L)
        hh hsmall hf t₀ hy y hyf n)
  have h19_nn : 0 ≤ (19 / 24 : ℝ) * h * L := by positivity
  have h5_nn : 0 ≤ (5 / 24 : ℝ) * h * L := by positivity
  have h1_nn : 0 ≤ (1 / 24 : ℝ) * h * L := by positivity
  have h19_le :
      (19 / 24 : ℝ) * h * L * en2
        ≤ (19 / 24 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen2_le_E h19_nn
  have h5_le :
      (5 / 24 : ℝ) * h * L * en1
        ≤ (5 / 24 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen1_le_E h5_nn
  have h1_le :
      (1 / 24 : ℝ) * h * L * en
        ≤ (1 / 24 : ℝ) * h * L * Emax :=
    mul_le_mul_of_nonneg_left hen_le_E h1_nn
  have hR_le :
      en2
          + (19 / 24 : ℝ) * h * L * en2
          + (5 / 24 : ℝ) * h * L * en1
          + (1 / 24 : ℝ) * h * L * en
          + τabs
        ≤ (1 + (25 / 24 : ℝ) * (h * L)) * Emax + τabs := by
    have h_alg :
        Emax + (19 / 24 : ℝ) * h * L * Emax
            + (5 / 24 : ℝ) * h * L * Emax
            + (1 / 24 : ℝ) * h * L * Emax + τabs
          = (1 + (25 / 24 : ℝ) * (h * L)) * Emax + τabs := by
      ring
    linarith
  have hcoeffE_le :
      1 + (25 / 24 : ℝ) * (h * L)
        ≤ (1 - (9 / 24 : ℝ) * h * L) * (1 + h * (3 * L)) := by
    nlinarith [hx_nn, hx_small]
  have hcoeffτ_le :
      (1 : ℝ) ≤ (1 - (9 / 24 : ℝ) * h * L) * 2 := by
    nlinarith [hsmall]
  have hE_part :
      (1 + (25 / 24 : ℝ) * (h * L)) * Emax
        ≤ ((1 - (9 / 24 : ℝ) * h * L) * (1 + h * (3 * L))) * Emax :=
    mul_le_mul_of_nonneg_right hcoeffE_le hE_nn
  have hτ_part :
      τabs ≤ ((1 - (9 / 24 : ℝ) * h * L) * 2) * τabs := by
    simpa using mul_le_mul_of_nonneg_right hcoeffτ_le hτ_nn
  have hfactor :
      (1 + (25 / 24 : ℝ) * (h * L)) * Emax + τabs
        ≤ (1 - (9 / 24 : ℝ) * h * L)
            * ((1 + h * (3 * L)) * Emax + 2 * τabs) := by
    have hsplit :
        (1 - (9 / 24 : ℝ) * h * L)
            * ((1 + h * (3 * L)) * Emax + 2 * τabs)
          = ((1 - (9 / 24 : ℝ) * h * L) * (1 + h * (3 * L))) * Emax
              + ((1 - (9 / 24 : ℝ) * h * L) * 2) * τabs := by
      ring
    rw [hsplit]
    linarith
  have hprod :
      (1 - (9 / 24 : ℝ) * h * L) * en3
        ≤ (1 - (9 / 24 : ℝ) * h * L)
            * ((1 + h * (3 * L)) * Emax + 2 * τabs) :=
    le_trans hstep (le_trans hR_le hfactor)
  exact le_of_mul_le_mul_left hprod hA_pos

/-- Max-norm AM3 vector one-step recurrence on the rolling triple
`(en, en1, en2)`. -/
theorem am3Vec_one_step_error_pair_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hsmall : (9 / 24 : ℝ) * h * L ≤ 1 / 2)
    {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) {yseq : ℕ → E}
    (hy : IsAM3TrajectoryVec h f t₀ yseq)
    (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max
          ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖
          ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖)
        ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖
      ≤ (1 + h * (3 * L))
            * max (max ‖yseq n - y (t₀ + (n : ℝ) * h)‖
                      ‖yseq (n + 1)
                          - y (t₀ + ((n : ℝ) + 1) * h)‖)
                  ‖yseq (n + 2)
                      - y (t₀ + ((n : ℝ) + 2) * h)‖
        + 2 * ‖am3VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set en : ℝ := ‖yseq n - y (t₀ + (n : ℝ) * h)‖ with hen_def
  set en1 : ℝ :=
    ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖ with hen1_def
  set en2 : ℝ :=
    ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖ with hen2_def
  set en3 : ℝ :=
    ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖ with hen3_def
  set τabs : ℝ :=
    ‖am3VecResidual h (t₀ + (n : ℝ) * h) y‖ with hτabs_def
  set Emax : ℝ := max (max en en1) en2 with hE_def
  have hen_nn : 0 ≤ en := norm_nonneg _
  have hen1_nn : 0 ≤ en1 := norm_nonneg _
  have hen2_nn : 0 ≤ en2 := norm_nonneg _
  have hτ_nn : 0 ≤ τabs := norm_nonneg _
  have hE_nn : 0 ≤ Emax := le_trans hen_nn (le_trans (le_max_left _ _) (le_max_left _ _))
  have hen1_le_E : en1 ≤ Emax := le_trans (le_max_right _ _) (le_max_left _ _)
  have hen2_le_E : en2 ≤ Emax := le_max_right _ _
  have h3hL_nn : 0 ≤ h * (3 * L) := by positivity
  have hen3_bd :
      en3 ≤ (1 + h * (3 * L)) * Emax + 2 * τabs := by
    simpa [hen_def, hen1_def, hen2_def, hen3_def, hτabs_def, hE_def] using
      (am3Vec_one_step_error_bound (E := E) (h := h) (L := L)
        hh hL hsmall hf t₀ hy y hyf n)
  have hE_le_grow : Emax ≤ (1 + h * (3 * L)) * Emax := by
    have hone : (1 : ℝ) * Emax ≤ (1 + h * (3 * L)) * Emax :=
      mul_le_mul_of_nonneg_right (by linarith) hE_nn
    linarith
  have hen1_bd : en1 ≤ (1 + h * (3 * L)) * Emax + 2 * τabs := by
    linarith [hen1_le_E, hE_le_grow]
  have hen2_bd : en2 ≤ (1 + h * (3 * L)) * Emax + 2 * τabs := by
    linarith [hen2_le_E, hE_le_grow]
  exact max_le (max_le hen1_bd hen2_bd) hen3_bd

/-- Pointwise vector AM3 truncation residual bound. -/
theorem am3Vec_pointwise_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 5 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 5 y t‖ ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    ‖y (t + 3 * h) - y (t + 2 * h)
        - h • ((9 / 24 : ℝ) • deriv y (t + 3 * h)
              + (19 / 24 : ℝ) • deriv y (t + 2 * h)
              - (5 / 24 : ℝ) • deriv y (t + h)
              + (1 / 24 : ℝ) • deriv y t)‖
      ≤ (5 : ℝ) * M * h ^ 5 := by
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have hRy2 :=
    y_fifth_order_taylor_remainder_vec hy hbnd ht ht2h h2h
  have hRy3 :=
    y_fifth_order_taylor_remainder_vec hy hbnd ht ht3h h3h
  have hRyp1 :=
    derivY_fourth_order_taylor_remainder_vec hy hbnd ht hth hh
  have hRyp2 :=
    derivY_fourth_order_taylor_remainder_vec hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_fourth_order_taylor_remainder_vec hy hbnd ht ht3h h3h
  set y0 : E := y t with hy0_def
  set y2 : E := y (t + 2 * h) with hy2_def
  set y3 : E := y (t + 3 * h) with hy3_def
  set d0 : E := deriv y t with hd0_def
  set d1 : E := deriv y (t + h) with hd1_def
  set d2 : E := deriv y (t + 2 * h) with hd2_def
  set d3 : E := deriv y (t + 3 * h) with hd3_def
  set dd : E := iteratedDeriv 2 y t with hdd_def
  set ddd : E := iteratedDeriv 3 y t with hddd_def
  set dddd : E := iteratedDeriv 4 y t with hdddd_def
  have hLTE_eq :
      y3 - y2 - h • ((9 / 24 : ℝ) • d3 + (19 / 24 : ℝ) • d2
                    - (5 / 24 : ℝ) • d1 + (1 / 24 : ℝ) • d0)
        = (y3 - y0 - (3 * h) • d0
              - (((3 * h) ^ 2) / 2) • dd
              - (((3 * h) ^ 3) / 6) • ddd
              - (((3 * h) ^ 4) / 24) • dddd)
          - (y2 - y0 - (2 * h) • d0
              - (((2 * h) ^ 2) / 2) • dd
              - (((2 * h) ^ 3) / 6) • ddd
              - (((2 * h) ^ 4) / 24) • dddd)
          - (9 * h / 24 : ℝ)
              • (d3 - d0 - (3 * h) • dd
                  - (((3 * h) ^ 2) / 2) • ddd
                  - (((3 * h) ^ 3) / 6) • dddd)
          - (19 * h / 24 : ℝ)
              • (d2 - d0 - (2 * h) • dd
                  - (((2 * h) ^ 2) / 2) • ddd
                  - (((2 * h) ^ 3) / 6) • dddd)
          + (5 * h / 24 : ℝ)
              • (d1 - d0 - h • dd
                  - (h ^ 2 / 2) • ddd
                  - (h ^ 3 / 6) • dddd) := by
    simp only [smul_sub, smul_add, smul_smul]
    module
  rw [hLTE_eq]
  set A : E := y3 - y0 - (3 * h) • d0
            - (((3 * h) ^ 2) / 2) • dd
            - (((3 * h) ^ 3) / 6) • ddd
            - (((3 * h) ^ 4) / 24) • dddd with hA_def
  set B : E := y2 - y0 - (2 * h) • d0
            - (((2 * h) ^ 2) / 2) • dd
            - (((2 * h) ^ 3) / 6) • ddd
            - (((2 * h) ^ 4) / 24) • dddd with hB_def
  set C : E := d3 - d0 - (3 * h) • dd
            - (((3 * h) ^ 2) / 2) • ddd
            - (((3 * h) ^ 3) / 6) • dddd with hC_def
  set D : E := d2 - d0 - (2 * h) • dd
            - (((2 * h) ^ 2) / 2) • ddd
            - (((2 * h) ^ 3) / 6) • dddd with hD_def
  set G : E := d1 - d0 - h • dd
            - (h ^ 2 / 2) • ddd
            - (h ^ 3 / 6) • dddd with hG_def
  have h9h_nn : 0 ≤ (9 * h / 24 : ℝ) := by linarith
  have h19h_nn : 0 ≤ (19 * h / 24 : ℝ) := by linarith
  have h5h_nn : 0 ≤ (5 * h / 24 : ℝ) := by linarith
  have htri :
      ‖A - B - (9 * h / 24 : ℝ) • C - (19 * h / 24 : ℝ) • D
          + (5 * h / 24 : ℝ) • G‖
        ≤ ‖A‖ + ‖B‖ + ‖(9 * h / 24 : ℝ) • C‖
            + ‖(19 * h / 24 : ℝ) • D‖
            + ‖(5 * h / 24 : ℝ) • G‖ := by
    have h1 : ‖A - B - (9 * h / 24 : ℝ) • C - (19 * h / 24 : ℝ) • D
          + (5 * h / 24 : ℝ) • G‖
        ≤ ‖A - B - (9 * h / 24 : ℝ) • C - (19 * h / 24 : ℝ) • D‖
          + ‖(5 * h / 24 : ℝ) • G‖ := norm_add_le _ _
    have h2 : ‖A - B - (9 * h / 24 : ℝ) • C - (19 * h / 24 : ℝ) • D‖
        ≤ ‖A - B - (9 * h / 24 : ℝ) • C‖
          + ‖(19 * h / 24 : ℝ) • D‖ := norm_sub_le _ _
    have h3 : ‖A - B - (9 * h / 24 : ℝ) • C‖
        ≤ ‖A - B‖ + ‖(9 * h / 24 : ℝ) • C‖ := norm_sub_le _ _
    have h4 : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
    linarith
  have hA_bd : ‖A‖ ≤ M / 120 * (3 * h) ^ 5 := hRy3
  have hB_bd : ‖B‖ ≤ M / 120 * (2 * h) ^ 5 := hRy2
  have hC_bd : ‖C‖ ≤ M / 24 * (3 * h) ^ 4 := hRyp3
  have hD_bd : ‖D‖ ≤ M / 24 * (2 * h) ^ 4 := hRyp2
  have hG_bd : ‖G‖ ≤ M / 24 * h ^ 4 := hRyp1
  have h9C_bd :
      ‖(9 * h / 24 : ℝ) • C‖
        ≤ (9 * h / 24 : ℝ) * (M / 24 * (3 * h) ^ 4) := by
    rw [norm_smul, Real.norm_of_nonneg h9h_nn]
    exact mul_le_mul_of_nonneg_left hC_bd h9h_nn
  have h19D_bd :
      ‖(19 * h / 24 : ℝ) • D‖
        ≤ (19 * h / 24 : ℝ) * (M / 24 * (2 * h) ^ 4) := by
    rw [norm_smul, Real.norm_of_nonneg h19h_nn]
    exact mul_le_mul_of_nonneg_left hD_bd h19h_nn
  have h5G_bd :
      ‖(5 * h / 24 : ℝ) • G‖
        ≤ (5 * h / 24 : ℝ) * (M / 24 * h ^ 4) := by
    rw [norm_smul, Real.norm_of_nonneg h5h_nn]
    exact mul_le_mul_of_nonneg_left hG_bd h5h_nn
  have hbound_alg :
      M / 120 * (3 * h) ^ 5 + M / 120 * (2 * h) ^ 5
        + (9 * h / 24) * (M / 24 * (3 * h) ^ 4)
        + (19 * h / 24) * (M / 24 * (2 * h) ^ 4)
        + (5 * h / 24) * (M / 24 * h ^ 4)
        = (131 / 32 : ℝ) * M * h ^ 5 := by
    ring
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (norm_nonneg _).trans this
  have hh5_nn : 0 ≤ h ^ 5 := by positivity
  have hMh5_nn : 0 ≤ M * h ^ 5 := mul_nonneg hMnn hh5_nn
  have hslack : (131 / 32 : ℝ) * M * h ^ 5 ≤ 5 * M * h ^ 5 := by
    have hle : (131 / 32 : ℝ) ≤ 5 := by norm_num
    have := mul_le_mul_of_nonneg_right hle hMh5_nn
    linarith [this]
  linarith [htri, hA_bd, hB_bd, h9C_bd, h19D_bd, h5G_bd,
    hbound_alg.le, hbound_alg.ge, hslack]

/-- Uniform bound on the AM3 vector one-step truncation residual on a finite
horizon, given a `C^5` exact solution. -/
theorem am3Vec_local_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 5 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 3) * h ≤ T →
        ‖am3VecResidual h (t₀ + (n : ℝ) * h) y‖
          ≤ C * h ^ 5 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_five_bounded_on_Icc_vec hy t₀ (t₀ + T + 1)
  refine ⟨(5 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 3) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 3) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 3) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 3 * h = ((n : ℝ) + 3) * h := by ring
    linarith
  show ‖am3VecResidual h t y‖ ≤ 5 * M * h ^ 5
  unfold am3VecResidual
  exact am3Vec_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem hh.le

/-- Headline AM3 vector global error bound. -/
theorem am3Vec_global_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy_smooth : ContDiff ℝ 5 y)
    {f : ℝ → E → E} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      (9 / 24 : ℝ) * h * L ≤ 1 / 2 →
      ∀ {yseq : ℕ → E} {ε₀ : ℝ},
      IsAM3TrajectoryVec h f t₀ yseq →
      0 ≤ ε₀ →
      ‖yseq 0 - y t₀‖ ≤ ε₀ →
      ‖yseq 1 - y (t₀ + h)‖ ≤ ε₀ →
      ‖yseq 2 - y (t₀ + 2 * h)‖ ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 2) * h ≤ T →
      ‖yseq N - y (t₀ + (N : ℝ) * h)‖
        ≤ Real.exp ((3 * L) * T) * ε₀ + K * h ^ 4 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    am3Vec_local_residual_bound hy_smooth t₀ T hT
  refine ⟨T * Real.exp ((3 * L) * T) * (2 * C), δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  intro h hh hδ_le hsmall yseq ε₀ hy_traj hε₀ he0_bd he1_bd he2_bd N hNh
  set eN : ℕ → ℝ :=
    fun k => ‖yseq k - y (t₀ + (k : ℝ) * h)‖ with heN_def
  set EN : ℕ → ℝ :=
    fun k => max (max (eN k) (eN (k + 1))) (eN (k + 2)) with hEN_def
  have heN_nn : ∀ k, 0 ≤ eN k := fun _ => norm_nonneg _
  have hEN_nn : ∀ k, 0 ≤ EN k := fun k =>
    le_max_of_le_left (le_max_of_le_left (heN_nn k))
  have hEN0_le : EN 0 ≤ ε₀ := by
    show max (max (eN 0) (eN 1)) (eN 2) ≤ ε₀
    refine max_le (max_le ?_ ?_) ?_
    · show ‖yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)‖ ≤ ε₀
      simpa using he0_bd
    · show ‖yseq 1 - y (t₀ + ((1 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((1 : ℕ) : ℝ) * h = h := by push_cast; ring
      rw [hcast]
      simpa using he1_bd
    · show ‖yseq 2 - y (t₀ + ((2 : ℕ) : ℝ) * h)‖ ≤ ε₀
      have hcast : ((2 : ℕ) : ℝ) * h = 2 * h := by push_cast; ring
      rw [hcast]
      simpa using he2_bd
  have h3L_nn : (0 : ℝ) ≤ 3 * L := by linarith
  have hstep_general : ∀ n : ℕ, ((n : ℝ) + 3) * h ≤ T →
      EN (n + 1) ≤ (1 + h * (3 * L)) * EN n + (2 * C) * h ^ 5 := by
    intro n hnh_le
    have honestep := am3Vec_one_step_error_pair_bound
      (E := E) (h := h) (L := L) hh.le hL hsmall hf t₀ hy_traj y hyf n
    have hres := hresidual hh hδ_le n hnh_le
    have hcast1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hcast2 : ((n + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    have hcast3 : ((n + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
    have heq_eN_n : eN n
        = ‖yseq n - y (t₀ + (n : ℝ) * h)‖ := rfl
    have heq_eN_n1 : eN (n + 1)
        = ‖yseq (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast1]
    have heq_eN_n2 : eN (n + 1 + 1)
        = ‖yseq (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast2]
    have heq_eN_n3 : eN (n + 1 + 1 + 1)
        = ‖yseq (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)‖ := by
      show ‖_ - _‖ = _
      rw [hcast3]
    show max (max (eN (n + 1)) (eN (n + 1 + 1))) (eN (n + 1 + 1 + 1))
        ≤ (1 + h * (3 * L)) * max (max (eN n) (eN (n + 1))) (eN (n + 1 + 1))
          + (2 * C) * h ^ 5
    rw [heq_eN_n, heq_eN_n1, heq_eN_n2, heq_eN_n3]
    have h2τ : 2 * ‖am3VecResidual h (t₀ + (n : ℝ) * h) y‖
        ≤ (2 * C) * h ^ 5 := by
      have h2nn : (0 : ℝ) ≤ 2 := by norm_num
      have := mul_le_mul_of_nonneg_left hres h2nn
      linarith [this]
    linarith [honestep, h2τ]
  have hexp_ge : (1 : ℝ) ≤ Real.exp ((3 * L) * T) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hKnn : 0 ≤ T * Real.exp ((3 * L) * T) * (2 * C) :=
    mul_nonneg (mul_nonneg hT.le (Real.exp_nonneg _)) (by linarith)
  have hh4_nn : 0 ≤ h ^ 4 := by positivity
  have hexp_nn : 0 ≤ Real.exp ((3 * L) * T) := Real.exp_nonneg _
  have hbase_to_headline : ∀ q : ℝ, q ≤ ε₀ →
      q ≤ Real.exp ((3 * L) * T) * ε₀
            + T * Real.exp ((3 * L) * T) * (2 * C) * h ^ 4 := by
    intro q hq
    have hexp_ε₀ : ε₀ ≤ Real.exp ((3 * L) * T) * ε₀ := by
      have hone : (1 : ℝ) * ε₀ ≤ Real.exp ((3 * L) * T) * ε₀ :=
        mul_le_mul_of_nonneg_right hexp_ge hε₀
      linarith
    have hKh4_nn : 0 ≤ T * Real.exp ((3 * L) * T) * (2 * C) * h ^ 4 :=
      mul_nonneg hKnn hh4_nn
    linarith
  match N, hNh with
  | 0, _ =>
    have hbase : ‖yseq 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      simpa using he0_bd
    exact hbase_to_headline _ hbase
  | 1, _ =>
    have hbase : ‖yseq 1 - y (t₀ + ((1 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((1 : ℕ) : ℝ) * h = h := by push_cast; ring
      rw [hcast]
      simpa using he1_bd
    exact hbase_to_headline _ hbase
  | 2, _ =>
    have hbase : ‖yseq 2 - y (t₀ + ((2 : ℕ) : ℝ) * h)‖ ≤ ε₀ := by
      have hcast : ((2 : ℕ) : ℝ) * h = 2 * h := by push_cast; ring
      rw [hcast]
      simpa using he2_bd
    exact hbase_to_headline _ hbase
  | N' + 3, hNh =>
    have hcast : (((N' + 3 : ℕ) : ℝ) + 2) = (N' : ℝ) + 5 := by
      push_cast
      ring
    have hN_hyp : ((N' : ℝ) + 5) * h ≤ T := by
      have := hNh
      rw [hcast] at this
      linarith
    have hgronwall_step : ∀ n, n < N' + 1 →
        EN (n + 1) ≤ (1 + h * (3 * L)) * EN n + (2 * C) * h ^ (4 + 1) := by
      intro n hn_lt
      have hpow : (2 * C) * h ^ (4 + 1) = (2 * C) * h ^ 5 := by norm_num
      rw [hpow]
      apply hstep_general
      have hn_le_N' : (n : ℝ) ≤ (N' : ℝ) := by
        exact_mod_cast Nat.lt_succ_iff.mp hn_lt
      have h_le_chain : (n : ℝ) + 3 ≤ (N' : ℝ) + 5 := by linarith
      have h_mul : ((n : ℝ) + 3) * h ≤ ((N' : ℝ) + 5) * h :=
        mul_le_mul_of_nonneg_right h_le_chain hh.le
      linarith
    have hN'1h_le_T : ((N' + 1 : ℕ) : ℝ) * h ≤ T := by
      have hcast' : ((N' + 1 : ℕ) : ℝ) = (N' : ℝ) + 1 := by push_cast; ring
      rw [hcast']
      have : (N' : ℝ) + 1 ≤ (N' : ℝ) + 5 := by linarith
      have := mul_le_mul_of_nonneg_right this hh.le
      linarith
    have hgronwall :=
      lmm_error_bound_from_local_truncation
        (h := h) (L := 3 * L) (C := 2 * C) (T := T) (p := 4)
        (e := EN) (N := N' + 1)
        hh.le h3L_nn (by linarith) (hEN_nn 0) hgronwall_step
        (N' + 1) le_rfl hN'1h_le_T
    have heN_le_EN : eN (N' + 3) ≤ EN (N' + 1) := by
      show eN (N' + 3) ≤ max (max (eN (N' + 1)) (eN (N' + 1 + 1))) (eN (N' + 1 + 2))
      have heq : N' + 3 = N' + 1 + 2 := by ring
      rw [heq]
      exact le_max_right _ _
    have h_chain :
        Real.exp ((3 * L) * T) * EN 0 ≤ Real.exp ((3 * L) * T) * ε₀ :=
      mul_le_mul_of_nonneg_left hEN0_le hexp_nn
    show ‖yseq (N' + 3) - y (t₀ + ((N' + 3 : ℕ) : ℝ) * h)‖
        ≤ Real.exp ((3 * L) * T) * ε₀
          + T * Real.exp ((3 * L) * T) * (2 * C) * h ^ 4
    have heN_eq :
        eN (N' + 3)
          = ‖yseq (N' + 3) - y (t₀ + ((N' + 3 : ℕ) : ℝ) * h)‖ := rfl
    linarith [heN_le_EN, hgronwall, h_chain, heN_eq.symm.le, heN_eq.le]

end LMM
