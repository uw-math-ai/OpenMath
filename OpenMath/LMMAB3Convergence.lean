import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp

/-! ## Adams–Bashforth 3-step Convergence Chain (Iserles §1.2)

Order-3 explicit 3-step LMM convergence scaffold. Mirrors the AB2 chain
in `OpenMath.LMMAB2Convergence`. Cycle 416 lands the iteration definition
and the textbook LTE rewrite; remaining declarations (Lipschitz one-step
recurrence, local residual bound, headline global error bound) follow in
later cycles. -/

namespace LMM

/-- AB3 iteration with three starting samples `y₀, y₁, y₂`:
`y_{n+3} = y_{n+2} + h · (23/12 · f(t_{n+2}, y_{n+2})
  − 16/12 · f(t_{n+1}, y_{n+1}) + 5/12 · f(t_n, y_n))`. -/
noncomputable def ab3Iter
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ : ℝ) : ℕ → ℝ
  | 0 => y₀
  | 1 => y₁
  | 2 => y₂
  | n + 3 =>
      ab3Iter h f t₀ y₀ y₁ y₂ (n + 2)
        + h * (23 / 12 * f (t₀ + ((n : ℝ) + 2) * h)
                (ab3Iter h f t₀ y₀ y₁ y₂ (n + 2))
              - 16 / 12 * f (t₀ + ((n : ℝ) + 1) * h)
                (ab3Iter h f t₀ y₀ y₁ y₂ (n + 1))
              + 5 / 12 * f (t₀ + (n : ℝ) * h)
                (ab3Iter h f t₀ y₀ y₁ y₂ n))

@[simp] lemma ab3Iter_zero
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ : ℝ) :
    ab3Iter h f t₀ y₀ y₁ y₂ 0 = y₀ := rfl

@[simp] lemma ab3Iter_one
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ : ℝ) :
    ab3Iter h f t₀ y₀ y₁ y₂ 1 = y₁ := rfl

@[simp] lemma ab3Iter_two
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ : ℝ) :
    ab3Iter h f t₀ y₀ y₁ y₂ 2 = y₂ := rfl

lemma ab3Iter_succ_succ_succ
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ : ℝ) (n : ℕ) :
    ab3Iter h f t₀ y₀ y₁ y₂ (n + 3)
      = ab3Iter h f t₀ y₀ y₁ y₂ (n + 2)
          + h * (23 / 12 * f (t₀ + ((n : ℝ) + 2) * h)
                  (ab3Iter h f t₀ y₀ y₁ y₂ (n + 2))
                - 16 / 12 * f (t₀ + ((n : ℝ) + 1) * h)
                    (ab3Iter h f t₀ y₀ y₁ y₂ (n + 1))
                + 5 / 12 * f (t₀ + (n : ℝ) * h)
                    (ab3Iter h f t₀ y₀ y₁ y₂ n)) := rfl

/-- AB3 local truncation operator reduces to the textbook 3-step residual
`y(t + 3h) − y(t + 2h) − h · (23/12 · y'(t + 2h) − 16/12 · y'(t + h)
  + 5/12 · y'(t))`. -/
theorem ab3_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    adamsBashforth3.localTruncationError h t y
      = y (t + 3 * h) - y (t + 2 * h)
          - h * (23 / 12 * deriv y (t + 2 * h)
                  - 16 / 12 * deriv y (t + h)
                  + 5 / 12 * deriv y t) := by
  unfold localTruncationError truncationOp
  simp [adamsBashforth3, Fin.sum_univ_four, iteratedDeriv_one,
    iteratedDeriv_zero]
  ring

/-- One-step AB3 Lipschitz step: a single linearised increment of the
global error from steps `n, n+1, n+2` to `n+3`, with three Lipschitz
contributions and additive `|τ_n|`. -/
theorem ab3_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ y₁ y₂ : ℝ) (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    |ab3Iter h f t₀ y₀ y₁ y₂ (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|
      ≤ |ab3Iter h f t₀ y₀ y₁ y₂ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|
        + (23 / 12) * h * L
            * |ab3Iter h f t₀ y₀ y₁ y₂ (n + 2)
                - y (t₀ + ((n : ℝ) + 2) * h)|
        + (16 / 12) * h * L
            * |ab3Iter h f t₀ y₀ y₁ y₂ (n + 1)
                - y (t₀ + ((n : ℝ) + 1) * h)|
        + (5 / 12) * h * L
            * |ab3Iter h f t₀ y₀ y₁ y₂ n - y (t₀ + (n : ℝ) * h)|
        + |adamsBashforth3.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  -- Abbreviations.
  set yn : ℝ := ab3Iter h f t₀ y₀ y₁ y₂ n with hyn_def
  set yn1 : ℝ := ab3Iter h f t₀ y₀ y₁ y₂ (n + 1) with hyn1_def
  set yn2 : ℝ := ab3Iter h f t₀ y₀ y₁ y₂ (n + 2) with hyn2_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set tn3 : ℝ := t₀ + ((n : ℝ) + 3) * h with htn3_def
  set zn : ℝ := y tn with hzn_def
  set zn1 : ℝ := y tn1 with hzn1_def
  set zn2 : ℝ := y tn2 with hzn2_def
  set zn3 : ℝ := y tn3 with hzn3_def
  set τ : ℝ := adamsBashforth3.localTruncationError h tn y with hτ_def
  -- AB3 step formula.
  have hstep : ab3Iter h f t₀ y₀ y₁ y₂ (n + 3)
      = yn2 + h * (23 / 12 * f tn2 yn2
                    - 16 / 12 * f tn1 yn1
                    + 5 / 12 * f tn yn) := by
    show ab3Iter h f t₀ y₀ y₁ y₂ (n + 3) = _
    rw [ab3Iter_succ_succ_succ]
  -- LTE residual at `tn`, expressed via `f` along the trajectory.
  have htn1_h : tn + h = tn1 := by simp [htn_def, htn1_def]; ring
  have htn_2h : tn + 2 * h = tn2 := by simp [htn_def, htn2_def]; ring
  have htn_3h : tn + 3 * h = tn3 := by simp [htn_def, htn3_def]; ring
  have hτ_eq : τ = zn3 - zn2
        - h * (23 / 12 * f tn2 zn2 - 16 / 12 * f tn1 zn1 + 5 / 12 * f tn zn) := by
    show adamsBashforth3.localTruncationError h tn y = _
    rw [ab3_localTruncationError_eq, htn1_h, htn_2h, htn_3h,
      hyf tn2, hyf tn1, hyf tn]
  -- Algebraic decomposition of the global error increment.
  have halg : ab3Iter h f t₀ y₀ y₁ y₂ (n + 3) - zn3
      = (yn2 - zn2)
        + (23 / 12) * h * (f tn2 yn2 - f tn2 zn2)
        - (16 / 12) * h * (f tn1 yn1 - f tn1 zn1)
        + (5 / 12) * h * (f tn yn - f tn zn)
        - τ := by
    rw [hstep, hτ_eq]; ring
  -- Lipschitz bounds on the three `f` increments.
  have hLip2 : |f tn2 yn2 - f tn2 zn2| ≤ L * |yn2 - zn2| := hf tn2 yn2 zn2
  have hLip1 : |f tn1 yn1 - f tn1 zn1| ≤ L * |yn1 - zn1| := hf tn1 yn1 zn1
  have hLip0 : |f tn yn - f tn zn| ≤ L * |yn - zn| := hf tn yn zn
  have h23_nn : 0 ≤ (23 / 12) * h := by linarith
  have h16_nn : 0 ≤ (16 / 12) * h := by linarith
  have h5_nn : 0 ≤ (5 / 12) * h := by linarith
  have h23_abs : |(23 / 12) * h * (f tn2 yn2 - f tn2 zn2)|
      ≤ (23 / 12) * h * L * |yn2 - zn2| := by
    rw [abs_mul, abs_of_nonneg h23_nn]
    calc (23 / 12) * h * |f tn2 yn2 - f tn2 zn2|
        ≤ (23 / 12) * h * (L * |yn2 - zn2|) :=
          mul_le_mul_of_nonneg_left hLip2 h23_nn
      _ = (23 / 12) * h * L * |yn2 - zn2| := by ring
  have h16_abs : |(16 / 12) * h * (f tn1 yn1 - f tn1 zn1)|
      ≤ (16 / 12) * h * L * |yn1 - zn1| := by
    rw [abs_mul, abs_of_nonneg h16_nn]
    calc (16 / 12) * h * |f tn1 yn1 - f tn1 zn1|
        ≤ (16 / 12) * h * (L * |yn1 - zn1|) :=
          mul_le_mul_of_nonneg_left hLip1 h16_nn
      _ = (16 / 12) * h * L * |yn1 - zn1| := by ring
  have h5_abs : |(5 / 12) * h * (f tn yn - f tn zn)|
      ≤ (5 / 12) * h * L * |yn - zn| := by
    rw [abs_mul, abs_of_nonneg h5_nn]
    calc (5 / 12) * h * |f tn yn - f tn zn|
        ≤ (5 / 12) * h * (L * |yn - zn|) :=
          mul_le_mul_of_nonneg_left hLip0 h5_nn
      _ = (5 / 12) * h * L * |yn - zn| := by ring
  -- Triangle inequality (chained four times).
  have htri :
      |(yn2 - zn2)
        + (23 / 12) * h * (f tn2 yn2 - f tn2 zn2)
        - (16 / 12) * h * (f tn1 yn1 - f tn1 zn1)
        + (5 / 12) * h * (f tn yn - f tn zn)
        - τ|
        ≤ |yn2 - zn2|
          + |(23 / 12) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(16 / 12) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(5 / 12) * h * (f tn yn - f tn zn)|
          + |τ| := by
    have h1 :
        |(yn2 - zn2)
          + (23 / 12) * h * (f tn2 yn2 - f tn2 zn2)
          - (16 / 12) * h * (f tn1 yn1 - f tn1 zn1)
          + (5 / 12) * h * (f tn yn - f tn zn)
          - τ|
          ≤ |(yn2 - zn2)
              + (23 / 12) * h * (f tn2 yn2 - f tn2 zn2)
              - (16 / 12) * h * (f tn1 yn1 - f tn1 zn1)
              + (5 / 12) * h * (f tn yn - f tn zn)|
            + |τ| := abs_sub _ _
    have h2 :
        |(yn2 - zn2)
          + (23 / 12) * h * (f tn2 yn2 - f tn2 zn2)
          - (16 / 12) * h * (f tn1 yn1 - f tn1 zn1)
          + (5 / 12) * h * (f tn yn - f tn zn)|
          ≤ |(yn2 - zn2)
              + (23 / 12) * h * (f tn2 yn2 - f tn2 zn2)
              - (16 / 12) * h * (f tn1 yn1 - f tn1 zn1)|
            + |(5 / 12) * h * (f tn yn - f tn zn)| := abs_add_le _ _
    have h3 :
        |(yn2 - zn2)
          + (23 / 12) * h * (f tn2 yn2 - f tn2 zn2)
          - (16 / 12) * h * (f tn1 yn1 - f tn1 zn1)|
          ≤ |(yn2 - zn2)
              + (23 / 12) * h * (f tn2 yn2 - f tn2 zn2)|
            + |(16 / 12) * h * (f tn1 yn1 - f tn1 zn1)| := abs_sub _ _
    have h4 :
        |(yn2 - zn2)
          + (23 / 12) * h * (f tn2 yn2 - f tn2 zn2)|
          ≤ |yn2 - zn2| + |(23 / 12) * h * (f tn2 yn2 - f tn2 zn2)| :=
      abs_add_le _ _
    linarith
  calc |ab3Iter h f t₀ y₀ y₁ y₂ (n + 3) - zn3|
      = |(yn2 - zn2)
          + (23 / 12) * h * (f tn2 yn2 - f tn2 zn2)
          - (16 / 12) * h * (f tn1 yn1 - f tn1 zn1)
          + (5 / 12) * h * (f tn yn - f tn zn)
          - τ| := by rw [halg]
    _ ≤ |yn2 - zn2|
          + |(23 / 12) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(16 / 12) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(5 / 12) * h * (f tn yn - f tn zn)|
          + |τ| := htri
    _ ≤ |yn2 - zn2|
          + (23 / 12) * h * L * |yn2 - zn2|
          + (16 / 12) * h * L * |yn1 - zn1|
          + (5 / 12) * h * L * |yn - zn|
          + |τ| := by linarith [h23_abs, h16_abs, h5_abs]

/-- Max-norm one-step error recurrence for AB3 with Lipschitz constant
`L`. With `eN k := |y_k − y(t_k)|` and
`EN k := max (max (eN k) (eN (k+1))) (eN (k+2))`,
`EN (n+1) ≤ (1 + h · (11/3) · L) · EN n + |τ_n|`. -/
theorem ab3_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ y₁ y₂ : ℝ) (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max
          |ab3Iter h f t₀ y₀ y₁ y₂ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
          |ab3Iter h f t₀ y₀ y₁ y₂ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|)
        |ab3Iter h f t₀ y₀ y₁ y₂ (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|
      ≤ (1 + h * ((11 / 3) * L))
            * max (max |ab3Iter h f t₀ y₀ y₁ y₂ n
                      - y (t₀ + (n : ℝ) * h)|
                      |ab3Iter h f t₀ y₀ y₁ y₂ (n + 1)
                          - y (t₀ + ((n : ℝ) + 1) * h)|)
                  |ab3Iter h f t₀ y₀ y₁ y₂ (n + 2)
                      - y (t₀ + ((n : ℝ) + 2) * h)|
        + |adamsBashforth3.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set en : ℝ := |ab3Iter h f t₀ y₀ y₁ y₂ n - y (t₀ + (n : ℝ) * h)|
    with hen_def
  set en1 : ℝ :=
    |ab3Iter h f t₀ y₀ y₁ y₂ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
    with hen1_def
  set en2 : ℝ :=
    |ab3Iter h f t₀ y₀ y₁ y₂ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|
    with hen2_def
  set en3 : ℝ :=
    |ab3Iter h f t₀ y₀ y₁ y₂ (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|
    with hen3_def
  set τabs : ℝ :=
    |adamsBashforth3.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  have hen_nn : 0 ≤ en := abs_nonneg _
  have hen1_nn : 0 ≤ en1 := abs_nonneg _
  have hen2_nn : 0 ≤ en2 := abs_nonneg _
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  -- One-step Lipschitz bound (from `ab3_one_step_lipschitz`).
  have hstep :
      en3 ≤ en2 + (23 / 12) * h * L * en2
                + (16 / 12) * h * L * en1
                + (5 / 12) * h * L * en + τabs := by
    have := ab3_one_step_lipschitz hh hf t₀ y₀ y₁ y₂ y hyf n
    show |ab3Iter h f t₀ y₀ y₁ y₂ (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|
        ≤ |ab3Iter h f t₀ y₀ y₁ y₂ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|
          + (23 / 12) * h * L
              * |ab3Iter h f t₀ y₀ y₁ y₂ (n + 2)
                  - y (t₀ + ((n : ℝ) + 2) * h)|
          + (16 / 12) * h * L
              * |ab3Iter h f t₀ y₀ y₁ y₂ (n + 1)
                  - y (t₀ + ((n : ℝ) + 1) * h)|
          + (5 / 12) * h * L
              * |ab3Iter h f t₀ y₀ y₁ y₂ n - y (t₀ + (n : ℝ) * h)|
          + |adamsBashforth3.localTruncationError h (t₀ + (n : ℝ) * h) y|
    exact this
  set EN_n : ℝ := max (max en en1) en2 with hEN_n_def
  have hen_le_EN : en ≤ EN_n :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hen1_le_EN : en1 ≤ EN_n :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hen2_le_EN : en2 ≤ EN_n := le_max_right _ _
  have h23_nn : 0 ≤ (23 / 12) * h * L := by positivity
  have h16_nn : 0 ≤ (16 / 12) * h * L := by positivity
  have h5_nn : 0 ≤ (5 / 12) * h * L := by positivity
  have hEN_nn : 0 ≤ EN_n := le_trans hen_nn hen_le_EN
  have hcoef_nn : 0 ≤ h * ((11 / 3) * L) := by positivity
  -- en3 ≤ (1 + h*(11/3*L)) * EN_n + τabs.
  have hen3_bd : en3 ≤ (1 + h * ((11 / 3) * L)) * EN_n + τabs := by
    have h1 : (23 / 12) * h * L * en2 ≤ (23 / 12) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen2_le_EN h23_nn
    have h2 : (16 / 12) * h * L * en1 ≤ (16 / 12) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen1_le_EN h16_nn
    have h3 : (5 / 12) * h * L * en ≤ (5 / 12) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen_le_EN h5_nn
    have h_alg :
        EN_n + (23 / 12) * h * L * EN_n
              + (16 / 12) * h * L * EN_n
              + (5 / 12) * h * L * EN_n + τabs
          = (1 + h * ((11 / 3) * L)) * EN_n + τabs := by ring
    linarith [hstep, hen2_le_EN, h1, h2, h3, h_alg.le]
  -- en1 ≤ EN_n ≤ (1 + h*(11/3*L)) * EN_n + τabs.
  have hEN_le_grow : EN_n ≤ (1 + h * ((11 / 3) * L)) * EN_n := by
    have hone : (1 : ℝ) * EN_n ≤ (1 + h * ((11 / 3) * L)) * EN_n :=
      mul_le_mul_of_nonneg_right (by linarith) hEN_nn
    linarith
  have hen1_bd : en1 ≤ (1 + h * ((11 / 3) * L)) * EN_n + τabs := by
    linarith [hen1_le_EN, hEN_le_grow]
  have hen2_bd : en2 ≤ (1 + h * ((11 / 3) * L)) * EN_n + τabs := by
    linarith [hen2_le_EN, hEN_le_grow]
  exact max_le (max_le hen1_bd hen2_bd) hen3_bd

/-- A `C^4` function has its fourth derivative bounded on every compact
interval `[a, b]`. -/
private theorem iteratedDeriv_four_bounded_on_Icc
    {y : ℝ → ℝ} (hy : ContDiff ℝ 4 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, |iteratedDeriv 4 y t| ≤ M := by
  have h_cont : Continuous (iteratedDeriv 4 y) :=
    hy.continuous_iteratedDeriv 4 (by norm_num)
  obtain ⟨M, hM⟩ :=
    IsCompact.exists_bound_of_continuousOn (CompactIccSpace.isCompact_Icc)
      h_cont.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro t ht
  exact (hM t ht).trans (le_max_left _ _)

/-- Pointwise fourth-order Taylor (Lagrange) remainder bound: if `y` is
`C^4` and `|iteratedDeriv 4 y| ≤ M` on `[a, b]`, then for `t, t + r ∈ [a, b]`
with `r ≥ 0`,
`|y(t+r) - y(t) - r·y'(t) - r²/2 · y''(t) - r³/6 · y'''(t)| ≤ M/24 · r⁴`. -/
private theorem y_fourth_order_taylor_remainder
    {y : ℝ → ℝ} (hy : ContDiff ℝ 4 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 4 y t| ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    |y (t + r) - y t - r * deriv y t
        - r ^ 2 / 2 * iteratedDeriv 2 y t
        - r ^ 3 / 6 * iteratedDeriv 3 y t|
      ≤ M / 24 * r ^ 4 := by
  by_cases hr' : r = 0
  · subst hr'; simp
  have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr')
  have htlt : t < t + r := by linarith
  have hUnique : UniqueDiffOn ℝ (Set.Icc t (t + r)) := uniqueDiffOn_Icc htlt
  have ht_mem_loc : t ∈ Set.Icc t (t + r) := Set.left_mem_Icc.mpr htlt.le
  -- Lagrange Taylor remainder at order 3 (fourth-derivative form).
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ : ∃ ξ ∈ Set.Ioo t (t + r),
      y (t + r) - taylorWithinEval y 3 (Set.Icc t (t + r)) t (t + r)
        = iteratedDeriv 4 y ξ * r ^ 4 / 24 := by
    have hcdo : ContDiffOn ℝ 4 y (Set.Icc t (t + r)) :=
      hy.contDiffOn.of_le le_rfl
    have ⟨ξ, hξ_mem, hξ_eq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 3) htlt hcdo
    refine ⟨ξ, hξ_mem, ?_⟩
    have hpow : (t + r - t) ^ 4 = r ^ 4 := by ring
    have hfact : (((3 + 1 : ℕ).factorial : ℝ)) = 24 := by
      simp [Nat.factorial]
    rw [hξ_eq, hpow, hfact]
  -- Compute the Taylor polynomial explicitly.
  have h_taylor :
      taylorWithinEval y 3 (Set.Icc t (t + r)) t (t + r)
        = y t + r * deriv y t + r ^ 2 / 2 * iteratedDeriv 2 y t
              + r ^ 3 / 6 * iteratedDeriv 3 y t := by
    have h1 : iteratedDerivWithin 1 y (Set.Icc t (t + r)) t = deriv y t := by
      have heq := iteratedDerivWithin_eq_iteratedDeriv (n := 1) hUnique
        (hy.contDiffAt.of_le (by norm_num)) ht_mem_loc
      simpa [iteratedDeriv_one] using heq
    have h2 :
        iteratedDerivWithin 2 y (Set.Icc t (t + r)) t = iteratedDeriv 2 y t :=
      iteratedDerivWithin_eq_iteratedDeriv (n := 2) hUnique
        (hy.contDiffAt.of_le (by norm_num)) ht_mem_loc
    have h3 :
        iteratedDerivWithin 3 y (Set.Icc t (t + r)) t = iteratedDeriv 3 y t :=
      iteratedDerivWithin_eq_iteratedDeriv (n := 3) hUnique
        (hy.contDiffAt.of_le (by norm_num)) ht_mem_loc
    have h0 :
        iteratedDerivWithin 0 y (Set.Icc t (t + r)) t = y t := by
      simp [iteratedDerivWithin_zero]
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero, h0, h1, h2, h3]
    simp only [smul_eq_mul, Nat.factorial_zero, Nat.factorial_one,
      Nat.factorial_succ, Nat.cast_one, Nat.cast_ofNat, Nat.cast_succ,
      Nat.cast_mul, pow_zero, pow_one, mul_one, one_mul, zero_add,
      inv_one, Nat.factorial]
    ring
  -- Conclude.
  have hξ_in : ξ ∈ Set.Icc a b :=
    ⟨by linarith [hξ_mem.1, ht.1], by linarith [hξ_mem.2, htr.2]⟩
  have hbnd_ξ : |iteratedDeriv 4 y ξ| ≤ M := hbnd ξ hξ_in
  have h_eq :
      y (t + r) - y t - r * deriv y t
          - r ^ 2 / 2 * iteratedDeriv 2 y t
          - r ^ 3 / 6 * iteratedDeriv 3 y t
        = iteratedDeriv 4 y ξ * r ^ 4 / 24 := by
    have := hξ_eq
    rw [h_taylor] at this
    linarith
  rw [h_eq]
  rw [show iteratedDeriv 4 y ξ * r ^ 4 / 24
      = (iteratedDeriv 4 y ξ) * (r ^ 4 / 24) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 4 / 24)]
  calc |iteratedDeriv 4 y ξ| * (r ^ 4 / 24)
      ≤ M * (r ^ 4 / 24) :=
        mul_le_mul_of_nonneg_right hbnd_ξ (by positivity)
    _ = M / 24 * r ^ 4 := by ring

/-- Pointwise third-order Taylor (Lagrange) remainder bound for the
derivative: if `y` is `C^4` and `|iteratedDeriv 4 y| ≤ M` on `[a, b]`,
then for `t, t + r ∈ [a, b]` with `r ≥ 0`,
`|y'(t+r) - y'(t) - r·y''(t) - r²/2 · y'''(t)| ≤ M/6 · r³`. -/
private theorem derivY_third_order_taylor_remainder
    {y : ℝ → ℝ} (hy : ContDiff ℝ 4 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 4 y t| ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    |deriv y (t + r) - deriv y t - r * iteratedDeriv 2 y t
        - r ^ 2 / 2 * iteratedDeriv 3 y t|
      ≤ M / 6 * r ^ 3 := by
  by_cases hr' : r = 0
  · subst hr'; simp
  have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr')
  have htlt : t < t + r := by linarith
  have hUnique : UniqueDiffOn ℝ (Set.Icc t (t + r)) := uniqueDiffOn_Icc htlt
  have ht_mem_loc : t ∈ Set.Icc t (t + r) := Set.left_mem_Icc.mpr htlt.le
  -- `deriv y` is `C^3` (since `y` is `C^4`).
  have hdy : ContDiff ℝ 3 (deriv y) := hy.deriv'
  -- Lagrange Taylor at order 2 for `deriv y` on `[t, t+r]`.
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ : ∃ ξ ∈ Set.Ioo t (t + r),
      deriv y (t + r) - taylorWithinEval (deriv y) 2 (Set.Icc t (t + r)) t (t + r)
        = iteratedDeriv 3 (deriv y) ξ * r ^ 3 / 6 := by
    have hcdo : ContDiffOn ℝ 3 (deriv y) (Set.Icc t (t + r)) :=
      hdy.contDiffOn.of_le le_rfl
    have ⟨ξ, hξ_mem, hξ_eq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) htlt hcdo
    refine ⟨ξ, hξ_mem, ?_⟩
    have hpow : (t + r - t) ^ 3 = r ^ 3 := by ring
    have hfact : (((2 + 1 : ℕ).factorial : ℝ)) = 6 := by
      simp [Nat.factorial]
    rw [hξ_eq, hpow, hfact]
  -- Compute the Taylor polynomial.
  have h_taylor :
      taylorWithinEval (deriv y) 2 (Set.Icc t (t + r)) t (t + r)
        = deriv y t + r * iteratedDeriv 2 y t
              + r ^ 2 / 2 * iteratedDeriv 3 y t := by
    have h0 :
        iteratedDerivWithin 0 (deriv y) (Set.Icc t (t + r)) t = deriv y t := by
      simp [iteratedDerivWithin_zero]
    have h1 :
        iteratedDerivWithin 1 (deriv y) (Set.Icc t (t + r)) t
          = iteratedDeriv 2 y t := by
      have heq := iteratedDerivWithin_eq_iteratedDeriv (n := 1) hUnique
        (hdy.contDiffAt.of_le (by norm_num)) ht_mem_loc
      simp only [iteratedDeriv_one] at heq
      rw [heq]
      rw [show iteratedDeriv 2 y = deriv (iteratedDeriv 1 y) from iteratedDeriv_succ]
      rw [iteratedDeriv_one]
    have h2 :
        iteratedDerivWithin 2 (deriv y) (Set.Icc t (t + r)) t
          = iteratedDeriv 3 y t := by
      have heq := iteratedDerivWithin_eq_iteratedDeriv (n := 2) hUnique
        (hdy.contDiffAt.of_le (by norm_num)) ht_mem_loc
      rw [heq]
      have : iteratedDeriv 3 y = iteratedDeriv 2 (deriv y) :=
        iteratedDeriv_succ' (n := 2) (f := y)
      rw [this]
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2]
    simp only [smul_eq_mul, Nat.factorial_zero, Nat.factorial_one,
      Nat.factorial_succ, Nat.cast_one, Nat.cast_ofNat, Nat.cast_succ,
      Nat.cast_mul, pow_zero, pow_one, mul_one, one_mul, zero_add,
      inv_one, Nat.factorial]
    ring
  -- Bound `iteratedDeriv 3 (deriv y) ξ = iteratedDeriv 4 y ξ`.
  have hidd_eq : iteratedDeriv 3 (deriv y) = iteratedDeriv 4 y := by
    have : iteratedDeriv 4 y = iteratedDeriv 3 (deriv y) :=
      iteratedDeriv_succ' (n := 3) (f := y)
    exact this.symm
  have hξ_in : ξ ∈ Set.Icc a b :=
    ⟨by linarith [hξ_mem.1, ht.1], by linarith [hξ_mem.2, htr.2]⟩
  have hbnd_ξ : |iteratedDeriv 4 y ξ| ≤ M := hbnd ξ hξ_in
  have h_eq :
      deriv y (t + r) - deriv y t - r * iteratedDeriv 2 y t
          - r ^ 2 / 2 * iteratedDeriv 3 y t
        = iteratedDeriv 4 y ξ * r ^ 3 / 6 := by
    have hraw := hξ_eq
    rw [h_taylor, hidd_eq] at hraw
    linarith
  rw [h_eq]
  rw [show iteratedDeriv 4 y ξ * r ^ 3 / 6
      = (iteratedDeriv 4 y ξ) * (r ^ 3 / 6) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 3 / 6)]
  calc |iteratedDeriv 4 y ξ| * (r ^ 3 / 6)
      ≤ M * (r ^ 3 / 6) :=
        mul_le_mul_of_nonneg_right hbnd_ξ (by positivity)
    _ = M / 6 * r ^ 3 := by ring

/-- Pointwise AB3 truncation residual bound. -/
private theorem ab3_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 4 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 4 y t| ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    |y (t + 3 * h) - y (t + 2 * h)
        - h * ((23 / 12) * deriv y (t + 2 * h)
              - (16 / 12) * deriv y (t + h)
              + (5 / 12) * deriv y t)|
      ≤ (7 : ℝ) * M * h ^ 4 := by
  -- Four Taylor remainders (R_y(2), R_y(3), R_y'(1), R_y'(2)).
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  -- R_y(1): y(t+h) - y(t) - h*y'(t) - h²/2*y''(t) - h³/6*y'''(t).
  -- (Not needed; only R_y(2) and R_y(3) appear.)
  -- R_y(2): y(t+2h) - y(t) - 2h*y'(t) - 2h²*y''(t) - (4h³/3)*y'''(t).
  have hRy2 :=
    y_fourth_order_taylor_remainder hy hbnd ht ht2h h2h
  -- R_y(3): y(t+3h) - y(t) - 3h*y'(t) - (9h²/2)*y''(t) - (9h³/2)*y'''(t).
  have hRy3 :=
    y_fourth_order_taylor_remainder hy hbnd ht ht3h h3h
  -- R_y'(1): y'(t+h) - y'(t) - h*y''(t) - (h²/2)*y'''(t).
  have hRyp1 :=
    derivY_third_order_taylor_remainder hy hbnd ht hth hh
  -- R_y'(2): y'(t+2h) - y'(t) - 2h*y''(t) - 2h²*y'''(t).
  have hRyp2 :=
    derivY_third_order_taylor_remainder hy hbnd ht ht2h h2h
  -- Abbreviations.
  set y0 := y t with hy0_def
  set y2 := y (t + 2 * h) with hy2_def
  set y3 := y (t + 3 * h) with hy3_def
  set d0 := deriv y t with hd0_def
  set d1 := deriv y (t + h) with hd1_def
  set d2 := deriv y (t + 2 * h) with hd2_def
  set dd := iteratedDeriv 2 y t with hdd_def
  set ddd := iteratedDeriv 3 y t with hddd_def
  -- Algebraic identity: residual = R_y(3) - R_y(2) - (23h/12)*R_y'(2) + (16h/12)*R_y'(1).
  -- Expand R_y(3), R_y(2), R_y'(2), R_y'(1) and verify the textbook AB3 residual.
  have hLTE_eq :
      y3 - y2 - h * ((23 / 12) * d2 - (16 / 12) * d1 + (5 / 12) * d0)
        = (y3 - y0 - (3 * h) * d0
              - (3 * h) ^ 2 / 2 * dd - (3 * h) ^ 3 / 6 * ddd)
          - (y2 - y0 - (2 * h) * d0
              - (2 * h) ^ 2 / 2 * dd - (2 * h) ^ 3 / 6 * ddd)
          - (23 * h / 12)
              * (d2 - d0 - (2 * h) * dd - (2 * h) ^ 2 / 2 * ddd)
          + (16 * h / 12)
              * (d1 - d0 - h * dd - h ^ 2 / 2 * ddd) := by ring
  rw [hLTE_eq]
  -- Triangle inequality (chained).
  set A := y3 - y0 - (3 * h) * d0
            - (3 * h) ^ 2 / 2 * dd - (3 * h) ^ 3 / 6 * ddd with hA_def
  set B := y2 - y0 - (2 * h) * d0
            - (2 * h) ^ 2 / 2 * dd - (2 * h) ^ 3 / 6 * ddd with hB_def
  set C := d2 - d0 - (2 * h) * dd - (2 * h) ^ 2 / 2 * ddd with hC_def
  set D := d1 - d0 - h * dd - h ^ 2 / 2 * ddd with hD_def
  have h23h_nn : 0 ≤ 23 * h / 12 := by linarith
  have h16h_nn : 0 ≤ 16 * h / 12 := by linarith
  have habs23 : |(23 * h / 12) * C| = (23 * h / 12) * |C| := by
    rw [abs_mul, abs_of_nonneg h23h_nn]
  have habs16 : |(16 * h / 12) * D| = (16 * h / 12) * |D| := by
    rw [abs_mul, abs_of_nonneg h16h_nn]
  have htri : |A - B - (23 * h / 12) * C + (16 * h / 12) * D|
      ≤ |A| + |B| + (23 * h / 12) * |C| + (16 * h / 12) * |D| := by
    have h1 : |A - B - (23 * h / 12) * C + (16 * h / 12) * D|
        ≤ |A - B - (23 * h / 12) * C| + |(16 * h / 12) * D| :=
      abs_add_le _ _
    have h2 : |A - B - (23 * h / 12) * C|
        ≤ |A - B| + |(23 * h / 12) * C| := abs_sub _ _
    have h3 : |A - B| ≤ |A| + |B| := abs_sub _ _
    linarith [habs23.le, habs23.ge, habs16.le, habs16.ge]
  -- Bounds on each piece.
  have hA_bd : |A| ≤ M / 24 * (3 * h) ^ 4 := hRy3
  have hB_bd : |B| ≤ M / 24 * (2 * h) ^ 4 := hRy2
  have hC_bd : |C| ≤ M / 6 * (2 * h) ^ 3 := hRyp2
  have hD_bd : |D| ≤ M / 6 * h ^ 3 := hRyp1
  -- Multiply scaled bounds.
  have h23C_bd : (23 * h / 12) * |C| ≤ (23 * h / 12) * (M / 6 * (2 * h) ^ 3) :=
    mul_le_mul_of_nonneg_left hC_bd h23h_nn
  have h16D_bd : (16 * h / 12) * |D| ≤ (16 * h / 12) * (M / 6 * h ^ 3) :=
    mul_le_mul_of_nonneg_left hD_bd h16h_nn
  -- Sum of upper bounds: 27/8 + 2/3 + 23/9 + 2/9 = 491/72 ≤ 7.
  have hbound_alg :
      M / 24 * (3 * h) ^ 4 + M / 24 * (2 * h) ^ 4
        + (23 * h / 12) * (M / 6 * (2 * h) ^ 3)
        + (16 * h / 12) * (M / 6 * h ^ 3)
        = (491 / 72 : ℝ) * M * h ^ 4 := by ring
  -- 491/72 ≤ 7 → over-estimate by 7 * M * h^4.
  -- Combine.
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (abs_nonneg _).trans this
  have hh4_nn : 0 ≤ h ^ 4 := by positivity
  have hslack : (491 / 72 : ℝ) * M * h ^ 4 ≤ 7 * M * h ^ 4 := by
    have : (491 / 72 : ℝ) ≤ 7 := by norm_num
    nlinarith [hMnn, hh4_nn]
  linarith [htri, hA_bd, hB_bd, h23C_bd, h16D_bd, hbound_alg.le,
    hbound_alg.ge, hslack]

/-- Uniform bound on the AB3 one-step truncation residual on a finite
horizon, given a `C^4` exact solution. -/
theorem ab3_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 4 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 3) * h ≤ T →
        |adamsBashforth3.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 4 := by
  -- Compact sample interval `[t₀, t₀ + T + 1]` covers all `t + kh` with `k ≤ 3`.
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_four_bounded_on_Icc hy t₀ (t₀ + T + 1)
  refine ⟨(7 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
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
  -- Rewrite the LTE in textbook form.
  rw [ab3_localTruncationError_eq]
  show |y (t + 3 * h) - y (t + 2 * h)
      - h * (23 / 12 * deriv y (t + 2 * h)
              - 16 / 12 * deriv y (t + h)
              + 5 / 12 * deriv y t)|
    ≤ 7 * M * h ^ 4
  -- The two presentations of `(23/12) * d2` agree literally.
  have hreshape :
      h * (23 / 12 * deriv y (t + 2 * h)
            - 16 / 12 * deriv y (t + h)
            + 5 / 12 * deriv y t)
        = h * ((23 / 12) * deriv y (t + 2 * h)
              - (16 / 12) * deriv y (t + h)
              + (5 / 12) * deriv y t) := by ring
  rw [hreshape]
  exact ab3_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem hh.le

/-- Final AB3 global error bound on `[t₀, t₀ + T]`. Under Lipschitz `f`,
`C^4` exact solution `y` with `deriv y t = f t (y t)`, and starting
errors `|y_i - y(t_i)| ≤ ε₀` for `i = 0, 1, 2`, the AB3 iterate error
obeys `O(ε₀ + h^3)` on a finite horizon. -/
theorem ab3_global_error_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 4 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      ∀ {y₀ y₁ y₂ ε₀ : ℝ}, 0 ≤ ε₀ →
      |y₀ - y t₀| ≤ ε₀ → |y₁ - y (t₀ + h)| ≤ ε₀ →
      |y₂ - y (t₀ + 2 * h)| ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 2) * h ≤ T →
      |ab3Iter h f t₀ y₀ y₁ y₂ N - y (t₀ + (N : ℝ) * h)|
        ≤ Real.exp ((11 / 3) * L * T) * ε₀ + K * h ^ 3 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    ab3_local_residual_bound hy t₀ T hT
  refine ⟨T * Real.exp ((11 / 3) * L * T) * C, δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
  intro h hh hδ_le y₀ y₁ y₂ ε₀ hε₀ he0_bd he1_bd he2_bd N hNh
  -- Error sequence and 3-window max-norm sequence.
  set eN : ℕ → ℝ :=
    fun k => |ab3Iter h f t₀ y₀ y₁ y₂ k - y (t₀ + (k : ℝ) * h)| with heN_def
  set EN : ℕ → ℝ :=
    fun k => max (max (eN k) (eN (k + 1))) (eN (k + 2)) with hEN_def
  have heN_nn : ∀ k, 0 ≤ eN k := fun _ => abs_nonneg _
  have hEN_nn : ∀ k, 0 ≤ EN k := fun k =>
    le_max_of_le_left (le_max_of_le_left (heN_nn k))
  -- Initial bound: EN 0 ≤ ε₀.
  have hEN0_le : EN 0 ≤ ε₀ := by
    show max (max (eN 0) (eN 1)) (eN 2) ≤ ε₀
    refine max_le (max_le ?_ ?_) ?_
    · show |ab3Iter h f t₀ y₀ y₁ y₂ 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)| ≤ ε₀
      simpa using he0_bd
    · show |ab3Iter h f t₀ y₀ y₁ y₂ 1 - y (t₀ + ((1 : ℕ) : ℝ) * h)| ≤ ε₀
      have hcast : ((1 : ℕ) : ℝ) * h = h := by push_cast; ring
      rw [hcast]
      have h0 : (t₀ + h) = (t₀ + h) := rfl
      simpa using he1_bd
    · show |ab3Iter h f t₀ y₀ y₁ y₂ 2 - y (t₀ + ((2 : ℕ) : ℝ) * h)| ≤ ε₀
      have hcast : ((2 : ℕ) : ℝ) * h = 2 * h := by push_cast; ring
      rw [hcast]
      simpa using he2_bd
  have hLeff_nn : (0 : ℝ) ≤ (11 / 3) * L := by positivity
  -- The general recurrence: when (n + 3) * h ≤ T,
  -- EN (n+1) ≤ (1 + h*((11/3)*L)) * EN n + C * h^4.
  have hstep_general : ∀ n : ℕ, ((n : ℝ) + 3) * h ≤ T →
      EN (n + 1) ≤ (1 + h * ((11 / 3) * L)) * EN n + C * h ^ 4 := by
    intro n hnh_le
    have honestep := ab3_one_step_error_bound (h := h) (L := L)
        hh.le hL hf t₀ y₀ y₁ y₂ y hyf n
    have hres := hresidual hh hδ_le n hnh_le
    have hcast1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hcast2 : ((n + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    have hcast3 : ((n + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
    have heq_eN_n : eN n
        = |ab3Iter h f t₀ y₀ y₁ y₂ n - y (t₀ + (n : ℝ) * h)| := rfl
    have heq_eN_n1 : eN (n + 1)
        = |ab3Iter h f t₀ y₀ y₁ y₂ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)| := by
      show |_ - _| = _
      rw [hcast1]
    have heq_eN_n2 : eN (n + 1 + 1)
        = |ab3Iter h f t₀ y₀ y₁ y₂ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)| := by
      show |_ - _| = _
      rw [hcast2]
    have heq_eN_n3 : eN (n + 1 + 1 + 1)
        = |ab3Iter h f t₀ y₀ y₁ y₂ (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)| := by
      show |_ - _| = _
      rw [hcast3]
    show max (max (eN (n + 1)) (eN (n + 1 + 1))) (eN (n + 1 + 1 + 1))
        ≤ (1 + h * ((11 / 3) * L)) * max (max (eN n) (eN (n + 1))) (eN (n + 1 + 1))
          + C * h ^ 4
    rw [heq_eN_n, heq_eN_n1, heq_eN_n2, heq_eN_n3]
    -- The inner `(eN (n+1))` on the RHS rewrites to itself; honestep closes this.
    linarith [honestep, hres]
  -- Split on N: cases for N = 0, 1, 2 are direct from initial bounds; otherwise Gronwall.
  have hexp_ge : (1 : ℝ) ≤ Real.exp ((11 / 3) * L * T) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hKnn : 0 ≤ T * Real.exp ((11 / 3) * L * T) * C :=
    mul_nonneg (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
  have hh3_nn : 0 ≤ h ^ 3 := by positivity
  have hexp_nn : 0 ≤ Real.exp ((11 / 3) * L * T) := Real.exp_nonneg _
  -- Helper: any base error ≤ ε₀ implies the headline bound.
  have hbase_to_headline : ∀ q : ℝ, q ≤ ε₀ →
      q ≤ Real.exp ((11 / 3) * L * T) * ε₀
            + T * Real.exp ((11 / 3) * L * T) * C * h ^ 3 := by
    intro q hq
    have hexp_ε₀ : ε₀ ≤ Real.exp ((11 / 3) * L * T) * ε₀ := by
      have hone : (1 : ℝ) * ε₀ ≤ Real.exp ((11 / 3) * L * T) * ε₀ :=
        mul_le_mul_of_nonneg_right hexp_ge hε₀
      linarith
    have hKh3_nn : 0 ≤ T * Real.exp ((11 / 3) * L * T) * C * h ^ 3 :=
      mul_nonneg hKnn hh3_nn
    linarith
  match N, hNh with
  | 0, _ =>
    have hbase : |ab3Iter h f t₀ y₀ y₁ y₂ 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)|
        ≤ ε₀ := by simpa using he0_bd
    exact hbase_to_headline _ hbase
  | 1, _ =>
    have hbase : |ab3Iter h f t₀ y₀ y₁ y₂ 1 - y (t₀ + ((1 : ℕ) : ℝ) * h)|
        ≤ ε₀ := by
      have hcast : ((1 : ℕ) : ℝ) * h = h := by push_cast; ring
      rw [hcast]; simpa using he1_bd
    exact hbase_to_headline _ hbase
  | 2, _ =>
    have hbase : |ab3Iter h f t₀ y₀ y₁ y₂ 2 - y (t₀ + ((2 : ℕ) : ℝ) * h)|
        ≤ ε₀ := by
      have hcast : ((2 : ℕ) : ℝ) * h = 2 * h := by push_cast; ring
      rw [hcast]; simpa using he2_bd
    exact hbase_to_headline _ hbase
  | N' + 3, hNh =>
    -- Apply Gronwall to EN at index N'+1, then use EN_{N'+1} ≥ e_{N'+3}.
    have hcast : (((N' + 3 : ℕ) : ℝ)) = (N' : ℝ) + 3 := by push_cast; ring
    have hN_hyp : ((N' : ℝ) + 3) * h ≤ T := by
      have := hNh
      rw [hcast] at this
      linarith
    have hgronwall_step : ∀ n, n < N' + 1 →
        EN (n + 1) ≤ (1 + h * ((11 / 3) * L)) * EN n + C * h ^ (3 + 1) := by
      intro n hn_lt
      have hpow : C * h ^ (3 + 1) = C * h ^ 4 := by norm_num
      rw [hpow]
      apply hstep_general
      have hn1_le_N' : (n : ℝ) + 1 ≤ (N' : ℝ) + 1 := by
        have : (n : ℝ) ≤ (N' : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp hn_lt
        linarith
      have h_le_chain : (n : ℝ) + 3 ≤ (N' : ℝ) + 3 := by linarith
      have h_mul : ((n : ℝ) + 3) * h ≤ ((N' : ℝ) + 3) * h :=
        mul_le_mul_of_nonneg_right h_le_chain hh.le
      linarith
    have hN'1h_le_T : ((N' + 1 : ℕ) : ℝ) * h ≤ T := by
      have hcast' : ((N' + 1 : ℕ) : ℝ) = (N' : ℝ) + 1 := by push_cast; ring
      rw [hcast']
      have : (N' : ℝ) + 1 ≤ (N' : ℝ) + 3 := by linarith
      have := mul_le_mul_of_nonneg_right this hh.le
      linarith
    have hgronwall :=
      lmm_error_bound_from_local_truncation
        (h := h) (L := (11 / 3) * L) (C := C) (T := T) (p := 3)
        (e := EN) (N := N' + 1)
        hh.le hLeff_nn hC_nn (hEN_nn 0) hgronwall_step (N' + 1) le_rfl hN'1h_le_T
    -- eN (N' + 3) ≤ EN (N' + 1).
    have heN_le_EN : eN (N' + 3) ≤ EN (N' + 1) := by
      show eN (N' + 3) ≤ max (max (eN (N' + 1)) (eN (N' + 1 + 1))) (eN (N' + 1 + 2))
      have heq : N' + 3 = N' + 1 + 2 := by ring
      rw [heq]
      exact le_max_right _ _
    have h_chain :
        Real.exp ((11 / 3) * L * T) * EN 0 ≤ Real.exp ((11 / 3) * L * T) * ε₀ :=
      mul_le_mul_of_nonneg_left hEN0_le hexp_nn
    show |ab3Iter h f t₀ y₀ y₁ y₂ (N' + 3) - y (t₀ + ((N' + 3 : ℕ) : ℝ) * h)|
        ≤ Real.exp ((11 / 3) * L * T) * ε₀
          + T * Real.exp ((11 / 3) * L * T) * C * h ^ 3
    have heN_eq :
        eN (N' + 3)
          = |ab3Iter h f t₀ y₀ y₁ y₂ (N' + 3)
              - y (t₀ + ((N' + 3 : ℕ) : ℝ) * h)| := rfl
    linarith [heN_le_EN, hgronwall, h_chain, heN_eq.symm.le, heN_eq.le]

end LMM
