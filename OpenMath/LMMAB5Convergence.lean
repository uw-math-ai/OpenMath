import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp

/-! ## Adams–Bashforth 5-step Convergence Chain (Iserles §1.2)

Order-5 explicit 5-step LMM convergence scaffold. Mirrors the AB4 chain
in `OpenMath.LMMAB4Convergence` at the next order. The AB5 step takes
five starting samples and combines five prior `f` evaluations. The
effective max-window Lipschitz constant is `(551/45) · L`, the residual
is `O(h^6)` and the headline global error bound is `O(ε₀ + h^5)`. -/

namespace LMM

/-- AB5 iteration with five starting samples `y₀, y₁, y₂, y₃, y₄`:
`y_{n+5} = y_{n+4} + h · ((1901/720) · f_{n+4} − (2774/720) · f_{n+3}
  + (2616/720) · f_{n+2} − (1274/720) · f_{n+1} + (251/720) · f_n)`. -/
noncomputable def ab5Iter
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ : ℝ) : ℕ → ℝ
  | 0 => y₀
  | 1 => y₁
  | 2 => y₂
  | 3 => y₃
  | 4 => y₄
  | n + 5 =>
      ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 4)
        + h * (1901 / 720 * f (t₀ + ((n : ℝ) + 4) * h)
                (ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 4))
              - 2774 / 720 * f (t₀ + ((n : ℝ) + 3) * h)
                (ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 3))
              + 2616 / 720 * f (t₀ + ((n : ℝ) + 2) * h)
                (ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 2))
              - 1274 / 720 * f (t₀ + ((n : ℝ) + 1) * h)
                (ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 1))
              + 251 / 720 * f (t₀ + (n : ℝ) * h)
                (ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ n))

@[simp] lemma ab5Iter_zero
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ : ℝ) :
    ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ 0 = y₀ := rfl

@[simp] lemma ab5Iter_one
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ : ℝ) :
    ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ 1 = y₁ := rfl

@[simp] lemma ab5Iter_two
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ : ℝ) :
    ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ 2 = y₂ := rfl

@[simp] lemma ab5Iter_three
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ : ℝ) :
    ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ 3 = y₃ := rfl

@[simp] lemma ab5Iter_four
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ : ℝ) :
    ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ 4 = y₄ := rfl

lemma ab5Iter_succ_succ_succ_succ_succ
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ : ℝ) (n : ℕ) :
    ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 5)
      = ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 4)
          + h * (1901 / 720 * f (t₀ + ((n : ℝ) + 4) * h)
                  (ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 4))
                - 2774 / 720 * f (t₀ + ((n : ℝ) + 3) * h)
                    (ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 3))
                + 2616 / 720 * f (t₀ + ((n : ℝ) + 2) * h)
                    (ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 2))
                - 1274 / 720 * f (t₀ + ((n : ℝ) + 1) * h)
                    (ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 1))
                + 251 / 720 * f (t₀ + (n : ℝ) * h)
                    (ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ n)) := rfl

/-- AB5 local truncation operator reduces to the textbook 5-step residual
`y(t + 5h) − y(t + 4h) − h · ((1901/720) y'(t + 4h) − (2774/720) y'(t + 3h)
  + (2616/720) y'(t + 2h) − (1274/720) y'(t + h) + (251/720) y'(t))`. -/
theorem ab5_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    adamsBashforth5.localTruncationError h t y
      = y (t + 5 * h) - y (t + 4 * h)
          - h * (1901 / 720 * deriv y (t + 4 * h)
                  - 2774 / 720 * deriv y (t + 3 * h)
                  + 2616 / 720 * deriv y (t + 2 * h)
                  - 1274 / 720 * deriv y (t + h)
                  + 251 / 720 * deriv y t) := by
  unfold localTruncationError truncationOp
  simp [adamsBashforth5, Fin.sum_univ_succ, iteratedDeriv_one,
    iteratedDeriv_zero]
  ring

/-- One-step AB5 Lipschitz step: a single linearised increment of the
global error from steps `n, n+1, n+2, n+3, n+4` to `n+5`, with five
Lipschitz contributions and additive `|τ_n|`. -/
theorem ab5_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ y₁ y₂ y₃ y₄ : ℝ) (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|
      ≤ |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|
        + (1901 / 720) * h * L
            * |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 4)
                - y (t₀ + ((n : ℝ) + 4) * h)|
        + (2774 / 720) * h * L
            * |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 3)
                - y (t₀ + ((n : ℝ) + 3) * h)|
        + (2616 / 720) * h * L
            * |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 2)
                - y (t₀ + ((n : ℝ) + 2) * h)|
        + (1274 / 720) * h * L
            * |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 1)
                - y (t₀ + ((n : ℝ) + 1) * h)|
        + (251 / 720) * h * L
            * |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ n - y (t₀ + (n : ℝ) * h)|
        + |adamsBashforth5.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set yn : ℝ := ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ n with hyn_def
  set yn1 : ℝ := ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 1) with hyn1_def
  set yn2 : ℝ := ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 2) with hyn2_def
  set yn3 : ℝ := ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 3) with hyn3_def
  set yn4 : ℝ := ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 4) with hyn4_def
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
  set τ : ℝ := adamsBashforth5.localTruncationError h tn y with hτ_def
  -- AB5 step formula.
  have hstep : ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 5)
      = yn4 + h * (1901 / 720 * f tn4 yn4
                    - 2774 / 720 * f tn3 yn3
                    + 2616 / 720 * f tn2 yn2
                    - 1274 / 720 * f tn1 yn1
                    + 251 / 720 * f tn yn) := by
    show ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 5) = _
    rw [ab5Iter_succ_succ_succ_succ_succ]
  -- Time arithmetic.
  have htn1_h : tn + h = tn1 := by simp [htn_def, htn1_def]; ring
  have htn_2h : tn + 2 * h = tn2 := by simp [htn_def, htn2_def]; ring
  have htn_3h : tn + 3 * h = tn3 := by simp [htn_def, htn3_def]; ring
  have htn_4h : tn + 4 * h = tn4 := by simp [htn_def, htn4_def]; ring
  have htn_5h : tn + 5 * h = tn5 := by simp [htn_def, htn5_def]; ring
  -- LTE residual at `tn`, expressed via `f` along the trajectory.
  have hτ_eq : τ = zn5 - zn4
        - h * (1901 / 720 * f tn4 zn4 - 2774 / 720 * f tn3 zn3
              + 2616 / 720 * f tn2 zn2 - 1274 / 720 * f tn1 zn1
              + 251 / 720 * f tn zn) := by
    show adamsBashforth5.localTruncationError h tn y = _
    rw [ab5_localTruncationError_eq, htn1_h, htn_2h, htn_3h, htn_4h, htn_5h,
      hyf tn4, hyf tn3, hyf tn2, hyf tn1, hyf tn]
  -- Algebraic decomposition of the global error increment.
  have halg : ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 5) - zn5
      = (yn4 - zn4)
        + (1901 / 720) * h * (f tn4 yn4 - f tn4 zn4)
        - (2774 / 720) * h * (f tn3 yn3 - f tn3 zn3)
        + (2616 / 720) * h * (f tn2 yn2 - f tn2 zn2)
        - (1274 / 720) * h * (f tn1 yn1 - f tn1 zn1)
        + (251 / 720) * h * (f tn yn - f tn zn)
        - τ := by
    rw [hstep, hτ_eq]; ring
  -- Lipschitz bounds on the five `f` increments.
  have hLip4 : |f tn4 yn4 - f tn4 zn4| ≤ L * |yn4 - zn4| := hf tn4 yn4 zn4
  have hLip3 : |f tn3 yn3 - f tn3 zn3| ≤ L * |yn3 - zn3| := hf tn3 yn3 zn3
  have hLip2 : |f tn2 yn2 - f tn2 zn2| ≤ L * |yn2 - zn2| := hf tn2 yn2 zn2
  have hLip1 : |f tn1 yn1 - f tn1 zn1| ≤ L * |yn1 - zn1| := hf tn1 yn1 zn1
  have hLip0 : |f tn yn - f tn zn| ≤ L * |yn - zn| := hf tn yn zn
  have h1901_nn : 0 ≤ (1901 / 720) * h := by linarith
  have h2774_nn : 0 ≤ (2774 / 720) * h := by linarith
  have h2616_nn : 0 ≤ (2616 / 720) * h := by linarith
  have h1274_nn : 0 ≤ (1274 / 720) * h := by linarith
  have h251_nn : 0 ≤ (251 / 720) * h := by linarith
  have h1901_abs : |(1901 / 720) * h * (f tn4 yn4 - f tn4 zn4)|
      ≤ (1901 / 720) * h * L * |yn4 - zn4| := by
    rw [abs_mul, abs_of_nonneg h1901_nn]
    calc (1901 / 720) * h * |f tn4 yn4 - f tn4 zn4|
        ≤ (1901 / 720) * h * (L * |yn4 - zn4|) :=
          mul_le_mul_of_nonneg_left hLip4 h1901_nn
      _ = (1901 / 720) * h * L * |yn4 - zn4| := by ring
  have h2774_abs : |(2774 / 720) * h * (f tn3 yn3 - f tn3 zn3)|
      ≤ (2774 / 720) * h * L * |yn3 - zn3| := by
    rw [abs_mul, abs_of_nonneg h2774_nn]
    calc (2774 / 720) * h * |f tn3 yn3 - f tn3 zn3|
        ≤ (2774 / 720) * h * (L * |yn3 - zn3|) :=
          mul_le_mul_of_nonneg_left hLip3 h2774_nn
      _ = (2774 / 720) * h * L * |yn3 - zn3| := by ring
  have h2616_abs : |(2616 / 720) * h * (f tn2 yn2 - f tn2 zn2)|
      ≤ (2616 / 720) * h * L * |yn2 - zn2| := by
    rw [abs_mul, abs_of_nonneg h2616_nn]
    calc (2616 / 720) * h * |f tn2 yn2 - f tn2 zn2|
        ≤ (2616 / 720) * h * (L * |yn2 - zn2|) :=
          mul_le_mul_of_nonneg_left hLip2 h2616_nn
      _ = (2616 / 720) * h * L * |yn2 - zn2| := by ring
  have h1274_abs : |(1274 / 720) * h * (f tn1 yn1 - f tn1 zn1)|
      ≤ (1274 / 720) * h * L * |yn1 - zn1| := by
    rw [abs_mul, abs_of_nonneg h1274_nn]
    calc (1274 / 720) * h * |f tn1 yn1 - f tn1 zn1|
        ≤ (1274 / 720) * h * (L * |yn1 - zn1|) :=
          mul_le_mul_of_nonneg_left hLip1 h1274_nn
      _ = (1274 / 720) * h * L * |yn1 - zn1| := by ring
  have h251_abs : |(251 / 720) * h * (f tn yn - f tn zn)|
      ≤ (251 / 720) * h * L * |yn - zn| := by
    rw [abs_mul, abs_of_nonneg h251_nn]
    calc (251 / 720) * h * |f tn yn - f tn zn|
        ≤ (251 / 720) * h * (L * |yn - zn|) :=
          mul_le_mul_of_nonneg_left hLip0 h251_nn
      _ = (251 / 720) * h * L * |yn - zn| := by ring
  -- Triangle inequality (chained six times).
  have htri :
      |(yn4 - zn4)
        + (1901 / 720) * h * (f tn4 yn4 - f tn4 zn4)
        - (2774 / 720) * h * (f tn3 yn3 - f tn3 zn3)
        + (2616 / 720) * h * (f tn2 yn2 - f tn2 zn2)
        - (1274 / 720) * h * (f tn1 yn1 - f tn1 zn1)
        + (251 / 720) * h * (f tn yn - f tn zn)
        - τ|
        ≤ |yn4 - zn4|
          + |(1901 / 720) * h * (f tn4 yn4 - f tn4 zn4)|
          + |(2774 / 720) * h * (f tn3 yn3 - f tn3 zn3)|
          + |(2616 / 720) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(1274 / 720) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(251 / 720) * h * (f tn yn - f tn zn)|
          + |τ| := by
    have h1 :
        |(yn4 - zn4)
          + (1901 / 720) * h * (f tn4 yn4 - f tn4 zn4)
          - (2774 / 720) * h * (f tn3 yn3 - f tn3 zn3)
          + (2616 / 720) * h * (f tn2 yn2 - f tn2 zn2)
          - (1274 / 720) * h * (f tn1 yn1 - f tn1 zn1)
          + (251 / 720) * h * (f tn yn - f tn zn)
          - τ|
          ≤ |(yn4 - zn4)
              + (1901 / 720) * h * (f tn4 yn4 - f tn4 zn4)
              - (2774 / 720) * h * (f tn3 yn3 - f tn3 zn3)
              + (2616 / 720) * h * (f tn2 yn2 - f tn2 zn2)
              - (1274 / 720) * h * (f tn1 yn1 - f tn1 zn1)
              + (251 / 720) * h * (f tn yn - f tn zn)|
            + |τ| := abs_sub _ _
    have h2 :
        |(yn4 - zn4)
          + (1901 / 720) * h * (f tn4 yn4 - f tn4 zn4)
          - (2774 / 720) * h * (f tn3 yn3 - f tn3 zn3)
          + (2616 / 720) * h * (f tn2 yn2 - f tn2 zn2)
          - (1274 / 720) * h * (f tn1 yn1 - f tn1 zn1)
          + (251 / 720) * h * (f tn yn - f tn zn)|
          ≤ |(yn4 - zn4)
              + (1901 / 720) * h * (f tn4 yn4 - f tn4 zn4)
              - (2774 / 720) * h * (f tn3 yn3 - f tn3 zn3)
              + (2616 / 720) * h * (f tn2 yn2 - f tn2 zn2)
              - (1274 / 720) * h * (f tn1 yn1 - f tn1 zn1)|
            + |(251 / 720) * h * (f tn yn - f tn zn)| := abs_add_le _ _
    have h3 :
        |(yn4 - zn4)
          + (1901 / 720) * h * (f tn4 yn4 - f tn4 zn4)
          - (2774 / 720) * h * (f tn3 yn3 - f tn3 zn3)
          + (2616 / 720) * h * (f tn2 yn2 - f tn2 zn2)
          - (1274 / 720) * h * (f tn1 yn1 - f tn1 zn1)|
          ≤ |(yn4 - zn4)
              + (1901 / 720) * h * (f tn4 yn4 - f tn4 zn4)
              - (2774 / 720) * h * (f tn3 yn3 - f tn3 zn3)
              + (2616 / 720) * h * (f tn2 yn2 - f tn2 zn2)|
            + |(1274 / 720) * h * (f tn1 yn1 - f tn1 zn1)| := abs_sub _ _
    have h4 :
        |(yn4 - zn4)
          + (1901 / 720) * h * (f tn4 yn4 - f tn4 zn4)
          - (2774 / 720) * h * (f tn3 yn3 - f tn3 zn3)
          + (2616 / 720) * h * (f tn2 yn2 - f tn2 zn2)|
          ≤ |(yn4 - zn4)
              + (1901 / 720) * h * (f tn4 yn4 - f tn4 zn4)
              - (2774 / 720) * h * (f tn3 yn3 - f tn3 zn3)|
            + |(2616 / 720) * h * (f tn2 yn2 - f tn2 zn2)| := abs_add_le _ _
    have h5 :
        |(yn4 - zn4)
          + (1901 / 720) * h * (f tn4 yn4 - f tn4 zn4)
          - (2774 / 720) * h * (f tn3 yn3 - f tn3 zn3)|
          ≤ |(yn4 - zn4)
              + (1901 / 720) * h * (f tn4 yn4 - f tn4 zn4)|
            + |(2774 / 720) * h * (f tn3 yn3 - f tn3 zn3)| := abs_sub _ _
    have h6 :
        |(yn4 - zn4)
          + (1901 / 720) * h * (f tn4 yn4 - f tn4 zn4)|
          ≤ |yn4 - zn4| + |(1901 / 720) * h * (f tn4 yn4 - f tn4 zn4)| :=
      abs_add_le _ _
    linarith
  calc |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 5) - zn5|
      = |(yn4 - zn4)
          + (1901 / 720) * h * (f tn4 yn4 - f tn4 zn4)
          - (2774 / 720) * h * (f tn3 yn3 - f tn3 zn3)
          + (2616 / 720) * h * (f tn2 yn2 - f tn2 zn2)
          - (1274 / 720) * h * (f tn1 yn1 - f tn1 zn1)
          + (251 / 720) * h * (f tn yn - f tn zn)
          - τ| := by rw [halg]
    _ ≤ |yn4 - zn4|
          + |(1901 / 720) * h * (f tn4 yn4 - f tn4 zn4)|
          + |(2774 / 720) * h * (f tn3 yn3 - f tn3 zn3)|
          + |(2616 / 720) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(1274 / 720) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(251 / 720) * h * (f tn yn - f tn zn)|
          + |τ| := htri
    _ ≤ |yn4 - zn4|
          + (1901 / 720) * h * L * |yn4 - zn4|
          + (2774 / 720) * h * L * |yn3 - zn3|
          + (2616 / 720) * h * L * |yn2 - zn2|
          + (1274 / 720) * h * L * |yn1 - zn1|
          + (251 / 720) * h * L * |yn - zn|
          + |τ| := by
        linarith [h1901_abs, h2774_abs, h2616_abs, h1274_abs, h251_abs]

/-- Max-norm one-step error recurrence for AB5 with Lipschitz constant
`L`. With `eN k := |y_k − y(t_k)|` and
`EN k := max (max (max (max (eN k) (eN (k+1))) (eN (k+2))) (eN (k+3))) (eN (k+4))`,
`EN (n+1) ≤ (1 + h · (551/45) · L) · EN n + |τ_n|`. The `(551/45)` factor is
the ℓ¹-norm of the AB5 coefficient vector
`(1901/720, 2774/720, 2616/720, 1274/720, 251/720)`. -/
theorem ab5_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ y₁ y₂ y₃ y₄ : ℝ) (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max (max (max
          |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
          |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|)
          |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|)
          |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|)
        |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|
      ≤ (1 + h * ((551 / 45) * L))
            * max (max (max (max
                  |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ n
                      - y (t₀ + (n : ℝ) * h)|
                  |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 1)
                      - y (t₀ + ((n : ℝ) + 1) * h)|)
                  |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 2)
                      - y (t₀ + ((n : ℝ) + 2) * h)|)
                  |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 3)
                      - y (t₀ + ((n : ℝ) + 3) * h)|)
                  |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 4)
                      - y (t₀ + ((n : ℝ) + 4) * h)|
        + |adamsBashforth5.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set en : ℝ := |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ n - y (t₀ + (n : ℝ) * h)|
    with hen_def
  set en1 : ℝ :=
    |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
    with hen1_def
  set en2 : ℝ :=
    |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|
    with hen2_def
  set en3 : ℝ :=
    |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|
    with hen3_def
  set en4 : ℝ :=
    |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|
    with hen4_def
  set en5 : ℝ :=
    |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|
    with hen5_def
  set τabs : ℝ :=
    |adamsBashforth5.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  have hen_nn : 0 ≤ en := abs_nonneg _
  have hen1_nn : 0 ≤ en1 := abs_nonneg _
  have hen2_nn : 0 ≤ en2 := abs_nonneg _
  have hen3_nn : 0 ≤ en3 := abs_nonneg _
  have hen4_nn : 0 ≤ en4 := abs_nonneg _
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  -- One-step Lipschitz bound (from `ab5_one_step_lipschitz`).
  have hstep :
      en5 ≤ en4 + (1901 / 720) * h * L * en4
                + (2774 / 720) * h * L * en3
                + (2616 / 720) * h * L * en2
                + (1274 / 720) * h * L * en1
                + (251 / 720) * h * L * en + τabs := by
    have := ab5_one_step_lipschitz hh hf t₀ y₀ y₁ y₂ y₃ y₄ y hyf n
    show |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|
        ≤ |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|
          + (1901 / 720) * h * L
              * |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 4)
                  - y (t₀ + ((n : ℝ) + 4) * h)|
          + (2774 / 720) * h * L
              * |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 3)
                  - y (t₀ + ((n : ℝ) + 3) * h)|
          + (2616 / 720) * h * L
              * |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 2)
                  - y (t₀ + ((n : ℝ) + 2) * h)|
          + (1274 / 720) * h * L
              * |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 1)
                  - y (t₀ + ((n : ℝ) + 1) * h)|
          + (251 / 720) * h * L
              * |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ n - y (t₀ + (n : ℝ) * h)|
          + |adamsBashforth5.localTruncationError h (t₀ + (n : ℝ) * h) y|
    exact this
  set EN_n : ℝ := max (max (max (max en en1) en2) en3) en4 with hEN_n_def
  have hen_le_EN : en ≤ EN_n :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)
  have hen1_le_EN : en1 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)
  have hen2_le_EN : en2 ≤ EN_n :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hen3_le_EN : en3 ≤ EN_n :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hen4_le_EN : en4 ≤ EN_n := le_max_right _ _
  have h1901_nn : 0 ≤ (1901 / 720) * h * L := by positivity
  have h2774_nn : 0 ≤ (2774 / 720) * h * L := by positivity
  have h2616_nn : 0 ≤ (2616 / 720) * h * L := by positivity
  have h1274_nn : 0 ≤ (1274 / 720) * h * L := by positivity
  have h251_nn : 0 ≤ (251 / 720) * h * L := by positivity
  have hEN_nn : 0 ≤ EN_n := le_trans hen_nn hen_le_EN
  have hcoef_nn : 0 ≤ h * ((551 / 45) * L) := by positivity
  -- en5 ≤ (1 + h*(551/45*L)) * EN_n + τabs.
  have hen5_bd : en5 ≤ (1 + h * ((551 / 45) * L)) * EN_n + τabs := by
    have h1 : (1901 / 720) * h * L * en4 ≤ (1901 / 720) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen4_le_EN h1901_nn
    have h2 : (2774 / 720) * h * L * en3 ≤ (2774 / 720) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen3_le_EN h2774_nn
    have h3 : (2616 / 720) * h * L * en2 ≤ (2616 / 720) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen2_le_EN h2616_nn
    have h4 : (1274 / 720) * h * L * en1 ≤ (1274 / 720) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen1_le_EN h1274_nn
    have h5 : (251 / 720) * h * L * en ≤ (251 / 720) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen_le_EN h251_nn
    have h_alg :
        EN_n + (1901 / 720) * h * L * EN_n
              + (2774 / 720) * h * L * EN_n
              + (2616 / 720) * h * L * EN_n
              + (1274 / 720) * h * L * EN_n
              + (251 / 720) * h * L * EN_n + τabs
          = (1 + h * ((551 / 45) * L)) * EN_n + τabs := by ring
    linarith [hstep, hen4_le_EN, h1, h2, h3, h4, h5, h_alg.le]
  -- en1, en2, en3, en4 ≤ EN_n ≤ (1 + h*(551/45*L)) * EN_n + τabs.
  have hEN_le_grow : EN_n ≤ (1 + h * ((551 / 45) * L)) * EN_n := by
    have hone : (1 : ℝ) * EN_n ≤ (1 + h * ((551 / 45) * L)) * EN_n :=
      mul_le_mul_of_nonneg_right (by linarith) hEN_nn
    linarith
  have hen1_bd : en1 ≤ (1 + h * ((551 / 45) * L)) * EN_n + τabs := by
    linarith [hen1_le_EN, hEN_le_grow]
  have hen2_bd : en2 ≤ (1 + h * ((551 / 45) * L)) * EN_n + τabs := by
    linarith [hen2_le_EN, hEN_le_grow]
  have hen3_bd : en3 ≤ (1 + h * ((551 / 45) * L)) * EN_n + τabs := by
    linarith [hen3_le_EN, hEN_le_grow]
  have hen4_bd : en4 ≤ (1 + h * ((551 / 45) * L)) * EN_n + τabs := by
    linarith [hen4_le_EN, hEN_le_grow]
  exact max_le (max_le (max_le (max_le hen1_bd hen2_bd) hen3_bd) hen4_bd) hen5_bd

/-- A `C^6` function has its sixth derivative bounded on every compact
interval `[a, b]`. -/
private theorem iteratedDeriv_six_bounded_on_Icc
    {y : ℝ → ℝ} (hy : ContDiff ℝ 6 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, |iteratedDeriv 6 y t| ≤ M := by
  have h_cont : Continuous (iteratedDeriv 6 y) :=
    hy.continuous_iteratedDeriv 6 (by norm_num)
  obtain ⟨M, hM⟩ :=
    IsCompact.exists_bound_of_continuousOn (CompactIccSpace.isCompact_Icc)
      h_cont.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro t ht
  exact (hM t ht).trans (le_max_left _ _)

/-- Pointwise sixth-order Taylor (Lagrange) remainder bound: if `y` is
`C^6` and `|iteratedDeriv 6 y| ≤ M` on `[a, b]`, then for `t, t + r ∈ [a, b]`
with `r ≥ 0`,
`|y(t+r) - y(t) - r·y'(t) - r²/2·y''(t) - r³/6·y'''(t) - r⁴/24·y⁽⁴⁾(t)
  - r⁵/120·y⁽⁵⁾(t)| ≤ M/720 · r⁶`. -/
private theorem y_sixth_order_taylor_remainder
    {y : ℝ → ℝ} (hy : ContDiff ℝ 6 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 6 y t| ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    |y (t + r) - y t - r * deriv y t
        - r ^ 2 / 2 * iteratedDeriv 2 y t
        - r ^ 3 / 6 * iteratedDeriv 3 y t
        - r ^ 4 / 24 * iteratedDeriv 4 y t
        - r ^ 5 / 120 * iteratedDeriv 5 y t|
      ≤ M / 720 * r ^ 6 := by
  by_cases hr' : r = 0
  · subst hr'; simp
  have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr')
  have htlt : t < t + r := by linarith
  have hUnique : UniqueDiffOn ℝ (Set.Icc t (t + r)) := uniqueDiffOn_Icc htlt
  have ht_mem_loc : t ∈ Set.Icc t (t + r) := Set.left_mem_Icc.mpr htlt.le
  -- Lagrange Taylor remainder at order 5 (sixth-derivative form).
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ : ∃ ξ ∈ Set.Ioo t (t + r),
      y (t + r) - taylorWithinEval y 5 (Set.Icc t (t + r)) t (t + r)
        = iteratedDeriv 6 y ξ * r ^ 6 / 720 := by
    have hcdo : ContDiffOn ℝ 6 y (Set.Icc t (t + r)) :=
      hy.contDiffOn.of_le le_rfl
    have ⟨ξ, hξ_mem, hξ_eq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 5) htlt hcdo
    refine ⟨ξ, hξ_mem, ?_⟩
    have hpow : (t + r - t) ^ 6 = r ^ 6 := by ring
    have hfact : (((5 + 1 : ℕ).factorial : ℝ)) = 720 := by
      simp [Nat.factorial]
    rw [hξ_eq, hpow, hfact]
  -- Compute the Taylor polynomial explicitly.
  have h_taylor :
      taylorWithinEval y 5 (Set.Icc t (t + r)) t (t + r)
        = y t + r * deriv y t + r ^ 2 / 2 * iteratedDeriv 2 y t
              + r ^ 3 / 6 * iteratedDeriv 3 y t
              + r ^ 4 / 24 * iteratedDeriv 4 y t
              + r ^ 5 / 120 * iteratedDeriv 5 y t := by
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
    have h4 :
        iteratedDerivWithin 4 y (Set.Icc t (t + r)) t = iteratedDeriv 4 y t :=
      iteratedDerivWithin_eq_iteratedDeriv (n := 4) hUnique
        (hy.contDiffAt.of_le (by norm_num)) ht_mem_loc
    have h5 :
        iteratedDerivWithin 5 y (Set.Icc t (t + r)) t = iteratedDeriv 5 y t :=
      iteratedDerivWithin_eq_iteratedDeriv (n := 5) hUnique
        (hy.contDiffAt.of_le (by norm_num)) ht_mem_loc
    have h0 :
        iteratedDerivWithin 0 y (Set.Icc t (t + r)) t = y t := by
      simp [iteratedDerivWithin_zero]
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, h3, h4, h5]
    simp only [smul_eq_mul, Nat.factorial_zero, Nat.factorial_one,
      Nat.factorial_succ, Nat.cast_one, Nat.cast_ofNat, Nat.cast_succ,
      Nat.cast_mul, pow_zero, pow_one, mul_one, one_mul, zero_add,
      inv_one, Nat.factorial]
    ring
  -- Conclude.
  have hξ_in : ξ ∈ Set.Icc a b :=
    ⟨by linarith [hξ_mem.1, ht.1], by linarith [hξ_mem.2, htr.2]⟩
  have hbnd_ξ : |iteratedDeriv 6 y ξ| ≤ M := hbnd ξ hξ_in
  have h_eq :
      y (t + r) - y t - r * deriv y t
          - r ^ 2 / 2 * iteratedDeriv 2 y t
          - r ^ 3 / 6 * iteratedDeriv 3 y t
          - r ^ 4 / 24 * iteratedDeriv 4 y t
          - r ^ 5 / 120 * iteratedDeriv 5 y t
        = iteratedDeriv 6 y ξ * r ^ 6 / 720 := by
    have := hξ_eq
    rw [h_taylor] at this
    linarith
  rw [h_eq]
  rw [show iteratedDeriv 6 y ξ * r ^ 6 / 720
      = (iteratedDeriv 6 y ξ) * (r ^ 6 / 720) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 6 / 720)]
  calc |iteratedDeriv 6 y ξ| * (r ^ 6 / 720)
      ≤ M * (r ^ 6 / 720) :=
        mul_le_mul_of_nonneg_right hbnd_ξ (by positivity)
    _ = M / 720 * r ^ 6 := by ring

/-- Pointwise fifth-order Taylor (Lagrange) remainder bound for the
derivative: if `y` is `C^6` and `|iteratedDeriv 6 y| ≤ M` on `[a, b]`,
then for `t, t + r ∈ [a, b]` with `r ≥ 0`,
`|y'(t+r) - y'(t) - r·y''(t) - r²/2·y'''(t) - r³/6·y⁽⁴⁾(t) - r⁴/24·y⁽⁵⁾(t)|
  ≤ M/120 · r⁵`. -/
private theorem derivY_fifth_order_taylor_remainder
    {y : ℝ → ℝ} (hy : ContDiff ℝ 6 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 6 y t| ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    |deriv y (t + r) - deriv y t - r * iteratedDeriv 2 y t
        - r ^ 2 / 2 * iteratedDeriv 3 y t
        - r ^ 3 / 6 * iteratedDeriv 4 y t
        - r ^ 4 / 24 * iteratedDeriv 5 y t|
      ≤ M / 120 * r ^ 5 := by
  by_cases hr' : r = 0
  · subst hr'; simp
  have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr')
  have htlt : t < t + r := by linarith
  have hUnique : UniqueDiffOn ℝ (Set.Icc t (t + r)) := uniqueDiffOn_Icc htlt
  have ht_mem_loc : t ∈ Set.Icc t (t + r) := Set.left_mem_Icc.mpr htlt.le
  -- `deriv y` is `C^5` (since `y` is `C^6`).
  have hdy : ContDiff ℝ 5 (deriv y) := hy.deriv'
  -- Lagrange Taylor at order 4 for `deriv y` on `[t, t+r]`.
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ : ∃ ξ ∈ Set.Ioo t (t + r),
      deriv y (t + r) - taylorWithinEval (deriv y) 4 (Set.Icc t (t + r)) t (t + r)
        = iteratedDeriv 5 (deriv y) ξ * r ^ 5 / 120 := by
    have hcdo : ContDiffOn ℝ 5 (deriv y) (Set.Icc t (t + r)) :=
      hdy.contDiffOn.of_le le_rfl
    have ⟨ξ, hξ_mem, hξ_eq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 4) htlt hcdo
    refine ⟨ξ, hξ_mem, ?_⟩
    have hpow : (t + r - t) ^ 5 = r ^ 5 := by ring
    have hfact : (((4 + 1 : ℕ).factorial : ℝ)) = 120 := by
      simp [Nat.factorial]
    rw [hξ_eq, hpow, hfact]
  -- Compute the Taylor polynomial.
  have h_taylor :
      taylorWithinEval (deriv y) 4 (Set.Icc t (t + r)) t (t + r)
        = deriv y t + r * iteratedDeriv 2 y t
              + r ^ 2 / 2 * iteratedDeriv 3 y t
              + r ^ 3 / 6 * iteratedDeriv 4 y t
              + r ^ 4 / 24 * iteratedDeriv 5 y t := by
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
    have h3 :
        iteratedDerivWithin 3 (deriv y) (Set.Icc t (t + r)) t
          = iteratedDeriv 4 y t := by
      have heq := iteratedDerivWithin_eq_iteratedDeriv (n := 3) hUnique
        (hdy.contDiffAt.of_le (by norm_num)) ht_mem_loc
      rw [heq]
      have : iteratedDeriv 4 y = iteratedDeriv 3 (deriv y) :=
        iteratedDeriv_succ' (n := 3) (f := y)
      rw [this]
    have h4 :
        iteratedDerivWithin 4 (deriv y) (Set.Icc t (t + r)) t
          = iteratedDeriv 5 y t := by
      have heq := iteratedDerivWithin_eq_iteratedDeriv (n := 4) hUnique
        (hdy.contDiffAt.of_le (by norm_num)) ht_mem_loc
      rw [heq]
      have : iteratedDeriv 5 y = iteratedDeriv 4 (deriv y) :=
        iteratedDeriv_succ' (n := 4) (f := y)
      rw [this]
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero, h0, h1, h2, h3, h4]
    simp only [smul_eq_mul, Nat.factorial_zero, Nat.factorial_one,
      Nat.factorial_succ, Nat.cast_one, Nat.cast_ofNat, Nat.cast_succ,
      Nat.cast_mul, pow_zero, pow_one, mul_one, one_mul, zero_add,
      inv_one, Nat.factorial]
    ring
  -- Bound `iteratedDeriv 5 (deriv y) ξ = iteratedDeriv 6 y ξ`.
  have hidd_eq : iteratedDeriv 5 (deriv y) = iteratedDeriv 6 y := by
    have : iteratedDeriv 6 y = iteratedDeriv 5 (deriv y) :=
      iteratedDeriv_succ' (n := 5) (f := y)
    exact this.symm
  have hξ_in : ξ ∈ Set.Icc a b :=
    ⟨by linarith [hξ_mem.1, ht.1], by linarith [hξ_mem.2, htr.2]⟩
  have hbnd_ξ : |iteratedDeriv 6 y ξ| ≤ M := hbnd ξ hξ_in
  have h_eq :
      deriv y (t + r) - deriv y t - r * iteratedDeriv 2 y t
          - r ^ 2 / 2 * iteratedDeriv 3 y t
          - r ^ 3 / 6 * iteratedDeriv 4 y t
          - r ^ 4 / 24 * iteratedDeriv 5 y t
        = iteratedDeriv 6 y ξ * r ^ 5 / 120 := by
    have hraw := hξ_eq
    rw [h_taylor, hidd_eq] at hraw
    linarith
  rw [h_eq]
  rw [show iteratedDeriv 6 y ξ * r ^ 5 / 120
      = (iteratedDeriv 6 y ξ) * (r ^ 5 / 120) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 5 / 120)]
  calc |iteratedDeriv 6 y ξ| * (r ^ 5 / 120)
      ≤ M * (r ^ 5 / 120) :=
        mul_le_mul_of_nonneg_right hbnd_ξ (by positivity)
    _ = M / 120 * r ^ 5 := by ring

/-- Pointwise AB5 truncation residual bound. The textbook AB5 residual
expands as
`R_y(5) − R_y(4) − (1901h/720)·R_y'(4) + (2774h/720)·R_y'(3)
  − (2616h/720)·R_y'(2) + (1274h/720)·R_y'(1)`,
with `R_y'(0) = 0`. The combined coefficient is
`5072212/86400 ≤ 59`. -/
private theorem ab5_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 6 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 6 y t| ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (ht4h : t + 4 * h ∈ Set.Icc a b)
    (ht5h : t + 5 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    |y (t + 5 * h) - y (t + 4 * h)
        - h * ((1901 / 720) * deriv y (t + 4 * h)
              - (2774 / 720) * deriv y (t + 3 * h)
              + (2616 / 720) * deriv y (t + 2 * h)
              - (1274 / 720) * deriv y (t + h)
              + (251 / 720) * deriv y t)|
      ≤ (59 : ℝ) * M * h ^ 6 := by
  -- Six Taylor remainders.
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have h5h : 0 ≤ 5 * h := by linarith
  -- R_y(4), R_y(5): y Taylor remainders at order 6.
  have hRy4 :=
    y_sixth_order_taylor_remainder hy hbnd ht ht4h h4h
  have hRy5 :=
    y_sixth_order_taylor_remainder hy hbnd ht ht5h h5h
  -- R_y'(1), R_y'(2), R_y'(3), R_y'(4): y' Taylor remainders at order 5.
  have hRyp1 :=
    derivY_fifth_order_taylor_remainder hy hbnd ht hth hh
  have hRyp2 :=
    derivY_fifth_order_taylor_remainder hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_fifth_order_taylor_remainder hy hbnd ht ht3h h3h
  have hRyp4 :=
    derivY_fifth_order_taylor_remainder hy hbnd ht ht4h h4h
  -- Abbreviations.
  set y0 := y t with hy0_def
  set y4 := y (t + 4 * h) with hy4_def
  set y5 := y (t + 5 * h) with hy5_def
  set d0 := deriv y t with hd0_def
  set d1 := deriv y (t + h) with hd1_def
  set d2 := deriv y (t + 2 * h) with hd2_def
  set d3 := deriv y (t + 3 * h) with hd3_def
  set d4 := deriv y (t + 4 * h) with hd4_def
  set dd := iteratedDeriv 2 y t with hdd_def
  set ddd := iteratedDeriv 3 y t with hddd_def
  set dddd := iteratedDeriv 4 y t with hdddd_def
  set ddddd := iteratedDeriv 5 y t with hddddd_def
  -- Algebraic identity for the residual.
  have hLTE_eq :
      y5 - y4 - h * ((1901 / 720) * d4 - (2774 / 720) * d3
                    + (2616 / 720) * d2 - (1274 / 720) * d1
                    + (251 / 720) * d0)
        = (y5 - y0 - (5 * h) * d0
              - (5 * h) ^ 2 / 2 * dd
              - (5 * h) ^ 3 / 6 * ddd
              - (5 * h) ^ 4 / 24 * dddd
              - (5 * h) ^ 5 / 120 * ddddd)
          - (y4 - y0 - (4 * h) * d0
              - (4 * h) ^ 2 / 2 * dd
              - (4 * h) ^ 3 / 6 * ddd
              - (4 * h) ^ 4 / 24 * dddd
              - (4 * h) ^ 5 / 120 * ddddd)
          - (1901 * h / 720)
              * (d4 - d0 - (4 * h) * dd
                  - (4 * h) ^ 2 / 2 * ddd
                  - (4 * h) ^ 3 / 6 * dddd
                  - (4 * h) ^ 4 / 24 * ddddd)
          + (2774 * h / 720)
              * (d3 - d0 - (3 * h) * dd
                  - (3 * h) ^ 2 / 2 * ddd
                  - (3 * h) ^ 3 / 6 * dddd
                  - (3 * h) ^ 4 / 24 * ddddd)
          - (2616 * h / 720)
              * (d2 - d0 - (2 * h) * dd
                  - (2 * h) ^ 2 / 2 * ddd
                  - (2 * h) ^ 3 / 6 * dddd
                  - (2 * h) ^ 4 / 24 * ddddd)
          + (1274 * h / 720)
              * (d1 - d0 - h * dd
                  - h ^ 2 / 2 * ddd
                  - h ^ 3 / 6 * dddd
                  - h ^ 4 / 24 * ddddd) := by ring
  rw [hLTE_eq]
  -- Triangle inequality (chained).
  set A := y5 - y0 - (5 * h) * d0
            - (5 * h) ^ 2 / 2 * dd
            - (5 * h) ^ 3 / 6 * ddd
            - (5 * h) ^ 4 / 24 * dddd
            - (5 * h) ^ 5 / 120 * ddddd with hA_def
  set B := y4 - y0 - (4 * h) * d0
            - (4 * h) ^ 2 / 2 * dd
            - (4 * h) ^ 3 / 6 * ddd
            - (4 * h) ^ 4 / 24 * dddd
            - (4 * h) ^ 5 / 120 * ddddd with hB_def
  set C := d4 - d0 - (4 * h) * dd
            - (4 * h) ^ 2 / 2 * ddd
            - (4 * h) ^ 3 / 6 * dddd
            - (4 * h) ^ 4 / 24 * ddddd with hC_def
  set D := d3 - d0 - (3 * h) * dd
            - (3 * h) ^ 2 / 2 * ddd
            - (3 * h) ^ 3 / 6 * dddd
            - (3 * h) ^ 4 / 24 * ddddd with hD_def
  set E := d2 - d0 - (2 * h) * dd
            - (2 * h) ^ 2 / 2 * ddd
            - (2 * h) ^ 3 / 6 * dddd
            - (2 * h) ^ 4 / 24 * ddddd with hE_def
  set F := d1 - d0 - h * dd
            - h ^ 2 / 2 * ddd
            - h ^ 3 / 6 * dddd
            - h ^ 4 / 24 * ddddd with hF_def
  have h1901h_nn : 0 ≤ 1901 * h / 720 := by linarith
  have h2774h_nn : 0 ≤ 2774 * h / 720 := by linarith
  have h2616h_nn : 0 ≤ 2616 * h / 720 := by linarith
  have h1274h_nn : 0 ≤ 1274 * h / 720 := by linarith
  have habs1901 : |(1901 * h / 720) * C| = (1901 * h / 720) * |C| := by
    rw [abs_mul, abs_of_nonneg h1901h_nn]
  have habs2774 : |(2774 * h / 720) * D| = (2774 * h / 720) * |D| := by
    rw [abs_mul, abs_of_nonneg h2774h_nn]
  have habs2616 : |(2616 * h / 720) * E| = (2616 * h / 720) * |E| := by
    rw [abs_mul, abs_of_nonneg h2616h_nn]
  have habs1274 : |(1274 * h / 720) * F| = (1274 * h / 720) * |F| := by
    rw [abs_mul, abs_of_nonneg h1274h_nn]
  have htri : |A - B - (1901 * h / 720) * C + (2774 * h / 720) * D
                  - (2616 * h / 720) * E + (1274 * h / 720) * F|
      ≤ |A| + |B| + (1901 * h / 720) * |C| + (2774 * h / 720) * |D|
          + (2616 * h / 720) * |E| + (1274 * h / 720) * |F| := by
    have h1 : |A - B - (1901 * h / 720) * C + (2774 * h / 720) * D
                  - (2616 * h / 720) * E + (1274 * h / 720) * F|
        ≤ |A - B - (1901 * h / 720) * C + (2774 * h / 720) * D
              - (2616 * h / 720) * E|
          + |(1274 * h / 720) * F| := abs_add_le _ _
    have h2 : |A - B - (1901 * h / 720) * C + (2774 * h / 720) * D
                  - (2616 * h / 720) * E|
        ≤ |A - B - (1901 * h / 720) * C + (2774 * h / 720) * D|
          + |(2616 * h / 720) * E| := abs_sub _ _
    have h3 : |A - B - (1901 * h / 720) * C + (2774 * h / 720) * D|
        ≤ |A - B - (1901 * h / 720) * C| + |(2774 * h / 720) * D| :=
      abs_add_le _ _
    have h4 : |A - B - (1901 * h / 720) * C|
        ≤ |A - B| + |(1901 * h / 720) * C| := abs_sub _ _
    have h5 : |A - B| ≤ |A| + |B| := abs_sub _ _
    linarith [habs1901.le, habs1901.ge, habs2774.le, habs2774.ge,
      habs2616.le, habs2616.ge, habs1274.le, habs1274.ge]
  -- Bounds on each piece.
  have hA_bd : |A| ≤ M / 720 * (5 * h) ^ 6 := hRy5
  have hB_bd : |B| ≤ M / 720 * (4 * h) ^ 6 := hRy4
  have hC_bd : |C| ≤ M / 120 * (4 * h) ^ 5 := hRyp4
  have hD_bd : |D| ≤ M / 120 * (3 * h) ^ 5 := hRyp3
  have hE_bd : |E| ≤ M / 120 * (2 * h) ^ 5 := hRyp2
  have hF_bd : |F| ≤ M / 120 * h ^ 5 := hRyp1
  -- Multiply scaled bounds.
  have h1901C_bd : (1901 * h / 720) * |C|
      ≤ (1901 * h / 720) * (M / 120 * (4 * h) ^ 5) :=
    mul_le_mul_of_nonneg_left hC_bd h1901h_nn
  have h2774D_bd : (2774 * h / 720) * |D|
      ≤ (2774 * h / 720) * (M / 120 * (3 * h) ^ 5) :=
    mul_le_mul_of_nonneg_left hD_bd h2774h_nn
  have h2616E_bd : (2616 * h / 720) * |E|
      ≤ (2616 * h / 720) * (M / 120 * (2 * h) ^ 5) :=
    mul_le_mul_of_nonneg_left hE_bd h2616h_nn
  have h1274F_bd : (1274 * h / 720) * |F|
      ≤ (1274 * h / 720) * (M / 120 * h ^ 5) :=
    mul_le_mul_of_nonneg_left hF_bd h1274h_nn
  -- Sum of upper bounds = 5072212/86400 · M · h^6 ≤ 59 · M · h^6.
  have hbound_alg :
      M / 720 * (5 * h) ^ 6 + M / 720 * (4 * h) ^ 6
        + (1901 * h / 720) * (M / 120 * (4 * h) ^ 5)
        + (2774 * h / 720) * (M / 120 * (3 * h) ^ 5)
        + (2616 * h / 720) * (M / 120 * (2 * h) ^ 5)
        + (1274 * h / 720) * (M / 120 * h ^ 5)
        = (5072212 / 86400 : ℝ) * M * h ^ 6 := by ring
  -- 5072212/86400 ≤ 59 → over-estimate by 59 * M * h^6.
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (abs_nonneg _).trans this
  have hh6_nn : 0 ≤ h ^ 6 := by positivity
  have hMh6_nn : 0 ≤ M * h ^ 6 := mul_nonneg hMnn hh6_nn
  have hslack : (5072212 / 86400 : ℝ) * M * h ^ 6 ≤ 59 * M * h ^ 6 := by
    have hle : (5072212 / 86400 : ℝ) ≤ 59 := by norm_num
    have := mul_le_mul_of_nonneg_right hle hMh6_nn
    linarith [this]
  linarith [htri, hA_bd, hB_bd, h1901C_bd, h2774D_bd, h2616E_bd, h1274F_bd,
    hbound_alg.le, hbound_alg.ge, hslack]

/-- Uniform bound on the AB5 one-step truncation residual on a finite
horizon, given a `C^6` exact solution. -/
theorem ab5_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 6 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 5) * h ≤ T →
        |adamsBashforth5.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 6 := by
  -- Compact sample interval `[t₀, t₀ + T + 1]` covers all `t + kh` with `k ≤ 5`.
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_six_bounded_on_Icc hy t₀ (t₀ + T + 1)
  refine ⟨(59 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
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
  -- Rewrite the LTE in textbook form.
  rw [ab5_localTruncationError_eq]
  show |y (t + 5 * h) - y (t + 4 * h)
      - h * (1901 / 720 * deriv y (t + 4 * h)
              - 2774 / 720 * deriv y (t + 3 * h)
              + 2616 / 720 * deriv y (t + 2 * h)
              - 1274 / 720 * deriv y (t + h)
              + 251 / 720 * deriv y t)|
    ≤ 59 * M * h ^ 6
  have hreshape :
      h * (1901 / 720 * deriv y (t + 4 * h)
            - 2774 / 720 * deriv y (t + 3 * h)
            + 2616 / 720 * deriv y (t + 2 * h)
            - 1274 / 720 * deriv y (t + h)
            + 251 / 720 * deriv y t)
        = h * ((1901 / 720) * deriv y (t + 4 * h)
              - (2774 / 720) * deriv y (t + 3 * h)
              + (2616 / 720) * deriv y (t + 2 * h)
              - (1274 / 720) * deriv y (t + h)
              + (251 / 720) * deriv y t) := by ring
  rw [hreshape]
  exact ab5_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem ht4h_mem ht5h_mem hh.le

/-- Final AB5 global error bound on `[t₀, t₀ + T]`. Under Lipschitz `f`,
`C^6` exact solution `y` with `deriv y t = f t (y t)`, and starting
errors `|y_i - y(t_i)| ≤ ε₀` for `i = 0, 1, 2, 3, 4`, the AB5 iterate
error obeys `O(ε₀ + h^5)` on a finite horizon. -/
theorem ab5_global_error_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 6 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      ∀ {y₀ y₁ y₂ y₃ y₄ ε₀ : ℝ}, 0 ≤ ε₀ →
      |y₀ - y t₀| ≤ ε₀ → |y₁ - y (t₀ + h)| ≤ ε₀ →
      |y₂ - y (t₀ + 2 * h)| ≤ ε₀ →
      |y₃ - y (t₀ + 3 * h)| ≤ ε₀ →
      |y₄ - y (t₀ + 4 * h)| ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 4) * h ≤ T →
      |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ N - y (t₀ + (N : ℝ) * h)|
        ≤ Real.exp ((551 / 45) * L * T) * ε₀ + K * h ^ 5 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    ab5_local_residual_bound hy t₀ T hT
  refine ⟨T * Real.exp ((551 / 45) * L * T) * C, δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
  intro h hh hδ_le y₀ y₁ y₂ y₃ y₄ ε₀ hε₀ he0_bd he1_bd he2_bd he3_bd he4_bd N hNh
  -- Error sequence and 5-window max-norm sequence.
  set eN : ℕ → ℝ :=
    fun k => |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ k - y (t₀ + (k : ℝ) * h)|
    with heN_def
  set EN : ℕ → ℝ :=
    fun k => max (max (max (max (eN k) (eN (k + 1))) (eN (k + 2)))
                  (eN (k + 3))) (eN (k + 4))
    with hEN_def
  have heN_nn : ∀ k, 0 ≤ eN k := fun _ => abs_nonneg _
  have hEN_nn : ∀ k, 0 ≤ EN k := fun k =>
    le_max_of_le_left (le_max_of_le_left (le_max_of_le_left
      (le_max_of_le_left (heN_nn k))))
  -- Initial bound: EN 0 ≤ ε₀.
  have hEN0_le : EN 0 ≤ ε₀ := by
    show max (max (max (max (eN 0) (eN 1)) (eN 2)) (eN 3)) (eN 4) ≤ ε₀
    refine max_le (max_le (max_le (max_le ?_ ?_) ?_) ?_) ?_
    · show |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)| ≤ ε₀
      simpa using he0_bd
    · show |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ 1 - y (t₀ + ((1 : ℕ) : ℝ) * h)| ≤ ε₀
      have hcast : ((1 : ℕ) : ℝ) * h = h := by push_cast; ring
      rw [hcast]
      simpa using he1_bd
    · show |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ 2 - y (t₀ + ((2 : ℕ) : ℝ) * h)| ≤ ε₀
      have hcast : ((2 : ℕ) : ℝ) * h = 2 * h := by push_cast; ring
      rw [hcast]
      simpa using he2_bd
    · show |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ 3 - y (t₀ + ((3 : ℕ) : ℝ) * h)| ≤ ε₀
      have hcast : ((3 : ℕ) : ℝ) * h = 3 * h := by push_cast; ring
      rw [hcast]
      simpa using he3_bd
    · show |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ 4 - y (t₀ + ((4 : ℕ) : ℝ) * h)| ≤ ε₀
      have hcast : ((4 : ℕ) : ℝ) * h = 4 * h := by push_cast; ring
      rw [hcast]
      simpa using he4_bd
  have hLeff_nn : (0 : ℝ) ≤ (551 / 45) * L := by positivity
  -- The general recurrence: when (n + 5) * h ≤ T,
  -- EN (n+1) ≤ (1 + h*((551/45)*L)) * EN n + C * h^6.
  have hstep_general : ∀ n : ℕ, ((n : ℝ) + 5) * h ≤ T →
      EN (n + 1) ≤ (1 + h * ((551 / 45) * L)) * EN n + C * h ^ 6 := by
    intro n hnh_le
    have honestep := ab5_one_step_error_bound (h := h) (L := L)
        hh.le hL hf t₀ y₀ y₁ y₂ y₃ y₄ y hyf n
    have hres := hresidual hh hδ_le n hnh_le
    have hcast1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hcast2 : ((n + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    have hcast3 : ((n + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
    have hcast4 : ((n + 1 + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 4 := by
      push_cast; ring
    have hcast5 : ((n + 1 + 1 + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 5 := by
      push_cast; ring
    have heq_eN_n1 : eN (n + 1)
        = |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 1)
            - y (t₀ + ((n : ℝ) + 1) * h)| := by
      show |_ - _| = _
      rw [hcast1]
    have heq_eN_n2 : eN (n + 1 + 1)
        = |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 2)
            - y (t₀ + ((n : ℝ) + 2) * h)| := by
      show |_ - _| = _
      rw [hcast2]
    have heq_eN_n3 : eN (n + 1 + 1 + 1)
        = |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 3)
            - y (t₀ + ((n : ℝ) + 3) * h)| := by
      show |_ - _| = _
      rw [hcast3]
    have heq_eN_n4 : eN (n + 1 + 1 + 1 + 1)
        = |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 4)
            - y (t₀ + ((n : ℝ) + 4) * h)| := by
      show |_ - _| = _
      rw [hcast4]
    have heq_eN_n5 : eN (n + 1 + 1 + 1 + 1 + 1)
        = |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 5)
            - y (t₀ + ((n : ℝ) + 5) * h)| := by
      show |_ - _| = _
      rw [hcast5]
    show max (max (max (max (eN (n + 1)) (eN (n + 1 + 1)))
            (eN (n + 1 + 1 + 1))) (eN (n + 1 + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1 + 1))
        ≤ (1 + h * ((551 / 45) * L))
            * max (max (max (max (eN n) (eN (n + 1))) (eN (n + 1 + 1)))
                  (eN (n + 1 + 1 + 1))) (eN (n + 1 + 1 + 1 + 1))
          + C * h ^ 6
    rw [heq_eN_n1, heq_eN_n2, heq_eN_n3, heq_eN_n4, heq_eN_n5]
    show max (max (max (max
              |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 1)
                - y (t₀ + ((n : ℝ) + 1) * h)|
              |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 2)
                - y (t₀ + ((n : ℝ) + 2) * h)|)
              |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 3)
                - y (t₀ + ((n : ℝ) + 3) * h)|)
              |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 4)
                - y (t₀ + ((n : ℝ) + 4) * h)|)
              |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 5)
                - y (t₀ + ((n : ℝ) + 5) * h)|
        ≤ (1 + h * ((551 / 45) * L))
            * max (max (max (max (eN n)
                  |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 1)
                    - y (t₀ + ((n : ℝ) + 1) * h)|)
                  |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 2)
                    - y (t₀ + ((n : ℝ) + 2) * h)|)
                  |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 3)
                    - y (t₀ + ((n : ℝ) + 3) * h)|)
                  |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (n + 4)
                    - y (t₀ + ((n : ℝ) + 4) * h)|
          + C * h ^ 6
    linarith [honestep, hres]
  have hexp_ge : (1 : ℝ) ≤ Real.exp ((551 / 45) * L * T) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hKnn : 0 ≤ T * Real.exp ((551 / 45) * L * T) * C :=
    mul_nonneg (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
  have hh5_nn : 0 ≤ h ^ 5 := by positivity
  have hexp_nn : 0 ≤ Real.exp ((551 / 45) * L * T) := Real.exp_nonneg _
  -- Helper: any base error ≤ ε₀ implies the headline bound.
  have hbase_to_headline : ∀ q : ℝ, q ≤ ε₀ →
      q ≤ Real.exp ((551 / 45) * L * T) * ε₀
            + T * Real.exp ((551 / 45) * L * T) * C * h ^ 5 := by
    intro q hq
    have hexp_ε₀ : ε₀ ≤ Real.exp ((551 / 45) * L * T) * ε₀ := by
      have hone : (1 : ℝ) * ε₀ ≤ Real.exp ((551 / 45) * L * T) * ε₀ :=
        mul_le_mul_of_nonneg_right hexp_ge hε₀
      linarith
    have hKh5_nn : 0 ≤ T * Real.exp ((551 / 45) * L * T) * C * h ^ 5 :=
      mul_nonneg hKnn hh5_nn
    linarith
  match N, hNh with
  | 0, _ =>
    have hbase : |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)|
        ≤ ε₀ := by simpa using he0_bd
    exact hbase_to_headline _ hbase
  | 1, _ =>
    have hbase : |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ 1 - y (t₀ + ((1 : ℕ) : ℝ) * h)|
        ≤ ε₀ := by
      have hcast : ((1 : ℕ) : ℝ) * h = h := by push_cast; ring
      rw [hcast]; simpa using he1_bd
    exact hbase_to_headline _ hbase
  | 2, _ =>
    have hbase : |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ 2 - y (t₀ + ((2 : ℕ) : ℝ) * h)|
        ≤ ε₀ := by
      have hcast : ((2 : ℕ) : ℝ) * h = 2 * h := by push_cast; ring
      rw [hcast]; simpa using he2_bd
    exact hbase_to_headline _ hbase
  | 3, _ =>
    have hbase : |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ 3 - y (t₀ + ((3 : ℕ) : ℝ) * h)|
        ≤ ε₀ := by
      have hcast : ((3 : ℕ) : ℝ) * h = 3 * h := by push_cast; ring
      rw [hcast]; simpa using he3_bd
    exact hbase_to_headline _ hbase
  | 4, _ =>
    have hbase : |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ 4 - y (t₀ + ((4 : ℕ) : ℝ) * h)|
        ≤ ε₀ := by
      have hcast : ((4 : ℕ) : ℝ) * h = 4 * h := by push_cast; ring
      rw [hcast]; simpa using he4_bd
    exact hbase_to_headline _ hbase
  | N' + 5, hNh =>
    -- Apply Gronwall to EN at index N'+1, then use EN_{N'+1} ≥ e_{N'+5}.
    have hcast : (((N' + 5 : ℕ) : ℝ)) = (N' : ℝ) + 5 := by push_cast; ring
    have hN_hyp : ((N' : ℝ) + 5) * h ≤ T := by
      have := hNh
      rw [hcast] at this
      linarith
    have hgronwall_step : ∀ n, n < N' + 1 →
        EN (n + 1) ≤ (1 + h * ((551 / 45) * L)) * EN n + C * h ^ (5 + 1) := by
      intro n hn_lt
      have hpow : C * h ^ (5 + 1) = C * h ^ 6 := by norm_num
      rw [hpow]
      apply hstep_general
      have hn1_le_N' : (n : ℝ) + 1 ≤ (N' : ℝ) + 1 := by
        have : (n : ℝ) ≤ (N' : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp hn_lt
        linarith
      have h_le_chain : (n : ℝ) + 5 ≤ (N' : ℝ) + 5 := by linarith
      have h_mul : ((n : ℝ) + 5) * h ≤ ((N' : ℝ) + 5) * h :=
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
        (h := h) (L := (551 / 45) * L) (C := C) (T := T) (p := 5)
        (e := EN) (N := N' + 1)
        hh.le hLeff_nn hC_nn (hEN_nn 0) hgronwall_step (N' + 1) le_rfl hN'1h_le_T
    -- eN (N' + 5) ≤ EN (N' + 1).
    have heN_le_EN : eN (N' + 5) ≤ EN (N' + 1) := by
      show eN (N' + 5) ≤ max (max (max (max (eN (N' + 1)) (eN (N' + 1 + 1)))
              (eN (N' + 1 + 2))) (eN (N' + 1 + 3))) (eN (N' + 1 + 4))
      have heq : N' + 5 = N' + 1 + 4 := by ring
      rw [heq]
      exact le_max_right _ _
    have h_chain :
        Real.exp ((551 / 45) * L * T) * EN 0
          ≤ Real.exp ((551 / 45) * L * T) * ε₀ :=
      mul_le_mul_of_nonneg_left hEN0_le hexp_nn
    show |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (N' + 5)
              - y (t₀ + ((N' + 5 : ℕ) : ℝ) * h)|
        ≤ Real.exp ((551 / 45) * L * T) * ε₀
          + T * Real.exp ((551 / 45) * L * T) * C * h ^ 5
    have heN_eq :
        eN (N' + 5)
          = |ab5Iter h f t₀ y₀ y₁ y₂ y₃ y₄ (N' + 5)
              - y (t₀ + ((N' + 5 : ℕ) : ℝ) * h)| := rfl
    linarith [heN_le_EN, hgronwall, h_chain, heN_eq.symm.le, heN_eq.le]

end LMM
