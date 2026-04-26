import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMABGenericConvergence

/-! ## Adams–Bashforth 6-step Scalar Convergence Chain (Iserles §1.2)

Order-6 explicit 6-step LMM convergence scaffold. Mirrors the AB5 chain
in `OpenMath.LMMAB5Convergence` at the next order. This scalar half takes
six starting samples and combines six prior `f` evaluations. The
effective max-window Lipschitz constant is `(114/5) · L`, the residual
is `O(h^7)` and the headline global error bound is `O(ε₀ + h^6)`. -/

namespace LMM

/-- AB6 iteration with six starting samples `y₀, y₁, y₂, y₃, y₄, y₅`:
`y_{n+6} = y_{n+5} + h · ((4277/1440) · f_{n+5} − (7923/1440) · f_{n+4}
  + (9982/1440) · f_{n+3} − (7298/1440) · f_{n+2} + (2877/1440) · f_{n+1}
  − (475/1440) · f_n)`. -/
noncomputable def ab6Iter
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ : ℝ) : ℕ → ℝ
  | 0 => y₀
  | 1 => y₁
  | 2 => y₂
  | 3 => y₃
  | 4 => y₄
  | 5 => y₅
  | n + 6 =>
      ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5)
        + h * (4277 / 1440 * f (t₀ + ((n : ℝ) + 5) * h)
                (ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5))
              - 7923 / 1440 * f (t₀ + ((n : ℝ) + 4) * h)
                (ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 4))
              + 9982 / 1440 * f (t₀ + ((n : ℝ) + 3) * h)
                (ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 3))
              - 7298 / 1440 * f (t₀ + ((n : ℝ) + 2) * h)
                (ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 2))
              + 2877 / 1440 * f (t₀ + ((n : ℝ) + 1) * h)
                (ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 1))
              - 475 / 1440 * f (t₀ + (n : ℝ) * h)
                (ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ n))

@[simp] lemma ab6Iter_zero
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ : ℝ) :
    ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 0 = y₀ := rfl

@[simp] lemma ab6Iter_one
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ : ℝ) :
    ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 1 = y₁ := rfl

@[simp] lemma ab6Iter_two
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ : ℝ) :
    ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 2 = y₂ := rfl

@[simp] lemma ab6Iter_three
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ : ℝ) :
    ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 3 = y₃ := rfl

@[simp] lemma ab6Iter_four
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ : ℝ) :
    ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 4 = y₄ := rfl

@[simp] lemma ab6Iter_five
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ : ℝ) :
    ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 5 = y₅ := rfl

lemma ab6Iter_succ_succ_succ_succ_succ_succ
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ : ℝ) (n : ℕ) :
    ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 6)
      = ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5)
          + h * (4277 / 1440 * f (t₀ + ((n : ℝ) + 5) * h)
                  (ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5))
                - 7923 / 1440 * f (t₀ + ((n : ℝ) + 4) * h)
                    (ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 4))
                + 9982 / 1440 * f (t₀ + ((n : ℝ) + 3) * h)
                    (ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 3))
                - 7298 / 1440 * f (t₀ + ((n : ℝ) + 2) * h)
                    (ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 2))
                + 2877 / 1440 * f (t₀ + ((n : ℝ) + 1) * h)
                    (ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 1))
                - 475 / 1440 * f (t₀ + (n : ℝ) * h)
                    (ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ n)) := rfl

/-- AB6 local truncation operator reduces to the textbook 6-step residual
`y(t + 6h) − y(t + 5h) − h · ((4277/1440) y'(t + 5h) − (7923/1440) y'(t + 4h)
  + (9982/1440) y'(t + 3h) − (7298/1440) y'(t + 2h) + (2877/1440) y'(t + h)
  − (475/1440) y'(t))`. -/
theorem ab6_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    adamsBashforth6.localTruncationError h t y
      = y (t + 6 * h) - y (t + 5 * h)
          - h * (4277 / 1440 * deriv y (t + 5 * h)
                  - 7923 / 1440 * deriv y (t + 4 * h)
                  + 9982 / 1440 * deriv y (t + 3 * h)
                  - 7298 / 1440 * deriv y (t + 2 * h)
                  + 2877 / 1440 * deriv y (t + h)
                  - 475 / 1440 * deriv y t) := by
  unfold localTruncationError truncationOp
  simp [adamsBashforth6, Fin.sum_univ_succ, iteratedDeriv_one,
    iteratedDeriv_zero]
  ring

/-- One-step AB6 Lipschitz step: a single linearised increment of the
global error from steps `n, n+1, …, n+5` to `n+6`, with six
Lipschitz contributions and additive `|τ_n|`. -/
theorem ab6_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ y₁ y₂ y₃ y₄ y₅ : ℝ) (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|
      ≤ |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|
        + (4277 / 1440) * h * L
            * |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5)
                - y (t₀ + ((n : ℝ) + 5) * h)|
        + (7923 / 1440) * h * L
            * |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 4)
                - y (t₀ + ((n : ℝ) + 4) * h)|
        + (9982 / 1440) * h * L
            * |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 3)
                - y (t₀ + ((n : ℝ) + 3) * h)|
        + (7298 / 1440) * h * L
            * |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 2)
                - y (t₀ + ((n : ℝ) + 2) * h)|
        + (2877 / 1440) * h * L
            * |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 1)
                - y (t₀ + ((n : ℝ) + 1) * h)|
        + (475 / 1440) * h * L
            * |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ n - y (t₀ + (n : ℝ) * h)|
        + |adamsBashforth6.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set yn : ℝ := ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ n with hyn_def
  set yn1 : ℝ := ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 1) with hyn1_def
  set yn2 : ℝ := ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 2) with hyn2_def
  set yn3 : ℝ := ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 3) with hyn3_def
  set yn4 : ℝ := ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 4) with hyn4_def
  set yn5 : ℝ := ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5) with hyn5_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set tn3 : ℝ := t₀ + ((n : ℝ) + 3) * h with htn3_def
  set tn4 : ℝ := t₀ + ((n : ℝ) + 4) * h with htn4_def
  set tn5 : ℝ := t₀ + ((n : ℝ) + 5) * h with htn5_def
  set tn6 : ℝ := t₀ + ((n : ℝ) + 6) * h with htn6_def
  set zn : ℝ := y tn with hzn_def
  set zn1 : ℝ := y tn1 with hzn1_def
  set zn2 : ℝ := y tn2 with hzn2_def
  set zn3 : ℝ := y tn3 with hzn3_def
  set zn4 : ℝ := y tn4 with hzn4_def
  set zn5 : ℝ := y tn5 with hzn5_def
  set zn6 : ℝ := y tn6 with hzn6_def
  set τ : ℝ := adamsBashforth6.localTruncationError h tn y with hτ_def
  -- AB6 step formula.
  have hstep : ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 6)
      = yn5 + h * (4277 / 1440 * f tn5 yn5
                    - 7923 / 1440 * f tn4 yn4
                    + 9982 / 1440 * f tn3 yn3
                    - 7298 / 1440 * f tn2 yn2
                    + 2877 / 1440 * f tn1 yn1
                    - 475 / 1440 * f tn yn) := by
    show ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 6) = _
    rw [ab6Iter_succ_succ_succ_succ_succ_succ]
  -- Time arithmetic.
  have htn1_h : tn + h = tn1 := by simp [htn_def, htn1_def]; ring
  have htn_2h : tn + 2 * h = tn2 := by simp [htn_def, htn2_def]; ring
  have htn_3h : tn + 3 * h = tn3 := by simp [htn_def, htn3_def]; ring
  have htn_4h : tn + 4 * h = tn4 := by simp [htn_def, htn4_def]; ring
  have htn_5h : tn + 5 * h = tn5 := by simp [htn_def, htn5_def]; ring
  have htn_6h : tn + 6 * h = tn6 := by simp [htn_def, htn6_def]; ring
  -- LTE residual at `tn`, expressed via `f` along the trajectory.
  have hτ_eq : τ = zn6 - zn5
        - h * (4277 / 1440 * f tn5 zn5 - 7923 / 1440 * f tn4 zn4
              + 9982 / 1440 * f tn3 zn3 - 7298 / 1440 * f tn2 zn2
              + 2877 / 1440 * f tn1 zn1 - 475 / 1440 * f tn zn) := by
    show adamsBashforth6.localTruncationError h tn y = _
    rw [ab6_localTruncationError_eq, htn1_h, htn_2h, htn_3h, htn_4h, htn_5h,
      htn_6h, hyf tn5, hyf tn4, hyf tn3, hyf tn2, hyf tn1, hyf tn]
  -- Algebraic decomposition of the global error increment.
  have halg : ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 6) - zn6
      = (yn5 - zn5)
        + (4277 / 1440) * h * (f tn5 yn5 - f tn5 zn5)
        - (7923 / 1440) * h * (f tn4 yn4 - f tn4 zn4)
        + (9982 / 1440) * h * (f tn3 yn3 - f tn3 zn3)
        - (7298 / 1440) * h * (f tn2 yn2 - f tn2 zn2)
        + (2877 / 1440) * h * (f tn1 yn1 - f tn1 zn1)
        - (475 / 1440) * h * (f tn yn - f tn zn)
        - τ := by
    rw [hstep, hτ_eq]; ring
  -- Lipschitz bounds on the six `f` increments.
  have hLip5 : |f tn5 yn5 - f tn5 zn5| ≤ L * |yn5 - zn5| := hf tn5 yn5 zn5
  have hLip4 : |f tn4 yn4 - f tn4 zn4| ≤ L * |yn4 - zn4| := hf tn4 yn4 zn4
  have hLip3 : |f tn3 yn3 - f tn3 zn3| ≤ L * |yn3 - zn3| := hf tn3 yn3 zn3
  have hLip2 : |f tn2 yn2 - f tn2 zn2| ≤ L * |yn2 - zn2| := hf tn2 yn2 zn2
  have hLip1 : |f tn1 yn1 - f tn1 zn1| ≤ L * |yn1 - zn1| := hf tn1 yn1 zn1
  have hLip0 : |f tn yn - f tn zn| ≤ L * |yn - zn| := hf tn yn zn
  have h4277_nn : 0 ≤ (4277 / 1440) * h := by linarith
  have h7923_nn : 0 ≤ (7923 / 1440) * h := by linarith
  have h9982_nn : 0 ≤ (9982 / 1440) * h := by linarith
  have h7298_nn : 0 ≤ (7298 / 1440) * h := by linarith
  have h2877_nn : 0 ≤ (2877 / 1440) * h := by linarith
  have h475_nn : 0 ≤ (475 / 1440) * h := by linarith
  have h4277_abs : |(4277 / 1440) * h * (f tn5 yn5 - f tn5 zn5)|
      ≤ (4277 / 1440) * h * L * |yn5 - zn5| := by
    rw [abs_mul, abs_of_nonneg h4277_nn]
    calc (4277 / 1440) * h * |f tn5 yn5 - f tn5 zn5|
        ≤ (4277 / 1440) * h * (L * |yn5 - zn5|) :=
          mul_le_mul_of_nonneg_left hLip5 h4277_nn
      _ = (4277 / 1440) * h * L * |yn5 - zn5| := by ring
  have h7923_abs : |(7923 / 1440) * h * (f tn4 yn4 - f tn4 zn4)|
      ≤ (7923 / 1440) * h * L * |yn4 - zn4| := by
    rw [abs_mul, abs_of_nonneg h7923_nn]
    calc (7923 / 1440) * h * |f tn4 yn4 - f tn4 zn4|
        ≤ (7923 / 1440) * h * (L * |yn4 - zn4|) :=
          mul_le_mul_of_nonneg_left hLip4 h7923_nn
      _ = (7923 / 1440) * h * L * |yn4 - zn4| := by ring
  have h9982_abs : |(9982 / 1440) * h * (f tn3 yn3 - f tn3 zn3)|
      ≤ (9982 / 1440) * h * L * |yn3 - zn3| := by
    rw [abs_mul, abs_of_nonneg h9982_nn]
    calc (9982 / 1440) * h * |f tn3 yn3 - f tn3 zn3|
        ≤ (9982 / 1440) * h * (L * |yn3 - zn3|) :=
          mul_le_mul_of_nonneg_left hLip3 h9982_nn
      _ = (9982 / 1440) * h * L * |yn3 - zn3| := by ring
  have h7298_abs : |(7298 / 1440) * h * (f tn2 yn2 - f tn2 zn2)|
      ≤ (7298 / 1440) * h * L * |yn2 - zn2| := by
    rw [abs_mul, abs_of_nonneg h7298_nn]
    calc (7298 / 1440) * h * |f tn2 yn2 - f tn2 zn2|
        ≤ (7298 / 1440) * h * (L * |yn2 - zn2|) :=
          mul_le_mul_of_nonneg_left hLip2 h7298_nn
      _ = (7298 / 1440) * h * L * |yn2 - zn2| := by ring
  have h2877_abs : |(2877 / 1440) * h * (f tn1 yn1 - f tn1 zn1)|
      ≤ (2877 / 1440) * h * L * |yn1 - zn1| := by
    rw [abs_mul, abs_of_nonneg h2877_nn]
    calc (2877 / 1440) * h * |f tn1 yn1 - f tn1 zn1|
        ≤ (2877 / 1440) * h * (L * |yn1 - zn1|) :=
          mul_le_mul_of_nonneg_left hLip1 h2877_nn
      _ = (2877 / 1440) * h * L * |yn1 - zn1| := by ring
  have h475_abs : |(475 / 1440) * h * (f tn yn - f tn zn)|
      ≤ (475 / 1440) * h * L * |yn - zn| := by
    rw [abs_mul, abs_of_nonneg h475_nn]
    calc (475 / 1440) * h * |f tn yn - f tn zn|
        ≤ (475 / 1440) * h * (L * |yn - zn|) :=
          mul_le_mul_of_nonneg_left hLip0 h475_nn
      _ = (475 / 1440) * h * L * |yn - zn| := by ring
  -- Triangle inequality (chained seven times).
  set S := (yn5 - zn5)
        + (4277 / 1440) * h * (f tn5 yn5 - f tn5 zn5)
        - (7923 / 1440) * h * (f tn4 yn4 - f tn4 zn4)
        + (9982 / 1440) * h * (f tn3 yn3 - f tn3 zn3)
        - (7298 / 1440) * h * (f tn2 yn2 - f tn2 zn2)
        + (2877 / 1440) * h * (f tn1 yn1 - f tn1 zn1)
        - (475 / 1440) * h * (f tn yn - f tn zn) with hS_def
  have hcalc : ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 6) - zn6 = S - τ := halg
  have htri_S : |S| ≤ |yn5 - zn5|
              + |(4277 / 1440) * h * (f tn5 yn5 - f tn5 zn5)|
              + |(7923 / 1440) * h * (f tn4 yn4 - f tn4 zn4)|
              + |(9982 / 1440) * h * (f tn3 yn3 - f tn3 zn3)|
              + |(7298 / 1440) * h * (f tn2 yn2 - f tn2 zn2)|
              + |(2877 / 1440) * h * (f tn1 yn1 - f tn1 zn1)|
              + |(475 / 1440) * h * (f tn yn - f tn zn)| := by
    have h1 : |(yn5 - zn5)
              + (4277 / 1440) * h * (f tn5 yn5 - f tn5 zn5)|
        ≤ |yn5 - zn5| + |(4277 / 1440) * h * (f tn5 yn5 - f tn5 zn5)| :=
      abs_add_le _ _
    have h2 : |(yn5 - zn5)
              + (4277 / 1440) * h * (f tn5 yn5 - f tn5 zn5)
              - (7923 / 1440) * h * (f tn4 yn4 - f tn4 zn4)|
        ≤ |(yn5 - zn5)
              + (4277 / 1440) * h * (f tn5 yn5 - f tn5 zn5)|
          + |(7923 / 1440) * h * (f tn4 yn4 - f tn4 zn4)| := abs_sub _ _
    have h3 : |(yn5 - zn5)
              + (4277 / 1440) * h * (f tn5 yn5 - f tn5 zn5)
              - (7923 / 1440) * h * (f tn4 yn4 - f tn4 zn4)
              + (9982 / 1440) * h * (f tn3 yn3 - f tn3 zn3)|
        ≤ |(yn5 - zn5)
              + (4277 / 1440) * h * (f tn5 yn5 - f tn5 zn5)
              - (7923 / 1440) * h * (f tn4 yn4 - f tn4 zn4)|
          + |(9982 / 1440) * h * (f tn3 yn3 - f tn3 zn3)| := abs_add_le _ _
    have h4 : |(yn5 - zn5)
              + (4277 / 1440) * h * (f tn5 yn5 - f tn5 zn5)
              - (7923 / 1440) * h * (f tn4 yn4 - f tn4 zn4)
              + (9982 / 1440) * h * (f tn3 yn3 - f tn3 zn3)
              - (7298 / 1440) * h * (f tn2 yn2 - f tn2 zn2)|
        ≤ |(yn5 - zn5)
              + (4277 / 1440) * h * (f tn5 yn5 - f tn5 zn5)
              - (7923 / 1440) * h * (f tn4 yn4 - f tn4 zn4)
              + (9982 / 1440) * h * (f tn3 yn3 - f tn3 zn3)|
          + |(7298 / 1440) * h * (f tn2 yn2 - f tn2 zn2)| := abs_sub _ _
    have h5 : |(yn5 - zn5)
              + (4277 / 1440) * h * (f tn5 yn5 - f tn5 zn5)
              - (7923 / 1440) * h * (f tn4 yn4 - f tn4 zn4)
              + (9982 / 1440) * h * (f tn3 yn3 - f tn3 zn3)
              - (7298 / 1440) * h * (f tn2 yn2 - f tn2 zn2)
              + (2877 / 1440) * h * (f tn1 yn1 - f tn1 zn1)|
        ≤ |(yn5 - zn5)
              + (4277 / 1440) * h * (f tn5 yn5 - f tn5 zn5)
              - (7923 / 1440) * h * (f tn4 yn4 - f tn4 zn4)
              + (9982 / 1440) * h * (f tn3 yn3 - f tn3 zn3)
              - (7298 / 1440) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(2877 / 1440) * h * (f tn1 yn1 - f tn1 zn1)| := abs_add_le _ _
    have h6 : |S| ≤ |(yn5 - zn5)
              + (4277 / 1440) * h * (f tn5 yn5 - f tn5 zn5)
              - (7923 / 1440) * h * (f tn4 yn4 - f tn4 zn4)
              + (9982 / 1440) * h * (f tn3 yn3 - f tn3 zn3)
              - (7298 / 1440) * h * (f tn2 yn2 - f tn2 zn2)
              + (2877 / 1440) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(475 / 1440) * h * (f tn yn - f tn zn)| := by
      show |_| ≤ _
      exact abs_sub _ _
    linarith
  have htri : |S - τ| ≤ |S| + |τ| := abs_sub _ _
  calc |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 6) - zn6|
      = |S - τ| := by rw [hcalc]
    _ ≤ |S| + |τ| := htri
    _ ≤ |yn5 - zn5|
          + |(4277 / 1440) * h * (f tn5 yn5 - f tn5 zn5)|
          + |(7923 / 1440) * h * (f tn4 yn4 - f tn4 zn4)|
          + |(9982 / 1440) * h * (f tn3 yn3 - f tn3 zn3)|
          + |(7298 / 1440) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(2877 / 1440) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(475 / 1440) * h * (f tn yn - f tn zn)|
          + |τ| := by linarith
    _ ≤ |yn5 - zn5|
          + (4277 / 1440) * h * L * |yn5 - zn5|
          + (7923 / 1440) * h * L * |yn4 - zn4|
          + (9982 / 1440) * h * L * |yn3 - zn3|
          + (7298 / 1440) * h * L * |yn2 - zn2|
          + (2877 / 1440) * h * L * |yn1 - zn1|
          + (475 / 1440) * h * L * |yn - zn|
          + |τ| := by
        linarith [h4277_abs, h7923_abs, h9982_abs, h7298_abs, h2877_abs, h475_abs]

/-- Max-norm one-step error recurrence for AB6 with Lipschitz constant
`L`. With `eN k := |y_k − y(t_k)|` and a 6-window max
`EN k := max (eN k, eN (k+1), …, eN (k+5))`,
`EN (n+1) ≤ (1 + h · (114/5) · L) · EN n + |τ_n|`. The `(114/5)` factor is
the ℓ¹-norm of the AB6 coefficient vector
`(4277/1440, 7923/1440, 9982/1440, 7298/1440, 2877/1440, 475/1440)`. -/
theorem ab6_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ y₁ y₂ y₃ y₄ y₅ : ℝ) (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max (max (max (max
          |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
          |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|)
          |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|)
          |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|)
          |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|)
        |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|
      ≤ (1 + h * ((114 / 5) * L))
            * max (max (max (max (max
                  |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ n
                      - y (t₀ + (n : ℝ) * h)|
                  |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 1)
                      - y (t₀ + ((n : ℝ) + 1) * h)|)
                  |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 2)
                      - y (t₀ + ((n : ℝ) + 2) * h)|)
                  |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 3)
                      - y (t₀ + ((n : ℝ) + 3) * h)|)
                  |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 4)
                      - y (t₀ + ((n : ℝ) + 4) * h)|)
                  |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5)
                      - y (t₀ + ((n : ℝ) + 5) * h)|
        + |adamsBashforth6.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set en : ℝ := |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ n - y (t₀ + (n : ℝ) * h)|
    with hen_def
  set en1 : ℝ :=
    |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
    with hen1_def
  set en2 : ℝ :=
    |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|
    with hen2_def
  set en3 : ℝ :=
    |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|
    with hen3_def
  set en4 : ℝ :=
    |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|
    with hen4_def
  set en5 : ℝ :=
    |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|
    with hen5_def
  set en6 : ℝ :=
    |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|
    with hen6_def
  set τabs : ℝ :=
    |adamsBashforth6.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  have hen_nn : 0 ≤ en := abs_nonneg _
  have hen1_nn : 0 ≤ en1 := abs_nonneg _
  have hen2_nn : 0 ≤ en2 := abs_nonneg _
  have hen3_nn : 0 ≤ en3 := abs_nonneg _
  have hen4_nn : 0 ≤ en4 := abs_nonneg _
  have hen5_nn : 0 ≤ en5 := abs_nonneg _
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  -- One-step Lipschitz bound (from `ab6_one_step_lipschitz`).
  have hstep :
      en6 ≤ en5 + (4277 / 1440) * h * L * en5
                + (7923 / 1440) * h * L * en4
                + (9982 / 1440) * h * L * en3
                + (7298 / 1440) * h * L * en2
                + (2877 / 1440) * h * L * en1
                + (475 / 1440) * h * L * en + τabs := by
    have := ab6_one_step_lipschitz hh hf t₀ y₀ y₁ y₂ y₃ y₄ y₅ y hyf n
    show |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|
        ≤ |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|
          + (4277 / 1440) * h * L
              * |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 5)
                  - y (t₀ + ((n : ℝ) + 5) * h)|
          + (7923 / 1440) * h * L
              * |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 4)
                  - y (t₀ + ((n : ℝ) + 4) * h)|
          + (9982 / 1440) * h * L
              * |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 3)
                  - y (t₀ + ((n : ℝ) + 3) * h)|
          + (7298 / 1440) * h * L
              * |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 2)
                  - y (t₀ + ((n : ℝ) + 2) * h)|
          + (2877 / 1440) * h * L
              * |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ (n + 1)
                  - y (t₀ + ((n : ℝ) + 1) * h)|
          + (475 / 1440) * h * L
              * |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ n - y (t₀ + (n : ℝ) * h)|
          + |adamsBashforth6.localTruncationError h (t₀ + (n : ℝ) * h) y|
    exact this
  set EN_n : ℝ := max (max (max (max (max en en1) en2) en3) en4) en5 with hEN_n_def
  have hen_le_EN : en ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _)
  have hen1_le_EN : en1 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _)
  have hen2_le_EN : en2 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)
  have hen3_le_EN : en3 ≤ EN_n :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hen4_le_EN : en4 ≤ EN_n :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hen5_le_EN : en5 ≤ EN_n := le_max_right _ _
  have h4277_nn : 0 ≤ (4277 / 1440) * h * L := by positivity
  have h7923_nn : 0 ≤ (7923 / 1440) * h * L := by positivity
  have h9982_nn : 0 ≤ (9982 / 1440) * h * L := by positivity
  have h7298_nn : 0 ≤ (7298 / 1440) * h * L := by positivity
  have h2877_nn : 0 ≤ (2877 / 1440) * h * L := by positivity
  have h475_nn : 0 ≤ (475 / 1440) * h * L := by positivity
  have hEN_nn : 0 ≤ EN_n := le_trans hen_nn hen_le_EN
  have hcoef_nn : 0 ≤ h * ((114 / 5) * L) := by positivity
  -- en6 ≤ (1 + h*(114/5*L)) * EN_n + τabs.
  have hen6_bd : en6 ≤ (1 + h * ((114 / 5) * L)) * EN_n + τabs := by
    have h1 : (4277 / 1440) * h * L * en5 ≤ (4277 / 1440) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen5_le_EN h4277_nn
    have h2 : (7923 / 1440) * h * L * en4 ≤ (7923 / 1440) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen4_le_EN h7923_nn
    have h3 : (9982 / 1440) * h * L * en3 ≤ (9982 / 1440) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen3_le_EN h9982_nn
    have h4 : (7298 / 1440) * h * L * en2 ≤ (7298 / 1440) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen2_le_EN h7298_nn
    have h5 : (2877 / 1440) * h * L * en1 ≤ (2877 / 1440) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen1_le_EN h2877_nn
    have h6 : (475 / 1440) * h * L * en ≤ (475 / 1440) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen_le_EN h475_nn
    have h_alg :
        EN_n + (4277 / 1440) * h * L * EN_n
              + (7923 / 1440) * h * L * EN_n
              + (9982 / 1440) * h * L * EN_n
              + (7298 / 1440) * h * L * EN_n
              + (2877 / 1440) * h * L * EN_n
              + (475 / 1440) * h * L * EN_n + τabs
          = (1 + h * ((114 / 5) * L)) * EN_n + τabs := by ring
    linarith [hstep, hen5_le_EN, h1, h2, h3, h4, h5, h6, h_alg.le]
  -- en1, ..., en5 ≤ EN_n ≤ (1 + h*(114/5*L)) * EN_n + τabs.
  have hEN_le_grow : EN_n ≤ (1 + h * ((114 / 5) * L)) * EN_n := by
    have hone : (1 : ℝ) * EN_n ≤ (1 + h * ((114 / 5) * L)) * EN_n :=
      mul_le_mul_of_nonneg_right (by linarith) hEN_nn
    linarith
  have hen1_bd : en1 ≤ (1 + h * ((114 / 5) * L)) * EN_n + τabs := by
    linarith [hen1_le_EN, hEN_le_grow]
  have hen2_bd : en2 ≤ (1 + h * ((114 / 5) * L)) * EN_n + τabs := by
    linarith [hen2_le_EN, hEN_le_grow]
  have hen3_bd : en3 ≤ (1 + h * ((114 / 5) * L)) * EN_n + τabs := by
    linarith [hen3_le_EN, hEN_le_grow]
  have hen4_bd : en4 ≤ (1 + h * ((114 / 5) * L)) * EN_n + τabs := by
    linarith [hen4_le_EN, hEN_le_grow]
  have hen5_bd : en5 ≤ (1 + h * ((114 / 5) * L)) * EN_n + τabs := by
    linarith [hen5_le_EN, hEN_le_grow]
  exact max_le (max_le (max_le (max_le (max_le hen1_bd hen2_bd) hen3_bd)
    hen4_bd) hen5_bd) hen6_bd

/-- A `C^7` function has its seventh derivative bounded on every compact
interval `[a, b]`. -/
private theorem iteratedDeriv_seven_bounded_on_Icc
    {y : ℝ → ℝ} (hy : ContDiff ℝ 7 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, |iteratedDeriv 7 y t| ≤ M := by
  have h_cont : Continuous (iteratedDeriv 7 y) :=
    hy.continuous_iteratedDeriv 7 (by norm_num)
  obtain ⟨M, hM⟩ :=
    IsCompact.exists_bound_of_continuousOn (CompactIccSpace.isCompact_Icc)
      h_cont.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro t ht
  exact (hM t ht).trans (le_max_left _ _)

/-- Pointwise seventh-order Taylor (Lagrange) remainder bound: if `y` is
`C^7` and `|iteratedDeriv 7 y| ≤ M` on `[a, b]`, then for `t, t + r ∈ [a, b]`
with `r ≥ 0`,
`|y(t+r) - y(t) - r·y'(t) - r²/2·y''(t) - r³/6·y'''(t) - r⁴/24·y⁽⁴⁾(t)
  - r⁵/120·y⁽⁵⁾(t) - r⁶/720·y⁽⁶⁾(t)| ≤ M/5040 · r⁷`. -/
private theorem y_seventh_order_taylor_remainder
    {y : ℝ → ℝ} (hy : ContDiff ℝ 7 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 7 y t| ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    |y (t + r) - y t - r * deriv y t
        - r ^ 2 / 2 * iteratedDeriv 2 y t
        - r ^ 3 / 6 * iteratedDeriv 3 y t
        - r ^ 4 / 24 * iteratedDeriv 4 y t
        - r ^ 5 / 120 * iteratedDeriv 5 y t
        - r ^ 6 / 720 * iteratedDeriv 6 y t|
      ≤ M / 5040 * r ^ 7 := by
  by_cases hr' : r = 0
  · subst hr'; simp
  have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr')
  have htlt : t < t + r := by linarith
  have hUnique : UniqueDiffOn ℝ (Set.Icc t (t + r)) := uniqueDiffOn_Icc htlt
  have ht_mem_loc : t ∈ Set.Icc t (t + r) := Set.left_mem_Icc.mpr htlt.le
  -- Lagrange Taylor remainder at order 6 (seventh-derivative form).
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ : ∃ ξ ∈ Set.Ioo t (t + r),
      y (t + r) - taylorWithinEval y 6 (Set.Icc t (t + r)) t (t + r)
        = iteratedDeriv 7 y ξ * r ^ 7 / 5040 := by
    have hcdo : ContDiffOn ℝ 7 y (Set.Icc t (t + r)) :=
      hy.contDiffOn.of_le le_rfl
    have ⟨ξ, hξ_mem, hξ_eq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 6) htlt hcdo
    refine ⟨ξ, hξ_mem, ?_⟩
    have hpow : (t + r - t) ^ 7 = r ^ 7 := by ring
    have hfact : (((6 + 1 : ℕ).factorial : ℝ)) = 5040 := by
      simp [Nat.factorial]
    rw [hξ_eq, hpow, hfact]
  -- Compute the Taylor polynomial explicitly.
  have h_taylor :
      taylorWithinEval y 6 (Set.Icc t (t + r)) t (t + r)
        = y t + r * deriv y t + r ^ 2 / 2 * iteratedDeriv 2 y t
              + r ^ 3 / 6 * iteratedDeriv 3 y t
              + r ^ 4 / 24 * iteratedDeriv 4 y t
              + r ^ 5 / 120 * iteratedDeriv 5 y t
              + r ^ 6 / 720 * iteratedDeriv 6 y t := by
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
    have h6 :
        iteratedDerivWithin 6 y (Set.Icc t (t + r)) t = iteratedDeriv 6 y t :=
      iteratedDerivWithin_eq_iteratedDeriv (n := 6) hUnique
        (hy.contDiffAt.of_le (by norm_num)) ht_mem_loc
    have h0 :
        iteratedDerivWithin 0 y (Set.Icc t (t + r)) t = y t := by
      simp [iteratedDerivWithin_zero]
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero, h0, h1, h2, h3, h4, h5, h6]
    simp only [smul_eq_mul, Nat.factorial_zero, Nat.factorial_one,
      Nat.factorial_succ, Nat.cast_one, Nat.cast_ofNat, Nat.cast_succ,
      Nat.cast_mul, pow_zero, pow_one, mul_one, one_mul, zero_add,
      inv_one, Nat.factorial]
    ring
  -- Conclude.
  have hξ_in : ξ ∈ Set.Icc a b :=
    ⟨by linarith [hξ_mem.1, ht.1], by linarith [hξ_mem.2, htr.2]⟩
  have hbnd_ξ : |iteratedDeriv 7 y ξ| ≤ M := hbnd ξ hξ_in
  have h_eq :
      y (t + r) - y t - r * deriv y t
          - r ^ 2 / 2 * iteratedDeriv 2 y t
          - r ^ 3 / 6 * iteratedDeriv 3 y t
          - r ^ 4 / 24 * iteratedDeriv 4 y t
          - r ^ 5 / 120 * iteratedDeriv 5 y t
          - r ^ 6 / 720 * iteratedDeriv 6 y t
        = iteratedDeriv 7 y ξ * r ^ 7 / 5040 := by
    have := hξ_eq
    rw [h_taylor] at this
    linarith
  rw [h_eq]
  rw [show iteratedDeriv 7 y ξ * r ^ 7 / 5040
      = (iteratedDeriv 7 y ξ) * (r ^ 7 / 5040) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 7 / 5040)]
  calc |iteratedDeriv 7 y ξ| * (r ^ 7 / 5040)
      ≤ M * (r ^ 7 / 5040) :=
        mul_le_mul_of_nonneg_right hbnd_ξ (by positivity)
    _ = M / 5040 * r ^ 7 := by ring

/-- Pointwise sixth-order Taylor (Lagrange) remainder bound for the
derivative: if `y` is `C^7` and `|iteratedDeriv 7 y| ≤ M` on `[a, b]`,
then for `t, t + r ∈ [a, b]` with `r ≥ 0`,
`|y'(t+r) - y'(t) - r·y''(t) - r²/2·y'''(t) - r³/6·y⁽⁴⁾(t) - r⁴/24·y⁽⁵⁾(t)
  - r⁵/120·y⁽⁶⁾(t)| ≤ M/720 · r⁶`. -/
private theorem derivY_sixth_order_taylor_remainder
    {y : ℝ → ℝ} (hy : ContDiff ℝ 7 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 7 y t| ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    |deriv y (t + r) - deriv y t - r * iteratedDeriv 2 y t
        - r ^ 2 / 2 * iteratedDeriv 3 y t
        - r ^ 3 / 6 * iteratedDeriv 4 y t
        - r ^ 4 / 24 * iteratedDeriv 5 y t
        - r ^ 5 / 120 * iteratedDeriv 6 y t|
      ≤ M / 720 * r ^ 6 := by
  by_cases hr' : r = 0
  · subst hr'; simp
  have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr')
  have htlt : t < t + r := by linarith
  have hUnique : UniqueDiffOn ℝ (Set.Icc t (t + r)) := uniqueDiffOn_Icc htlt
  have ht_mem_loc : t ∈ Set.Icc t (t + r) := Set.left_mem_Icc.mpr htlt.le
  -- `deriv y` is `C^6` (since `y` is `C^7`).
  have hdy : ContDiff ℝ 6 (deriv y) := hy.deriv'
  -- Lagrange Taylor at order 5 for `deriv y` on `[t, t+r]`.
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ : ∃ ξ ∈ Set.Ioo t (t + r),
      deriv y (t + r) - taylorWithinEval (deriv y) 5 (Set.Icc t (t + r)) t (t + r)
        = iteratedDeriv 6 (deriv y) ξ * r ^ 6 / 720 := by
    have hcdo : ContDiffOn ℝ 6 (deriv y) (Set.Icc t (t + r)) :=
      hdy.contDiffOn.of_le le_rfl
    have ⟨ξ, hξ_mem, hξ_eq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 5) htlt hcdo
    refine ⟨ξ, hξ_mem, ?_⟩
    have hpow : (t + r - t) ^ 6 = r ^ 6 := by ring
    have hfact : (((5 + 1 : ℕ).factorial : ℝ)) = 720 := by
      simp [Nat.factorial]
    rw [hξ_eq, hpow, hfact]
  -- Compute the Taylor polynomial.
  have h_taylor :
      taylorWithinEval (deriv y) 5 (Set.Icc t (t + r)) t (t + r)
        = deriv y t + r * iteratedDeriv 2 y t
              + r ^ 2 / 2 * iteratedDeriv 3 y t
              + r ^ 3 / 6 * iteratedDeriv 4 y t
              + r ^ 4 / 24 * iteratedDeriv 5 y t
              + r ^ 5 / 120 * iteratedDeriv 6 y t := by
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
    have h5 :
        iteratedDerivWithin 5 (deriv y) (Set.Icc t (t + r)) t
          = iteratedDeriv 6 y t := by
      have heq := iteratedDerivWithin_eq_iteratedDeriv (n := 5) hUnique
        (hdy.contDiffAt.of_le (by norm_num)) ht_mem_loc
      rw [heq]
      have : iteratedDeriv 6 y = iteratedDeriv 5 (deriv y) :=
        iteratedDeriv_succ' (n := 5) (f := y)
      rw [this]
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, h3, h4, h5]
    simp only [smul_eq_mul, Nat.factorial_zero, Nat.factorial_one,
      Nat.factorial_succ, Nat.cast_one, Nat.cast_ofNat, Nat.cast_succ,
      Nat.cast_mul, pow_zero, pow_one, mul_one, one_mul, zero_add,
      inv_one, Nat.factorial]
    ring
  -- Bound `iteratedDeriv 6 (deriv y) ξ = iteratedDeriv 7 y ξ`.
  have hidd_eq : iteratedDeriv 6 (deriv y) = iteratedDeriv 7 y := by
    have : iteratedDeriv 7 y = iteratedDeriv 6 (deriv y) :=
      iteratedDeriv_succ' (n := 6) (f := y)
    exact this.symm
  have hξ_in : ξ ∈ Set.Icc a b :=
    ⟨by linarith [hξ_mem.1, ht.1], by linarith [hξ_mem.2, htr.2]⟩
  have hbnd_ξ : |iteratedDeriv 7 y ξ| ≤ M := hbnd ξ hξ_in
  have h_eq :
      deriv y (t + r) - deriv y t - r * iteratedDeriv 2 y t
          - r ^ 2 / 2 * iteratedDeriv 3 y t
          - r ^ 3 / 6 * iteratedDeriv 4 y t
          - r ^ 4 / 24 * iteratedDeriv 5 y t
          - r ^ 5 / 120 * iteratedDeriv 6 y t
        = iteratedDeriv 7 y ξ * r ^ 6 / 720 := by
    have hraw := hξ_eq
    rw [h_taylor, hidd_eq] at hraw
    linarith
  rw [h_eq]
  rw [show iteratedDeriv 7 y ξ * r ^ 6 / 720
      = (iteratedDeriv 7 y ξ) * (r ^ 6 / 720) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 6 / 720)]
  calc |iteratedDeriv 7 y ξ| * (r ^ 6 / 720)
      ≤ M * (r ^ 6 / 720) :=
        mul_le_mul_of_nonneg_right hbnd_ξ (by positivity)
    _ = M / 720 * r ^ 6 := by ring

/-- Pure algebraic identity: the AB6 residual rewrites as a signed sum of
seven Taylor remainders. Extracted as a stand-alone lemma so the kernel
checks the (large) `ring` proof term in isolation. -/
private lemma ab6_residual_alg_identity
    (y0 y5 y6 d0 d1 d2 d3 d4 d5 dd ddd dddd ddddd dddddd h : ℝ) :
    y6 - y5 - h * ((4277 / 1440) * d5 - (7923 / 1440) * d4
                  + (9982 / 1440) * d3 - (7298 / 1440) * d2
                  + (2877 / 1440) * d1 - (475 / 1440) * d0)
      = (y6 - y0 - (6 * h) * d0
            - (6 * h) ^ 2 / 2 * dd
            - (6 * h) ^ 3 / 6 * ddd
            - (6 * h) ^ 4 / 24 * dddd
            - (6 * h) ^ 5 / 120 * ddddd
            - (6 * h) ^ 6 / 720 * dddddd)
        - (y5 - y0 - (5 * h) * d0
            - (5 * h) ^ 2 / 2 * dd
            - (5 * h) ^ 3 / 6 * ddd
            - (5 * h) ^ 4 / 24 * dddd
            - (5 * h) ^ 5 / 120 * ddddd
            - (5 * h) ^ 6 / 720 * dddddd)
        - (4277 * h / 1440)
            * (d5 - d0 - (5 * h) * dd
                - (5 * h) ^ 2 / 2 * ddd
                - (5 * h) ^ 3 / 6 * dddd
                - (5 * h) ^ 4 / 24 * ddddd
                - (5 * h) ^ 5 / 120 * dddddd)
        + (7923 * h / 1440)
            * (d4 - d0 - (4 * h) * dd
                - (4 * h) ^ 2 / 2 * ddd
                - (4 * h) ^ 3 / 6 * dddd
                - (4 * h) ^ 4 / 24 * ddddd
                - (4 * h) ^ 5 / 120 * dddddd)
        - (9982 * h / 1440)
            * (d3 - d0 - (3 * h) * dd
                - (3 * h) ^ 2 / 2 * ddd
                - (3 * h) ^ 3 / 6 * dddd
                - (3 * h) ^ 4 / 24 * ddddd
                - (3 * h) ^ 5 / 120 * dddddd)
        + (7298 * h / 1440)
            * (d2 - d0 - (2 * h) * dd
                - (2 * h) ^ 2 / 2 * ddd
                - (2 * h) ^ 3 / 6 * dddd
                - (2 * h) ^ 4 / 24 * ddddd
                - (2 * h) ^ 5 / 120 * dddddd)
        - (2877 * h / 1440)
            * (d1 - d0 - h * dd
                - h ^ 2 / 2 * ddd
                - h ^ 3 / 6 * dddd
                - h ^ 4 / 24 * ddddd
                - h ^ 5 / 120 * dddddd) := by
  ring

/-- Pure algebraic identity: the sum of the seven scaled Lagrange
remainder bounds equals `(1264800760/7257600) · M · h^7`. -/
private lemma ab6_residual_bound_alg_identity (M h : ℝ) :
    M / 5040 * (6 * h) ^ 7 + M / 5040 * (5 * h) ^ 7
      + (4277 * h / 1440) * (M / 720 * (5 * h) ^ 6)
      + (7923 * h / 1440) * (M / 720 * (4 * h) ^ 6)
      + (9982 * h / 1440) * (M / 720 * (3 * h) ^ 6)
      + (7298 * h / 1440) * (M / 720 * (2 * h) ^ 6)
      + (2877 * h / 1440) * (M / 720 * h ^ 6)
      = (1264800760 / 7257600 : ℝ) * M * h ^ 7 := by
  ring

/-- Triangle inequality for the seven-term AB6 residual chunk. -/
private lemma ab6_residual_seven_term_triangle
    (A B C D E F G h : ℝ) (hh : 0 ≤ h) :
    |A - B - (4277 * h / 1440) * C + (7923 * h / 1440) * D
        - (9982 * h / 1440) * E + (7298 * h / 1440) * F
        - (2877 * h / 1440) * G|
      ≤ |A| + |B| + (4277 * h / 1440) * |C| + (7923 * h / 1440) * |D|
          + (9982 * h / 1440) * |E| + (7298 * h / 1440) * |F|
          + (2877 * h / 1440) * |G| := by
  have h4277h_nn : 0 ≤ 4277 * h / 1440 := by linarith
  have h7923h_nn : 0 ≤ 7923 * h / 1440 := by linarith
  have h9982h_nn : 0 ≤ 9982 * h / 1440 := by linarith
  have h7298h_nn : 0 ≤ 7298 * h / 1440 := by linarith
  have h2877h_nn : 0 ≤ 2877 * h / 1440 := by linarith
  have habs4277 : |(4277 * h / 1440) * C| = (4277 * h / 1440) * |C| := by
    rw [abs_mul, abs_of_nonneg h4277h_nn]
  have habs7923 : |(7923 * h / 1440) * D| = (7923 * h / 1440) * |D| := by
    rw [abs_mul, abs_of_nonneg h7923h_nn]
  have habs9982 : |(9982 * h / 1440) * E| = (9982 * h / 1440) * |E| := by
    rw [abs_mul, abs_of_nonneg h9982h_nn]
  have habs7298 : |(7298 * h / 1440) * F| = (7298 * h / 1440) * |F| := by
    rw [abs_mul, abs_of_nonneg h7298h_nn]
  have habs2877 : |(2877 * h / 1440) * G| = (2877 * h / 1440) * |G| := by
    rw [abs_mul, abs_of_nonneg h2877h_nn]
  have h1 : |A - B - (4277 * h / 1440) * C + (7923 * h / 1440) * D
                - (9982 * h / 1440) * E + (7298 * h / 1440) * F
                - (2877 * h / 1440) * G|
      ≤ |A - B - (4277 * h / 1440) * C + (7923 * h / 1440) * D
            - (9982 * h / 1440) * E + (7298 * h / 1440) * F|
        + |(2877 * h / 1440) * G| := abs_sub _ _
  have h2 : |A - B - (4277 * h / 1440) * C + (7923 * h / 1440) * D
                - (9982 * h / 1440) * E + (7298 * h / 1440) * F|
      ≤ |A - B - (4277 * h / 1440) * C + (7923 * h / 1440) * D
            - (9982 * h / 1440) * E|
        + |(7298 * h / 1440) * F| := abs_add_le _ _
  have h3 : |A - B - (4277 * h / 1440) * C + (7923 * h / 1440) * D
                - (9982 * h / 1440) * E|
      ≤ |A - B - (4277 * h / 1440) * C + (7923 * h / 1440) * D|
        + |(9982 * h / 1440) * E| := abs_sub _ _
  have h4 : |A - B - (4277 * h / 1440) * C + (7923 * h / 1440) * D|
      ≤ |A - B - (4277 * h / 1440) * C| + |(7923 * h / 1440) * D| :=
    abs_add_le _ _
  have h5 : |A - B - (4277 * h / 1440) * C|
      ≤ |A - B| + |(4277 * h / 1440) * C| := abs_sub _ _
  have h6 : |A - B| ≤ |A| + |B| := abs_sub _ _
  linarith [habs4277.le, habs4277.ge, habs7923.le, habs7923.ge,
    habs9982.le, habs9982.ge, habs7298.le, habs7298.ge,
    habs2877.le, habs2877.ge]

/-- Pointwise AB6 truncation residual bound. The textbook AB6 residual
expands as
`R_y(6) − R_y(5) − (4277h/1440)·R_y'(5) + (7923h/1440)·R_y'(4)
  − (9982h/1440)·R_y'(3) + (7298h/1440)·R_y'(2) − (2877h/1440)·R_y'(1)`,
with `R_y'(0) = 0`. The combined coefficient is
`1264800760/7257600 ≤ 175`. -/
private theorem ab6_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 7 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 7 y t| ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (ht4h : t + 4 * h ∈ Set.Icc a b)
    (ht5h : t + 5 * h ∈ Set.Icc a b)
    (ht6h : t + 6 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    |y (t + 6 * h) - y (t + 5 * h)
        - h * ((4277 / 1440) * deriv y (t + 5 * h)
              - (7923 / 1440) * deriv y (t + 4 * h)
              + (9982 / 1440) * deriv y (t + 3 * h)
              - (7298 / 1440) * deriv y (t + 2 * h)
              + (2877 / 1440) * deriv y (t + h)
              - (475 / 1440) * deriv y t)|
      ≤ (175 : ℝ) * M * h ^ 7 := by
  -- Seven Taylor remainders.
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have h5h : 0 ≤ 5 * h := by linarith
  have h6h : 0 ≤ 6 * h := by linarith
  -- R_y(5), R_y(6): y Taylor remainders at order 7.
  have hRy5 :=
    y_seventh_order_taylor_remainder hy hbnd ht ht5h h5h
  have hRy6 :=
    y_seventh_order_taylor_remainder hy hbnd ht ht6h h6h
  -- R_y'(1), …, R_y'(5): y' Taylor remainders at order 6.
  have hRyp1 :=
    derivY_sixth_order_taylor_remainder hy hbnd ht hth hh
  have hRyp2 :=
    derivY_sixth_order_taylor_remainder hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_sixth_order_taylor_remainder hy hbnd ht ht3h h3h
  have hRyp4 :=
    derivY_sixth_order_taylor_remainder hy hbnd ht ht4h h4h
  have hRyp5 :=
    derivY_sixth_order_taylor_remainder hy hbnd ht ht5h h5h
  -- Abbreviations.
  set y0 := y t with hy0_def
  set y5 := y (t + 5 * h) with hy5_def
  set y6 := y (t + 6 * h) with hy6_def
  set d0 := deriv y t with hd0_def
  set d1 := deriv y (t + h) with hd1_def
  set d2 := deriv y (t + 2 * h) with hd2_def
  set d3 := deriv y (t + 3 * h) with hd3_def
  set d4 := deriv y (t + 4 * h) with hd4_def
  set d5 := deriv y (t + 5 * h) with hd5_def
  set dd := iteratedDeriv 2 y t with hdd_def
  set ddd := iteratedDeriv 3 y t with hddd_def
  set dddd := iteratedDeriv 4 y t with hdddd_def
  set ddddd := iteratedDeriv 5 y t with hddddd_def
  set dddddd := iteratedDeriv 6 y t with hdddddd_def
  -- Algebraic identity for the residual.
  have hLTE_eq :
      y6 - y5 - h * ((4277 / 1440) * d5 - (7923 / 1440) * d4
                    + (9982 / 1440) * d3 - (7298 / 1440) * d2
                    + (2877 / 1440) * d1 - (475 / 1440) * d0)
        = (y6 - y0 - (6 * h) * d0
              - (6 * h) ^ 2 / 2 * dd
              - (6 * h) ^ 3 / 6 * ddd
              - (6 * h) ^ 4 / 24 * dddd
              - (6 * h) ^ 5 / 120 * ddddd
              - (6 * h) ^ 6 / 720 * dddddd)
          - (y5 - y0 - (5 * h) * d0
              - (5 * h) ^ 2 / 2 * dd
              - (5 * h) ^ 3 / 6 * ddd
              - (5 * h) ^ 4 / 24 * dddd
              - (5 * h) ^ 5 / 120 * ddddd
              - (5 * h) ^ 6 / 720 * dddddd)
          - (4277 * h / 1440)
              * (d5 - d0 - (5 * h) * dd
                  - (5 * h) ^ 2 / 2 * ddd
                  - (5 * h) ^ 3 / 6 * dddd
                  - (5 * h) ^ 4 / 24 * ddddd
                  - (5 * h) ^ 5 / 120 * dddddd)
          + (7923 * h / 1440)
              * (d4 - d0 - (4 * h) * dd
                  - (4 * h) ^ 2 / 2 * ddd
                  - (4 * h) ^ 3 / 6 * dddd
                  - (4 * h) ^ 4 / 24 * ddddd
                  - (4 * h) ^ 5 / 120 * dddddd)
          - (9982 * h / 1440)
              * (d3 - d0 - (3 * h) * dd
                  - (3 * h) ^ 2 / 2 * ddd
                  - (3 * h) ^ 3 / 6 * dddd
                  - (3 * h) ^ 4 / 24 * ddddd
                  - (3 * h) ^ 5 / 120 * dddddd)
          + (7298 * h / 1440)
              * (d2 - d0 - (2 * h) * dd
                  - (2 * h) ^ 2 / 2 * ddd
                  - (2 * h) ^ 3 / 6 * dddd
                  - (2 * h) ^ 4 / 24 * ddddd
                  - (2 * h) ^ 5 / 120 * dddddd)
          - (2877 * h / 1440)
              * (d1 - d0 - h * dd
                  - h ^ 2 / 2 * ddd
                  - h ^ 3 / 6 * dddd
                  - h ^ 4 / 24 * ddddd
                  - h ^ 5 / 120 * dddddd) :=
    ab6_residual_alg_identity y0 y5 y6 d0 d1 d2 d3 d4 d5 dd ddd dddd ddddd dddddd h
  rw [hLTE_eq]
  -- Triangle inequality (chained).
  set A := y6 - y0 - (6 * h) * d0
            - (6 * h) ^ 2 / 2 * dd
            - (6 * h) ^ 3 / 6 * ddd
            - (6 * h) ^ 4 / 24 * dddd
            - (6 * h) ^ 5 / 120 * ddddd
            - (6 * h) ^ 6 / 720 * dddddd with hA_def
  set B := y5 - y0 - (5 * h) * d0
            - (5 * h) ^ 2 / 2 * dd
            - (5 * h) ^ 3 / 6 * ddd
            - (5 * h) ^ 4 / 24 * dddd
            - (5 * h) ^ 5 / 120 * ddddd
            - (5 * h) ^ 6 / 720 * dddddd with hB_def
  set C := d5 - d0 - (5 * h) * dd
            - (5 * h) ^ 2 / 2 * ddd
            - (5 * h) ^ 3 / 6 * dddd
            - (5 * h) ^ 4 / 24 * ddddd
            - (5 * h) ^ 5 / 120 * dddddd with hC_def
  set D := d4 - d0 - (4 * h) * dd
            - (4 * h) ^ 2 / 2 * ddd
            - (4 * h) ^ 3 / 6 * dddd
            - (4 * h) ^ 4 / 24 * ddddd
            - (4 * h) ^ 5 / 120 * dddddd with hD_def
  set E := d3 - d0 - (3 * h) * dd
            - (3 * h) ^ 2 / 2 * ddd
            - (3 * h) ^ 3 / 6 * dddd
            - (3 * h) ^ 4 / 24 * ddddd
            - (3 * h) ^ 5 / 120 * dddddd with hE_def
  set F := d2 - d0 - (2 * h) * dd
            - (2 * h) ^ 2 / 2 * ddd
            - (2 * h) ^ 3 / 6 * dddd
            - (2 * h) ^ 4 / 24 * ddddd
            - (2 * h) ^ 5 / 120 * dddddd with hF_def
  set G := d1 - d0 - h * dd
            - h ^ 2 / 2 * ddd
            - h ^ 3 / 6 * dddd
            - h ^ 4 / 24 * ddddd
            - h ^ 5 / 120 * dddddd with hG_def
  have h4277h_nn : 0 ≤ 4277 * h / 1440 := by linarith
  have h7923h_nn : 0 ≤ 7923 * h / 1440 := by linarith
  have h9982h_nn : 0 ≤ 9982 * h / 1440 := by linarith
  have h7298h_nn : 0 ≤ 7298 * h / 1440 := by linarith
  have h2877h_nn : 0 ≤ 2877 * h / 1440 := by linarith
  have htri := ab6_residual_seven_term_triangle A B C D E F G h hh
  -- Bounds on each piece.
  have hA_bd : |A| ≤ M / 5040 * (6 * h) ^ 7 := hRy6
  have hB_bd : |B| ≤ M / 5040 * (5 * h) ^ 7 := hRy5
  have hC_bd : |C| ≤ M / 720 * (5 * h) ^ 6 := hRyp5
  have hD_bd : |D| ≤ M / 720 * (4 * h) ^ 6 := hRyp4
  have hE_bd : |E| ≤ M / 720 * (3 * h) ^ 6 := hRyp3
  have hF_bd : |F| ≤ M / 720 * (2 * h) ^ 6 := hRyp2
  have hG_bd : |G| ≤ M / 720 * h ^ 6 := hRyp1
  -- Multiply scaled bounds.
  have h4277C_bd : (4277 * h / 1440) * |C|
      ≤ (4277 * h / 1440) * (M / 720 * (5 * h) ^ 6) :=
    mul_le_mul_of_nonneg_left hC_bd h4277h_nn
  have h7923D_bd : (7923 * h / 1440) * |D|
      ≤ (7923 * h / 1440) * (M / 720 * (4 * h) ^ 6) :=
    mul_le_mul_of_nonneg_left hD_bd h7923h_nn
  have h9982E_bd : (9982 * h / 1440) * |E|
      ≤ (9982 * h / 1440) * (M / 720 * (3 * h) ^ 6) :=
    mul_le_mul_of_nonneg_left hE_bd h9982h_nn
  have h7298F_bd : (7298 * h / 1440) * |F|
      ≤ (7298 * h / 1440) * (M / 720 * (2 * h) ^ 6) :=
    mul_le_mul_of_nonneg_left hF_bd h7298h_nn
  have h2877G_bd : (2877 * h / 1440) * |G|
      ≤ (2877 * h / 1440) * (M / 720 * h ^ 6) :=
    mul_le_mul_of_nonneg_left hG_bd h2877h_nn
  -- Sum of upper bounds = (1264802020/7257600) · M · h^7 ≤ 175 · M · h^7.
  have hbound_alg :
      M / 5040 * (6 * h) ^ 7 + M / 5040 * (5 * h) ^ 7
        + (4277 * h / 1440) * (M / 720 * (5 * h) ^ 6)
        + (7923 * h / 1440) * (M / 720 * (4 * h) ^ 6)
        + (9982 * h / 1440) * (M / 720 * (3 * h) ^ 6)
        + (7298 * h / 1440) * (M / 720 * (2 * h) ^ 6)
        + (2877 * h / 1440) * (M / 720 * h ^ 6)
        = (1264800760 / 7257600 : ℝ) * M * h ^ 7 :=
    ab6_residual_bound_alg_identity M h
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (abs_nonneg _).trans this
  have hh7_nn : 0 ≤ h ^ 7 := by positivity
  have hMh7_nn : 0 ≤ M * h ^ 7 := mul_nonneg hMnn hh7_nn
  have hslack : (1264800760 / 7257600 : ℝ) * M * h ^ 7 ≤ 175 * M * h ^ 7 := by
    have hle : (1264800760 / 7257600 : ℝ) ≤ 175 := by norm_num
    have := mul_le_mul_of_nonneg_right hle hMh7_nn
    linarith [this]
  calc |A - B - (4277 * h / 1440) * C + (7923 * h / 1440) * D
            - (9982 * h / 1440) * E + (7298 * h / 1440) * F
            - (2877 * h / 1440) * G|
      ≤ |A| + |B| + (4277 * h / 1440) * |C| + (7923 * h / 1440) * |D|
          + (9982 * h / 1440) * |E| + (7298 * h / 1440) * |F|
          + (2877 * h / 1440) * |G| := htri
    _ ≤ M / 5040 * (6 * h) ^ 7 + M / 5040 * (5 * h) ^ 7
          + (4277 * h / 1440) * (M / 720 * (5 * h) ^ 6)
          + (7923 * h / 1440) * (M / 720 * (4 * h) ^ 6)
          + (9982 * h / 1440) * (M / 720 * (3 * h) ^ 6)
          + (7298 * h / 1440) * (M / 720 * (2 * h) ^ 6)
          + (2877 * h / 1440) * (M / 720 * h ^ 6) := by
        linarith [hA_bd, hB_bd, h4277C_bd, h7923D_bd, h9982E_bd, h7298F_bd,
          h2877G_bd]
    _ = (1264800760 / 7257600 : ℝ) * M * h ^ 7 := hbound_alg
    _ ≤ 175 * M * h ^ 7 := hslack

/-- Uniform bound on the AB6 one-step truncation residual on a finite
horizon, given a `C^7` exact solution. -/
theorem ab6_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 7 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 6) * h ≤ T →
        |adamsBashforth6.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 7 := by
  -- Compact sample interval `[t₀, t₀ + T + 1]` covers all `t + kh` with `k ≤ 6`.
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_seven_bounded_on_Icc hy t₀ (t₀ + T + 1)
  refine ⟨(175 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 6) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 6) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 6) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 6) * h := by nlinarith
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 4 * h ≤ ((n : ℝ) + 6) * h := by nlinarith
    linarith
  have ht5h_mem : t + 5 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 5 * h ≤ ((n : ℝ) + 6) * h := by nlinarith
    linarith
  have ht6h_mem : t + 6 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 6 * h = ((n : ℝ) + 6) * h := by ring
    linarith
  -- Rewrite the LTE in textbook form.
  rw [ab6_localTruncationError_eq]
  show |y (t + 6 * h) - y (t + 5 * h)
      - h * (4277 / 1440 * deriv y (t + 5 * h)
              - 7923 / 1440 * deriv y (t + 4 * h)
              + 9982 / 1440 * deriv y (t + 3 * h)
              - 7298 / 1440 * deriv y (t + 2 * h)
              + 2877 / 1440 * deriv y (t + h)
              - 475 / 1440 * deriv y t)|
    ≤ 175 * M * h ^ 7
  have hreshape :
      h * (4277 / 1440 * deriv y (t + 5 * h)
            - 7923 / 1440 * deriv y (t + 4 * h)
            + 9982 / 1440 * deriv y (t + 3 * h)
            - 7298 / 1440 * deriv y (t + 2 * h)
            + 2877 / 1440 * deriv y (t + h)
            - 475 / 1440 * deriv y t)
        = h * ((4277 / 1440) * deriv y (t + 5 * h)
              - (7923 / 1440) * deriv y (t + 4 * h)
              + (9982 / 1440) * deriv y (t + 3 * h)
              - (7298 / 1440) * deriv y (t + 2 * h)
              + (2877 / 1440) * deriv y (t + h)
              - (475 / 1440) * deriv y t) := by ring
  rw [hreshape]
  exact ab6_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem ht4h_mem ht5h_mem ht6h_mem hh.le

/-! #### Generic AB scalar bridge

Cycle 432 routes the scalar AB6 headline through the generic AB scaffold
at `s = 6`, mirroring the AB5 scalar bridge. The coefficient tuple,
Lipschitz constant lemma, iteration bridge, and residual bridge are
introduced here so the scalar `ab6_global_error_bound` proof body can
specialize `ab_global_error_bound_generic`. -/

/-- AB6 coefficient vector for the generic AB scaffold, ordered from the
oldest to newest sample in the six-step window. -/
noncomputable def ab6GenericCoeff : Fin 6 → ℝ :=
  ![-(475 : ℝ) / 1440, (2877 : ℝ) / 1440, -(7298 : ℝ) / 1440,
    (9982 : ℝ) / 1440, -(7923 : ℝ) / 1440, (4277 : ℝ) / 1440]

@[simp] lemma ab6GenericCoeff_zero :
    ab6GenericCoeff 0 = -(475 : ℝ) / 1440 := rfl

@[simp] lemma ab6GenericCoeff_one :
    ab6GenericCoeff 1 = (2877 : ℝ) / 1440 := rfl

@[simp] lemma ab6GenericCoeff_two :
    ab6GenericCoeff 2 = -(7298 : ℝ) / 1440 := rfl

@[simp] lemma ab6GenericCoeff_three :
    ab6GenericCoeff 3 = (9982 : ℝ) / 1440 := rfl

@[simp] lemma ab6GenericCoeff_four :
    ab6GenericCoeff 4 = -(7923 : ℝ) / 1440 := rfl

@[simp] lemma ab6GenericCoeff_five :
    ab6GenericCoeff 5 = (4277 : ℝ) / 1440 := rfl

/-- The effective Lipschitz constant for the generic AB scaffold at the
AB6 coefficient tuple is `(114/5) · L`. -/
lemma abLip_ab6GenericCoeff (L : ℝ) :
    abLip 6 ab6GenericCoeff L = (114 / 5) * L := by
  rw [abLip, Fin.sum_univ_six, ab6GenericCoeff_zero, ab6GenericCoeff_one,
    ab6GenericCoeff_two, ab6GenericCoeff_three, ab6GenericCoeff_four,
    ab6GenericCoeff_five]
  rw [show |(-(475 : ℝ) / 1440)| = (475 : ℝ) / 1440 by norm_num,
      show |((2877 : ℝ) / 1440)| = (2877 : ℝ) / 1440 by norm_num,
      show |(-(7298 : ℝ) / 1440)| = (7298 : ℝ) / 1440 by norm_num,
      show |((9982 : ℝ) / 1440)| = (9982 : ℝ) / 1440 by norm_num,
      show |(-(7923 : ℝ) / 1440)| = (7923 : ℝ) / 1440 by norm_num,
      show |((4277 : ℝ) / 1440)| = (4277 : ℝ) / 1440 by norm_num]
  ring

/-- Bridge: the AB6 scalar iteration is the generic AB iteration
at `s = 6` with `α = ab6GenericCoeff` and starting samples
`![y₀, y₁, y₂, y₃, y₄, y₅]`. -/
lemma ab6Iter_eq_abIter
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ : ℝ) (n : ℕ) :
    ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ n
      = abIter 6 ab6GenericCoeff h f t₀ ![y₀, y₁, y₂, y₃, y₄, y₅] n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      show ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 0 = _
      rw [ab6Iter_zero]
      unfold abIter
      simp
    | 1 =>
      show ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 1 = _
      rw [ab6Iter_one]
      unfold abIter
      simp
    | 2 =>
      show ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 2 = _
      rw [ab6Iter_two]
      unfold abIter
      simp
    | 3 =>
      show ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 3 = _
      rw [ab6Iter_three]
      unfold abIter
      simp
    | 4 =>
      show ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 4 = _
      rw [ab6Iter_four]
      unfold abIter
      simp
    | 5 =>
      show ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ 5 = _
      rw [ab6Iter_five]
      unfold abIter
      simp
    | k + 6 =>
      rw [ab6Iter_succ_succ_succ_succ_succ_succ]
      rw [abIter_step (s := 6) (by norm_num)
          ab6GenericCoeff h f t₀ ![y₀, y₁, y₂, y₃, y₄, y₅] k]
      rw [show (k + 6 - 1 : ℕ) = k + 5 from by omega]
      rw [Fin.sum_univ_six]
      have hval3 : ((3 : Fin 6) : ℕ) = 3 := rfl
      have hval4 : ((4 : Fin 6) : ℕ) = 4 := rfl
      have hval5 : ((5 : Fin 6) : ℕ) = 5 := rfl
      simp only [ab6GenericCoeff_zero, ab6GenericCoeff_one, ab6GenericCoeff_two,
        ab6GenericCoeff_three, ab6GenericCoeff_four, ab6GenericCoeff_five,
        Fin.val_zero, Fin.val_one, Fin.val_two, hval3, hval4, hval5,
        Nat.add_zero]
      rw [← ih k (by omega), ← ih (k + 1) (by omega), ← ih (k + 2) (by omega),
        ← ih (k + 3) (by omega), ← ih (k + 4) (by omega),
        ← ih (k + 5) (by omega)]
      rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring,
        show ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 by push_cast; ring,
        show ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 by push_cast; ring,
        show ((k + 4 : ℕ) : ℝ) = (k : ℝ) + 4 by push_cast; ring,
        show ((k + 5 : ℕ) : ℝ) = (k : ℝ) + 5 by push_cast; ring]
      ring

/-- Bridge: the AB6 scalar truncation residual at base point `t₀ + n · h`
equals the generic AB residual at index `n`. -/
lemma ab6Residual_eq_abResidual
    (h : ℝ) (y : ℝ → ℝ) (t₀ : ℝ) (n : ℕ) :
    y (t₀ + (n : ℝ) * h + 6 * h) - y (t₀ + (n : ℝ) * h + 5 * h)
        - h * ((4277 / 1440) * deriv y (t₀ + (n : ℝ) * h + 5 * h)
              - (7923 / 1440) * deriv y (t₀ + (n : ℝ) * h + 4 * h)
              + (9982 / 1440) * deriv y (t₀ + (n : ℝ) * h + 3 * h)
              - (7298 / 1440) * deriv y (t₀ + (n : ℝ) * h + 2 * h)
              + (2877 / 1440) * deriv y (t₀ + (n : ℝ) * h + h)
              - (475 / 1440) * deriv y (t₀ + (n : ℝ) * h))
      = abResidual 6 ab6GenericCoeff h y t₀ n := by
  unfold abResidual
  rw [Fin.sum_univ_six, ab6GenericCoeff_zero, ab6GenericCoeff_one,
    ab6GenericCoeff_two, ab6GenericCoeff_three, ab6GenericCoeff_four,
    ab6GenericCoeff_five]
  have eA : t₀ + (n : ℝ) * h + 6 * h = t₀ + ((n + 6 : ℕ) : ℝ) * h := by
    push_cast; ring
  have eB :
      t₀ + (n : ℝ) * h + 5 * h = t₀ + ((n + 6 - 1 : ℕ) : ℝ) * h := by
    have hsub : (n + 6 - 1 : ℕ) = n + 5 := by omega
    rw [hsub]; push_cast; ring
  have eC : t₀ + (n : ℝ) * h
      = t₀ + ((n + ((0 : Fin 6) : ℕ) : ℕ) : ℝ) * h := by
    simp [Fin.val_zero]
  have eD : t₀ + (n : ℝ) * h + h
      = t₀ + ((n + ((1 : Fin 6) : ℕ) : ℕ) : ℝ) * h := by
    simp [Fin.val_one]; ring
  have eE : t₀ + (n : ℝ) * h + 2 * h
      = t₀ + ((n + ((2 : Fin 6) : ℕ) : ℕ) : ℝ) * h := by
    simp [Fin.val_two]; ring
  have eF : t₀ + (n : ℝ) * h + 3 * h
      = t₀ + ((n + ((3 : Fin 6) : ℕ) : ℕ) : ℝ) * h := by
    have : ((3 : Fin 6) : ℕ) = 3 := rfl
    rw [this]; push_cast; ring
  have eG : t₀ + (n : ℝ) * h + 4 * h
      = t₀ + ((n + ((4 : Fin 6) : ℕ) : ℕ) : ℝ) * h := by
    have : ((4 : Fin 6) : ℕ) = 4 := rfl
    rw [this]; push_cast; ring
  have eH : t₀ + (n : ℝ) * h + 5 * h
      = t₀ + ((n + ((5 : Fin 6) : ℕ) : ℕ) : ℝ) * h := by
    have : ((5 : Fin 6) : ℕ) = 5 := rfl
    rw [this]; push_cast; ring
  rw [← eA, ← eB, ← eC, ← eD, ← eE, ← eF, ← eG, ← eH]
  ring

/-- Final AB6 global error bound on `[t₀, t₀ + T]`. Under Lipschitz `f`,
`C^7` exact solution `y` with `deriv y t = f t (y t)`, and starting
errors `|y_i - y(t_i)| ≤ ε₀` for `i = 0, 1, 2, 3, 4, 5`, the AB6 iterate
error obeys `O(ε₀ + h^6)` on a finite horizon. -/
theorem ab6_global_error_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 7 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      ∀ {y₀ y₁ y₂ y₃ y₄ y₅ ε₀ : ℝ}, 0 ≤ ε₀ →
      |y₀ - y t₀| ≤ ε₀ → |y₁ - y (t₀ + h)| ≤ ε₀ →
      |y₂ - y (t₀ + 2 * h)| ≤ ε₀ →
      |y₃ - y (t₀ + 3 * h)| ≤ ε₀ →
      |y₄ - y (t₀ + 4 * h)| ≤ ε₀ →
      |y₅ - y (t₀ + 5 * h)| ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 5) * h ≤ T →
      |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ N - y (t₀ + (N : ℝ) * h)|
        ≤ Real.exp ((114 / 5) * L * T) * ε₀ + K * h ^ 6 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    ab6_local_residual_bound hy t₀ T hT
  refine ⟨T * Real.exp ((114 / 5) * L * T) * C, δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
  intro h hh hδ_le y₀ y₁ y₂ y₃ y₄ y₅ ε₀ hε₀
    he0_bd he1_bd he2_bd he3_bd he4_bd he5_bd N hNh
  set α : Fin 6 → ℝ := ab6GenericCoeff with hα_def
  set y₀_sext : Fin 6 → ℝ := ![y₀, y₁, y₂, y₃, y₄, y₅] with hy_sext_def
  have hs : (1 : ℕ) ≤ 6 := by norm_num
  haveI : Nonempty (Fin 6) := ⟨⟨0, hs⟩⟩
  have hiter0 : abIter 6 α h f t₀ y₀_sext 0 = y₀ := by
    unfold abIter; simp [hy_sext_def]
  have hiter1 : abIter 6 α h f t₀ y₀_sext 1 = y₁ := by
    unfold abIter; simp [hy_sext_def]
  have hiter2 : abIter 6 α h f t₀ y₀_sext 2 = y₂ := by
    unfold abIter; simp [hy_sext_def]
  have hiter3 : abIter 6 α h f t₀ y₀_sext 3 = y₃ := by
    unfold abIter; simp [hy_sext_def]
  have hiter4 : abIter 6 α h f t₀ y₀_sext 4 = y₄ := by
    unfold abIter; simp [hy_sext_def]
  have hiter5 : abIter 6 α h f t₀ y₀_sext 5 = y₅ := by
    unfold abIter; simp [hy_sext_def]
  have hstart : abErrWindow hs α h f t₀ y₀_sext y 0 ≤ ε₀ := by
    unfold abErrWindow
    apply Finset.sup'_le
    intro j _
    show abErr 6 α h f t₀ y₀_sext y (0 + (j : ℕ)) ≤ ε₀
    unfold abErr
    fin_cases j
    · show |abIter 6 α h f t₀ y₀_sext 0
          - y (t₀ + ((0 + (((0 : Fin 6) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter0]
      have : ((0 + (((0 : Fin 6) : ℕ) : ℕ) : ℕ) : ℝ) = 0 := by simp
      rw [this, zero_mul, add_zero]; exact he0_bd
    · show |abIter 6 α h f t₀ y₀_sext 1
          - y (t₀ + ((0 + (((1 : Fin 6) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter1]
      have : ((0 + (((1 : Fin 6) : ℕ) : ℕ) : ℕ) : ℝ) = 1 := by simp
      rw [this, one_mul]; exact he1_bd
    · show |abIter 6 α h f t₀ y₀_sext 2
          - y (t₀ + ((0 + (((2 : Fin 6) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter2]
      have : ((0 + (((2 : Fin 6) : ℕ) : ℕ) : ℕ) : ℝ) = 2 := by simp
      rw [this]; exact he2_bd
    · show |abIter 6 α h f t₀ y₀_sext 3
          - y (t₀ + ((0 + (((3 : Fin 6) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter3]
      have hval3 : ((3 : Fin 6) : ℕ) = 3 := rfl
      have : ((0 + (((3 : Fin 6) : ℕ) : ℕ) : ℕ) : ℝ) = 3 := by
        rw [hval3]; push_cast; ring
      rw [this]; exact he3_bd
    · show |abIter 6 α h f t₀ y₀_sext 4
          - y (t₀ + ((0 + (((4 : Fin 6) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter4]
      have hval4 : ((4 : Fin 6) : ℕ) = 4 := rfl
      have : ((0 + (((4 : Fin 6) : ℕ) : ℕ) : ℕ) : ℝ) = 4 := by
        rw [hval4]; push_cast; ring
      rw [this]; exact he4_bd
    · show |abIter 6 α h f t₀ y₀_sext 5
          - y (t₀ + ((0 + (((5 : Fin 6) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter5]
      have hval5 : ((5 : Fin 6) : ℕ) = 5 := rfl
      have : ((0 + (((5 : Fin 6) : ℕ) : ℕ) : ℕ) : ℝ) = 5 := by
        rw [hval5]; push_cast; ring
      rw [this]; exact he5_bd
  have hres_gen : ∀ n : ℕ, n < N →
      |abResidual 6 α h y t₀ n| ≤ C * h ^ (6 + 1) := by
    intro n hn_lt
    have hcast : (n : ℝ) + 6 ≤ (N : ℝ) + 5 := by
      have : (n : ℝ) + 1 ≤ (N : ℝ) := by
        exact_mod_cast Nat.lt_iff_add_one_le.mp hn_lt
      linarith
    have hn6_le : ((n : ℝ) + 6) * h ≤ T := by
      have hmul : ((n : ℝ) + 6) * h ≤ ((N : ℝ) + 5) * h :=
        mul_le_mul_of_nonneg_right hcast hh.le
      linarith
    have hres := hresidual hh hδ_le n hn6_le
    have hLTE_eq := ab6_localTruncationError_eq h (t₀ + (n : ℝ) * h) y
    have hbridge := ab6Residual_eq_abResidual h y t₀ n
    have hpow : C * h ^ (6 + 1) = C * h ^ 7 := by norm_num
    rw [hα_def, ← hbridge]
    have hreshape :
        h * ((4277 / 1440) * deriv y (t₀ + (n : ℝ) * h + 5 * h)
              - (7923 / 1440) * deriv y (t₀ + (n : ℝ) * h + 4 * h)
              + (9982 / 1440) * deriv y (t₀ + (n : ℝ) * h + 3 * h)
              - (7298 / 1440) * deriv y (t₀ + (n : ℝ) * h + 2 * h)
              + (2877 / 1440) * deriv y (t₀ + (n : ℝ) * h + h)
              - (475 / 1440) * deriv y (t₀ + (n : ℝ) * h))
          = h * (4277 / 1440 * deriv y (t₀ + (n : ℝ) * h + 5 * h)
                - 7923 / 1440 * deriv y (t₀ + (n : ℝ) * h + 4 * h)
                + 9982 / 1440 * deriv y (t₀ + (n : ℝ) * h + 3 * h)
                - 7298 / 1440 * deriv y (t₀ + (n : ℝ) * h + 2 * h)
                + 2877 / 1440 * deriv y (t₀ + (n : ℝ) * h + h)
                - 475 / 1440 * deriv y (t₀ + (n : ℝ) * h)) := by ring
    rw [hreshape, ← hLTE_eq]
    linarith [hres, hpow.symm.le, hpow.le]
  have hNh' : (N : ℝ) * h ≤ T := by
    have hmono : (N : ℝ) * h ≤ ((N : ℝ) + 5) * h := by
      have h1 : (N : ℝ) ≤ (N : ℝ) + 5 := by linarith
      exact mul_le_mul_of_nonneg_right h1 hh.le
    linarith
  have hgeneric :=
    ab_global_error_bound_generic (p := 6) hs α hh.le hL hC_nn hf t₀
      y₀_sext y hyf hε₀ hstart N hNh' hres_gen
  rw [show abLip 6 α L = (114 / 5) * L from by
    rw [hα_def]; exact abLip_ab6GenericCoeff L] at hgeneric
  have hwindow_ge : abErr 6 α h f t₀ y₀_sext y N
      ≤ abErrWindow hs α h f t₀ y₀_sext y N := by
    show abErr 6 α h f t₀ y₀_sext y (N + ((⟨0, hs⟩ : Fin 6) : ℕ))
        ≤ abErrWindow hs α h f t₀ y₀_sext y N
    unfold abErrWindow
    exact Finset.le_sup' (b := ⟨0, hs⟩)
      (f := fun j : Fin 6 => abErr 6 α h f t₀ y₀_sext y (N + (j : ℕ)))
      (Finset.mem_univ _)
  have hbridge :
      abIter 6 α h f t₀ y₀_sext N
        = ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ N := by
    rw [hα_def, hy_sext_def]
    exact (ab6Iter_eq_abIter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ N).symm
  have habsErr :
      abErr 6 α h f t₀ y₀_sext y N
        = |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ N - y (t₀ + (N : ℝ) * h)| := by
    show |abIter 6 α h f t₀ y₀_sext N - y (t₀ + (N : ℝ) * h)|
        = |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ N - y (t₀ + (N : ℝ) * h)|
    rw [hbridge]
  show |ab6Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ N - y (t₀ + (N : ℝ) * h)|
      ≤ Real.exp ((114 / 5) * L * T) * ε₀
        + T * Real.exp ((114 / 5) * L * T) * C * h ^ 6
  linarith [hwindow_ge, hgeneric, habsErr.symm.le, habsErr.le]

end LMM
