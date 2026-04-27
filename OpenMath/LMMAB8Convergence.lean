import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMABGenericConvergence
import OpenMath.LMMAM7Convergence

/-! ## Adams–Bashforth 8-step Scalar Convergence Chain (Iserles §1.2)

Order-8 explicit 8-step LMM convergence scaffold. Mirrors the AB7 chain
in `OpenMath.LMMAB7Convergence` at the next order. This scalar half takes
eight starting samples and combines eight prior `f` evaluations. The
effective max-window Lipschitz constant is `(77432/945) · L`
(`= sum |β_k|`), the residual is `O(h^9)` and the headline global error
bound is `O(ε₀ + h^8)`.

Reuses the public ninth-order Taylor helpers
`iteratedDeriv_nine_bounded_on_Icc`,
`y_ninth_order_taylor_remainder`,
`derivY_eighth_order_taylor_remainder` from `LMMAM7Convergence`. -/

namespace LMM

/-- AB8 iteration with eight starting samples `y₀, y₁, …, y₇`:
`y_{n+8} = y_{n+7} + h · ((434241/120960) · f_{n+7} − (1152169/120960) · f_{n+6}
  + (2183877/120960) · f_{n+5} − (2664477/120960) · f_{n+4}
  + (2102243/120960) · f_{n+3} − (1041723/120960) · f_{n+2}
  + (295767/120960) · f_{n+1} − (36799/120960) · f_n)`. -/
noncomputable def ab8Iter
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : ℝ) : ℕ → ℝ
  | 0 => y₀
  | 1 => y₁
  | 2 => y₂
  | 3 => y₃
  | 4 => y₄
  | 5 => y₅
  | 6 => y₆
  | 7 => y₇
  | n + 8 =>
      ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 7)
        + h * (434241 / 120960 * f (t₀ + ((n : ℝ) + 7) * h)
                (ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 7))
              - 1152169 / 120960 * f (t₀ + ((n : ℝ) + 6) * h)
                (ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 6))
              + 2183877 / 120960 * f (t₀ + ((n : ℝ) + 5) * h)
                (ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 5))
              - 2664477 / 120960 * f (t₀ + ((n : ℝ) + 4) * h)
                (ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 4))
              + 2102243 / 120960 * f (t₀ + ((n : ℝ) + 3) * h)
                (ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 3))
              - 1041723 / 120960 * f (t₀ + ((n : ℝ) + 2) * h)
                (ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 2))
              + 295767 / 120960 * f (t₀ + ((n : ℝ) + 1) * h)
                (ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 1))
              - 36799 / 120960 * f (t₀ + (n : ℝ) * h)
                (ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ n))

@[simp] lemma ab8Iter_zero
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : ℝ) :
    ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 0 = y₀ := rfl

@[simp] lemma ab8Iter_one
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : ℝ) :
    ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 1 = y₁ := rfl

@[simp] lemma ab8Iter_two
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : ℝ) :
    ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 2 = y₂ := rfl

@[simp] lemma ab8Iter_three
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : ℝ) :
    ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 3 = y₃ := rfl

@[simp] lemma ab8Iter_four
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : ℝ) :
    ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 4 = y₄ := rfl

@[simp] lemma ab8Iter_five
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : ℝ) :
    ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 5 = y₅ := rfl

@[simp] lemma ab8Iter_six
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : ℝ) :
    ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 6 = y₆ := rfl

@[simp] lemma ab8Iter_seven
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : ℝ) :
    ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 7 = y₇ := rfl

lemma ab8Iter_succ_eight
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : ℝ) (n : ℕ) :
    ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 8)
      = ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 7)
          + h * (434241 / 120960 * f (t₀ + ((n : ℝ) + 7) * h)
                  (ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 7))
                - 1152169 / 120960 * f (t₀ + ((n : ℝ) + 6) * h)
                    (ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 6))
                + 2183877 / 120960 * f (t₀ + ((n : ℝ) + 5) * h)
                    (ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 5))
                - 2664477 / 120960 * f (t₀ + ((n : ℝ) + 4) * h)
                    (ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 4))
                + 2102243 / 120960 * f (t₀ + ((n : ℝ) + 3) * h)
                    (ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 3))
                - 1041723 / 120960 * f (t₀ + ((n : ℝ) + 2) * h)
                    (ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 2))
                + 295767 / 120960 * f (t₀ + ((n : ℝ) + 1) * h)
                    (ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 1))
                - 36799 / 120960 * f (t₀ + (n : ℝ) * h)
                    (ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ n)) := rfl

/-- AB8 local truncation operator reduces to the textbook 8-step residual. -/
theorem ab8_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    adamsBashforth8.localTruncationError h t y
      = y (t + 8 * h) - y (t + 7 * h)
          - h * (434241 / 120960 * deriv y (t + 7 * h)
                  - 1152169 / 120960 * deriv y (t + 6 * h)
                  + 2183877 / 120960 * deriv y (t + 5 * h)
                  - 2664477 / 120960 * deriv y (t + 4 * h)
                  + 2102243 / 120960 * deriv y (t + 3 * h)
                  - 1041723 / 120960 * deriv y (t + 2 * h)
                  + 295767 / 120960 * deriv y (t + h)
                  - 36799 / 120960 * deriv y t) := by
  unfold localTruncationError truncationOp
  simp [adamsBashforth8, Fin.sum_univ_succ, iteratedDeriv_one,
    iteratedDeriv_zero]
  norm_num
  ring

/-- One-step AB8 Lipschitz step: a single linearised increment of the
global error from steps `n, n+1, …, n+7` to `n+8`, with eight Lipschitz
contributions and additive `|τ_n|`. -/
theorem ab8_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : ℝ) (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)|
      ≤ |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)|
        + (434241 / 120960) * h * L
            * |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 7)
                - y (t₀ + ((n : ℝ) + 7) * h)|
        + (1152169 / 120960) * h * L
            * |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 6)
                - y (t₀ + ((n : ℝ) + 6) * h)|
        + (2183877 / 120960) * h * L
            * |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 5)
                - y (t₀ + ((n : ℝ) + 5) * h)|
        + (2664477 / 120960) * h * L
            * |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 4)
                - y (t₀ + ((n : ℝ) + 4) * h)|
        + (2102243 / 120960) * h * L
            * |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 3)
                - y (t₀ + ((n : ℝ) + 3) * h)|
        + (1041723 / 120960) * h * L
            * |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 2)
                - y (t₀ + ((n : ℝ) + 2) * h)|
        + (295767 / 120960) * h * L
            * |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 1)
                - y (t₀ + ((n : ℝ) + 1) * h)|
        + (36799 / 120960) * h * L
            * |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ n - y (t₀ + (n : ℝ) * h)|
        + |adamsBashforth8.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set yn : ℝ := ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ n with hyn_def
  set yn1 : ℝ := ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 1) with hyn1_def
  set yn2 : ℝ := ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 2) with hyn2_def
  set yn3 : ℝ := ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 3) with hyn3_def
  set yn4 : ℝ := ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 4) with hyn4_def
  set yn5 : ℝ := ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 5) with hyn5_def
  set yn6 : ℝ := ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 6) with hyn6_def
  set yn7 : ℝ := ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 7) with hyn7_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set tn3 : ℝ := t₀ + ((n : ℝ) + 3) * h with htn3_def
  set tn4 : ℝ := t₀ + ((n : ℝ) + 4) * h with htn4_def
  set tn5 : ℝ := t₀ + ((n : ℝ) + 5) * h with htn5_def
  set tn6 : ℝ := t₀ + ((n : ℝ) + 6) * h with htn6_def
  set tn7 : ℝ := t₀ + ((n : ℝ) + 7) * h with htn7_def
  set tn8 : ℝ := t₀ + ((n : ℝ) + 8) * h with htn8_def
  set zn : ℝ := y tn with hzn_def
  set zn1 : ℝ := y tn1 with hzn1_def
  set zn2 : ℝ := y tn2 with hzn2_def
  set zn3 : ℝ := y tn3 with hzn3_def
  set zn4 : ℝ := y tn4 with hzn4_def
  set zn5 : ℝ := y tn5 with hzn5_def
  set zn6 : ℝ := y tn6 with hzn6_def
  set zn7 : ℝ := y tn7 with hzn7_def
  set zn8 : ℝ := y tn8 with hzn8_def
  set τ : ℝ := adamsBashforth8.localTruncationError h tn y with hτ_def
  -- AB8 step formula.
  have hstep : ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 8)
      = yn7 + h * (434241 / 120960 * f tn7 yn7
                    - 1152169 / 120960 * f tn6 yn6
                    + 2183877 / 120960 * f tn5 yn5
                    - 2664477 / 120960 * f tn4 yn4
                    + 2102243 / 120960 * f tn3 yn3
                    - 1041723 / 120960 * f tn2 yn2
                    + 295767 / 120960 * f tn1 yn1
                    - 36799 / 120960 * f tn yn) := by
    show ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 8) = _
    rw [ab8Iter_succ_eight]
  -- Time arithmetic.
  have htn1_h : tn + h = tn1 := by simp [htn_def, htn1_def]; ring
  have htn_2h : tn + 2 * h = tn2 := by simp [htn_def, htn2_def]; ring
  have htn_3h : tn + 3 * h = tn3 := by simp [htn_def, htn3_def]; ring
  have htn_4h : tn + 4 * h = tn4 := by simp [htn_def, htn4_def]; ring
  have htn_5h : tn + 5 * h = tn5 := by simp [htn_def, htn5_def]; ring
  have htn_6h : tn + 6 * h = tn6 := by simp [htn_def, htn6_def]; ring
  have htn_7h : tn + 7 * h = tn7 := by simp [htn_def, htn7_def]; ring
  have htn_8h : tn + 8 * h = tn8 := by simp [htn_def, htn8_def]; ring
  -- LTE residual at `tn`, expressed via `f` along the trajectory.
  have hτ_eq : τ = zn8 - zn7
        - h * (434241 / 120960 * f tn7 zn7 - 1152169 / 120960 * f tn6 zn6
              + 2183877 / 120960 * f tn5 zn5 - 2664477 / 120960 * f tn4 zn4
              + 2102243 / 120960 * f tn3 zn3 - 1041723 / 120960 * f tn2 zn2
              + 295767 / 120960 * f tn1 zn1 - 36799 / 120960 * f tn zn) := by
    show adamsBashforth8.localTruncationError h tn y = _
    rw [ab8_localTruncationError_eq, htn1_h, htn_2h, htn_3h, htn_4h, htn_5h,
      htn_6h, htn_7h, htn_8h, hyf tn7, hyf tn6, hyf tn5, hyf tn4, hyf tn3,
      hyf tn2, hyf tn1, hyf tn]
  -- Algebraic decomposition of the global error increment.
  have halg : ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 8) - zn8
      = (yn7 - zn7)
        + (434241 / 120960) * h * (f tn7 yn7 - f tn7 zn7)
        - (1152169 / 120960) * h * (f tn6 yn6 - f tn6 zn6)
        + (2183877 / 120960) * h * (f tn5 yn5 - f tn5 zn5)
        - (2664477 / 120960) * h * (f tn4 yn4 - f tn4 zn4)
        + (2102243 / 120960) * h * (f tn3 yn3 - f tn3 zn3)
        - (1041723 / 120960) * h * (f tn2 yn2 - f tn2 zn2)
        + (295767 / 120960) * h * (f tn1 yn1 - f tn1 zn1)
        - (36799 / 120960) * h * (f tn yn - f tn zn)
        - τ := by
    rw [hstep, hτ_eq]; ring
  -- Lipschitz bounds.
  have hLip7 : |f tn7 yn7 - f tn7 zn7| ≤ L * |yn7 - zn7| := hf tn7 yn7 zn7
  have hLip6 : |f tn6 yn6 - f tn6 zn6| ≤ L * |yn6 - zn6| := hf tn6 yn6 zn6
  have hLip5 : |f tn5 yn5 - f tn5 zn5| ≤ L * |yn5 - zn5| := hf tn5 yn5 zn5
  have hLip4 : |f tn4 yn4 - f tn4 zn4| ≤ L * |yn4 - zn4| := hf tn4 yn4 zn4
  have hLip3 : |f tn3 yn3 - f tn3 zn3| ≤ L * |yn3 - zn3| := hf tn3 yn3 zn3
  have hLip2 : |f tn2 yn2 - f tn2 zn2| ≤ L * |yn2 - zn2| := hf tn2 yn2 zn2
  have hLip1 : |f tn1 yn1 - f tn1 zn1| ≤ L * |yn1 - zn1| := hf tn1 yn1 zn1
  have hLip0 : |f tn yn - f tn zn| ≤ L * |yn - zn| := hf tn yn zn
  have h434241_nn : 0 ≤ (434241 / 120960) * h := by linarith
  have h1152169_nn : 0 ≤ (1152169 / 120960) * h := by linarith
  have h2183877_nn : 0 ≤ (2183877 / 120960) * h := by linarith
  have h2664477_nn : 0 ≤ (2664477 / 120960) * h := by linarith
  have h2102243_nn : 0 ≤ (2102243 / 120960) * h := by linarith
  have h1041723_nn : 0 ≤ (1041723 / 120960) * h := by linarith
  have h295767_nn : 0 ≤ (295767 / 120960) * h := by linarith
  have h36799_nn : 0 ≤ (36799 / 120960) * h := by linarith
  have h434241_abs : |(434241 / 120960) * h * (f tn7 yn7 - f tn7 zn7)|
      ≤ (434241 / 120960) * h * L * |yn7 - zn7| := by
    rw [abs_mul, abs_of_nonneg h434241_nn]
    calc (434241 / 120960) * h * |f tn7 yn7 - f tn7 zn7|
        ≤ (434241 / 120960) * h * (L * |yn7 - zn7|) :=
          mul_le_mul_of_nonneg_left hLip7 h434241_nn
      _ = (434241 / 120960) * h * L * |yn7 - zn7| := by ring
  have h1152169_abs : |(1152169 / 120960) * h * (f tn6 yn6 - f tn6 zn6)|
      ≤ (1152169 / 120960) * h * L * |yn6 - zn6| := by
    rw [abs_mul, abs_of_nonneg h1152169_nn]
    calc (1152169 / 120960) * h * |f tn6 yn6 - f tn6 zn6|
        ≤ (1152169 / 120960) * h * (L * |yn6 - zn6|) :=
          mul_le_mul_of_nonneg_left hLip6 h1152169_nn
      _ = (1152169 / 120960) * h * L * |yn6 - zn6| := by ring
  have h2183877_abs : |(2183877 / 120960) * h * (f tn5 yn5 - f tn5 zn5)|
      ≤ (2183877 / 120960) * h * L * |yn5 - zn5| := by
    rw [abs_mul, abs_of_nonneg h2183877_nn]
    calc (2183877 / 120960) * h * |f tn5 yn5 - f tn5 zn5|
        ≤ (2183877 / 120960) * h * (L * |yn5 - zn5|) :=
          mul_le_mul_of_nonneg_left hLip5 h2183877_nn
      _ = (2183877 / 120960) * h * L * |yn5 - zn5| := by ring
  have h2664477_abs : |(2664477 / 120960) * h * (f tn4 yn4 - f tn4 zn4)|
      ≤ (2664477 / 120960) * h * L * |yn4 - zn4| := by
    rw [abs_mul, abs_of_nonneg h2664477_nn]
    calc (2664477 / 120960) * h * |f tn4 yn4 - f tn4 zn4|
        ≤ (2664477 / 120960) * h * (L * |yn4 - zn4|) :=
          mul_le_mul_of_nonneg_left hLip4 h2664477_nn
      _ = (2664477 / 120960) * h * L * |yn4 - zn4| := by ring
  have h2102243_abs : |(2102243 / 120960) * h * (f tn3 yn3 - f tn3 zn3)|
      ≤ (2102243 / 120960) * h * L * |yn3 - zn3| := by
    rw [abs_mul, abs_of_nonneg h2102243_nn]
    calc (2102243 / 120960) * h * |f tn3 yn3 - f tn3 zn3|
        ≤ (2102243 / 120960) * h * (L * |yn3 - zn3|) :=
          mul_le_mul_of_nonneg_left hLip3 h2102243_nn
      _ = (2102243 / 120960) * h * L * |yn3 - zn3| := by ring
  have h1041723_abs : |(1041723 / 120960) * h * (f tn2 yn2 - f tn2 zn2)|
      ≤ (1041723 / 120960) * h * L * |yn2 - zn2| := by
    rw [abs_mul, abs_of_nonneg h1041723_nn]
    calc (1041723 / 120960) * h * |f tn2 yn2 - f tn2 zn2|
        ≤ (1041723 / 120960) * h * (L * |yn2 - zn2|) :=
          mul_le_mul_of_nonneg_left hLip2 h1041723_nn
      _ = (1041723 / 120960) * h * L * |yn2 - zn2| := by ring
  have h295767_abs : |(295767 / 120960) * h * (f tn1 yn1 - f tn1 zn1)|
      ≤ (295767 / 120960) * h * L * |yn1 - zn1| := by
    rw [abs_mul, abs_of_nonneg h295767_nn]
    calc (295767 / 120960) * h * |f tn1 yn1 - f tn1 zn1|
        ≤ (295767 / 120960) * h * (L * |yn1 - zn1|) :=
          mul_le_mul_of_nonneg_left hLip1 h295767_nn
      _ = (295767 / 120960) * h * L * |yn1 - zn1| := by ring
  have h36799_abs : |(36799 / 120960) * h * (f tn yn - f tn zn)|
      ≤ (36799 / 120960) * h * L * |yn - zn| := by
    rw [abs_mul, abs_of_nonneg h36799_nn]
    calc (36799 / 120960) * h * |f tn yn - f tn zn|
        ≤ (36799 / 120960) * h * (L * |yn - zn|) :=
          mul_le_mul_of_nonneg_left hLip0 h36799_nn
      _ = (36799 / 120960) * h * L * |yn - zn| := by ring
  -- Triangle inequality (chained nine times).
  set S := (yn7 - zn7)
        + (434241 / 120960) * h * (f tn7 yn7 - f tn7 zn7)
        - (1152169 / 120960) * h * (f tn6 yn6 - f tn6 zn6)
        + (2183877 / 120960) * h * (f tn5 yn5 - f tn5 zn5)
        - (2664477 / 120960) * h * (f tn4 yn4 - f tn4 zn4)
        + (2102243 / 120960) * h * (f tn3 yn3 - f tn3 zn3)
        - (1041723 / 120960) * h * (f tn2 yn2 - f tn2 zn2)
        + (295767 / 120960) * h * (f tn1 yn1 - f tn1 zn1)
        - (36799 / 120960) * h * (f tn yn - f tn zn) with hS_def
  have hcalc : ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 8) - zn8 = S - τ := halg
  have htri_S : |S| ≤ |yn7 - zn7|
              + |(434241 / 120960) * h * (f tn7 yn7 - f tn7 zn7)|
              + |(1152169 / 120960) * h * (f tn6 yn6 - f tn6 zn6)|
              + |(2183877 / 120960) * h * (f tn5 yn5 - f tn5 zn5)|
              + |(2664477 / 120960) * h * (f tn4 yn4 - f tn4 zn4)|
              + |(2102243 / 120960) * h * (f tn3 yn3 - f tn3 zn3)|
              + |(1041723 / 120960) * h * (f tn2 yn2 - f tn2 zn2)|
              + |(295767 / 120960) * h * (f tn1 yn1 - f tn1 zn1)|
              + |(36799 / 120960) * h * (f tn yn - f tn zn)| := by
    have h1 : |(yn7 - zn7)
              + (434241 / 120960) * h * (f tn7 yn7 - f tn7 zn7)|
        ≤ |yn7 - zn7| + |(434241 / 120960) * h * (f tn7 yn7 - f tn7 zn7)| :=
      abs_add_le _ _
    have h2 : |(yn7 - zn7)
              + (434241 / 120960) * h * (f tn7 yn7 - f tn7 zn7)
              - (1152169 / 120960) * h * (f tn6 yn6 - f tn6 zn6)|
        ≤ |(yn7 - zn7)
              + (434241 / 120960) * h * (f tn7 yn7 - f tn7 zn7)|
          + |(1152169 / 120960) * h * (f tn6 yn6 - f tn6 zn6)| := abs_sub _ _
    have h3 : |(yn7 - zn7)
              + (434241 / 120960) * h * (f tn7 yn7 - f tn7 zn7)
              - (1152169 / 120960) * h * (f tn6 yn6 - f tn6 zn6)
              + (2183877 / 120960) * h * (f tn5 yn5 - f tn5 zn5)|
        ≤ |(yn7 - zn7)
              + (434241 / 120960) * h * (f tn7 yn7 - f tn7 zn7)
              - (1152169 / 120960) * h * (f tn6 yn6 - f tn6 zn6)|
          + |(2183877 / 120960) * h * (f tn5 yn5 - f tn5 zn5)| := abs_add_le _ _
    have h4 : |(yn7 - zn7)
              + (434241 / 120960) * h * (f tn7 yn7 - f tn7 zn7)
              - (1152169 / 120960) * h * (f tn6 yn6 - f tn6 zn6)
              + (2183877 / 120960) * h * (f tn5 yn5 - f tn5 zn5)
              - (2664477 / 120960) * h * (f tn4 yn4 - f tn4 zn4)|
        ≤ |(yn7 - zn7)
              + (434241 / 120960) * h * (f tn7 yn7 - f tn7 zn7)
              - (1152169 / 120960) * h * (f tn6 yn6 - f tn6 zn6)
              + (2183877 / 120960) * h * (f tn5 yn5 - f tn5 zn5)|
          + |(2664477 / 120960) * h * (f tn4 yn4 - f tn4 zn4)| := abs_sub _ _
    have h5 : |(yn7 - zn7)
              + (434241 / 120960) * h * (f tn7 yn7 - f tn7 zn7)
              - (1152169 / 120960) * h * (f tn6 yn6 - f tn6 zn6)
              + (2183877 / 120960) * h * (f tn5 yn5 - f tn5 zn5)
              - (2664477 / 120960) * h * (f tn4 yn4 - f tn4 zn4)
              + (2102243 / 120960) * h * (f tn3 yn3 - f tn3 zn3)|
        ≤ |(yn7 - zn7)
              + (434241 / 120960) * h * (f tn7 yn7 - f tn7 zn7)
              - (1152169 / 120960) * h * (f tn6 yn6 - f tn6 zn6)
              + (2183877 / 120960) * h * (f tn5 yn5 - f tn5 zn5)
              - (2664477 / 120960) * h * (f tn4 yn4 - f tn4 zn4)|
          + |(2102243 / 120960) * h * (f tn3 yn3 - f tn3 zn3)| := abs_add_le _ _
    have h6 : |(yn7 - zn7)
              + (434241 / 120960) * h * (f tn7 yn7 - f tn7 zn7)
              - (1152169 / 120960) * h * (f tn6 yn6 - f tn6 zn6)
              + (2183877 / 120960) * h * (f tn5 yn5 - f tn5 zn5)
              - (2664477 / 120960) * h * (f tn4 yn4 - f tn4 zn4)
              + (2102243 / 120960) * h * (f tn3 yn3 - f tn3 zn3)
              - (1041723 / 120960) * h * (f tn2 yn2 - f tn2 zn2)|
        ≤ |(yn7 - zn7)
              + (434241 / 120960) * h * (f tn7 yn7 - f tn7 zn7)
              - (1152169 / 120960) * h * (f tn6 yn6 - f tn6 zn6)
              + (2183877 / 120960) * h * (f tn5 yn5 - f tn5 zn5)
              - (2664477 / 120960) * h * (f tn4 yn4 - f tn4 zn4)
              + (2102243 / 120960) * h * (f tn3 yn3 - f tn3 zn3)|
          + |(1041723 / 120960) * h * (f tn2 yn2 - f tn2 zn2)| := abs_sub _ _
    have h7 : |(yn7 - zn7)
              + (434241 / 120960) * h * (f tn7 yn7 - f tn7 zn7)
              - (1152169 / 120960) * h * (f tn6 yn6 - f tn6 zn6)
              + (2183877 / 120960) * h * (f tn5 yn5 - f tn5 zn5)
              - (2664477 / 120960) * h * (f tn4 yn4 - f tn4 zn4)
              + (2102243 / 120960) * h * (f tn3 yn3 - f tn3 zn3)
              - (1041723 / 120960) * h * (f tn2 yn2 - f tn2 zn2)
              + (295767 / 120960) * h * (f tn1 yn1 - f tn1 zn1)|
        ≤ |(yn7 - zn7)
              + (434241 / 120960) * h * (f tn7 yn7 - f tn7 zn7)
              - (1152169 / 120960) * h * (f tn6 yn6 - f tn6 zn6)
              + (2183877 / 120960) * h * (f tn5 yn5 - f tn5 zn5)
              - (2664477 / 120960) * h * (f tn4 yn4 - f tn4 zn4)
              + (2102243 / 120960) * h * (f tn3 yn3 - f tn3 zn3)
              - (1041723 / 120960) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(295767 / 120960) * h * (f tn1 yn1 - f tn1 zn1)| := abs_add_le _ _
    have h8 : |S| ≤ |(yn7 - zn7)
              + (434241 / 120960) * h * (f tn7 yn7 - f tn7 zn7)
              - (1152169 / 120960) * h * (f tn6 yn6 - f tn6 zn6)
              + (2183877 / 120960) * h * (f tn5 yn5 - f tn5 zn5)
              - (2664477 / 120960) * h * (f tn4 yn4 - f tn4 zn4)
              + (2102243 / 120960) * h * (f tn3 yn3 - f tn3 zn3)
              - (1041723 / 120960) * h * (f tn2 yn2 - f tn2 zn2)
              + (295767 / 120960) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(36799 / 120960) * h * (f tn yn - f tn zn)| := by
      show |_| ≤ _
      exact abs_sub _ _
    linarith
  have htri : |S - τ| ≤ |S| + |τ| := abs_sub _ _
  calc |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 8) - zn8|
      = |S - τ| := by rw [hcalc]
    _ ≤ |S| + |τ| := htri
    _ ≤ |yn7 - zn7|
          + |(434241 / 120960) * h * (f tn7 yn7 - f tn7 zn7)|
          + |(1152169 / 120960) * h * (f tn6 yn6 - f tn6 zn6)|
          + |(2183877 / 120960) * h * (f tn5 yn5 - f tn5 zn5)|
          + |(2664477 / 120960) * h * (f tn4 yn4 - f tn4 zn4)|
          + |(2102243 / 120960) * h * (f tn3 yn3 - f tn3 zn3)|
          + |(1041723 / 120960) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(295767 / 120960) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(36799 / 120960) * h * (f tn yn - f tn zn)|
          + |τ| := by linarith
    _ ≤ |yn7 - zn7|
          + (434241 / 120960) * h * L * |yn7 - zn7|
          + (1152169 / 120960) * h * L * |yn6 - zn6|
          + (2183877 / 120960) * h * L * |yn5 - zn5|
          + (2664477 / 120960) * h * L * |yn4 - zn4|
          + (2102243 / 120960) * h * L * |yn3 - zn3|
          + (1041723 / 120960) * h * L * |yn2 - zn2|
          + (295767 / 120960) * h * L * |yn1 - zn1|
          + (36799 / 120960) * h * L * |yn - zn|
          + |τ| := by
        linarith [h434241_abs, h1152169_abs, h2183877_abs, h2664477_abs,
          h2102243_abs, h1041723_abs, h295767_abs, h36799_abs]

/-- Max-norm one-step error recurrence for AB8 with Lipschitz constant
`L`. With `eN k := |y_k − y(t_k)|` and an 8-window max
`EN k := max (eN k, eN (k+1), …, eN (k+7))`,
`EN (n+1) ≤ (1 + h · (77432/945) · L) · EN n + |τ_n|`. The `(77432/945)`
factor is the ℓ¹-norm of the AB8 coefficient vector. -/
theorem ab8_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : ℝ) (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max (max (max (max (max (max
          |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
          |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|)
          |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|)
          |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|)
          |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|)
          |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|)
          |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)|)
        |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)|
      ≤ (1 + h * ((77432 / 945) * L))
            * max (max (max (max (max (max (max
                  |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ n
                      - y (t₀ + (n : ℝ) * h)|
                  |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 1)
                      - y (t₀ + ((n : ℝ) + 1) * h)|)
                  |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 2)
                      - y (t₀ + ((n : ℝ) + 2) * h)|)
                  |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 3)
                      - y (t₀ + ((n : ℝ) + 3) * h)|)
                  |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 4)
                      - y (t₀ + ((n : ℝ) + 4) * h)|)
                  |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 5)
                      - y (t₀ + ((n : ℝ) + 5) * h)|)
                  |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 6)
                      - y (t₀ + ((n : ℝ) + 6) * h)|)
                  |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 7)
                      - y (t₀ + ((n : ℝ) + 7) * h)|
        + |adamsBashforth8.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set en : ℝ := |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ n - y (t₀ + (n : ℝ) * h)|
    with hen_def
  set en1 : ℝ :=
    |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
    with hen1_def
  set en2 : ℝ :=
    |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|
    with hen2_def
  set en3 : ℝ :=
    |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|
    with hen3_def
  set en4 : ℝ :=
    |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|
    with hen4_def
  set en5 : ℝ :=
    |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|
    with hen5_def
  set en6 : ℝ :=
    |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|
    with hen6_def
  set en7 : ℝ :=
    |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)|
    with hen7_def
  set en8 : ℝ :=
    |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)|
    with hen8_def
  set τabs : ℝ :=
    |adamsBashforth8.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  have hen_nn : 0 ≤ en := abs_nonneg _
  have hen1_nn : 0 ≤ en1 := abs_nonneg _
  have hen2_nn : 0 ≤ en2 := abs_nonneg _
  have hen3_nn : 0 ≤ en3 := abs_nonneg _
  have hen4_nn : 0 ≤ en4 := abs_nonneg _
  have hen5_nn : 0 ≤ en5 := abs_nonneg _
  have hen6_nn : 0 ≤ en6 := abs_nonneg _
  have hen7_nn : 0 ≤ en7 := abs_nonneg _
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  -- One-step Lipschitz bound (from `ab8_one_step_lipschitz`).
  have hstep :
      en8 ≤ en7 + (434241 / 120960) * h * L * en7
                + (1152169 / 120960) * h * L * en6
                + (2183877 / 120960) * h * L * en5
                + (2664477 / 120960) * h * L * en4
                + (2102243 / 120960) * h * L * en3
                + (1041723 / 120960) * h * L * en2
                + (295767 / 120960) * h * L * en1
                + (36799 / 120960) * h * L * en + τabs := by
    have := ab8_one_step_lipschitz hh hf t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y hyf n
    show |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)|
        ≤ |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)|
          + (434241 / 120960) * h * L
              * |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 7)
                  - y (t₀ + ((n : ℝ) + 7) * h)|
          + (1152169 / 120960) * h * L
              * |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 6)
                  - y (t₀ + ((n : ℝ) + 6) * h)|
          + (2183877 / 120960) * h * L
              * |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 5)
                  - y (t₀ + ((n : ℝ) + 5) * h)|
          + (2664477 / 120960) * h * L
              * |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 4)
                  - y (t₀ + ((n : ℝ) + 4) * h)|
          + (2102243 / 120960) * h * L
              * |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 3)
                  - y (t₀ + ((n : ℝ) + 3) * h)|
          + (1041723 / 120960) * h * L
              * |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 2)
                  - y (t₀ + ((n : ℝ) + 2) * h)|
          + (295767 / 120960) * h * L
              * |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ (n + 1)
                  - y (t₀ + ((n : ℝ) + 1) * h)|
          + (36799 / 120960) * h * L
              * |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ n - y (t₀ + (n : ℝ) * h)|
          + |adamsBashforth8.localTruncationError h (t₀ + (n : ℝ) * h) y|
    exact this
  set EN_n : ℝ :=
    max (max (max (max (max (max (max en en1) en2) en3) en4) en5) en6) en7
    with hEN_n_def
  have hen_le_EN : en ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left _ _)
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _)
  have hen1_le_EN : en1 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_max_right _ _)
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _)
  have hen2_le_EN : en2 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_max_right _ _)
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)
  have hen3_le_EN : en3 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _)
  have hen4_le_EN : en4 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)
  have hen5_le_EN : en5 ≤ EN_n :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hen6_le_EN : en6 ≤ EN_n :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hen7_le_EN : en7 ≤ EN_n := le_max_right _ _
  have h434241_nn : 0 ≤ (434241 / 120960) * h * L := by positivity
  have h1152169_nn : 0 ≤ (1152169 / 120960) * h * L := by positivity
  have h2183877_nn : 0 ≤ (2183877 / 120960) * h * L := by positivity
  have h2664477_nn : 0 ≤ (2664477 / 120960) * h * L := by positivity
  have h2102243_nn : 0 ≤ (2102243 / 120960) * h * L := by positivity
  have h1041723_nn : 0 ≤ (1041723 / 120960) * h * L := by positivity
  have h295767_nn : 0 ≤ (295767 / 120960) * h * L := by positivity
  have h36799_nn : 0 ≤ (36799 / 120960) * h * L := by positivity
  have hEN_nn : 0 ≤ EN_n := le_trans hen_nn hen_le_EN
  have hcoef_nn : 0 ≤ h * ((77432 / 945) * L) := by positivity
  have hen8_bd : en8 ≤ (1 + h * ((77432 / 945) * L)) * EN_n + τabs := by
    have h1 : (434241 / 120960) * h * L * en7 ≤ (434241 / 120960) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen7_le_EN h434241_nn
    have h2 : (1152169 / 120960) * h * L * en6 ≤ (1152169 / 120960) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen6_le_EN h1152169_nn
    have h3 : (2183877 / 120960) * h * L * en5 ≤ (2183877 / 120960) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen5_le_EN h2183877_nn
    have h4 : (2664477 / 120960) * h * L * en4 ≤ (2664477 / 120960) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen4_le_EN h2664477_nn
    have h5 : (2102243 / 120960) * h * L * en3 ≤ (2102243 / 120960) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen3_le_EN h2102243_nn
    have h6 : (1041723 / 120960) * h * L * en2 ≤ (1041723 / 120960) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen2_le_EN h1041723_nn
    have h7 : (295767 / 120960) * h * L * en1 ≤ (295767 / 120960) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen1_le_EN h295767_nn
    have h8 : (36799 / 120960) * h * L * en ≤ (36799 / 120960) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen_le_EN h36799_nn
    have h_alg :
        EN_n + (434241 / 120960) * h * L * EN_n
              + (1152169 / 120960) * h * L * EN_n
              + (2183877 / 120960) * h * L * EN_n
              + (2664477 / 120960) * h * L * EN_n
              + (2102243 / 120960) * h * L * EN_n
              + (1041723 / 120960) * h * L * EN_n
              + (295767 / 120960) * h * L * EN_n
              + (36799 / 120960) * h * L * EN_n + τabs
          = (1 + h * ((77432 / 945) * L)) * EN_n + τabs := by ring
    linarith [hstep, hen7_le_EN, h1, h2, h3, h4, h5, h6, h7, h8, h_alg.le]
  have hEN_le_grow : EN_n ≤ (1 + h * ((77432 / 945) * L)) * EN_n := by
    have hone : (1 : ℝ) * EN_n ≤ (1 + h * ((77432 / 945) * L)) * EN_n :=
      mul_le_mul_of_nonneg_right (by linarith) hEN_nn
    linarith
  have hen1_bd : en1 ≤ (1 + h * ((77432 / 945) * L)) * EN_n + τabs := by
    linarith [hen1_le_EN, hEN_le_grow]
  have hen2_bd : en2 ≤ (1 + h * ((77432 / 945) * L)) * EN_n + τabs := by
    linarith [hen2_le_EN, hEN_le_grow]
  have hen3_bd : en3 ≤ (1 + h * ((77432 / 945) * L)) * EN_n + τabs := by
    linarith [hen3_le_EN, hEN_le_grow]
  have hen4_bd : en4 ≤ (1 + h * ((77432 / 945) * L)) * EN_n + τabs := by
    linarith [hen4_le_EN, hEN_le_grow]
  have hen5_bd : en5 ≤ (1 + h * ((77432 / 945) * L)) * EN_n + τabs := by
    linarith [hen5_le_EN, hEN_le_grow]
  have hen6_bd : en6 ≤ (1 + h * ((77432 / 945) * L)) * EN_n + τabs := by
    linarith [hen6_le_EN, hEN_le_grow]
  have hen7_bd : en7 ≤ (1 + h * ((77432 / 945) * L)) * EN_n + τabs := by
    linarith [hen7_le_EN, hEN_le_grow]
  exact max_le (max_le (max_le (max_le (max_le (max_le (max_le hen1_bd hen2_bd)
    hen3_bd) hen4_bd) hen5_bd) hen6_bd) hen7_bd) hen8_bd

/-- Pure algebraic identity: the AB8 residual rewrites as a signed sum of
nine Taylor remainders (two `y` 9th-order remainders and seven `y'`
8th-order remainders). Extracted as a stand-alone lemma so the kernel
checks the (large) `ring` proof term in isolation. -/
private lemma ab8_residual_alg_identity
    (y0 y7 y8 d0 d1 d2 d3 d4 d5 d6 d7 dd ddd dddd ddddd dddddd ddddddd
      dddddddd h : ℝ) :
    y8 - y7 - h * ((434241 / 120960) * d7 - (1152169 / 120960) * d6
                  + (2183877 / 120960) * d5 - (2664477 / 120960) * d4
                  + (2102243 / 120960) * d3 - (1041723 / 120960) * d2
                  + (295767 / 120960) * d1 - (36799 / 120960) * d0)
      = (y8 - y0 - (8 * h) * d0
            - (8 * h) ^ 2 / 2 * dd
            - (8 * h) ^ 3 / 6 * ddd
            - (8 * h) ^ 4 / 24 * dddd
            - (8 * h) ^ 5 / 120 * ddddd
            - (8 * h) ^ 6 / 720 * dddddd
            - (8 * h) ^ 7 / 5040 * ddddddd
            - (8 * h) ^ 8 / 40320 * dddddddd)
        - (y7 - y0 - (7 * h) * d0
            - (7 * h) ^ 2 / 2 * dd
            - (7 * h) ^ 3 / 6 * ddd
            - (7 * h) ^ 4 / 24 * dddd
            - (7 * h) ^ 5 / 120 * ddddd
            - (7 * h) ^ 6 / 720 * dddddd
            - (7 * h) ^ 7 / 5040 * ddddddd
            - (7 * h) ^ 8 / 40320 * dddddddd)
        - (434241 * h / 120960)
            * (d7 - d0 - (7 * h) * dd
                - (7 * h) ^ 2 / 2 * ddd
                - (7 * h) ^ 3 / 6 * dddd
                - (7 * h) ^ 4 / 24 * ddddd
                - (7 * h) ^ 5 / 120 * dddddd
                - (7 * h) ^ 6 / 720 * ddddddd
                - (7 * h) ^ 7 / 5040 * dddddddd)
        + (1152169 * h / 120960)
            * (d6 - d0 - (6 * h) * dd
                - (6 * h) ^ 2 / 2 * ddd
                - (6 * h) ^ 3 / 6 * dddd
                - (6 * h) ^ 4 / 24 * ddddd
                - (6 * h) ^ 5 / 120 * dddddd
                - (6 * h) ^ 6 / 720 * ddddddd
                - (6 * h) ^ 7 / 5040 * dddddddd)
        - (2183877 * h / 120960)
            * (d5 - d0 - (5 * h) * dd
                - (5 * h) ^ 2 / 2 * ddd
                - (5 * h) ^ 3 / 6 * dddd
                - (5 * h) ^ 4 / 24 * ddddd
                - (5 * h) ^ 5 / 120 * dddddd
                - (5 * h) ^ 6 / 720 * ddddddd
                - (5 * h) ^ 7 / 5040 * dddddddd)
        + (2664477 * h / 120960)
            * (d4 - d0 - (4 * h) * dd
                - (4 * h) ^ 2 / 2 * ddd
                - (4 * h) ^ 3 / 6 * dddd
                - (4 * h) ^ 4 / 24 * ddddd
                - (4 * h) ^ 5 / 120 * dddddd
                - (4 * h) ^ 6 / 720 * ddddddd
                - (4 * h) ^ 7 / 5040 * dddddddd)
        - (2102243 * h / 120960)
            * (d3 - d0 - (3 * h) * dd
                - (3 * h) ^ 2 / 2 * ddd
                - (3 * h) ^ 3 / 6 * dddd
                - (3 * h) ^ 4 / 24 * ddddd
                - (3 * h) ^ 5 / 120 * dddddd
                - (3 * h) ^ 6 / 720 * ddddddd
                - (3 * h) ^ 7 / 5040 * dddddddd)
        + (1041723 * h / 120960)
            * (d2 - d0 - (2 * h) * dd
                - (2 * h) ^ 2 / 2 * ddd
                - (2 * h) ^ 3 / 6 * dddd
                - (2 * h) ^ 4 / 24 * ddddd
                - (2 * h) ^ 5 / 120 * dddddd
                - (2 * h) ^ 6 / 720 * ddddddd
                - (2 * h) ^ 7 / 5040 * dddddddd)
        - (295767 * h / 120960)
            * (d1 - d0 - h * dd
                - h ^ 2 / 2 * ddd
                - h ^ 3 / 6 * dddd
                - h ^ 4 / 24 * ddddd
                - h ^ 5 / 120 * dddddd
                - h ^ 6 / 720 * ddddddd
                - h ^ 7 / 5040 * dddddddd) := by
  ring

/-- Pure algebraic identity: the sum of the nine scaled Lagrange
remainder bounds equals a fixed rational coefficient times `M · h^9`. -/
private lemma ab8_residual_bound_alg_identity (M h : ℝ) :
    M / 362880 * (8 * h) ^ 9 + M / 362880 * (7 * h) ^ 9
      + (434241 * h / 120960) * (M / 40320 * (7 * h) ^ 8)
      + (1152169 * h / 120960) * (M / 40320 * (6 * h) ^ 8)
      + (2183877 * h / 120960) * (M / 40320 * (5 * h) ^ 8)
      + (2664477 * h / 120960) * (M / 40320 * (4 * h) ^ 8)
      + (2102243 * h / 120960) * (M / 40320 * (3 * h) ^ 8)
      + (1041723 * h / 120960) * (M / 40320 * (2 * h) ^ 8)
      + (295767 * h / 120960) * (M / 40320 * h ^ 8)
      = (388219697 / 241920 : ℝ) * M * h ^ 9 := by
  ring

/-- Triangle inequality for the nine-term AB8 residual chunk. -/
private lemma ab8_residual_nine_term_triangle
    (A B C D E F G H I h : ℝ) (hh : 0 ≤ h) :
    |A - B - (434241 * h / 120960) * C + (1152169 * h / 120960) * D
        - (2183877 * h / 120960) * E + (2664477 * h / 120960) * F
        - (2102243 * h / 120960) * G + (1041723 * h / 120960) * H
        - (295767 * h / 120960) * I|
      ≤ |A| + |B| + (434241 * h / 120960) * |C| + (1152169 * h / 120960) * |D|
          + (2183877 * h / 120960) * |E| + (2664477 * h / 120960) * |F|
          + (2102243 * h / 120960) * |G| + (1041723 * h / 120960) * |H|
          + (295767 * h / 120960) * |I| := by
  have h434241h_nn : 0 ≤ 434241 * h / 120960 := by linarith
  have h1152169h_nn : 0 ≤ 1152169 * h / 120960 := by linarith
  have h2183877h_nn : 0 ≤ 2183877 * h / 120960 := by linarith
  have h2664477h_nn : 0 ≤ 2664477 * h / 120960 := by linarith
  have h2102243h_nn : 0 ≤ 2102243 * h / 120960 := by linarith
  have h1041723h_nn : 0 ≤ 1041723 * h / 120960 := by linarith
  have h295767h_nn : 0 ≤ 295767 * h / 120960 := by linarith
  have habs434241 : |(434241 * h / 120960) * C| = (434241 * h / 120960) * |C| := by
    rw [abs_mul, abs_of_nonneg h434241h_nn]
  have habs1152169 : |(1152169 * h / 120960) * D| = (1152169 * h / 120960) * |D| := by
    rw [abs_mul, abs_of_nonneg h1152169h_nn]
  have habs2183877 : |(2183877 * h / 120960) * E| = (2183877 * h / 120960) * |E| := by
    rw [abs_mul, abs_of_nonneg h2183877h_nn]
  have habs2664477 : |(2664477 * h / 120960) * F| = (2664477 * h / 120960) * |F| := by
    rw [abs_mul, abs_of_nonneg h2664477h_nn]
  have habs2102243 : |(2102243 * h / 120960) * G| = (2102243 * h / 120960) * |G| := by
    rw [abs_mul, abs_of_nonneg h2102243h_nn]
  have habs1041723 : |(1041723 * h / 120960) * H| = (1041723 * h / 120960) * |H| := by
    rw [abs_mul, abs_of_nonneg h1041723h_nn]
  have habs295767 : |(295767 * h / 120960) * I| = (295767 * h / 120960) * |I| := by
    rw [abs_mul, abs_of_nonneg h295767h_nn]
  have h1 : |A - B - (434241 * h / 120960) * C + (1152169 * h / 120960) * D
                - (2183877 * h / 120960) * E + (2664477 * h / 120960) * F
                - (2102243 * h / 120960) * G + (1041723 * h / 120960) * H
                - (295767 * h / 120960) * I|
      ≤ |A - B - (434241 * h / 120960) * C + (1152169 * h / 120960) * D
            - (2183877 * h / 120960) * E + (2664477 * h / 120960) * F
            - (2102243 * h / 120960) * G + (1041723 * h / 120960) * H|
        + |(295767 * h / 120960) * I| := abs_sub _ _
  have h2 : |A - B - (434241 * h / 120960) * C + (1152169 * h / 120960) * D
                - (2183877 * h / 120960) * E + (2664477 * h / 120960) * F
                - (2102243 * h / 120960) * G + (1041723 * h / 120960) * H|
      ≤ |A - B - (434241 * h / 120960) * C + (1152169 * h / 120960) * D
            - (2183877 * h / 120960) * E + (2664477 * h / 120960) * F
            - (2102243 * h / 120960) * G|
        + |(1041723 * h / 120960) * H| := abs_add_le _ _
  have h3 : |A - B - (434241 * h / 120960) * C + (1152169 * h / 120960) * D
                - (2183877 * h / 120960) * E + (2664477 * h / 120960) * F
                - (2102243 * h / 120960) * G|
      ≤ |A - B - (434241 * h / 120960) * C + (1152169 * h / 120960) * D
            - (2183877 * h / 120960) * E + (2664477 * h / 120960) * F|
        + |(2102243 * h / 120960) * G| := abs_sub _ _
  have h4 : |A - B - (434241 * h / 120960) * C + (1152169 * h / 120960) * D
                - (2183877 * h / 120960) * E + (2664477 * h / 120960) * F|
      ≤ |A - B - (434241 * h / 120960) * C + (1152169 * h / 120960) * D
            - (2183877 * h / 120960) * E|
        + |(2664477 * h / 120960) * F| := abs_add_le _ _
  have h5 : |A - B - (434241 * h / 120960) * C + (1152169 * h / 120960) * D
                - (2183877 * h / 120960) * E|
      ≤ |A - B - (434241 * h / 120960) * C + (1152169 * h / 120960) * D|
        + |(2183877 * h / 120960) * E| := abs_sub _ _
  have h6 : |A - B - (434241 * h / 120960) * C + (1152169 * h / 120960) * D|
      ≤ |A - B - (434241 * h / 120960) * C| + |(1152169 * h / 120960) * D| :=
    abs_add_le _ _
  have h7 : |A - B - (434241 * h / 120960) * C|
      ≤ |A - B| + |(434241 * h / 120960) * C| := abs_sub _ _
  have h8 : |A - B| ≤ |A| + |B| := abs_sub _ _
  linarith [habs434241.le, habs434241.ge, habs1152169.le, habs1152169.ge,
    habs2183877.le, habs2183877.ge, habs2664477.le, habs2664477.ge,
    habs2102243.le, habs2102243.ge, habs1041723.le, habs1041723.ge,
    habs295767.le, habs295767.ge]

/-- AB8 residual at a single base point `t` is `O(M · h^9)`, where `M`
bounds the 9th derivative of the exact solution on a window covering
`[t, t + 8h]`. Decomposes the residual into eight Taylor remainders
(two y 9th-order, seven y' 8th-order). -/
private theorem ab8_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 9 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 9 y t| ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (ht4h : t + 4 * h ∈ Set.Icc a b)
    (ht5h : t + 5 * h ∈ Set.Icc a b)
    (ht6h : t + 6 * h ∈ Set.Icc a b)
    (ht7h : t + 7 * h ∈ Set.Icc a b)
    (ht8h : t + 8 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    |y (t + 8 * h) - y (t + 7 * h)
        - h * ((434241 / 120960) * deriv y (t + 7 * h)
              - (1152169 / 120960) * deriv y (t + 6 * h)
              + (2183877 / 120960) * deriv y (t + 5 * h)
              - (2664477 / 120960) * deriv y (t + 4 * h)
              + (2102243 / 120960) * deriv y (t + 3 * h)
              - (1041723 / 120960) * deriv y (t + 2 * h)
              + (295767 / 120960) * deriv y (t + h)
              - (36799 / 120960) * deriv y t)|
      ≤ (1605 : ℝ) * M * h ^ 9 := by
  -- Nine Taylor remainders.
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have h5h : 0 ≤ 5 * h := by linarith
  have h6h : 0 ≤ 6 * h := by linarith
  have h7h : 0 ≤ 7 * h := by linarith
  have h8h : 0 ≤ 8 * h := by linarith
  -- R_y(7), R_y(8): y Taylor remainders at order 9.
  have hRy7 :=
    y_ninth_order_taylor_remainder hy hbnd ht ht7h h7h
  have hRy8 :=
    y_ninth_order_taylor_remainder hy hbnd ht ht8h h8h
  -- R_y'(1), …, R_y'(7): y' Taylor remainders at order 8.
  have hRyp1 :=
    derivY_eighth_order_taylor_remainder hy hbnd ht hth hh
  have hRyp2 :=
    derivY_eighth_order_taylor_remainder hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_eighth_order_taylor_remainder hy hbnd ht ht3h h3h
  have hRyp4 :=
    derivY_eighth_order_taylor_remainder hy hbnd ht ht4h h4h
  have hRyp5 :=
    derivY_eighth_order_taylor_remainder hy hbnd ht ht5h h5h
  have hRyp6 :=
    derivY_eighth_order_taylor_remainder hy hbnd ht ht6h h6h
  have hRyp7 :=
    derivY_eighth_order_taylor_remainder hy hbnd ht ht7h h7h
  -- Abbreviations.
  set y0 := y t with hy0_def
  set y7 := y (t + 7 * h) with hy7_def
  set y8 := y (t + 8 * h) with hy8_def
  set d0 := deriv y t with hd0_def
  set d1 := deriv y (t + h) with hd1_def
  set d2 := deriv y (t + 2 * h) with hd2_def
  set d3 := deriv y (t + 3 * h) with hd3_def
  set d4 := deriv y (t + 4 * h) with hd4_def
  set d5 := deriv y (t + 5 * h) with hd5_def
  set d6 := deriv y (t + 6 * h) with hd6_def
  set d7 := deriv y (t + 7 * h) with hd7_def
  set dd := iteratedDeriv 2 y t with hdd_def
  set ddd := iteratedDeriv 3 y t with hddd_def
  set dddd := iteratedDeriv 4 y t with hdddd_def
  set ddddd := iteratedDeriv 5 y t with hddddd_def
  set dddddd := iteratedDeriv 6 y t with hdddddd_def
  set ddddddd := iteratedDeriv 7 y t with hddddddd_def
  set dddddddd := iteratedDeriv 8 y t with hdddddddd_def
  clear_value y0 y7 y8 d0 d1 d2 d3 d4 d5 d6 d7
    dd ddd dddd ddddd dddddd ddddddd dddddddd
  -- Algebraic identity for the residual.
  have hLTE_eq :=
    ab8_residual_alg_identity y0 y7 y8 d0 d1 d2 d3 d4 d5 d6 d7
      dd ddd dddd ddddd dddddd ddddddd dddddddd h
  rw [hLTE_eq]
  -- Triangle inequality (chained).
  set A := y8 - y0 - (8 * h) * d0
            - (8 * h) ^ 2 / 2 * dd
            - (8 * h) ^ 3 / 6 * ddd
            - (8 * h) ^ 4 / 24 * dddd
            - (8 * h) ^ 5 / 120 * ddddd
            - (8 * h) ^ 6 / 720 * dddddd
            - (8 * h) ^ 7 / 5040 * ddddddd
            - (8 * h) ^ 8 / 40320 * dddddddd with hA_def
  set B := y7 - y0 - (7 * h) * d0
            - (7 * h) ^ 2 / 2 * dd
            - (7 * h) ^ 3 / 6 * ddd
            - (7 * h) ^ 4 / 24 * dddd
            - (7 * h) ^ 5 / 120 * ddddd
            - (7 * h) ^ 6 / 720 * dddddd
            - (7 * h) ^ 7 / 5040 * ddddddd
            - (7 * h) ^ 8 / 40320 * dddddddd with hB_def
  set C := d7 - d0 - (7 * h) * dd
            - (7 * h) ^ 2 / 2 * ddd
            - (7 * h) ^ 3 / 6 * dddd
            - (7 * h) ^ 4 / 24 * ddddd
            - (7 * h) ^ 5 / 120 * dddddd
            - (7 * h) ^ 6 / 720 * ddddddd
            - (7 * h) ^ 7 / 5040 * dddddddd with hC_def
  set D := d6 - d0 - (6 * h) * dd
            - (6 * h) ^ 2 / 2 * ddd
            - (6 * h) ^ 3 / 6 * dddd
            - (6 * h) ^ 4 / 24 * ddddd
            - (6 * h) ^ 5 / 120 * dddddd
            - (6 * h) ^ 6 / 720 * ddddddd
            - (6 * h) ^ 7 / 5040 * dddddddd with hD_def
  set E := d5 - d0 - (5 * h) * dd
            - (5 * h) ^ 2 / 2 * ddd
            - (5 * h) ^ 3 / 6 * dddd
            - (5 * h) ^ 4 / 24 * ddddd
            - (5 * h) ^ 5 / 120 * dddddd
            - (5 * h) ^ 6 / 720 * ddddddd
            - (5 * h) ^ 7 / 5040 * dddddddd with hE_def
  set F := d4 - d0 - (4 * h) * dd
            - (4 * h) ^ 2 / 2 * ddd
            - (4 * h) ^ 3 / 6 * dddd
            - (4 * h) ^ 4 / 24 * ddddd
            - (4 * h) ^ 5 / 120 * dddddd
            - (4 * h) ^ 6 / 720 * ddddddd
            - (4 * h) ^ 7 / 5040 * dddddddd with hF_def
  set G := d3 - d0 - (3 * h) * dd
            - (3 * h) ^ 2 / 2 * ddd
            - (3 * h) ^ 3 / 6 * dddd
            - (3 * h) ^ 4 / 24 * ddddd
            - (3 * h) ^ 5 / 120 * dddddd
            - (3 * h) ^ 6 / 720 * ddddddd
            - (3 * h) ^ 7 / 5040 * dddddddd with hG_def
  set H := d2 - d0 - (2 * h) * dd
            - (2 * h) ^ 2 / 2 * ddd
            - (2 * h) ^ 3 / 6 * dddd
            - (2 * h) ^ 4 / 24 * ddddd
            - (2 * h) ^ 5 / 120 * dddddd
            - (2 * h) ^ 6 / 720 * ddddddd
            - (2 * h) ^ 7 / 5040 * dddddddd with hH_def
  set I := d1 - d0 - h * dd
            - h ^ 2 / 2 * ddd
            - h ^ 3 / 6 * dddd
            - h ^ 4 / 24 * ddddd
            - h ^ 5 / 120 * dddddd
            - h ^ 6 / 720 * ddddddd
            - h ^ 7 / 5040 * dddddddd with hI_def
  clear_value A B C D E F G H I
  have h434241h_nn : 0 ≤ 434241 * h / 120960 := by linarith
  have h1152169h_nn : 0 ≤ 1152169 * h / 120960 := by linarith
  have h2183877h_nn : 0 ≤ 2183877 * h / 120960 := by linarith
  have h2664477h_nn : 0 ≤ 2664477 * h / 120960 := by linarith
  have h2102243h_nn : 0 ≤ 2102243 * h / 120960 := by linarith
  have h1041723h_nn : 0 ≤ 1041723 * h / 120960 := by linarith
  have h295767h_nn : 0 ≤ 295767 * h / 120960 := by linarith
  have htri := ab8_residual_nine_term_triangle A B C D E F G H I h hh
  -- Bounds on each piece.
  have hA_bd : |A| ≤ M / 362880 * (8 * h) ^ 9 := hRy8
  have hB_bd : |B| ≤ M / 362880 * (7 * h) ^ 9 := hRy7
  have hC_bd : |C| ≤ M / 40320 * (7 * h) ^ 8 := hRyp7
  have hD_bd : |D| ≤ M / 40320 * (6 * h) ^ 8 := hRyp6
  have hE_bd : |E| ≤ M / 40320 * (5 * h) ^ 8 := hRyp5
  have hF_bd : |F| ≤ M / 40320 * (4 * h) ^ 8 := hRyp4
  have hG_bd : |G| ≤ M / 40320 * (3 * h) ^ 8 := hRyp3
  have hH_bd : |H| ≤ M / 40320 * (2 * h) ^ 8 := hRyp2
  have hI_bd : |I| ≤ M / 40320 * h ^ 8 := hRyp1
  -- Multiply scaled bounds.
  have h434241C_bd : (434241 * h / 120960) * |C|
      ≤ (434241 * h / 120960) * (M / 40320 * (7 * h) ^ 8) :=
    mul_le_mul_of_nonneg_left hC_bd h434241h_nn
  have h1152169D_bd : (1152169 * h / 120960) * |D|
      ≤ (1152169 * h / 120960) * (M / 40320 * (6 * h) ^ 8) :=
    mul_le_mul_of_nonneg_left hD_bd h1152169h_nn
  have h2183877E_bd : (2183877 * h / 120960) * |E|
      ≤ (2183877 * h / 120960) * (M / 40320 * (5 * h) ^ 8) :=
    mul_le_mul_of_nonneg_left hE_bd h2183877h_nn
  have h2664477F_bd : (2664477 * h / 120960) * |F|
      ≤ (2664477 * h / 120960) * (M / 40320 * (4 * h) ^ 8) :=
    mul_le_mul_of_nonneg_left hF_bd h2664477h_nn
  have h2102243G_bd : (2102243 * h / 120960) * |G|
      ≤ (2102243 * h / 120960) * (M / 40320 * (3 * h) ^ 8) :=
    mul_le_mul_of_nonneg_left hG_bd h2102243h_nn
  have h1041723H_bd : (1041723 * h / 120960) * |H|
      ≤ (1041723 * h / 120960) * (M / 40320 * (2 * h) ^ 8) :=
    mul_le_mul_of_nonneg_left hH_bd h1041723h_nn
  have h295767I_bd : (295767 * h / 120960) * |I|
      ≤ (295767 * h / 120960) * (M / 40320 * h ^ 8) :=
    mul_le_mul_of_nonneg_left hI_bd h295767h_nn
  -- Sum of upper bounds equals (388219697/241920) · M · h^9 ≤ 1605 · M · h^9.
  have hbound_alg := ab8_residual_bound_alg_identity M h
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (abs_nonneg _).trans this
  have hh9_nn : 0 ≤ h ^ 9 := by positivity
  have hMh9_nn : 0 ≤ M * h ^ 9 := mul_nonneg hMnn hh9_nn
  have hslack : (388219697 / 241920 : ℝ) * M * h ^ 9 ≤ 1605 * M * h ^ 9 := by
    rw [mul_assoc, mul_assoc (1605 : ℝ)]
    have hle : (388219697 / 241920 : ℝ) ≤ 1605 := by norm_num
    exact mul_le_mul_of_nonneg_right hle hMh9_nn
  calc |A - B - (434241 * h / 120960) * C + (1152169 * h / 120960) * D
            - (2183877 * h / 120960) * E + (2664477 * h / 120960) * F
            - (2102243 * h / 120960) * G + (1041723 * h / 120960) * H
            - (295767 * h / 120960) * I|
      ≤ |A| + |B| + (434241 * h / 120960) * |C| + (1152169 * h / 120960) * |D|
          + (2183877 * h / 120960) * |E| + (2664477 * h / 120960) * |F|
          + (2102243 * h / 120960) * |G| + (1041723 * h / 120960) * |H|
          + (295767 * h / 120960) * |I| := htri
    _ ≤ M / 362880 * (8 * h) ^ 9 + M / 362880 * (7 * h) ^ 9
          + (434241 * h / 120960) * (M / 40320 * (7 * h) ^ 8)
          + (1152169 * h / 120960) * (M / 40320 * (6 * h) ^ 8)
          + (2183877 * h / 120960) * (M / 40320 * (5 * h) ^ 8)
          + (2664477 * h / 120960) * (M / 40320 * (4 * h) ^ 8)
          + (2102243 * h / 120960) * (M / 40320 * (3 * h) ^ 8)
          + (1041723 * h / 120960) * (M / 40320 * (2 * h) ^ 8)
          + (295767 * h / 120960) * (M / 40320 * h ^ 8) := by
        linarith [hA_bd, hB_bd, h434241C_bd, h1152169D_bd, h2183877E_bd,
          h2664477F_bd, h2102243G_bd, h1041723H_bd, h295767I_bd]
    _ = (388219697 / 241920 : ℝ) * M * h ^ 9 := hbound_alg
    _ ≤ 1605 * M * h ^ 9 := hslack

/-- Uniform bound on the AB8 one-step truncation residual on a finite
horizon, given a `C^9` exact solution. -/
theorem ab8_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 9 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 8) * h ≤ T →
        |adamsBashforth8.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 9 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_nine_bounded_on_Icc hy t₀ (t₀ + T + 1)
  refine ⟨(1605 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 8) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 8) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 8) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 8) * h := by nlinarith
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 4 * h ≤ ((n : ℝ) + 8) * h := by nlinarith
    linarith
  have ht5h_mem : t + 5 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 5 * h ≤ ((n : ℝ) + 8) * h := by nlinarith
    linarith
  have ht6h_mem : t + 6 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 6 * h ≤ ((n : ℝ) + 8) * h := by nlinarith
    linarith
  have ht7h_mem : t + 7 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 7 * h ≤ ((n : ℝ) + 8) * h := by nlinarith
    linarith
  have ht8h_mem : t + 8 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 8 * h = ((n : ℝ) + 8) * h := by ring
    linarith
  -- Rewrite the LTE in textbook form.
  rw [ab8_localTruncationError_eq]
  show |y (t + 8 * h) - y (t + 7 * h)
      - h * (434241 / 120960 * deriv y (t + 7 * h)
              - 1152169 / 120960 * deriv y (t + 6 * h)
              + 2183877 / 120960 * deriv y (t + 5 * h)
              - 2664477 / 120960 * deriv y (t + 4 * h)
              + 2102243 / 120960 * deriv y (t + 3 * h)
              - 1041723 / 120960 * deriv y (t + 2 * h)
              + 295767 / 120960 * deriv y (t + h)
              - 36799 / 120960 * deriv y t)|
    ≤ 1605 * M * h ^ 9
  have hreshape :
      h * (434241 / 120960 * deriv y (t + 7 * h)
            - 1152169 / 120960 * deriv y (t + 6 * h)
            + 2183877 / 120960 * deriv y (t + 5 * h)
            - 2664477 / 120960 * deriv y (t + 4 * h)
            + 2102243 / 120960 * deriv y (t + 3 * h)
            - 1041723 / 120960 * deriv y (t + 2 * h)
            + 295767 / 120960 * deriv y (t + h)
            - 36799 / 120960 * deriv y t)
        = h * ((434241 / 120960) * deriv y (t + 7 * h)
              - (1152169 / 120960) * deriv y (t + 6 * h)
              + (2183877 / 120960) * deriv y (t + 5 * h)
              - (2664477 / 120960) * deriv y (t + 4 * h)
              + (2102243 / 120960) * deriv y (t + 3 * h)
              - (1041723 / 120960) * deriv y (t + 2 * h)
              + (295767 / 120960) * deriv y (t + h)
              - (36799 / 120960) * deriv y t) := by ring
  rw [hreshape]
  exact ab8_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem ht4h_mem ht5h_mem ht6h_mem ht7h_mem ht8h_mem hh.le

/-! #### Generic AB scalar bridge

Routes the scalar AB8 headline through the generic AB scaffold at `s = 8`,
mirroring the AB7 scalar bridge. -/

/-- AB8 coefficient vector for the generic AB scaffold, ordered from the
oldest to newest sample in the eight-step window. -/
noncomputable def ab8GenericCoeff : Fin 8 → ℝ :=
  ![-(36799 : ℝ) / 120960, (295767 : ℝ) / 120960, -(1041723 : ℝ) / 120960,
    (2102243 : ℝ) / 120960, -(2664477 : ℝ) / 120960, (2183877 : ℝ) / 120960,
    -(1152169 : ℝ) / 120960, (434241 : ℝ) / 120960]

@[simp] lemma ab8GenericCoeff_zero :
    ab8GenericCoeff 0 = -(36799 : ℝ) / 120960 := rfl

@[simp] lemma ab8GenericCoeff_one :
    ab8GenericCoeff 1 = (295767 : ℝ) / 120960 := rfl

@[simp] lemma ab8GenericCoeff_two :
    ab8GenericCoeff 2 = -(1041723 : ℝ) / 120960 := rfl

@[simp] lemma ab8GenericCoeff_three :
    ab8GenericCoeff 3 = (2102243 : ℝ) / 120960 := rfl

@[simp] lemma ab8GenericCoeff_four :
    ab8GenericCoeff 4 = -(2664477 : ℝ) / 120960 := rfl

@[simp] lemma ab8GenericCoeff_five :
    ab8GenericCoeff 5 = (2183877 : ℝ) / 120960 := rfl

@[simp] lemma ab8GenericCoeff_six :
    ab8GenericCoeff 6 = -(1152169 : ℝ) / 120960 := rfl

@[simp] lemma ab8GenericCoeff_seven :
    ab8GenericCoeff 7 = (434241 : ℝ) / 120960 := rfl

/-- The effective Lipschitz constant for the generic AB scaffold at the
AB8 coefficient tuple is `(77432/945) · L`. -/
lemma abLip_ab8GenericCoeff (L : ℝ) :
    abLip 8 ab8GenericCoeff L = (77432 / 945) * L := by
  rw [abLip, Fin.sum_univ_eight, ab8GenericCoeff_zero, ab8GenericCoeff_one,
    ab8GenericCoeff_two, ab8GenericCoeff_three, ab8GenericCoeff_four,
    ab8GenericCoeff_five, ab8GenericCoeff_six, ab8GenericCoeff_seven]
  rw [show |(-(36799 : ℝ) / 120960)| = (36799 : ℝ) / 120960 by norm_num,
      show |((295767 : ℝ) / 120960)| = (295767 : ℝ) / 120960 by norm_num,
      show |(-(1041723 : ℝ) / 120960)| = (1041723 : ℝ) / 120960 by norm_num,
      show |((2102243 : ℝ) / 120960)| = (2102243 : ℝ) / 120960 by norm_num,
      show |(-(2664477 : ℝ) / 120960)| = (2664477 : ℝ) / 120960 by norm_num,
      show |((2183877 : ℝ) / 120960)| = (2183877 : ℝ) / 120960 by norm_num,
      show |(-(1152169 : ℝ) / 120960)| = (1152169 : ℝ) / 120960 by norm_num,
      show |((434241 : ℝ) / 120960)| = (434241 : ℝ) / 120960 by norm_num]
  ring

/-- Bridge: the AB8 scalar iteration is the generic AB iteration
at `s = 8` with `α = ab8GenericCoeff` and starting samples
`![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇]`. -/
lemma ab8Iter_eq_abIter
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : ℝ) (n : ℕ) :
    ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ n
      = abIter 8 ab8GenericCoeff h f t₀
          ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇] n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      show ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 0 = _
      rw [ab8Iter_zero]
      unfold abIter
      simp
    | 1 =>
      show ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 1 = _
      rw [ab8Iter_one]
      unfold abIter
      simp
    | 2 =>
      show ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 2 = _
      rw [ab8Iter_two]
      unfold abIter
      simp
    | 3 =>
      show ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 3 = _
      rw [ab8Iter_three]
      unfold abIter
      simp
    | 4 =>
      show ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 4 = _
      rw [ab8Iter_four]
      unfold abIter
      simp
    | 5 =>
      show ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 5 = _
      rw [ab8Iter_five]
      unfold abIter
      simp
    | 6 =>
      show ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 6 = _
      rw [ab8Iter_six]
      unfold abIter
      simp
    | 7 =>
      show ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ 7 = _
      rw [ab8Iter_seven]
      unfold abIter
      simp
    | k + 8 =>
      rw [ab8Iter_succ_eight]
      rw [abIter_step (s := 8) (by norm_num)
          ab8GenericCoeff h f t₀ ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇] k]
      rw [show (k + 8 - 1 : ℕ) = k + 7 from by omega]
      rw [Fin.sum_univ_eight]
      have hval3 : ((3 : Fin 8) : ℕ) = 3 := rfl
      have hval4 : ((4 : Fin 8) : ℕ) = 4 := rfl
      have hval5 : ((5 : Fin 8) : ℕ) = 5 := rfl
      have hval6 : ((6 : Fin 8) : ℕ) = 6 := rfl
      have hval7 : ((7 : Fin 8) : ℕ) = 7 := rfl
      simp only [ab8GenericCoeff_zero, ab8GenericCoeff_one, ab8GenericCoeff_two,
        ab8GenericCoeff_three, ab8GenericCoeff_four, ab8GenericCoeff_five,
        ab8GenericCoeff_six, ab8GenericCoeff_seven,
        Fin.val_zero, Fin.val_one, Fin.val_two, hval3, hval4, hval5, hval6,
        hval7, Nat.add_zero]
      rw [← ih k (by omega), ← ih (k + 1) (by omega), ← ih (k + 2) (by omega),
        ← ih (k + 3) (by omega), ← ih (k + 4) (by omega),
        ← ih (k + 5) (by omega), ← ih (k + 6) (by omega),
        ← ih (k + 7) (by omega)]
      rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring,
        show ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 by push_cast; ring,
        show ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 by push_cast; ring,
        show ((k + 4 : ℕ) : ℝ) = (k : ℝ) + 4 by push_cast; ring,
        show ((k + 5 : ℕ) : ℝ) = (k : ℝ) + 5 by push_cast; ring,
        show ((k + 6 : ℕ) : ℝ) = (k : ℝ) + 6 by push_cast; ring,
        show ((k + 7 : ℕ) : ℝ) = (k : ℝ) + 7 by push_cast; ring]
      ring

/-- Bridge: the AB8 scalar truncation residual at base point `t₀ + n · h`
equals the generic AB residual at index `n`. -/
lemma ab8Residual_eq_abResidual
    (h : ℝ) (y : ℝ → ℝ) (t₀ : ℝ) (n : ℕ) :
    y (t₀ + (n : ℝ) * h + 8 * h) - y (t₀ + (n : ℝ) * h + 7 * h)
        - h * ((434241 / 120960) * deriv y (t₀ + (n : ℝ) * h + 7 * h)
              - (1152169 / 120960) * deriv y (t₀ + (n : ℝ) * h + 6 * h)
              + (2183877 / 120960) * deriv y (t₀ + (n : ℝ) * h + 5 * h)
              - (2664477 / 120960) * deriv y (t₀ + (n : ℝ) * h + 4 * h)
              + (2102243 / 120960) * deriv y (t₀ + (n : ℝ) * h + 3 * h)
              - (1041723 / 120960) * deriv y (t₀ + (n : ℝ) * h + 2 * h)
              + (295767 / 120960) * deriv y (t₀ + (n : ℝ) * h + h)
              - (36799 / 120960) * deriv y (t₀ + (n : ℝ) * h))
      = abResidual 8 ab8GenericCoeff h y t₀ n := by
  unfold abResidual
  rw [Fin.sum_univ_eight, ab8GenericCoeff_zero, ab8GenericCoeff_one,
    ab8GenericCoeff_two, ab8GenericCoeff_three, ab8GenericCoeff_four,
    ab8GenericCoeff_five, ab8GenericCoeff_six, ab8GenericCoeff_seven]
  have eA : t₀ + (n : ℝ) * h + 8 * h = t₀ + ((n + 8 : ℕ) : ℝ) * h := by
    push_cast; ring
  have eB :
      t₀ + (n : ℝ) * h + 7 * h = t₀ + ((n + 8 - 1 : ℕ) : ℝ) * h := by
    have hsub : (n + 8 - 1 : ℕ) = n + 7 := by omega
    rw [hsub]; push_cast; ring
  have eC : t₀ + (n : ℝ) * h
      = t₀ + ((n + ((0 : Fin 8) : ℕ) : ℕ) : ℝ) * h := by
    simp
  have eD : t₀ + (n : ℝ) * h + h
      = t₀ + ((n + ((1 : Fin 8) : ℕ) : ℕ) : ℝ) * h := by
    simp; ring
  have eE : t₀ + (n : ℝ) * h + 2 * h
      = t₀ + ((n + ((2 : Fin 8) : ℕ) : ℕ) : ℝ) * h := by
    simp; ring
  have eF : t₀ + (n : ℝ) * h + 3 * h
      = t₀ + ((n + ((3 : Fin 8) : ℕ) : ℕ) : ℝ) * h := by
    have : ((3 : Fin 8) : ℕ) = 3 := rfl
    rw [this]; push_cast; ring
  have eG : t₀ + (n : ℝ) * h + 4 * h
      = t₀ + ((n + ((4 : Fin 8) : ℕ) : ℕ) : ℝ) * h := by
    have : ((4 : Fin 8) : ℕ) = 4 := rfl
    rw [this]; push_cast; ring
  have eH : t₀ + (n : ℝ) * h + 5 * h
      = t₀ + ((n + ((5 : Fin 8) : ℕ) : ℕ) : ℝ) * h := by
    have : ((5 : Fin 8) : ℕ) = 5 := rfl
    rw [this]; push_cast; ring
  have eI : t₀ + (n : ℝ) * h + 6 * h
      = t₀ + ((n + ((6 : Fin 8) : ℕ) : ℕ) : ℝ) * h := by
    have : ((6 : Fin 8) : ℕ) = 6 := rfl
    rw [this]; push_cast; ring
  have eJ : t₀ + (n : ℝ) * h + 7 * h
      = t₀ + ((n + ((7 : Fin 8) : ℕ) : ℕ) : ℝ) * h := by
    have : ((7 : Fin 8) : ℕ) = 7 := rfl
    rw [this]; push_cast; ring
  rw [← eA, ← eB, ← eC, ← eD, ← eE, ← eF, ← eG, ← eH, ← eI, ← eJ]
  ring

/-- Final AB8 global error bound on `[t₀, t₀ + T]`. Under Lipschitz `f`,
`C^9` exact solution `y` with `deriv y t = f t (y t)`, and starting
errors `|y_i - y(t_i)| ≤ ε₀` for `i = 0, 1, …, 7`, the AB8 iterate error
obeys `O(ε₀ + h^8)` on a finite horizon. -/
theorem ab8_global_error_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 9 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      ∀ {y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ ε₀ : ℝ}, 0 ≤ ε₀ →
      |y₀ - y t₀| ≤ ε₀ → |y₁ - y (t₀ + h)| ≤ ε₀ →
      |y₂ - y (t₀ + 2 * h)| ≤ ε₀ →
      |y₃ - y (t₀ + 3 * h)| ≤ ε₀ →
      |y₄ - y (t₀ + 4 * h)| ≤ ε₀ →
      |y₅ - y (t₀ + 5 * h)| ≤ ε₀ →
      |y₆ - y (t₀ + 6 * h)| ≤ ε₀ →
      |y₇ - y (t₀ + 7 * h)| ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 7) * h ≤ T →
      |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ N - y (t₀ + (N : ℝ) * h)|
        ≤ Real.exp ((77432 / 945) * L * T) * ε₀ + K * h ^ 8 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    ab8_local_residual_bound hy t₀ T hT
  refine ⟨T * Real.exp ((77432 / 945) * L * T) * C, δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
  intro h hh hδ_le y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ ε₀ hε₀
    he0_bd he1_bd he2_bd he3_bd he4_bd he5_bd he6_bd he7_bd N hNh
  set α : Fin 8 → ℝ := ab8GenericCoeff with hα_def
  set y₀_oct : Fin 8 → ℝ := ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇] with hy_oct_def
  have hs : (1 : ℕ) ≤ 8 := by norm_num
  haveI : Nonempty (Fin 8) := ⟨⟨0, hs⟩⟩
  have hiter0 : abIter 8 α h f t₀ y₀_oct 0 = y₀ := by
    unfold abIter; simp [hy_oct_def]
  have hiter1 : abIter 8 α h f t₀ y₀_oct 1 = y₁ := by
    unfold abIter; simp [hy_oct_def]
  have hiter2 : abIter 8 α h f t₀ y₀_oct 2 = y₂ := by
    unfold abIter; simp [hy_oct_def]
  have hiter3 : abIter 8 α h f t₀ y₀_oct 3 = y₃ := by
    unfold abIter; simp [hy_oct_def]
  have hiter4 : abIter 8 α h f t₀ y₀_oct 4 = y₄ := by
    unfold abIter; simp [hy_oct_def]
  have hiter5 : abIter 8 α h f t₀ y₀_oct 5 = y₅ := by
    unfold abIter; simp [hy_oct_def]
  have hiter6 : abIter 8 α h f t₀ y₀_oct 6 = y₆ := by
    unfold abIter; simp [hy_oct_def]
  have hiter7 : abIter 8 α h f t₀ y₀_oct 7 = y₇ := by
    unfold abIter; simp [hy_oct_def]
  have hstart : abErrWindow hs α h f t₀ y₀_oct y 0 ≤ ε₀ := by
    unfold abErrWindow
    apply Finset.sup'_le
    intro j _
    show abErr 8 α h f t₀ y₀_oct y (0 + (j : ℕ)) ≤ ε₀
    unfold abErr
    fin_cases j
    · show |abIter 8 α h f t₀ y₀_oct 0
          - y (t₀ + ((0 + (((0 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter0]
      have : ((0 + (((0 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) = 0 := by simp
      rw [this, zero_mul, add_zero]; exact he0_bd
    · show |abIter 8 α h f t₀ y₀_oct 1
          - y (t₀ + ((0 + (((1 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter1]
      have : ((0 + (((1 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) = 1 := by simp
      rw [this, one_mul]; exact he1_bd
    · show |abIter 8 α h f t₀ y₀_oct 2
          - y (t₀ + ((0 + (((2 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter2]
      have : ((0 + (((2 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) = 2 := by simp
      rw [this]; exact he2_bd
    · show |abIter 8 α h f t₀ y₀_oct 3
          - y (t₀ + ((0 + (((3 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter3]
      have hval3 : ((3 : Fin 8) : ℕ) = 3 := rfl
      have : ((0 + (((3 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) = 3 := by
        rw [hval3]; push_cast; ring
      rw [this]; exact he3_bd
    · show |abIter 8 α h f t₀ y₀_oct 4
          - y (t₀ + ((0 + (((4 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter4]
      have hval4 : ((4 : Fin 8) : ℕ) = 4 := rfl
      have : ((0 + (((4 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) = 4 := by
        rw [hval4]; push_cast; ring
      rw [this]; exact he4_bd
    · show |abIter 8 α h f t₀ y₀_oct 5
          - y (t₀ + ((0 + (((5 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter5]
      have hval5 : ((5 : Fin 8) : ℕ) = 5 := rfl
      have : ((0 + (((5 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) = 5 := by
        rw [hval5]; push_cast; ring
      rw [this]; exact he5_bd
    · show |abIter 8 α h f t₀ y₀_oct 6
          - y (t₀ + ((0 + (((6 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter6]
      have hval6 : ((6 : Fin 8) : ℕ) = 6 := rfl
      have : ((0 + (((6 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) = 6 := by
        rw [hval6]; push_cast; ring
      rw [this]; exact he6_bd
    · show |abIter 8 α h f t₀ y₀_oct 7
          - y (t₀ + ((0 + (((7 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter7]
      have hval7 : ((7 : Fin 8) : ℕ) = 7 := rfl
      have : ((0 + (((7 : Fin 8) : ℕ) : ℕ) : ℕ) : ℝ) = 7 := by
        rw [hval7]; push_cast; ring
      rw [this]; exact he7_bd
  have hres_gen : ∀ n : ℕ, n < N →
      |abResidual 8 α h y t₀ n| ≤ C * h ^ (8 + 1) := by
    intro n hn_lt
    have hcast : (n : ℝ) + 8 ≤ (N : ℝ) + 7 := by
      have : (n : ℝ) + 1 ≤ (N : ℝ) := by
        exact_mod_cast Nat.lt_iff_add_one_le.mp hn_lt
      linarith
    have hn8_le : ((n : ℝ) + 8) * h ≤ T := by
      have hmul : ((n : ℝ) + 8) * h ≤ ((N : ℝ) + 7) * h :=
        mul_le_mul_of_nonneg_right hcast hh.le
      linarith
    have hres := hresidual hh hδ_le n hn8_le
    have hLTE_eq := ab8_localTruncationError_eq h (t₀ + (n : ℝ) * h) y
    have hbridge := ab8Residual_eq_abResidual h y t₀ n
    have hpow : C * h ^ (8 + 1) = C * h ^ 9 := by norm_num
    rw [hα_def, ← hbridge]
    have hreshape :
        h * ((434241 / 120960) * deriv y (t₀ + (n : ℝ) * h + 7 * h)
              - (1152169 / 120960) * deriv y (t₀ + (n : ℝ) * h + 6 * h)
              + (2183877 / 120960) * deriv y (t₀ + (n : ℝ) * h + 5 * h)
              - (2664477 / 120960) * deriv y (t₀ + (n : ℝ) * h + 4 * h)
              + (2102243 / 120960) * deriv y (t₀ + (n : ℝ) * h + 3 * h)
              - (1041723 / 120960) * deriv y (t₀ + (n : ℝ) * h + 2 * h)
              + (295767 / 120960) * deriv y (t₀ + (n : ℝ) * h + h)
              - (36799 / 120960) * deriv y (t₀ + (n : ℝ) * h))
          = h * (434241 / 120960 * deriv y (t₀ + (n : ℝ) * h + 7 * h)
                - 1152169 / 120960 * deriv y (t₀ + (n : ℝ) * h + 6 * h)
                + 2183877 / 120960 * deriv y (t₀ + (n : ℝ) * h + 5 * h)
                - 2664477 / 120960 * deriv y (t₀ + (n : ℝ) * h + 4 * h)
                + 2102243 / 120960 * deriv y (t₀ + (n : ℝ) * h + 3 * h)
                - 1041723 / 120960 * deriv y (t₀ + (n : ℝ) * h + 2 * h)
                + 295767 / 120960 * deriv y (t₀ + (n : ℝ) * h + h)
                - 36799 / 120960 * deriv y (t₀ + (n : ℝ) * h)) := by ring
    rw [hreshape, ← hLTE_eq]
    linarith [hres, hpow.symm.le, hpow.le]
  have hNh' : (N : ℝ) * h ≤ T := by
    have hmono : (N : ℝ) * h ≤ ((N : ℝ) + 7) * h := by
      have h1 : (N : ℝ) ≤ (N : ℝ) + 7 := by linarith
      exact mul_le_mul_of_nonneg_right h1 hh.le
    linarith
  have hgeneric :=
    ab_global_error_bound_generic (p := 8) hs α hh.le hL hC_nn hf t₀
      y₀_oct y hyf hε₀ hstart N hNh' hres_gen
  rw [show abLip 8 α L = (77432 / 945) * L from by
    rw [hα_def]; exact abLip_ab8GenericCoeff L] at hgeneric
  have hwindow_ge : abErr 8 α h f t₀ y₀_oct y N
      ≤ abErrWindow hs α h f t₀ y₀_oct y N := by
    show abErr 8 α h f t₀ y₀_oct y (N + ((⟨0, hs⟩ : Fin 8) : ℕ))
        ≤ abErrWindow hs α h f t₀ y₀_oct y N
    unfold abErrWindow
    exact Finset.le_sup' (b := ⟨0, hs⟩)
      (f := fun j : Fin 8 => abErr 8 α h f t₀ y₀_oct y (N + (j : ℕ)))
      (Finset.mem_univ _)
  have hbridge :
      abIter 8 α h f t₀ y₀_oct N
        = ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ N := by
    rw [hα_def, hy_oct_def]
    exact (ab8Iter_eq_abIter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ N).symm
  have habsErr :
      abErr 8 α h f t₀ y₀_oct y N
        = |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ N - y (t₀ + (N : ℝ) * h)| := by
    show |abIter 8 α h f t₀ y₀_oct N - y (t₀ + (N : ℝ) * h)|
        = |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ N - y (t₀ + (N : ℝ) * h)|
    rw [hbridge]
  show |ab8Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ N - y (t₀ + (N : ℝ) * h)|
      ≤ Real.exp ((77432 / 945) * L * T) * ε₀
        + T * Real.exp ((77432 / 945) * L * T) * C * h ^ 8
  linarith [hwindow_ge, hgeneric, habsErr.symm.le, habsErr.le]

end LMM
