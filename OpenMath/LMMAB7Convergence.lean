import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMABGenericConvergence
import OpenMath.LMMAM6Convergence

/-! ## Adams–Bashforth 7-step Scalar Convergence Chain (Iserles §1.2)

Order-7 explicit 7-step LMM convergence scaffold. Mirrors the AB6 chain
in `OpenMath.LMMAB6ScalarConvergence` at the next order. This scalar half
takes seven starting samples and combines seven prior `f` evaluations.
The effective max-window Lipschitz constant is `(40633/945) · L`
(equivalently `2600512/60480 · L ≈ 43 · L`), the residual is `O(h^8)`
and the headline global error bound is `O(ε₀ + h^7)`. -/

namespace LMM

/-- AB7 iteration with seven starting samples `y₀, y₁, y₂, y₃, y₄, y₅, y₆`:
`y_{n+7} = y_{n+6} + h · ((198721/60480) · f_{n+6} − (447288/60480) · f_{n+5}
  + (705549/60480) · f_{n+4} − (688256/60480) · f_{n+3}
  + (407139/60480) · f_{n+2} − (134472/60480) · f_{n+1}
  + (19087/60480) · f_n)`. -/
noncomputable def ab7Iter
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ : ℝ) : ℕ → ℝ
  | 0 => y₀
  | 1 => y₁
  | 2 => y₂
  | 3 => y₃
  | 4 => y₄
  | 5 => y₅
  | 6 => y₆
  | n + 7 =>
      ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 6)
        + h * (198721 / 60480 * f (t₀ + ((n : ℝ) + 6) * h)
                (ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 6))
              - 447288 / 60480 * f (t₀ + ((n : ℝ) + 5) * h)
                (ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 5))
              + 705549 / 60480 * f (t₀ + ((n : ℝ) + 4) * h)
                (ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 4))
              - 688256 / 60480 * f (t₀ + ((n : ℝ) + 3) * h)
                (ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 3))
              + 407139 / 60480 * f (t₀ + ((n : ℝ) + 2) * h)
                (ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 2))
              - 134472 / 60480 * f (t₀ + ((n : ℝ) + 1) * h)
                (ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 1))
              + 19087 / 60480 * f (t₀ + (n : ℝ) * h)
                (ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ n))

@[simp] lemma ab7Iter_zero
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ : ℝ) :
    ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 0 = y₀ := rfl

@[simp] lemma ab7Iter_one
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ : ℝ) :
    ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 1 = y₁ := rfl

@[simp] lemma ab7Iter_two
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ : ℝ) :
    ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 2 = y₂ := rfl

@[simp] lemma ab7Iter_three
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ : ℝ) :
    ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 3 = y₃ := rfl

@[simp] lemma ab7Iter_four
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ : ℝ) :
    ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 4 = y₄ := rfl

@[simp] lemma ab7Iter_five
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ : ℝ) :
    ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 5 = y₅ := rfl

@[simp] lemma ab7Iter_six
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ : ℝ) :
    ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 6 = y₆ := rfl

lemma ab7Iter_succ_seven
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ : ℝ) (n : ℕ) :
    ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 7)
      = ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 6)
          + h * (198721 / 60480 * f (t₀ + ((n : ℝ) + 6) * h)
                  (ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 6))
                - 447288 / 60480 * f (t₀ + ((n : ℝ) + 5) * h)
                    (ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 5))
                + 705549 / 60480 * f (t₀ + ((n : ℝ) + 4) * h)
                    (ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 4))
                - 688256 / 60480 * f (t₀ + ((n : ℝ) + 3) * h)
                    (ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 3))
                + 407139 / 60480 * f (t₀ + ((n : ℝ) + 2) * h)
                    (ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 2))
                - 134472 / 60480 * f (t₀ + ((n : ℝ) + 1) * h)
                    (ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 1))
                + 19087 / 60480 * f (t₀ + (n : ℝ) * h)
                    (ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ n)) := rfl

/-- AB7 local truncation operator reduces to the textbook 7-step residual. -/
theorem ab7_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    adamsBashforth7.localTruncationError h t y
      = y (t + 7 * h) - y (t + 6 * h)
          - h * (198721 / 60480 * deriv y (t + 6 * h)
                  - 447288 / 60480 * deriv y (t + 5 * h)
                  + 705549 / 60480 * deriv y (t + 4 * h)
                  - 688256 / 60480 * deriv y (t + 3 * h)
                  + 407139 / 60480 * deriv y (t + 2 * h)
                  - 134472 / 60480 * deriv y (t + h)
                  + 19087 / 60480 * deriv y t) := by
  unfold localTruncationError truncationOp
  simp [adamsBashforth7, Fin.sum_univ_succ, iteratedDeriv_one,
    iteratedDeriv_zero]
  ring_nf

/-- One-step AB7 Lipschitz step: a single linearised increment of the
global error from steps `n, n+1, …, n+6` to `n+7`, with seven Lipschitz
contributions and additive `|τ_n|`. -/
theorem ab7_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ : ℝ) (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)|
      ≤ |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|
        + (198721 / 60480) * h * L
            * |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 6)
                - y (t₀ + ((n : ℝ) + 6) * h)|
        + (447288 / 60480) * h * L
            * |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 5)
                - y (t₀ + ((n : ℝ) + 5) * h)|
        + (705549 / 60480) * h * L
            * |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 4)
                - y (t₀ + ((n : ℝ) + 4) * h)|
        + (688256 / 60480) * h * L
            * |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 3)
                - y (t₀ + ((n : ℝ) + 3) * h)|
        + (407139 / 60480) * h * L
            * |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 2)
                - y (t₀ + ((n : ℝ) + 2) * h)|
        + (134472 / 60480) * h * L
            * |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 1)
                - y (t₀ + ((n : ℝ) + 1) * h)|
        + (19087 / 60480) * h * L
            * |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ n - y (t₀ + (n : ℝ) * h)|
        + |adamsBashforth7.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set yn : ℝ := ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ n with hyn_def
  set yn1 : ℝ := ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 1) with hyn1_def
  set yn2 : ℝ := ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 2) with hyn2_def
  set yn3 : ℝ := ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 3) with hyn3_def
  set yn4 : ℝ := ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 4) with hyn4_def
  set yn5 : ℝ := ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 5) with hyn5_def
  set yn6 : ℝ := ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 6) with hyn6_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set tn3 : ℝ := t₀ + ((n : ℝ) + 3) * h with htn3_def
  set tn4 : ℝ := t₀ + ((n : ℝ) + 4) * h with htn4_def
  set tn5 : ℝ := t₀ + ((n : ℝ) + 5) * h with htn5_def
  set tn6 : ℝ := t₀ + ((n : ℝ) + 6) * h with htn6_def
  set tn7 : ℝ := t₀ + ((n : ℝ) + 7) * h with htn7_def
  set zn : ℝ := y tn with hzn_def
  set zn1 : ℝ := y tn1 with hzn1_def
  set zn2 : ℝ := y tn2 with hzn2_def
  set zn3 : ℝ := y tn3 with hzn3_def
  set zn4 : ℝ := y tn4 with hzn4_def
  set zn5 : ℝ := y tn5 with hzn5_def
  set zn6 : ℝ := y tn6 with hzn6_def
  set zn7 : ℝ := y tn7 with hzn7_def
  set τ : ℝ := adamsBashforth7.localTruncationError h tn y with hτ_def
  -- AB7 step formula.
  have hstep : ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 7)
      = yn6 + h * (198721 / 60480 * f tn6 yn6
                    - 447288 / 60480 * f tn5 yn5
                    + 705549 / 60480 * f tn4 yn4
                    - 688256 / 60480 * f tn3 yn3
                    + 407139 / 60480 * f tn2 yn2
                    - 134472 / 60480 * f tn1 yn1
                    + 19087 / 60480 * f tn yn) := by
    show ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 7) = _
    rw [ab7Iter_succ_seven]
  -- Time arithmetic.
  have htn1_h : tn + h = tn1 := by simp [htn_def, htn1_def]; ring
  have htn_2h : tn + 2 * h = tn2 := by simp [htn_def, htn2_def]; ring
  have htn_3h : tn + 3 * h = tn3 := by simp [htn_def, htn3_def]; ring
  have htn_4h : tn + 4 * h = tn4 := by simp [htn_def, htn4_def]; ring
  have htn_5h : tn + 5 * h = tn5 := by simp [htn_def, htn5_def]; ring
  have htn_6h : tn + 6 * h = tn6 := by simp [htn_def, htn6_def]; ring
  have htn_7h : tn + 7 * h = tn7 := by simp [htn_def, htn7_def]; ring
  -- LTE residual at `tn`, expressed via `f` along the trajectory.
  have hτ_eq : τ = zn7 - zn6
        - h * (198721 / 60480 * f tn6 zn6 - 447288 / 60480 * f tn5 zn5
              + 705549 / 60480 * f tn4 zn4 - 688256 / 60480 * f tn3 zn3
              + 407139 / 60480 * f tn2 zn2 - 134472 / 60480 * f tn1 zn1
              + 19087 / 60480 * f tn zn) := by
    show adamsBashforth7.localTruncationError h tn y = _
    rw [ab7_localTruncationError_eq, htn1_h, htn_2h, htn_3h, htn_4h, htn_5h,
      htn_6h, htn_7h, hyf tn6, hyf tn5, hyf tn4, hyf tn3, hyf tn2, hyf tn1,
      hyf tn]
  -- Algebraic decomposition of the global error increment.
  have halg : ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 7) - zn7
      = (yn6 - zn6)
        + (198721 / 60480) * h * (f tn6 yn6 - f tn6 zn6)
        - (447288 / 60480) * h * (f tn5 yn5 - f tn5 zn5)
        + (705549 / 60480) * h * (f tn4 yn4 - f tn4 zn4)
        - (688256 / 60480) * h * (f tn3 yn3 - f tn3 zn3)
        + (407139 / 60480) * h * (f tn2 yn2 - f tn2 zn2)
        - (134472 / 60480) * h * (f tn1 yn1 - f tn1 zn1)
        + (19087 / 60480) * h * (f tn yn - f tn zn)
        - τ := by
    rw [hstep, hτ_eq]; ring
  -- Lipschitz bounds.
  have hLip6 : |f tn6 yn6 - f tn6 zn6| ≤ L * |yn6 - zn6| := hf tn6 yn6 zn6
  have hLip5 : |f tn5 yn5 - f tn5 zn5| ≤ L * |yn5 - zn5| := hf tn5 yn5 zn5
  have hLip4 : |f tn4 yn4 - f tn4 zn4| ≤ L * |yn4 - zn4| := hf tn4 yn4 zn4
  have hLip3 : |f tn3 yn3 - f tn3 zn3| ≤ L * |yn3 - zn3| := hf tn3 yn3 zn3
  have hLip2 : |f tn2 yn2 - f tn2 zn2| ≤ L * |yn2 - zn2| := hf tn2 yn2 zn2
  have hLip1 : |f tn1 yn1 - f tn1 zn1| ≤ L * |yn1 - zn1| := hf tn1 yn1 zn1
  have hLip0 : |f tn yn - f tn zn| ≤ L * |yn - zn| := hf tn yn zn
  have h198721_nn : 0 ≤ (198721 / 60480) * h := by linarith
  have h447288_nn : 0 ≤ (447288 / 60480) * h := by linarith
  have h705549_nn : 0 ≤ (705549 / 60480) * h := by linarith
  have h688256_nn : 0 ≤ (688256 / 60480) * h := by linarith
  have h407139_nn : 0 ≤ (407139 / 60480) * h := by linarith
  have h134472_nn : 0 ≤ (134472 / 60480) * h := by linarith
  have h19087_nn : 0 ≤ (19087 / 60480) * h := by linarith
  have h198721_abs : |(198721 / 60480) * h * (f tn6 yn6 - f tn6 zn6)|
      ≤ (198721 / 60480) * h * L * |yn6 - zn6| := by
    rw [abs_mul, abs_of_nonneg h198721_nn]
    calc (198721 / 60480) * h * |f tn6 yn6 - f tn6 zn6|
        ≤ (198721 / 60480) * h * (L * |yn6 - zn6|) :=
          mul_le_mul_of_nonneg_left hLip6 h198721_nn
      _ = (198721 / 60480) * h * L * |yn6 - zn6| := by ring
  have h447288_abs : |(447288 / 60480) * h * (f tn5 yn5 - f tn5 zn5)|
      ≤ (447288 / 60480) * h * L * |yn5 - zn5| := by
    rw [abs_mul, abs_of_nonneg h447288_nn]
    calc (447288 / 60480) * h * |f tn5 yn5 - f tn5 zn5|
        ≤ (447288 / 60480) * h * (L * |yn5 - zn5|) :=
          mul_le_mul_of_nonneg_left hLip5 h447288_nn
      _ = (447288 / 60480) * h * L * |yn5 - zn5| := by ring
  have h705549_abs : |(705549 / 60480) * h * (f tn4 yn4 - f tn4 zn4)|
      ≤ (705549 / 60480) * h * L * |yn4 - zn4| := by
    rw [abs_mul, abs_of_nonneg h705549_nn]
    calc (705549 / 60480) * h * |f tn4 yn4 - f tn4 zn4|
        ≤ (705549 / 60480) * h * (L * |yn4 - zn4|) :=
          mul_le_mul_of_nonneg_left hLip4 h705549_nn
      _ = (705549 / 60480) * h * L * |yn4 - zn4| := by ring
  have h688256_abs : |(688256 / 60480) * h * (f tn3 yn3 - f tn3 zn3)|
      ≤ (688256 / 60480) * h * L * |yn3 - zn3| := by
    rw [abs_mul, abs_of_nonneg h688256_nn]
    calc (688256 / 60480) * h * |f tn3 yn3 - f tn3 zn3|
        ≤ (688256 / 60480) * h * (L * |yn3 - zn3|) :=
          mul_le_mul_of_nonneg_left hLip3 h688256_nn
      _ = (688256 / 60480) * h * L * |yn3 - zn3| := by ring
  have h407139_abs : |(407139 / 60480) * h * (f tn2 yn2 - f tn2 zn2)|
      ≤ (407139 / 60480) * h * L * |yn2 - zn2| := by
    rw [abs_mul, abs_of_nonneg h407139_nn]
    calc (407139 / 60480) * h * |f tn2 yn2 - f tn2 zn2|
        ≤ (407139 / 60480) * h * (L * |yn2 - zn2|) :=
          mul_le_mul_of_nonneg_left hLip2 h407139_nn
      _ = (407139 / 60480) * h * L * |yn2 - zn2| := by ring
  have h134472_abs : |(134472 / 60480) * h * (f tn1 yn1 - f tn1 zn1)|
      ≤ (134472 / 60480) * h * L * |yn1 - zn1| := by
    rw [abs_mul, abs_of_nonneg h134472_nn]
    calc (134472 / 60480) * h * |f tn1 yn1 - f tn1 zn1|
        ≤ (134472 / 60480) * h * (L * |yn1 - zn1|) :=
          mul_le_mul_of_nonneg_left hLip1 h134472_nn
      _ = (134472 / 60480) * h * L * |yn1 - zn1| := by ring
  have h19087_abs : |(19087 / 60480) * h * (f tn yn - f tn zn)|
      ≤ (19087 / 60480) * h * L * |yn - zn| := by
    rw [abs_mul, abs_of_nonneg h19087_nn]
    calc (19087 / 60480) * h * |f tn yn - f tn zn|
        ≤ (19087 / 60480) * h * (L * |yn - zn|) :=
          mul_le_mul_of_nonneg_left hLip0 h19087_nn
      _ = (19087 / 60480) * h * L * |yn - zn| := by ring
  -- Triangle inequality (chained eight times).
  set S := (yn6 - zn6)
        + (198721 / 60480) * h * (f tn6 yn6 - f tn6 zn6)
        - (447288 / 60480) * h * (f tn5 yn5 - f tn5 zn5)
        + (705549 / 60480) * h * (f tn4 yn4 - f tn4 zn4)
        - (688256 / 60480) * h * (f tn3 yn3 - f tn3 zn3)
        + (407139 / 60480) * h * (f tn2 yn2 - f tn2 zn2)
        - (134472 / 60480) * h * (f tn1 yn1 - f tn1 zn1)
        + (19087 / 60480) * h * (f tn yn - f tn zn) with hS_def
  have hcalc : ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 7) - zn7 = S - τ := halg
  have htri_S : |S| ≤ |yn6 - zn6|
              + |(198721 / 60480) * h * (f tn6 yn6 - f tn6 zn6)|
              + |(447288 / 60480) * h * (f tn5 yn5 - f tn5 zn5)|
              + |(705549 / 60480) * h * (f tn4 yn4 - f tn4 zn4)|
              + |(688256 / 60480) * h * (f tn3 yn3 - f tn3 zn3)|
              + |(407139 / 60480) * h * (f tn2 yn2 - f tn2 zn2)|
              + |(134472 / 60480) * h * (f tn1 yn1 - f tn1 zn1)|
              + |(19087 / 60480) * h * (f tn yn - f tn zn)| := by
    have h1 : |(yn6 - zn6)
              + (198721 / 60480) * h * (f tn6 yn6 - f tn6 zn6)|
        ≤ |yn6 - zn6| + |(198721 / 60480) * h * (f tn6 yn6 - f tn6 zn6)| :=
      abs_add_le _ _
    have h2 : |(yn6 - zn6)
              + (198721 / 60480) * h * (f tn6 yn6 - f tn6 zn6)
              - (447288 / 60480) * h * (f tn5 yn5 - f tn5 zn5)|
        ≤ |(yn6 - zn6)
              + (198721 / 60480) * h * (f tn6 yn6 - f tn6 zn6)|
          + |(447288 / 60480) * h * (f tn5 yn5 - f tn5 zn5)| := abs_sub _ _
    have h3 : |(yn6 - zn6)
              + (198721 / 60480) * h * (f tn6 yn6 - f tn6 zn6)
              - (447288 / 60480) * h * (f tn5 yn5 - f tn5 zn5)
              + (705549 / 60480) * h * (f tn4 yn4 - f tn4 zn4)|
        ≤ |(yn6 - zn6)
              + (198721 / 60480) * h * (f tn6 yn6 - f tn6 zn6)
              - (447288 / 60480) * h * (f tn5 yn5 - f tn5 zn5)|
          + |(705549 / 60480) * h * (f tn4 yn4 - f tn4 zn4)| := abs_add_le _ _
    have h4 : |(yn6 - zn6)
              + (198721 / 60480) * h * (f tn6 yn6 - f tn6 zn6)
              - (447288 / 60480) * h * (f tn5 yn5 - f tn5 zn5)
              + (705549 / 60480) * h * (f tn4 yn4 - f tn4 zn4)
              - (688256 / 60480) * h * (f tn3 yn3 - f tn3 zn3)|
        ≤ |(yn6 - zn6)
              + (198721 / 60480) * h * (f tn6 yn6 - f tn6 zn6)
              - (447288 / 60480) * h * (f tn5 yn5 - f tn5 zn5)
              + (705549 / 60480) * h * (f tn4 yn4 - f tn4 zn4)|
          + |(688256 / 60480) * h * (f tn3 yn3 - f tn3 zn3)| := abs_sub _ _
    have h5 : |(yn6 - zn6)
              + (198721 / 60480) * h * (f tn6 yn6 - f tn6 zn6)
              - (447288 / 60480) * h * (f tn5 yn5 - f tn5 zn5)
              + (705549 / 60480) * h * (f tn4 yn4 - f tn4 zn4)
              - (688256 / 60480) * h * (f tn3 yn3 - f tn3 zn3)
              + (407139 / 60480) * h * (f tn2 yn2 - f tn2 zn2)|
        ≤ |(yn6 - zn6)
              + (198721 / 60480) * h * (f tn6 yn6 - f tn6 zn6)
              - (447288 / 60480) * h * (f tn5 yn5 - f tn5 zn5)
              + (705549 / 60480) * h * (f tn4 yn4 - f tn4 zn4)
              - (688256 / 60480) * h * (f tn3 yn3 - f tn3 zn3)|
          + |(407139 / 60480) * h * (f tn2 yn2 - f tn2 zn2)| := abs_add_le _ _
    have h6 : |(yn6 - zn6)
              + (198721 / 60480) * h * (f tn6 yn6 - f tn6 zn6)
              - (447288 / 60480) * h * (f tn5 yn5 - f tn5 zn5)
              + (705549 / 60480) * h * (f tn4 yn4 - f tn4 zn4)
              - (688256 / 60480) * h * (f tn3 yn3 - f tn3 zn3)
              + (407139 / 60480) * h * (f tn2 yn2 - f tn2 zn2)
              - (134472 / 60480) * h * (f tn1 yn1 - f tn1 zn1)|
        ≤ |(yn6 - zn6)
              + (198721 / 60480) * h * (f tn6 yn6 - f tn6 zn6)
              - (447288 / 60480) * h * (f tn5 yn5 - f tn5 zn5)
              + (705549 / 60480) * h * (f tn4 yn4 - f tn4 zn4)
              - (688256 / 60480) * h * (f tn3 yn3 - f tn3 zn3)
              + (407139 / 60480) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(134472 / 60480) * h * (f tn1 yn1 - f tn1 zn1)| := abs_sub _ _
    have h7 : |S| ≤ |(yn6 - zn6)
              + (198721 / 60480) * h * (f tn6 yn6 - f tn6 zn6)
              - (447288 / 60480) * h * (f tn5 yn5 - f tn5 zn5)
              + (705549 / 60480) * h * (f tn4 yn4 - f tn4 zn4)
              - (688256 / 60480) * h * (f tn3 yn3 - f tn3 zn3)
              + (407139 / 60480) * h * (f tn2 yn2 - f tn2 zn2)
              - (134472 / 60480) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(19087 / 60480) * h * (f tn yn - f tn zn)| := by
      show |_| ≤ _
      exact abs_add_le _ _
    linarith
  have htri : |S - τ| ≤ |S| + |τ| := abs_sub _ _
  calc |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 7) - zn7|
      = |S - τ| := by rw [hcalc]
    _ ≤ |S| + |τ| := htri
    _ ≤ |yn6 - zn6|
          + |(198721 / 60480) * h * (f tn6 yn6 - f tn6 zn6)|
          + |(447288 / 60480) * h * (f tn5 yn5 - f tn5 zn5)|
          + |(705549 / 60480) * h * (f tn4 yn4 - f tn4 zn4)|
          + |(688256 / 60480) * h * (f tn3 yn3 - f tn3 zn3)|
          + |(407139 / 60480) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(134472 / 60480) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(19087 / 60480) * h * (f tn yn - f tn zn)|
          + |τ| := by linarith
    _ ≤ |yn6 - zn6|
          + (198721 / 60480) * h * L * |yn6 - zn6|
          + (447288 / 60480) * h * L * |yn5 - zn5|
          + (705549 / 60480) * h * L * |yn4 - zn4|
          + (688256 / 60480) * h * L * |yn3 - zn3|
          + (407139 / 60480) * h * L * |yn2 - zn2|
          + (134472 / 60480) * h * L * |yn1 - zn1|
          + (19087 / 60480) * h * L * |yn - zn|
          + |τ| := by
        linarith [h198721_abs, h447288_abs, h705549_abs, h688256_abs,
          h407139_abs, h134472_abs, h19087_abs]

/-- Max-norm one-step error recurrence for AB7 with Lipschitz constant
`L`. With `eN k := |y_k − y(t_k)|` and a 7-window max
`EN k := max (eN k, eN (k+1), …, eN (k+6))`,
`EN (n+1) ≤ (1 + h · (40633/945) · L) · EN n + |τ_n|`. The `(40633/945)`
factor is `2600512/60480`, the ℓ¹-norm of the AB7 coefficient vector. -/
theorem ab7_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ : ℝ) (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max (max (max (max (max
          |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
          |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|)
          |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|)
          |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|)
          |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|)
          |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|)
        |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)|
      ≤ (1 + h * ((40633 / 945) * L))
            * max (max (max (max (max (max
                  |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ n
                      - y (t₀ + (n : ℝ) * h)|
                  |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 1)
                      - y (t₀ + ((n : ℝ) + 1) * h)|)
                  |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 2)
                      - y (t₀ + ((n : ℝ) + 2) * h)|)
                  |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 3)
                      - y (t₀ + ((n : ℝ) + 3) * h)|)
                  |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 4)
                      - y (t₀ + ((n : ℝ) + 4) * h)|)
                  |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 5)
                      - y (t₀ + ((n : ℝ) + 5) * h)|)
                  |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 6)
                      - y (t₀ + ((n : ℝ) + 6) * h)|
        + |adamsBashforth7.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set en : ℝ := |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ n - y (t₀ + (n : ℝ) * h)|
    with hen_def
  set en1 : ℝ :=
    |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
    with hen1_def
  set en2 : ℝ :=
    |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|
    with hen2_def
  set en3 : ℝ :=
    |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|
    with hen3_def
  set en4 : ℝ :=
    |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|
    with hen4_def
  set en5 : ℝ :=
    |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|
    with hen5_def
  set en6 : ℝ :=
    |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|
    with hen6_def
  set en7 : ℝ :=
    |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)|
    with hen7_def
  set τabs : ℝ :=
    |adamsBashforth7.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  have hen_nn : 0 ≤ en := abs_nonneg _
  have hen1_nn : 0 ≤ en1 := abs_nonneg _
  have hen2_nn : 0 ≤ en2 := abs_nonneg _
  have hen3_nn : 0 ≤ en3 := abs_nonneg _
  have hen4_nn : 0 ≤ en4 := abs_nonneg _
  have hen5_nn : 0 ≤ en5 := abs_nonneg _
  have hen6_nn : 0 ≤ en6 := abs_nonneg _
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  -- One-step Lipschitz bound (from `ab7_one_step_lipschitz`).
  have hstep :
      en7 ≤ en6 + (198721 / 60480) * h * L * en6
                + (447288 / 60480) * h * L * en5
                + (705549 / 60480) * h * L * en4
                + (688256 / 60480) * h * L * en3
                + (407139 / 60480) * h * L * en2
                + (134472 / 60480) * h * L * en1
                + (19087 / 60480) * h * L * en + τabs := by
    have := ab7_one_step_lipschitz hh hf t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y hyf n
    show |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)|
        ≤ |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|
          + (198721 / 60480) * h * L
              * |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 6)
                  - y (t₀ + ((n : ℝ) + 6) * h)|
          + (447288 / 60480) * h * L
              * |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 5)
                  - y (t₀ + ((n : ℝ) + 5) * h)|
          + (705549 / 60480) * h * L
              * |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 4)
                  - y (t₀ + ((n : ℝ) + 4) * h)|
          + (688256 / 60480) * h * L
              * |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 3)
                  - y (t₀ + ((n : ℝ) + 3) * h)|
          + (407139 / 60480) * h * L
              * |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 2)
                  - y (t₀ + ((n : ℝ) + 2) * h)|
          + (134472 / 60480) * h * L
              * |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ (n + 1)
                  - y (t₀ + ((n : ℝ) + 1) * h)|
          + (19087 / 60480) * h * L
              * |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ n - y (t₀ + (n : ℝ) * h)|
          + |adamsBashforth7.localTruncationError h (t₀ + (n : ℝ) * h) y|
    exact this
  set EN_n : ℝ := max (max (max (max (max (max en en1) en2) en3) en4) en5) en6
    with hEN_n_def
  have hen_le_EN : en ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left _ _)
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)
  have hen1_le_EN : en1 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_max_right _ _)
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)
  have hen2_le_EN : en2 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_max_right _ _)
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)
  have hen3_le_EN : en3 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)
  have hen4_le_EN : en4 ≤ EN_n :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hen5_le_EN : en5 ≤ EN_n :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hen6_le_EN : en6 ≤ EN_n := le_max_right _ _
  have h198721_nn : 0 ≤ (198721 / 60480) * h * L := by positivity
  have h447288_nn : 0 ≤ (447288 / 60480) * h * L := by positivity
  have h705549_nn : 0 ≤ (705549 / 60480) * h * L := by positivity
  have h688256_nn : 0 ≤ (688256 / 60480) * h * L := by positivity
  have h407139_nn : 0 ≤ (407139 / 60480) * h * L := by positivity
  have h134472_nn : 0 ≤ (134472 / 60480) * h * L := by positivity
  have h19087_nn : 0 ≤ (19087 / 60480) * h * L := by positivity
  have hEN_nn : 0 ≤ EN_n := le_trans hen_nn hen_le_EN
  have hcoef_nn : 0 ≤ h * ((40633 / 945) * L) := by positivity
  have hen7_bd : en7 ≤ (1 + h * ((40633 / 945) * L)) * EN_n + τabs := by
    have h1 : (198721 / 60480) * h * L * en6 ≤ (198721 / 60480) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen6_le_EN h198721_nn
    have h2 : (447288 / 60480) * h * L * en5 ≤ (447288 / 60480) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen5_le_EN h447288_nn
    have h3 : (705549 / 60480) * h * L * en4 ≤ (705549 / 60480) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen4_le_EN h705549_nn
    have h4 : (688256 / 60480) * h * L * en3 ≤ (688256 / 60480) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen3_le_EN h688256_nn
    have h5 : (407139 / 60480) * h * L * en2 ≤ (407139 / 60480) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen2_le_EN h407139_nn
    have h6 : (134472 / 60480) * h * L * en1 ≤ (134472 / 60480) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen1_le_EN h134472_nn
    have h7 : (19087 / 60480) * h * L * en ≤ (19087 / 60480) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen_le_EN h19087_nn
    have h_alg :
        EN_n + (198721 / 60480) * h * L * EN_n
              + (447288 / 60480) * h * L * EN_n
              + (705549 / 60480) * h * L * EN_n
              + (688256 / 60480) * h * L * EN_n
              + (407139 / 60480) * h * L * EN_n
              + (134472 / 60480) * h * L * EN_n
              + (19087 / 60480) * h * L * EN_n + τabs
          = (1 + h * ((40633 / 945) * L)) * EN_n + τabs := by ring
    linarith [hstep, hen6_le_EN, h1, h2, h3, h4, h5, h6, h7, h_alg.le]
  have hEN_le_grow : EN_n ≤ (1 + h * ((40633 / 945) * L)) * EN_n := by
    have hone : (1 : ℝ) * EN_n ≤ (1 + h * ((40633 / 945) * L)) * EN_n :=
      mul_le_mul_of_nonneg_right (by linarith) hEN_nn
    linarith
  have hen1_bd : en1 ≤ (1 + h * ((40633 / 945) * L)) * EN_n + τabs := by
    linarith [hen1_le_EN, hEN_le_grow]
  have hen2_bd : en2 ≤ (1 + h * ((40633 / 945) * L)) * EN_n + τabs := by
    linarith [hen2_le_EN, hEN_le_grow]
  have hen3_bd : en3 ≤ (1 + h * ((40633 / 945) * L)) * EN_n + τabs := by
    linarith [hen3_le_EN, hEN_le_grow]
  have hen4_bd : en4 ≤ (1 + h * ((40633 / 945) * L)) * EN_n + τabs := by
    linarith [hen4_le_EN, hEN_le_grow]
  have hen5_bd : en5 ≤ (1 + h * ((40633 / 945) * L)) * EN_n + τabs := by
    linarith [hen5_le_EN, hEN_le_grow]
  have hen6_bd : en6 ≤ (1 + h * ((40633 / 945) * L)) * EN_n + τabs := by
    linarith [hen6_le_EN, hEN_le_grow]
  exact max_le (max_le (max_le (max_le (max_le (max_le hen1_bd hen2_bd) hen3_bd)
    hen4_bd) hen5_bd) hen6_bd) hen7_bd

/-- Pure algebraic identity: the AB7 residual rewrites as a signed sum of
eight Taylor remainders. Extracted as a stand-alone lemma so the kernel
checks the (large) `ring` proof term in isolation. -/
private lemma ab7_residual_alg_identity
    (y0 y6 y7 d0 d1 d2 d3 d4 d5 d6 dd ddd dddd ddddd dddddd ddddddd h : ℝ) :
    y7 - y6 - h * ((198721 / 60480) * d6 - (447288 / 60480) * d5
                  + (705549 / 60480) * d4 - (688256 / 60480) * d3
                  + (407139 / 60480) * d2 - (134472 / 60480) * d1
                  + (19087 / 60480) * d0)
      = (y7 - y0 - (7 * h) * d0
            - (7 * h) ^ 2 / 2 * dd
            - (7 * h) ^ 3 / 6 * ddd
            - (7 * h) ^ 4 / 24 * dddd
            - (7 * h) ^ 5 / 120 * ddddd
            - (7 * h) ^ 6 / 720 * dddddd
            - (7 * h) ^ 7 / 5040 * ddddddd)
        - (y6 - y0 - (6 * h) * d0
            - (6 * h) ^ 2 / 2 * dd
            - (6 * h) ^ 3 / 6 * ddd
            - (6 * h) ^ 4 / 24 * dddd
            - (6 * h) ^ 5 / 120 * ddddd
            - (6 * h) ^ 6 / 720 * dddddd
            - (6 * h) ^ 7 / 5040 * ddddddd)
        - (198721 * h / 60480)
            * (d6 - d0 - (6 * h) * dd
                - (6 * h) ^ 2 / 2 * ddd
                - (6 * h) ^ 3 / 6 * dddd
                - (6 * h) ^ 4 / 24 * ddddd
                - (6 * h) ^ 5 / 120 * dddddd
                - (6 * h) ^ 6 / 720 * ddddddd)
        + (447288 * h / 60480)
            * (d5 - d0 - (5 * h) * dd
                - (5 * h) ^ 2 / 2 * ddd
                - (5 * h) ^ 3 / 6 * dddd
                - (5 * h) ^ 4 / 24 * ddddd
                - (5 * h) ^ 5 / 120 * dddddd
                - (5 * h) ^ 6 / 720 * ddddddd)
        - (705549 * h / 60480)
            * (d4 - d0 - (4 * h) * dd
                - (4 * h) ^ 2 / 2 * ddd
                - (4 * h) ^ 3 / 6 * dddd
                - (4 * h) ^ 4 / 24 * ddddd
                - (4 * h) ^ 5 / 120 * dddddd
                - (4 * h) ^ 6 / 720 * ddddddd)
        + (688256 * h / 60480)
            * (d3 - d0 - (3 * h) * dd
                - (3 * h) ^ 2 / 2 * ddd
                - (3 * h) ^ 3 / 6 * dddd
                - (3 * h) ^ 4 / 24 * ddddd
                - (3 * h) ^ 5 / 120 * dddddd
                - (3 * h) ^ 6 / 720 * ddddddd)
        - (407139 * h / 60480)
            * (d2 - d0 - (2 * h) * dd
                - (2 * h) ^ 2 / 2 * ddd
                - (2 * h) ^ 3 / 6 * dddd
                - (2 * h) ^ 4 / 24 * ddddd
                - (2 * h) ^ 5 / 120 * dddddd
                - (2 * h) ^ 6 / 720 * ddddddd)
        + (134472 * h / 60480)
            * (d1 - d0 - h * dd
                - h ^ 2 / 2 * ddd
                - h ^ 3 / 6 * dddd
                - h ^ 4 / 24 * ddddd
                - h ^ 5 / 120 * dddddd
                - h ^ 6 / 720 * ddddddd) := by
  ring

/-- Pure algebraic identity: the sum of the eight scaled Lagrange
remainder bounds equals a fixed rational coefficient times `M · h^8`. -/
private lemma ab7_residual_bound_alg_identity (M h : ℝ) :
    M / 40320 * (7 * h) ^ 8 + M / 40320 * (6 * h) ^ 8
      + (198721 * h / 60480) * (M / 5040 * (6 * h) ^ 7)
      + (447288 * h / 60480) * (M / 5040 * (5 * h) ^ 7)
      + (705549 * h / 60480) * (M / 5040 * (4 * h) ^ 7)
      + (688256 * h / 60480) * (M / 5040 * (3 * h) ^ 7)
      + (407139 * h / 60480) * (M / 5040 * (2 * h) ^ 7)
      + (134472 * h / 60480) * (M / 5040 * h ^ 7)
      = (159970508328 / 304819200 : ℝ) * M * h ^ 8 := by
  ring

/-- Triangle inequality for the eight-term AB7 residual chunk. -/
private lemma ab7_residual_eight_term_triangle
    (A B C D E F G H h : ℝ) (hh : 0 ≤ h) :
    |A - B - (198721 * h / 60480) * C + (447288 * h / 60480) * D
        - (705549 * h / 60480) * E + (688256 * h / 60480) * F
        - (407139 * h / 60480) * G + (134472 * h / 60480) * H|
      ≤ |A| + |B| + (198721 * h / 60480) * |C| + (447288 * h / 60480) * |D|
          + (705549 * h / 60480) * |E| + (688256 * h / 60480) * |F|
          + (407139 * h / 60480) * |G| + (134472 * h / 60480) * |H| := by
  have h198721h_nn : 0 ≤ 198721 * h / 60480 := by linarith
  have h447288h_nn : 0 ≤ 447288 * h / 60480 := by linarith
  have h705549h_nn : 0 ≤ 705549 * h / 60480 := by linarith
  have h688256h_nn : 0 ≤ 688256 * h / 60480 := by linarith
  have h407139h_nn : 0 ≤ 407139 * h / 60480 := by linarith
  have h134472h_nn : 0 ≤ 134472 * h / 60480 := by linarith
  have habs198721 : |(198721 * h / 60480) * C| = (198721 * h / 60480) * |C| := by
    rw [abs_mul, abs_of_nonneg h198721h_nn]
  have habs447288 : |(447288 * h / 60480) * D| = (447288 * h / 60480) * |D| := by
    rw [abs_mul, abs_of_nonneg h447288h_nn]
  have habs705549 : |(705549 * h / 60480) * E| = (705549 * h / 60480) * |E| := by
    rw [abs_mul, abs_of_nonneg h705549h_nn]
  have habs688256 : |(688256 * h / 60480) * F| = (688256 * h / 60480) * |F| := by
    rw [abs_mul, abs_of_nonneg h688256h_nn]
  have habs407139 : |(407139 * h / 60480) * G| = (407139 * h / 60480) * |G| := by
    rw [abs_mul, abs_of_nonneg h407139h_nn]
  have habs134472 : |(134472 * h / 60480) * H| = (134472 * h / 60480) * |H| := by
    rw [abs_mul, abs_of_nonneg h134472h_nn]
  have h1 : |A - B - (198721 * h / 60480) * C + (447288 * h / 60480) * D
                - (705549 * h / 60480) * E + (688256 * h / 60480) * F
                - (407139 * h / 60480) * G + (134472 * h / 60480) * H|
      ≤ |A - B - (198721 * h / 60480) * C + (447288 * h / 60480) * D
            - (705549 * h / 60480) * E + (688256 * h / 60480) * F
            - (407139 * h / 60480) * G|
        + |(134472 * h / 60480) * H| := abs_add_le _ _
  have h2 : |A - B - (198721 * h / 60480) * C + (447288 * h / 60480) * D
                - (705549 * h / 60480) * E + (688256 * h / 60480) * F
                - (407139 * h / 60480) * G|
      ≤ |A - B - (198721 * h / 60480) * C + (447288 * h / 60480) * D
            - (705549 * h / 60480) * E + (688256 * h / 60480) * F|
        + |(407139 * h / 60480) * G| := abs_sub _ _
  have h3 : |A - B - (198721 * h / 60480) * C + (447288 * h / 60480) * D
                - (705549 * h / 60480) * E + (688256 * h / 60480) * F|
      ≤ |A - B - (198721 * h / 60480) * C + (447288 * h / 60480) * D
            - (705549 * h / 60480) * E|
        + |(688256 * h / 60480) * F| := abs_add_le _ _
  have h4 : |A - B - (198721 * h / 60480) * C + (447288 * h / 60480) * D
                - (705549 * h / 60480) * E|
      ≤ |A - B - (198721 * h / 60480) * C + (447288 * h / 60480) * D|
        + |(705549 * h / 60480) * E| := abs_sub _ _
  have h5 : |A - B - (198721 * h / 60480) * C + (447288 * h / 60480) * D|
      ≤ |A - B - (198721 * h / 60480) * C| + |(447288 * h / 60480) * D| :=
    abs_add_le _ _
  have h6 : |A - B - (198721 * h / 60480) * C|
      ≤ |A - B| + |(198721 * h / 60480) * C| := abs_sub _ _
  have h7 : |A - B| ≤ |A| + |B| := abs_sub _ _
  linarith [habs198721.le, habs198721.ge, habs447288.le, habs447288.ge,
    habs705549.le, habs705549.ge, habs688256.le, habs688256.ge,
    habs407139.le, habs407139.ge, habs134472.le, habs134472.ge]

/-- Pointwise AB7 truncation residual bound. The textbook AB7 residual
expands as
`R_y(7) − R_y(6) − (198721h/60480)·R_y'(6) + (447288h/60480)·R_y'(5)
  − (705549h/60480)·R_y'(4) + (688256h/60480)·R_y'(3)
  − (407139h/60480)·R_y'(2) + (134472h/60480)·R_y'(1)`,
with `R_y'(0) = 0`. The combined coefficient is
`159970508328/304819200 ≤ 525`. -/
private theorem ab7_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 8 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 8 y t| ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (ht4h : t + 4 * h ∈ Set.Icc a b)
    (ht5h : t + 5 * h ∈ Set.Icc a b)
    (ht6h : t + 6 * h ∈ Set.Icc a b)
    (ht7h : t + 7 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    |y (t + 7 * h) - y (t + 6 * h)
        - h * ((198721 / 60480) * deriv y (t + 6 * h)
              - (447288 / 60480) * deriv y (t + 5 * h)
              + (705549 / 60480) * deriv y (t + 4 * h)
              - (688256 / 60480) * deriv y (t + 3 * h)
              + (407139 / 60480) * deriv y (t + 2 * h)
              - (134472 / 60480) * deriv y (t + h)
              + (19087 / 60480) * deriv y t)|
      ≤ (525 : ℝ) * M * h ^ 8 := by
  -- Eight Taylor remainders.
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have h5h : 0 ≤ 5 * h := by linarith
  have h6h : 0 ≤ 6 * h := by linarith
  have h7h : 0 ≤ 7 * h := by linarith
  -- R_y(6), R_y(7): y Taylor remainders at order 8.
  have hRy6 :=
    y_eighth_order_taylor_remainder hy hbnd ht ht6h h6h
  have hRy7 :=
    y_eighth_order_taylor_remainder hy hbnd ht ht7h h7h
  -- R_y'(1), …, R_y'(6): y' Taylor remainders at order 7.
  have hRyp1 :=
    derivY_seventh_order_taylor_remainder hy hbnd ht hth hh
  have hRyp2 :=
    derivY_seventh_order_taylor_remainder hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_seventh_order_taylor_remainder hy hbnd ht ht3h h3h
  have hRyp4 :=
    derivY_seventh_order_taylor_remainder hy hbnd ht ht4h h4h
  have hRyp5 :=
    derivY_seventh_order_taylor_remainder hy hbnd ht ht5h h5h
  have hRyp6 :=
    derivY_seventh_order_taylor_remainder hy hbnd ht ht6h h6h
  -- Abbreviations.
  set y0 := y t with hy0_def
  set y6 := y (t + 6 * h) with hy6_def
  set y7 := y (t + 7 * h) with hy7_def
  set d0 := deriv y t with hd0_def
  set d1 := deriv y (t + h) with hd1_def
  set d2 := deriv y (t + 2 * h) with hd2_def
  set d3 := deriv y (t + 3 * h) with hd3_def
  set d4 := deriv y (t + 4 * h) with hd4_def
  set d5 := deriv y (t + 5 * h) with hd5_def
  set d6 := deriv y (t + 6 * h) with hd6_def
  set dd := iteratedDeriv 2 y t with hdd_def
  set ddd := iteratedDeriv 3 y t with hddd_def
  set dddd := iteratedDeriv 4 y t with hdddd_def
  set ddddd := iteratedDeriv 5 y t with hddddd_def
  set dddddd := iteratedDeriv 6 y t with hdddddd_def
  set ddddddd := iteratedDeriv 7 y t with hddddddd_def
  clear_value y0 y6 y7 d0 d1 d2 d3 d4 d5 d6 dd ddd dddd ddddd dddddd ddddddd
  -- Algebraic identity for the residual.
  have hLTE_eq :
      y7 - y6 - h * ((198721 / 60480) * d6 - (447288 / 60480) * d5
                    + (705549 / 60480) * d4 - (688256 / 60480) * d3
                    + (407139 / 60480) * d2 - (134472 / 60480) * d1
                    + (19087 / 60480) * d0)
        = (y7 - y0 - (7 * h) * d0
              - (7 * h) ^ 2 / 2 * dd
              - (7 * h) ^ 3 / 6 * ddd
              - (7 * h) ^ 4 / 24 * dddd
              - (7 * h) ^ 5 / 120 * ddddd
              - (7 * h) ^ 6 / 720 * dddddd
              - (7 * h) ^ 7 / 5040 * ddddddd)
          - (y6 - y0 - (6 * h) * d0
              - (6 * h) ^ 2 / 2 * dd
              - (6 * h) ^ 3 / 6 * ddd
              - (6 * h) ^ 4 / 24 * dddd
              - (6 * h) ^ 5 / 120 * ddddd
              - (6 * h) ^ 6 / 720 * dddddd
              - (6 * h) ^ 7 / 5040 * ddddddd)
          - (198721 * h / 60480)
              * (d6 - d0 - (6 * h) * dd
                  - (6 * h) ^ 2 / 2 * ddd
                  - (6 * h) ^ 3 / 6 * dddd
                  - (6 * h) ^ 4 / 24 * ddddd
                  - (6 * h) ^ 5 / 120 * dddddd
                  - (6 * h) ^ 6 / 720 * ddddddd)
          + (447288 * h / 60480)
              * (d5 - d0 - (5 * h) * dd
                  - (5 * h) ^ 2 / 2 * ddd
                  - (5 * h) ^ 3 / 6 * dddd
                  - (5 * h) ^ 4 / 24 * ddddd
                  - (5 * h) ^ 5 / 120 * dddddd
                  - (5 * h) ^ 6 / 720 * ddddddd)
          - (705549 * h / 60480)
              * (d4 - d0 - (4 * h) * dd
                  - (4 * h) ^ 2 / 2 * ddd
                  - (4 * h) ^ 3 / 6 * dddd
                  - (4 * h) ^ 4 / 24 * ddddd
                  - (4 * h) ^ 5 / 120 * dddddd
                  - (4 * h) ^ 6 / 720 * ddddddd)
          + (688256 * h / 60480)
              * (d3 - d0 - (3 * h) * dd
                  - (3 * h) ^ 2 / 2 * ddd
                  - (3 * h) ^ 3 / 6 * dddd
                  - (3 * h) ^ 4 / 24 * ddddd
                  - (3 * h) ^ 5 / 120 * dddddd
                  - (3 * h) ^ 6 / 720 * ddddddd)
          - (407139 * h / 60480)
              * (d2 - d0 - (2 * h) * dd
                  - (2 * h) ^ 2 / 2 * ddd
                  - (2 * h) ^ 3 / 6 * dddd
                  - (2 * h) ^ 4 / 24 * ddddd
                  - (2 * h) ^ 5 / 120 * dddddd
                  - (2 * h) ^ 6 / 720 * ddddddd)
          + (134472 * h / 60480)
              * (d1 - d0 - h * dd
                  - h ^ 2 / 2 * ddd
                  - h ^ 3 / 6 * dddd
                  - h ^ 4 / 24 * ddddd
                  - h ^ 5 / 120 * dddddd
                  - h ^ 6 / 720 * ddddddd) :=
    ab7_residual_alg_identity y0 y6 y7 d0 d1 d2 d3 d4 d5 d6
      dd ddd dddd ddddd dddddd ddddddd h
  rw [hLTE_eq]
  -- Triangle inequality (chained).
  set A := y7 - y0 - (7 * h) * d0
            - (7 * h) ^ 2 / 2 * dd
            - (7 * h) ^ 3 / 6 * ddd
            - (7 * h) ^ 4 / 24 * dddd
            - (7 * h) ^ 5 / 120 * ddddd
            - (7 * h) ^ 6 / 720 * dddddd
            - (7 * h) ^ 7 / 5040 * ddddddd with hA_def
  set B := y6 - y0 - (6 * h) * d0
            - (6 * h) ^ 2 / 2 * dd
            - (6 * h) ^ 3 / 6 * ddd
            - (6 * h) ^ 4 / 24 * dddd
            - (6 * h) ^ 5 / 120 * ddddd
            - (6 * h) ^ 6 / 720 * dddddd
            - (6 * h) ^ 7 / 5040 * ddddddd with hB_def
  set C := d6 - d0 - (6 * h) * dd
            - (6 * h) ^ 2 / 2 * ddd
            - (6 * h) ^ 3 / 6 * dddd
            - (6 * h) ^ 4 / 24 * ddddd
            - (6 * h) ^ 5 / 120 * dddddd
            - (6 * h) ^ 6 / 720 * ddddddd with hC_def
  set D := d5 - d0 - (5 * h) * dd
            - (5 * h) ^ 2 / 2 * ddd
            - (5 * h) ^ 3 / 6 * dddd
            - (5 * h) ^ 4 / 24 * ddddd
            - (5 * h) ^ 5 / 120 * dddddd
            - (5 * h) ^ 6 / 720 * ddddddd with hD_def
  set E := d4 - d0 - (4 * h) * dd
            - (4 * h) ^ 2 / 2 * ddd
            - (4 * h) ^ 3 / 6 * dddd
            - (4 * h) ^ 4 / 24 * ddddd
            - (4 * h) ^ 5 / 120 * dddddd
            - (4 * h) ^ 6 / 720 * ddddddd with hE_def
  set F := d3 - d0 - (3 * h) * dd
            - (3 * h) ^ 2 / 2 * ddd
            - (3 * h) ^ 3 / 6 * dddd
            - (3 * h) ^ 4 / 24 * ddddd
            - (3 * h) ^ 5 / 120 * dddddd
            - (3 * h) ^ 6 / 720 * ddddddd with hF_def
  set G := d2 - d0 - (2 * h) * dd
            - (2 * h) ^ 2 / 2 * ddd
            - (2 * h) ^ 3 / 6 * dddd
            - (2 * h) ^ 4 / 24 * ddddd
            - (2 * h) ^ 5 / 120 * dddddd
            - (2 * h) ^ 6 / 720 * ddddddd with hG_def
  set H := d1 - d0 - h * dd
            - h ^ 2 / 2 * ddd
            - h ^ 3 / 6 * dddd
            - h ^ 4 / 24 * ddddd
            - h ^ 5 / 120 * dddddd
            - h ^ 6 / 720 * ddddddd with hH_def
  clear_value A B C D E F G H
  have h198721h_nn : 0 ≤ 198721 * h / 60480 := by linarith
  have h447288h_nn : 0 ≤ 447288 * h / 60480 := by linarith
  have h705549h_nn : 0 ≤ 705549 * h / 60480 := by linarith
  have h688256h_nn : 0 ≤ 688256 * h / 60480 := by linarith
  have h407139h_nn : 0 ≤ 407139 * h / 60480 := by linarith
  have h134472h_nn : 0 ≤ 134472 * h / 60480 := by linarith
  have htri := ab7_residual_eight_term_triangle A B C D E F G H h hh
  -- Bounds on each piece.
  have hA_bd : |A| ≤ M / 40320 * (7 * h) ^ 8 := hRy7
  have hB_bd : |B| ≤ M / 40320 * (6 * h) ^ 8 := hRy6
  have hC_bd : |C| ≤ M / 5040 * (6 * h) ^ 7 := hRyp6
  have hD_bd : |D| ≤ M / 5040 * (5 * h) ^ 7 := hRyp5
  have hE_bd : |E| ≤ M / 5040 * (4 * h) ^ 7 := hRyp4
  have hF_bd : |F| ≤ M / 5040 * (3 * h) ^ 7 := hRyp3
  have hG_bd : |G| ≤ M / 5040 * (2 * h) ^ 7 := hRyp2
  have hH_bd : |H| ≤ M / 5040 * h ^ 7 := hRyp1
  -- Multiply scaled bounds.
  have h198721C_bd : (198721 * h / 60480) * |C|
      ≤ (198721 * h / 60480) * (M / 5040 * (6 * h) ^ 7) :=
    mul_le_mul_of_nonneg_left hC_bd h198721h_nn
  have h447288D_bd : (447288 * h / 60480) * |D|
      ≤ (447288 * h / 60480) * (M / 5040 * (5 * h) ^ 7) :=
    mul_le_mul_of_nonneg_left hD_bd h447288h_nn
  have h705549E_bd : (705549 * h / 60480) * |E|
      ≤ (705549 * h / 60480) * (M / 5040 * (4 * h) ^ 7) :=
    mul_le_mul_of_nonneg_left hE_bd h705549h_nn
  have h688256F_bd : (688256 * h / 60480) * |F|
      ≤ (688256 * h / 60480) * (M / 5040 * (3 * h) ^ 7) :=
    mul_le_mul_of_nonneg_left hF_bd h688256h_nn
  have h407139G_bd : (407139 * h / 60480) * |G|
      ≤ (407139 * h / 60480) * (M / 5040 * (2 * h) ^ 7) :=
    mul_le_mul_of_nonneg_left hG_bd h407139h_nn
  have h134472H_bd : (134472 * h / 60480) * |H|
      ≤ (134472 * h / 60480) * (M / 5040 * h ^ 7) :=
    mul_le_mul_of_nonneg_left hH_bd h134472h_nn
  -- Sum of upper bounds equals (159970508328/304819200) · M · h^8 ≤ 525 · M · h^8.
  have hbound_alg :
      M / 40320 * (7 * h) ^ 8 + M / 40320 * (6 * h) ^ 8
        + (198721 * h / 60480) * (M / 5040 * (6 * h) ^ 7)
        + (447288 * h / 60480) * (M / 5040 * (5 * h) ^ 7)
        + (705549 * h / 60480) * (M / 5040 * (4 * h) ^ 7)
        + (688256 * h / 60480) * (M / 5040 * (3 * h) ^ 7)
        + (407139 * h / 60480) * (M / 5040 * (2 * h) ^ 7)
        + (134472 * h / 60480) * (M / 5040 * h ^ 7)
        = (159970508328 / 304819200 : ℝ) * M * h ^ 8 :=
    ab7_residual_bound_alg_identity M h
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (abs_nonneg _).trans this
  have hh8_nn : 0 ≤ h ^ 8 := by positivity
  have hMh8_nn : 0 ≤ M * h ^ 8 := mul_nonneg hMnn hh8_nn
  have hslack : (159970508328 / 304819200 : ℝ) * M * h ^ 8 ≤ 525 * M * h ^ 8 := by
    rw [mul_assoc, mul_assoc (525 : ℝ)]
    have hle : (159970508328 / 304819200 : ℝ) ≤ 525 := by norm_num
    exact mul_le_mul_of_nonneg_right hle hMh8_nn
  calc |A - B - (198721 * h / 60480) * C + (447288 * h / 60480) * D
            - (705549 * h / 60480) * E + (688256 * h / 60480) * F
            - (407139 * h / 60480) * G + (134472 * h / 60480) * H|
      ≤ |A| + |B| + (198721 * h / 60480) * |C| + (447288 * h / 60480) * |D|
          + (705549 * h / 60480) * |E| + (688256 * h / 60480) * |F|
          + (407139 * h / 60480) * |G| + (134472 * h / 60480) * |H| := htri
    _ ≤ M / 40320 * (7 * h) ^ 8 + M / 40320 * (6 * h) ^ 8
          + (198721 * h / 60480) * (M / 5040 * (6 * h) ^ 7)
          + (447288 * h / 60480) * (M / 5040 * (5 * h) ^ 7)
          + (705549 * h / 60480) * (M / 5040 * (4 * h) ^ 7)
          + (688256 * h / 60480) * (M / 5040 * (3 * h) ^ 7)
          + (407139 * h / 60480) * (M / 5040 * (2 * h) ^ 7)
          + (134472 * h / 60480) * (M / 5040 * h ^ 7) := by
        linarith [hA_bd, hB_bd, h198721C_bd, h447288D_bd, h705549E_bd,
          h688256F_bd, h407139G_bd, h134472H_bd]
    _ = (159970508328 / 304819200 : ℝ) * M * h ^ 8 := hbound_alg
    _ ≤ 525 * M * h ^ 8 := hslack

/-- Uniform bound on the AB7 one-step truncation residual on a finite
horizon, given a `C^8` exact solution. -/
theorem ab7_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 8 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 7) * h ≤ T →
        |adamsBashforth7.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 8 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_eight_bounded_on_Icc hy t₀ (t₀ + T + 1)
  refine ⟨(525 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 7) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 7) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 7) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 7) * h := by nlinarith
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 4 * h ≤ ((n : ℝ) + 7) * h := by nlinarith
    linarith
  have ht5h_mem : t + 5 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 5 * h ≤ ((n : ℝ) + 7) * h := by nlinarith
    linarith
  have ht6h_mem : t + 6 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 6 * h ≤ ((n : ℝ) + 7) * h := by nlinarith
    linarith
  have ht7h_mem : t + 7 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 7 * h = ((n : ℝ) + 7) * h := by ring
    linarith
  -- Rewrite the LTE in textbook form.
  rw [ab7_localTruncationError_eq]
  show |y (t + 7 * h) - y (t + 6 * h)
      - h * (198721 / 60480 * deriv y (t + 6 * h)
              - 447288 / 60480 * deriv y (t + 5 * h)
              + 705549 / 60480 * deriv y (t + 4 * h)
              - 688256 / 60480 * deriv y (t + 3 * h)
              + 407139 / 60480 * deriv y (t + 2 * h)
              - 134472 / 60480 * deriv y (t + h)
              + 19087 / 60480 * deriv y t)|
    ≤ 525 * M * h ^ 8
  have hreshape :
      h * (198721 / 60480 * deriv y (t + 6 * h)
            - 447288 / 60480 * deriv y (t + 5 * h)
            + 705549 / 60480 * deriv y (t + 4 * h)
            - 688256 / 60480 * deriv y (t + 3 * h)
            + 407139 / 60480 * deriv y (t + 2 * h)
            - 134472 / 60480 * deriv y (t + h)
            + 19087 / 60480 * deriv y t)
        = h * ((198721 / 60480) * deriv y (t + 6 * h)
              - (447288 / 60480) * deriv y (t + 5 * h)
              + (705549 / 60480) * deriv y (t + 4 * h)
              - (688256 / 60480) * deriv y (t + 3 * h)
              + (407139 / 60480) * deriv y (t + 2 * h)
              - (134472 / 60480) * deriv y (t + h)
              + (19087 / 60480) * deriv y t) := by ring
  rw [hreshape]
  exact ab7_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem ht4h_mem ht5h_mem ht6h_mem ht7h_mem hh.le

/-! #### Generic AB scalar bridge

Routes the scalar AB7 headline through the generic AB scaffold at `s = 7`,
mirroring the AB6 scalar bridge. -/

/-- AB7 coefficient vector for the generic AB scaffold, ordered from the
oldest to newest sample in the seven-step window. -/
noncomputable def ab7GenericCoeff : Fin 7 → ℝ :=
  ![(19087 : ℝ) / 60480, -(134472 : ℝ) / 60480, (407139 : ℝ) / 60480,
    -(688256 : ℝ) / 60480, (705549 : ℝ) / 60480, -(447288 : ℝ) / 60480,
    (198721 : ℝ) / 60480]

@[simp] lemma ab7GenericCoeff_zero :
    ab7GenericCoeff 0 = (19087 : ℝ) / 60480 := rfl

@[simp] lemma ab7GenericCoeff_one :
    ab7GenericCoeff 1 = -(134472 : ℝ) / 60480 := rfl

@[simp] lemma ab7GenericCoeff_two :
    ab7GenericCoeff 2 = (407139 : ℝ) / 60480 := rfl

@[simp] lemma ab7GenericCoeff_three :
    ab7GenericCoeff 3 = -(688256 : ℝ) / 60480 := rfl

@[simp] lemma ab7GenericCoeff_four :
    ab7GenericCoeff 4 = (705549 : ℝ) / 60480 := rfl

@[simp] lemma ab7GenericCoeff_five :
    ab7GenericCoeff 5 = -(447288 : ℝ) / 60480 := rfl

@[simp] lemma ab7GenericCoeff_six :
    ab7GenericCoeff 6 = (198721 : ℝ) / 60480 := rfl

/-- The effective Lipschitz constant for the generic AB scaffold at the
AB7 coefficient tuple is `(40633/945) · L`. -/
lemma abLip_ab7GenericCoeff (L : ℝ) :
    abLip 7 ab7GenericCoeff L = (40633 / 945) * L := by
  rw [abLip, Fin.sum_univ_seven, ab7GenericCoeff_zero, ab7GenericCoeff_one,
    ab7GenericCoeff_two, ab7GenericCoeff_three, ab7GenericCoeff_four,
    ab7GenericCoeff_five, ab7GenericCoeff_six]
  rw [show |((19087 : ℝ) / 60480)| = (19087 : ℝ) / 60480 by norm_num,
      show |(-(134472 : ℝ) / 60480)| = (134472 : ℝ) / 60480 by norm_num,
      show |((407139 : ℝ) / 60480)| = (407139 : ℝ) / 60480 by norm_num,
      show |(-(688256 : ℝ) / 60480)| = (688256 : ℝ) / 60480 by norm_num,
      show |((705549 : ℝ) / 60480)| = (705549 : ℝ) / 60480 by norm_num,
      show |(-(447288 : ℝ) / 60480)| = (447288 : ℝ) / 60480 by norm_num,
      show |((198721 : ℝ) / 60480)| = (198721 : ℝ) / 60480 by norm_num]
  ring

/-- Bridge: the AB7 scalar iteration is the generic AB iteration
at `s = 7` with `α = ab7GenericCoeff` and starting samples
`![y₀, y₁, y₂, y₃, y₄, y₅, y₆]`. -/
lemma ab7Iter_eq_abIter
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ : ℝ) (n : ℕ) :
    ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ n
      = abIter 7 ab7GenericCoeff h f t₀ ![y₀, y₁, y₂, y₃, y₄, y₅, y₆] n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      show ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 0 = _
      rw [ab7Iter_zero]
      unfold abIter
      simp
    | 1 =>
      show ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 1 = _
      rw [ab7Iter_one]
      unfold abIter
      simp
    | 2 =>
      show ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 2 = _
      rw [ab7Iter_two]
      unfold abIter
      simp
    | 3 =>
      show ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 3 = _
      rw [ab7Iter_three]
      unfold abIter
      simp
    | 4 =>
      show ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 4 = _
      rw [ab7Iter_four]
      unfold abIter
      simp
    | 5 =>
      show ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 5 = _
      rw [ab7Iter_five]
      unfold abIter
      simp
    | 6 =>
      show ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ 6 = _
      rw [ab7Iter_six]
      unfold abIter
      simp
    | k + 7 =>
      rw [ab7Iter_succ_seven]
      rw [abIter_step (s := 7) (by norm_num)
          ab7GenericCoeff h f t₀ ![y₀, y₁, y₂, y₃, y₄, y₅, y₆] k]
      rw [show (k + 7 - 1 : ℕ) = k + 6 from by omega]
      rw [Fin.sum_univ_seven]
      have hval3 : ((3 : Fin 7) : ℕ) = 3 := rfl
      have hval4 : ((4 : Fin 7) : ℕ) = 4 := rfl
      have hval5 : ((5 : Fin 7) : ℕ) = 5 := rfl
      have hval6 : ((6 : Fin 7) : ℕ) = 6 := rfl
      simp only [ab7GenericCoeff_zero, ab7GenericCoeff_one, ab7GenericCoeff_two,
        ab7GenericCoeff_three, ab7GenericCoeff_four, ab7GenericCoeff_five,
        ab7GenericCoeff_six,
        Fin.val_zero, Fin.val_one, Fin.val_two, hval3, hval4, hval5, hval6,
        Nat.add_zero]
      rw [← ih k (by omega), ← ih (k + 1) (by omega), ← ih (k + 2) (by omega),
        ← ih (k + 3) (by omega), ← ih (k + 4) (by omega),
        ← ih (k + 5) (by omega), ← ih (k + 6) (by omega)]
      rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring,
        show ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 by push_cast; ring,
        show ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 by push_cast; ring,
        show ((k + 4 : ℕ) : ℝ) = (k : ℝ) + 4 by push_cast; ring,
        show ((k + 5 : ℕ) : ℝ) = (k : ℝ) + 5 by push_cast; ring,
        show ((k + 6 : ℕ) : ℝ) = (k : ℝ) + 6 by push_cast; ring]
      ring

/-- Bridge: the AB7 scalar truncation residual at base point `t₀ + n · h`
equals the generic AB residual at index `n`. -/
lemma ab7Residual_eq_abResidual
    (h : ℝ) (y : ℝ → ℝ) (t₀ : ℝ) (n : ℕ) :
    y (t₀ + (n : ℝ) * h + 7 * h) - y (t₀ + (n : ℝ) * h + 6 * h)
        - h * ((198721 / 60480) * deriv y (t₀ + (n : ℝ) * h + 6 * h)
              - (447288 / 60480) * deriv y (t₀ + (n : ℝ) * h + 5 * h)
              + (705549 / 60480) * deriv y (t₀ + (n : ℝ) * h + 4 * h)
              - (688256 / 60480) * deriv y (t₀ + (n : ℝ) * h + 3 * h)
              + (407139 / 60480) * deriv y (t₀ + (n : ℝ) * h + 2 * h)
              - (134472 / 60480) * deriv y (t₀ + (n : ℝ) * h + h)
              + (19087 / 60480) * deriv y (t₀ + (n : ℝ) * h))
      = abResidual 7 ab7GenericCoeff h y t₀ n := by
  unfold abResidual
  rw [Fin.sum_univ_seven, ab7GenericCoeff_zero, ab7GenericCoeff_one,
    ab7GenericCoeff_two, ab7GenericCoeff_three, ab7GenericCoeff_four,
    ab7GenericCoeff_five, ab7GenericCoeff_six]
  have eA : t₀ + (n : ℝ) * h + 7 * h = t₀ + ((n + 7 : ℕ) : ℝ) * h := by
    push_cast; ring
  have eB :
      t₀ + (n : ℝ) * h + 6 * h = t₀ + ((n + 7 - 1 : ℕ) : ℝ) * h := by
    have hsub : (n + 7 - 1 : ℕ) = n + 6 := by omega
    rw [hsub]; push_cast; ring
  have eC : t₀ + (n : ℝ) * h
      = t₀ + ((n + ((0 : Fin 7) : ℕ) : ℕ) : ℝ) * h := by
    simp
  have eD : t₀ + (n : ℝ) * h + h
      = t₀ + ((n + ((1 : Fin 7) : ℕ) : ℕ) : ℝ) * h := by
    simp; ring
  have eE : t₀ + (n : ℝ) * h + 2 * h
      = t₀ + ((n + ((2 : Fin 7) : ℕ) : ℕ) : ℝ) * h := by
    simp; ring
  have eF : t₀ + (n : ℝ) * h + 3 * h
      = t₀ + ((n + ((3 : Fin 7) : ℕ) : ℕ) : ℝ) * h := by
    have : ((3 : Fin 7) : ℕ) = 3 := rfl
    rw [this]; push_cast; ring
  have eG : t₀ + (n : ℝ) * h + 4 * h
      = t₀ + ((n + ((4 : Fin 7) : ℕ) : ℕ) : ℝ) * h := by
    have : ((4 : Fin 7) : ℕ) = 4 := rfl
    rw [this]; push_cast; ring
  have eH : t₀ + (n : ℝ) * h + 5 * h
      = t₀ + ((n + ((5 : Fin 7) : ℕ) : ℕ) : ℝ) * h := by
    have : ((5 : Fin 7) : ℕ) = 5 := rfl
    rw [this]; push_cast; ring
  have eI : t₀ + (n : ℝ) * h + 6 * h
      = t₀ + ((n + ((6 : Fin 7) : ℕ) : ℕ) : ℝ) * h := by
    have : ((6 : Fin 7) : ℕ) = 6 := rfl
    rw [this]; push_cast; ring
  rw [← eA, ← eB, ← eC, ← eD, ← eE, ← eF, ← eG, ← eH, ← eI]
  ring

/-- Final AB7 global error bound on `[t₀, t₀ + T]`. Under Lipschitz `f`,
`C^8` exact solution `y` with `deriv y t = f t (y t)`, and starting
errors `|y_i - y(t_i)| ≤ ε₀` for `i = 0, 1, …, 6`, the AB7 iterate error
obeys `O(ε₀ + h^7)` on a finite horizon. -/
theorem ab7_global_error_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 8 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      ∀ {y₀ y₁ y₂ y₃ y₄ y₅ y₆ ε₀ : ℝ}, 0 ≤ ε₀ →
      |y₀ - y t₀| ≤ ε₀ → |y₁ - y (t₀ + h)| ≤ ε₀ →
      |y₂ - y (t₀ + 2 * h)| ≤ ε₀ →
      |y₃ - y (t₀ + 3 * h)| ≤ ε₀ →
      |y₄ - y (t₀ + 4 * h)| ≤ ε₀ →
      |y₅ - y (t₀ + 5 * h)| ≤ ε₀ →
      |y₆ - y (t₀ + 6 * h)| ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 6) * h ≤ T →
      |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ N - y (t₀ + (N : ℝ) * h)|
        ≤ Real.exp ((40633 / 945) * L * T) * ε₀ + K * h ^ 7 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    ab7_local_residual_bound hy t₀ T hT
  refine ⟨T * Real.exp ((40633 / 945) * L * T) * C, δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
  intro h hh hδ_le y₀ y₁ y₂ y₃ y₄ y₅ y₆ ε₀ hε₀
    he0_bd he1_bd he2_bd he3_bd he4_bd he5_bd he6_bd N hNh
  set α : Fin 7 → ℝ := ab7GenericCoeff with hα_def
  set y₀_sept : Fin 7 → ℝ := ![y₀, y₁, y₂, y₃, y₄, y₅, y₆] with hy_sept_def
  have hs : (1 : ℕ) ≤ 7 := by norm_num
  haveI : Nonempty (Fin 7) := ⟨⟨0, hs⟩⟩
  have hiter0 : abIter 7 α h f t₀ y₀_sept 0 = y₀ := by
    unfold abIter; simp [hy_sept_def]
  have hiter1 : abIter 7 α h f t₀ y₀_sept 1 = y₁ := by
    unfold abIter; simp [hy_sept_def]
  have hiter2 : abIter 7 α h f t₀ y₀_sept 2 = y₂ := by
    unfold abIter; simp [hy_sept_def]
  have hiter3 : abIter 7 α h f t₀ y₀_sept 3 = y₃ := by
    unfold abIter; simp [hy_sept_def]
  have hiter4 : abIter 7 α h f t₀ y₀_sept 4 = y₄ := by
    unfold abIter; simp [hy_sept_def]
  have hiter5 : abIter 7 α h f t₀ y₀_sept 5 = y₅ := by
    unfold abIter; simp [hy_sept_def]
  have hiter6 : abIter 7 α h f t₀ y₀_sept 6 = y₆ := by
    unfold abIter; simp [hy_sept_def]
  have hstart : abErrWindow hs α h f t₀ y₀_sept y 0 ≤ ε₀ := by
    unfold abErrWindow
    apply Finset.sup'_le
    intro j _
    show abErr 7 α h f t₀ y₀_sept y (0 + (j : ℕ)) ≤ ε₀
    unfold abErr
    fin_cases j
    · show |abIter 7 α h f t₀ y₀_sept 0
          - y (t₀ + ((0 + (((0 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter0]
      have : ((0 + (((0 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) = 0 := by simp
      rw [this, zero_mul, add_zero]; exact he0_bd
    · show |abIter 7 α h f t₀ y₀_sept 1
          - y (t₀ + ((0 + (((1 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter1]
      have : ((0 + (((1 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) = 1 := by simp
      rw [this, one_mul]; exact he1_bd
    · show |abIter 7 α h f t₀ y₀_sept 2
          - y (t₀ + ((0 + (((2 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter2]
      have : ((0 + (((2 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) = 2 := by simp
      rw [this]; exact he2_bd
    · show |abIter 7 α h f t₀ y₀_sept 3
          - y (t₀ + ((0 + (((3 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter3]
      have hval3 : ((3 : Fin 7) : ℕ) = 3 := rfl
      have : ((0 + (((3 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) = 3 := by
        rw [hval3]; push_cast; ring
      rw [this]; exact he3_bd
    · show |abIter 7 α h f t₀ y₀_sept 4
          - y (t₀ + ((0 + (((4 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter4]
      have hval4 : ((4 : Fin 7) : ℕ) = 4 := rfl
      have : ((0 + (((4 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) = 4 := by
        rw [hval4]; push_cast; ring
      rw [this]; exact he4_bd
    · show |abIter 7 α h f t₀ y₀_sept 5
          - y (t₀ + ((0 + (((5 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter5]
      have hval5 : ((5 : Fin 7) : ℕ) = 5 := rfl
      have : ((0 + (((5 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) = 5 := by
        rw [hval5]; push_cast; ring
      rw [this]; exact he5_bd
    · show |abIter 7 α h f t₀ y₀_sept 6
          - y (t₀ + ((0 + (((6 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter6]
      have hval6 : ((6 : Fin 7) : ℕ) = 6 := rfl
      have : ((0 + (((6 : Fin 7) : ℕ) : ℕ) : ℕ) : ℝ) = 6 := by
        rw [hval6]; push_cast; ring
      rw [this]; exact he6_bd
  have hres_gen : ∀ n : ℕ, n < N →
      |abResidual 7 α h y t₀ n| ≤ C * h ^ (7 + 1) := by
    intro n hn_lt
    have hcast : (n : ℝ) + 7 ≤ (N : ℝ) + 6 := by
      have : (n : ℝ) + 1 ≤ (N : ℝ) := by
        exact_mod_cast Nat.lt_iff_add_one_le.mp hn_lt
      linarith
    have hn7_le : ((n : ℝ) + 7) * h ≤ T := by
      have hmul : ((n : ℝ) + 7) * h ≤ ((N : ℝ) + 6) * h :=
        mul_le_mul_of_nonneg_right hcast hh.le
      linarith
    have hres := hresidual hh hδ_le n hn7_le
    have hLTE_eq := ab7_localTruncationError_eq h (t₀ + (n : ℝ) * h) y
    have hbridge := ab7Residual_eq_abResidual h y t₀ n
    have hpow : C * h ^ (7 + 1) = C * h ^ 8 := by norm_num
    rw [hα_def, ← hbridge]
    have hreshape :
        h * ((198721 / 60480) * deriv y (t₀ + (n : ℝ) * h + 6 * h)
              - (447288 / 60480) * deriv y (t₀ + (n : ℝ) * h + 5 * h)
              + (705549 / 60480) * deriv y (t₀ + (n : ℝ) * h + 4 * h)
              - (688256 / 60480) * deriv y (t₀ + (n : ℝ) * h + 3 * h)
              + (407139 / 60480) * deriv y (t₀ + (n : ℝ) * h + 2 * h)
              - (134472 / 60480) * deriv y (t₀ + (n : ℝ) * h + h)
              + (19087 / 60480) * deriv y (t₀ + (n : ℝ) * h))
          = h * (198721 / 60480 * deriv y (t₀ + (n : ℝ) * h + 6 * h)
                - 447288 / 60480 * deriv y (t₀ + (n : ℝ) * h + 5 * h)
                + 705549 / 60480 * deriv y (t₀ + (n : ℝ) * h + 4 * h)
                - 688256 / 60480 * deriv y (t₀ + (n : ℝ) * h + 3 * h)
                + 407139 / 60480 * deriv y (t₀ + (n : ℝ) * h + 2 * h)
                - 134472 / 60480 * deriv y (t₀ + (n : ℝ) * h + h)
                + 19087 / 60480 * deriv y (t₀ + (n : ℝ) * h)) := by ring
    rw [hreshape, ← hLTE_eq]
    linarith [hres, hpow.symm.le, hpow.le]
  have hNh' : (N : ℝ) * h ≤ T := by
    have hmono : (N : ℝ) * h ≤ ((N : ℝ) + 6) * h := by
      have h1 : (N : ℝ) ≤ (N : ℝ) + 6 := by linarith
      exact mul_le_mul_of_nonneg_right h1 hh.le
    linarith
  have hgeneric :=
    ab_global_error_bound_generic (p := 7) hs α hh.le hL hC_nn hf t₀
      y₀_sept y hyf hε₀ hstart N hNh' hres_gen
  rw [show abLip 7 α L = (40633 / 945) * L from by
    rw [hα_def]; exact abLip_ab7GenericCoeff L] at hgeneric
  have hwindow_ge : abErr 7 α h f t₀ y₀_sept y N
      ≤ abErrWindow hs α h f t₀ y₀_sept y N := by
    show abErr 7 α h f t₀ y₀_sept y (N + ((⟨0, hs⟩ : Fin 7) : ℕ))
        ≤ abErrWindow hs α h f t₀ y₀_sept y N
    unfold abErrWindow
    exact Finset.le_sup' (b := ⟨0, hs⟩)
      (f := fun j : Fin 7 => abErr 7 α h f t₀ y₀_sept y (N + (j : ℕ)))
      (Finset.mem_univ _)
  have hbridge :
      abIter 7 α h f t₀ y₀_sept N
        = ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ N := by
    rw [hα_def, hy_sept_def]
    exact (ab7Iter_eq_abIter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ N).symm
  have habsErr :
      abErr 7 α h f t₀ y₀_sept y N
        = |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ N - y (t₀ + (N : ℝ) * h)| := by
    show |abIter 7 α h f t₀ y₀_sept N - y (t₀ + (N : ℝ) * h)|
        = |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ N - y (t₀ + (N : ℝ) * h)|
    rw [hbridge]
  show |ab7Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ N - y (t₀ + (N : ℝ) * h)|
      ≤ Real.exp ((40633 / 945) * L * T) * ε₀
        + T * Real.exp ((40633 / 945) * L * T) * C * h ^ 7
  linarith [hwindow_ge, hgeneric, habsErr.symm.le, habsErr.le]

end LMM
