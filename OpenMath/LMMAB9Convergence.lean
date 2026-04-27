import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMABGenericConvergence
import OpenMath.LMMAM8Convergence

/-! ## Adams–Bashforth 9-step Scalar Convergence Chain (Iserles §1.2)

Order-9 explicit 9-step LMM convergence scaffold. Mirrors the AB8 chain
in `OpenMath.LMMAB8Convergence` at the next order. This scalar half takes
nine starting samples and combines nine prior `f` evaluations. The
effective max-window Lipschitz constant is `(2231497/14175) · L`
(`= sum |β_k|`), the residual is `O(h^10)` and the headline global error
bound is `O(ε₀ + h^9)`.

Reuses the public tenth-order Taylor helpers
`iteratedDeriv_ten_bounded_on_Icc`,
`y_tenth_order_taylor_remainder`,
`derivY_ninth_order_taylor_remainder` from `LMMAM8Convergence`. -/

namespace LMM

/-- AB9 iteration with nine starting samples `y₀, y₁, …, y₈`:
`y_{n+9} = y_{n+8} + h · ((14097247/3628800) · f_{n+8}
  − (43125206/3628800) · f_{n+7} + (95476786/3628800) · f_{n+6}
  − (139855262/3628800) · f_{n+5} + (137968480/3628800) · f_{n+4}
  − (91172642/3628800) · f_{n+3} + (38833486/3628800) · f_{n+2}
  − (9664106/3628800) · f_{n+1} + (1070017/3628800) · f_n)`. -/
noncomputable def ab9Iter
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : ℝ) : ℕ → ℝ
  | 0 => y₀
  | 1 => y₁
  | 2 => y₂
  | 3 => y₃
  | 4 => y₄
  | 5 => y₅
  | 6 => y₆
  | 7 => y₇
  | 8 => y₈
  | n + 9 =>
      ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 8)
        + h * (14097247 / 3628800 * f (t₀ + ((n : ℝ) + 8) * h)
                (ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 8))
              - 43125206 / 3628800 * f (t₀ + ((n : ℝ) + 7) * h)
                (ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 7))
              + 95476786 / 3628800 * f (t₀ + ((n : ℝ) + 6) * h)
                (ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 6))
              - 139855262 / 3628800 * f (t₀ + ((n : ℝ) + 5) * h)
                (ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 5))
              + 137968480 / 3628800 * f (t₀ + ((n : ℝ) + 4) * h)
                (ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 4))
              - 91172642 / 3628800 * f (t₀ + ((n : ℝ) + 3) * h)
                (ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 3))
              + 38833486 / 3628800 * f (t₀ + ((n : ℝ) + 2) * h)
                (ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 2))
              - 9664106 / 3628800 * f (t₀ + ((n : ℝ) + 1) * h)
                (ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 1))
              + 1070017 / 3628800 * f (t₀ + (n : ℝ) * h)
                (ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ n))

@[simp] lemma ab9Iter_zero
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : ℝ) :
    ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 0 = y₀ := rfl

@[simp] lemma ab9Iter_one
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : ℝ) :
    ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 1 = y₁ := rfl

@[simp] lemma ab9Iter_two
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : ℝ) :
    ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 2 = y₂ := rfl

@[simp] lemma ab9Iter_three
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : ℝ) :
    ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 3 = y₃ := rfl

@[simp] lemma ab9Iter_four
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : ℝ) :
    ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 4 = y₄ := rfl

@[simp] lemma ab9Iter_five
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : ℝ) :
    ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 5 = y₅ := rfl

@[simp] lemma ab9Iter_six
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : ℝ) :
    ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 6 = y₆ := rfl

@[simp] lemma ab9Iter_seven
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : ℝ) :
    ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 7 = y₇ := rfl

@[simp] lemma ab9Iter_eight
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : ℝ) :
    ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 8 = y₈ := rfl

lemma ab9Iter_succ_nine
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : ℝ) (n : ℕ) :
    ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 9)
      = ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 8)
          + h * (14097247 / 3628800 * f (t₀ + ((n : ℝ) + 8) * h)
                  (ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 8))
                - 43125206 / 3628800 * f (t₀ + ((n : ℝ) + 7) * h)
                    (ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 7))
                + 95476786 / 3628800 * f (t₀ + ((n : ℝ) + 6) * h)
                    (ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 6))
                - 139855262 / 3628800 * f (t₀ + ((n : ℝ) + 5) * h)
                    (ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 5))
                + 137968480 / 3628800 * f (t₀ + ((n : ℝ) + 4) * h)
                    (ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 4))
                - 91172642 / 3628800 * f (t₀ + ((n : ℝ) + 3) * h)
                    (ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 3))
                + 38833486 / 3628800 * f (t₀ + ((n : ℝ) + 2) * h)
                    (ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 2))
                - 9664106 / 3628800 * f (t₀ + ((n : ℝ) + 1) * h)
                    (ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 1))
                + 1070017 / 3628800 * f (t₀ + (n : ℝ) * h)
                    (ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ n)) := rfl

/-- AB9 local truncation operator reduces to the textbook 9-step residual. -/
theorem ab9_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    adamsBashforth9.localTruncationError h t y
      = y (t + 9 * h) - y (t + 8 * h)
          - h * (14097247 / 3628800 * deriv y (t + 8 * h)
                  - 43125206 / 3628800 * deriv y (t + 7 * h)
                  + 95476786 / 3628800 * deriv y (t + 6 * h)
                  - 139855262 / 3628800 * deriv y (t + 5 * h)
                  + 137968480 / 3628800 * deriv y (t + 4 * h)
                  - 91172642 / 3628800 * deriv y (t + 3 * h)
                  + 38833486 / 3628800 * deriv y (t + 2 * h)
                  - 9664106 / 3628800 * deriv y (t + h)
                  + 1070017 / 3628800 * deriv y t) := by
  unfold localTruncationError truncationOp
  simp [adamsBashforth9, Fin.sum_univ_succ, iteratedDeriv_one,
    iteratedDeriv_zero]
  norm_num
  ring

/-- Algebraic decomposition of the AB9 global-error increment. Pure
`ring` identity isolated to keep the kernel cost of
`ab9_one_step_lipschitz` manageable. -/
private lemma ab9_step_alg_decomp
    (h : ℝ) (yn8 zn8 zn9 τ : ℝ)
    (a8 a7 a6 a5 a4 a3 a2 a1 a0 : ℝ)
    (next : ℝ)
    (hstep : next = yn8 + h * (14097247 / 3628800 * a8
                    - 43125206 / 3628800 * a7
                    + 95476786 / 3628800 * a6
                    - 139855262 / 3628800 * a5
                    + 137968480 / 3628800 * a4
                    - 91172642 / 3628800 * a3
                    + 38833486 / 3628800 * a2
                    - 9664106 / 3628800 * a1
                    + 1070017 / 3628800 * a0))
    (b8 b7 b6 b5 b4 b3 b2 b1 b0 : ℝ)
    (hτ_eq : τ = zn9 - zn8 - h * (14097247 / 3628800 * b8
                    - 43125206 / 3628800 * b7
                    + 95476786 / 3628800 * b6
                    - 139855262 / 3628800 * b5
                    + 137968480 / 3628800 * b4
                    - 91172642 / 3628800 * b3
                    + 38833486 / 3628800 * b2
                    - 9664106 / 3628800 * b1
                    + 1070017 / 3628800 * b0)) :
    next - zn9
      = (yn8 - zn8)
        + (14097247 / 3628800) * h * (a8 - b8)
        - (43125206 / 3628800) * h * (a7 - b7)
        + (95476786 / 3628800) * h * (a6 - b6)
        - (139855262 / 3628800) * h * (a5 - b5)
        + (137968480 / 3628800) * h * (a4 - b4)
        - (91172642 / 3628800) * h * (a3 - b3)
        + (38833486 / 3628800) * h * (a2 - b2)
        - (9664106 / 3628800) * h * (a1 - b1)
        + (1070017 / 3628800) * h * (a0 - b0)
        - τ := by
  rw [hstep, hτ_eq]; ring

/-- One-step AB9 Lipschitz step: a single linearised increment of the
global error from steps `n, n+1, …, n+8` to `n+9`, with nine Lipschitz
contributions and additive `|τ_n|`. -/
theorem ab9_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : ℝ) (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)|
      ≤ |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)|
        + (14097247 / 3628800) * h * L
            * |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 8)
                - y (t₀ + ((n : ℝ) + 8) * h)|
        + (43125206 / 3628800) * h * L
            * |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 7)
                - y (t₀ + ((n : ℝ) + 7) * h)|
        + (95476786 / 3628800) * h * L
            * |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 6)
                - y (t₀ + ((n : ℝ) + 6) * h)|
        + (139855262 / 3628800) * h * L
            * |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 5)
                - y (t₀ + ((n : ℝ) + 5) * h)|
        + (137968480 / 3628800) * h * L
            * |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 4)
                - y (t₀ + ((n : ℝ) + 4) * h)|
        + (91172642 / 3628800) * h * L
            * |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 3)
                - y (t₀ + ((n : ℝ) + 3) * h)|
        + (38833486 / 3628800) * h * L
            * |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 2)
                - y (t₀ + ((n : ℝ) + 2) * h)|
        + (9664106 / 3628800) * h * L
            * |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 1)
                - y (t₀ + ((n : ℝ) + 1) * h)|
        + (1070017 / 3628800) * h * L
            * |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ n - y (t₀ + (n : ℝ) * h)|
        + |adamsBashforth9.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set yn : ℝ := ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ n with hyn_def
  set yn1 : ℝ := ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 1) with hyn1_def
  set yn2 : ℝ := ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 2) with hyn2_def
  set yn3 : ℝ := ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 3) with hyn3_def
  set yn4 : ℝ := ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 4) with hyn4_def
  set yn5 : ℝ := ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 5) with hyn5_def
  set yn6 : ℝ := ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 6) with hyn6_def
  set yn7 : ℝ := ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 7) with hyn7_def
  set yn8 : ℝ := ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 8) with hyn8_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set tn3 : ℝ := t₀ + ((n : ℝ) + 3) * h with htn3_def
  set tn4 : ℝ := t₀ + ((n : ℝ) + 4) * h with htn4_def
  set tn5 : ℝ := t₀ + ((n : ℝ) + 5) * h with htn5_def
  set tn6 : ℝ := t₀ + ((n : ℝ) + 6) * h with htn6_def
  set tn7 : ℝ := t₀ + ((n : ℝ) + 7) * h with htn7_def
  set tn8 : ℝ := t₀ + ((n : ℝ) + 8) * h with htn8_def
  set tn9 : ℝ := t₀ + ((n : ℝ) + 9) * h with htn9_def
  set zn : ℝ := y tn with hzn_def
  set zn1 : ℝ := y tn1 with hzn1_def
  set zn2 : ℝ := y tn2 with hzn2_def
  set zn3 : ℝ := y tn3 with hzn3_def
  set zn4 : ℝ := y tn4 with hzn4_def
  set zn5 : ℝ := y tn5 with hzn5_def
  set zn6 : ℝ := y tn6 with hzn6_def
  set zn7 : ℝ := y tn7 with hzn7_def
  set zn8 : ℝ := y tn8 with hzn8_def
  set zn9 : ℝ := y tn9 with hzn9_def
  set τ : ℝ := adamsBashforth9.localTruncationError h tn y with hτ_def
  -- AB9 step formula.
  have hstep : ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 9)
      = yn8 + h * (14097247 / 3628800 * f tn8 yn8
                    - 43125206 / 3628800 * f tn7 yn7
                    + 95476786 / 3628800 * f tn6 yn6
                    - 139855262 / 3628800 * f tn5 yn5
                    + 137968480 / 3628800 * f tn4 yn4
                    - 91172642 / 3628800 * f tn3 yn3
                    + 38833486 / 3628800 * f tn2 yn2
                    - 9664106 / 3628800 * f tn1 yn1
                    + 1070017 / 3628800 * f tn yn) := by
    show ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 9) = _
    rw [ab9Iter_succ_nine]
  -- Time arithmetic.
  have htn1_h : tn + h = tn1 := by simp [htn_def, htn1_def]; ring
  have htn_2h : tn + 2 * h = tn2 := by simp [htn_def, htn2_def]; ring
  have htn_3h : tn + 3 * h = tn3 := by simp [htn_def, htn3_def]; ring
  have htn_4h : tn + 4 * h = tn4 := by simp [htn_def, htn4_def]; ring
  have htn_5h : tn + 5 * h = tn5 := by simp [htn_def, htn5_def]; ring
  have htn_6h : tn + 6 * h = tn6 := by simp [htn_def, htn6_def]; ring
  have htn_7h : tn + 7 * h = tn7 := by simp [htn_def, htn7_def]; ring
  have htn_8h : tn + 8 * h = tn8 := by simp [htn_def, htn8_def]; ring
  have htn_9h : tn + 9 * h = tn9 := by simp [htn_def, htn9_def]; ring
  -- LTE residual at `tn`, expressed via `f` along the trajectory.
  have hτ_eq : τ = zn9 - zn8
        - h * (14097247 / 3628800 * f tn8 zn8 - 43125206 / 3628800 * f tn7 zn7
              + 95476786 / 3628800 * f tn6 zn6 - 139855262 / 3628800 * f tn5 zn5
              + 137968480 / 3628800 * f tn4 zn4 - 91172642 / 3628800 * f tn3 zn3
              + 38833486 / 3628800 * f tn2 zn2 - 9664106 / 3628800 * f tn1 zn1
              + 1070017 / 3628800 * f tn zn) := by
    show adamsBashforth9.localTruncationError h tn y = _
    rw [ab9_localTruncationError_eq, htn1_h, htn_2h, htn_3h, htn_4h, htn_5h,
      htn_6h, htn_7h, htn_8h, htn_9h, hyf tn8, hyf tn7, hyf tn6, hyf tn5,
      hyf tn4, hyf tn3, hyf tn2, hyf tn1, hyf tn]
  -- Algebraic decomposition of the global error increment.
  have halg : ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 9) - zn9
      = (yn8 - zn8)
        + (14097247 / 3628800) * h * (f tn8 yn8 - f tn8 zn8)
        - (43125206 / 3628800) * h * (f tn7 yn7 - f tn7 zn7)
        + (95476786 / 3628800) * h * (f tn6 yn6 - f tn6 zn6)
        - (139855262 / 3628800) * h * (f tn5 yn5 - f tn5 zn5)
        + (137968480 / 3628800) * h * (f tn4 yn4 - f tn4 zn4)
        - (91172642 / 3628800) * h * (f tn3 yn3 - f tn3 zn3)
        + (38833486 / 3628800) * h * (f tn2 yn2 - f tn2 zn2)
        - (9664106 / 3628800) * h * (f tn1 yn1 - f tn1 zn1)
        + (1070017 / 3628800) * h * (f tn yn - f tn zn)
        - τ :=
    ab9_step_alg_decomp h yn8 zn8 zn9 τ
      (f tn8 yn8) (f tn7 yn7) (f tn6 yn6) (f tn5 yn5) (f tn4 yn4)
      (f tn3 yn3) (f tn2 yn2) (f tn1 yn1) (f tn yn) _ hstep
      (f tn8 zn8) (f tn7 zn7) (f tn6 zn6) (f tn5 zn5) (f tn4 zn4)
      (f tn3 zn3) (f tn2 zn2) (f tn1 zn1) (f tn zn) hτ_eq
  clear_value yn yn1 yn2 yn3 yn4 yn5 yn6 yn7 yn8
    tn tn1 tn2 tn3 tn4 tn5 tn6 tn7 tn8 tn9
    zn zn1 zn2 zn3 zn4 zn5 zn6 zn7 zn8 zn9 τ
  -- Lipschitz bounds.
  have hLip8 : |f tn8 yn8 - f tn8 zn8| ≤ L * |yn8 - zn8| := hf tn8 yn8 zn8
  have hLip7 : |f tn7 yn7 - f tn7 zn7| ≤ L * |yn7 - zn7| := hf tn7 yn7 zn7
  have hLip6 : |f tn6 yn6 - f tn6 zn6| ≤ L * |yn6 - zn6| := hf tn6 yn6 zn6
  have hLip5 : |f tn5 yn5 - f tn5 zn5| ≤ L * |yn5 - zn5| := hf tn5 yn5 zn5
  have hLip4 : |f tn4 yn4 - f tn4 zn4| ≤ L * |yn4 - zn4| := hf tn4 yn4 zn4
  have hLip3 : |f tn3 yn3 - f tn3 zn3| ≤ L * |yn3 - zn3| := hf tn3 yn3 zn3
  have hLip2 : |f tn2 yn2 - f tn2 zn2| ≤ L * |yn2 - zn2| := hf tn2 yn2 zn2
  have hLip1 : |f tn1 yn1 - f tn1 zn1| ≤ L * |yn1 - zn1| := hf tn1 yn1 zn1
  have hLip0 : |f tn yn - f tn zn| ≤ L * |yn - zn| := hf tn yn zn
  have c8_nn : 0 ≤ (14097247 / 3628800) * h := by linarith
  have c7_nn : 0 ≤ (43125206 / 3628800) * h := by linarith
  have c6_nn : 0 ≤ (95476786 / 3628800) * h := by linarith
  have c5_nn : 0 ≤ (139855262 / 3628800) * h := by linarith
  have c4_nn : 0 ≤ (137968480 / 3628800) * h := by linarith
  have c3_nn : 0 ≤ (91172642 / 3628800) * h := by linarith
  have c2_nn : 0 ≤ (38833486 / 3628800) * h := by linarith
  have c1_nn : 0 ≤ (9664106 / 3628800) * h := by linarith
  have c0_nn : 0 ≤ (1070017 / 3628800) * h := by linarith
  have h8_abs : |(14097247 / 3628800) * h * (f tn8 yn8 - f tn8 zn8)|
      ≤ (14097247 / 3628800) * h * L * |yn8 - zn8| := by
    rw [abs_mul, abs_of_nonneg c8_nn]
    calc (14097247 / 3628800) * h * |f tn8 yn8 - f tn8 zn8|
        ≤ (14097247 / 3628800) * h * (L * |yn8 - zn8|) :=
          mul_le_mul_of_nonneg_left hLip8 c8_nn
      _ = (14097247 / 3628800) * h * L * |yn8 - zn8| := by ring
  have h7_abs : |(43125206 / 3628800) * h * (f tn7 yn7 - f tn7 zn7)|
      ≤ (43125206 / 3628800) * h * L * |yn7 - zn7| := by
    rw [abs_mul, abs_of_nonneg c7_nn]
    calc (43125206 / 3628800) * h * |f tn7 yn7 - f tn7 zn7|
        ≤ (43125206 / 3628800) * h * (L * |yn7 - zn7|) :=
          mul_le_mul_of_nonneg_left hLip7 c7_nn
      _ = (43125206 / 3628800) * h * L * |yn7 - zn7| := by ring
  have h6_abs : |(95476786 / 3628800) * h * (f tn6 yn6 - f tn6 zn6)|
      ≤ (95476786 / 3628800) * h * L * |yn6 - zn6| := by
    rw [abs_mul, abs_of_nonneg c6_nn]
    calc (95476786 / 3628800) * h * |f tn6 yn6 - f tn6 zn6|
        ≤ (95476786 / 3628800) * h * (L * |yn6 - zn6|) :=
          mul_le_mul_of_nonneg_left hLip6 c6_nn
      _ = (95476786 / 3628800) * h * L * |yn6 - zn6| := by ring
  have h5_abs : |(139855262 / 3628800) * h * (f tn5 yn5 - f tn5 zn5)|
      ≤ (139855262 / 3628800) * h * L * |yn5 - zn5| := by
    rw [abs_mul, abs_of_nonneg c5_nn]
    calc (139855262 / 3628800) * h * |f tn5 yn5 - f tn5 zn5|
        ≤ (139855262 / 3628800) * h * (L * |yn5 - zn5|) :=
          mul_le_mul_of_nonneg_left hLip5 c5_nn
      _ = (139855262 / 3628800) * h * L * |yn5 - zn5| := by ring
  have h4_abs : |(137968480 / 3628800) * h * (f tn4 yn4 - f tn4 zn4)|
      ≤ (137968480 / 3628800) * h * L * |yn4 - zn4| := by
    rw [abs_mul, abs_of_nonneg c4_nn]
    calc (137968480 / 3628800) * h * |f tn4 yn4 - f tn4 zn4|
        ≤ (137968480 / 3628800) * h * (L * |yn4 - zn4|) :=
          mul_le_mul_of_nonneg_left hLip4 c4_nn
      _ = (137968480 / 3628800) * h * L * |yn4 - zn4| := by ring
  have h3_abs : |(91172642 / 3628800) * h * (f tn3 yn3 - f tn3 zn3)|
      ≤ (91172642 / 3628800) * h * L * |yn3 - zn3| := by
    rw [abs_mul, abs_of_nonneg c3_nn]
    calc (91172642 / 3628800) * h * |f tn3 yn3 - f tn3 zn3|
        ≤ (91172642 / 3628800) * h * (L * |yn3 - zn3|) :=
          mul_le_mul_of_nonneg_left hLip3 c3_nn
      _ = (91172642 / 3628800) * h * L * |yn3 - zn3| := by ring
  have h2_abs : |(38833486 / 3628800) * h * (f tn2 yn2 - f tn2 zn2)|
      ≤ (38833486 / 3628800) * h * L * |yn2 - zn2| := by
    rw [abs_mul, abs_of_nonneg c2_nn]
    calc (38833486 / 3628800) * h * |f tn2 yn2 - f tn2 zn2|
        ≤ (38833486 / 3628800) * h * (L * |yn2 - zn2|) :=
          mul_le_mul_of_nonneg_left hLip2 c2_nn
      _ = (38833486 / 3628800) * h * L * |yn2 - zn2| := by ring
  have h1_abs : |(9664106 / 3628800) * h * (f tn1 yn1 - f tn1 zn1)|
      ≤ (9664106 / 3628800) * h * L * |yn1 - zn1| := by
    rw [abs_mul, abs_of_nonneg c1_nn]
    calc (9664106 / 3628800) * h * |f tn1 yn1 - f tn1 zn1|
        ≤ (9664106 / 3628800) * h * (L * |yn1 - zn1|) :=
          mul_le_mul_of_nonneg_left hLip1 c1_nn
      _ = (9664106 / 3628800) * h * L * |yn1 - zn1| := by ring
  have h0_abs : |(1070017 / 3628800) * h * (f tn yn - f tn zn)|
      ≤ (1070017 / 3628800) * h * L * |yn - zn| := by
    rw [abs_mul, abs_of_nonneg c0_nn]
    calc (1070017 / 3628800) * h * |f tn yn - f tn zn|
        ≤ (1070017 / 3628800) * h * (L * |yn - zn|) :=
          mul_le_mul_of_nonneg_left hLip0 c0_nn
      _ = (1070017 / 3628800) * h * L * |yn - zn| := by ring
  -- Triangle inequality (chained nine times).
  set S := (yn8 - zn8)
        + (14097247 / 3628800) * h * (f tn8 yn8 - f tn8 zn8)
        - (43125206 / 3628800) * h * (f tn7 yn7 - f tn7 zn7)
        + (95476786 / 3628800) * h * (f tn6 yn6 - f tn6 zn6)
        - (139855262 / 3628800) * h * (f tn5 yn5 - f tn5 zn5)
        + (137968480 / 3628800) * h * (f tn4 yn4 - f tn4 zn4)
        - (91172642 / 3628800) * h * (f tn3 yn3 - f tn3 zn3)
        + (38833486 / 3628800) * h * (f tn2 yn2 - f tn2 zn2)
        - (9664106 / 3628800) * h * (f tn1 yn1 - f tn1 zn1)
        + (1070017 / 3628800) * h * (f tn yn - f tn zn) with hS_def
  have hcalc : ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 9) - zn9 = S - τ := halg
  have htri_S : |S| ≤ |yn8 - zn8|
              + |(14097247 / 3628800) * h * (f tn8 yn8 - f tn8 zn8)|
              + |(43125206 / 3628800) * h * (f tn7 yn7 - f tn7 zn7)|
              + |(95476786 / 3628800) * h * (f tn6 yn6 - f tn6 zn6)|
              + |(139855262 / 3628800) * h * (f tn5 yn5 - f tn5 zn5)|
              + |(137968480 / 3628800) * h * (f tn4 yn4 - f tn4 zn4)|
              + |(91172642 / 3628800) * h * (f tn3 yn3 - f tn3 zn3)|
              + |(38833486 / 3628800) * h * (f tn2 yn2 - f tn2 zn2)|
              + |(9664106 / 3628800) * h * (f tn1 yn1 - f tn1 zn1)|
              + |(1070017 / 3628800) * h * (f tn yn - f tn zn)| := by
    have h1 : |(yn8 - zn8)
              + (14097247 / 3628800) * h * (f tn8 yn8 - f tn8 zn8)|
        ≤ |yn8 - zn8| + |(14097247 / 3628800) * h * (f tn8 yn8 - f tn8 zn8)| :=
      abs_add_le _ _
    have h2 : |(yn8 - zn8)
              + (14097247 / 3628800) * h * (f tn8 yn8 - f tn8 zn8)
              - (43125206 / 3628800) * h * (f tn7 yn7 - f tn7 zn7)|
        ≤ |(yn8 - zn8)
              + (14097247 / 3628800) * h * (f tn8 yn8 - f tn8 zn8)|
          + |(43125206 / 3628800) * h * (f tn7 yn7 - f tn7 zn7)| := abs_sub _ _
    have h3 : |(yn8 - zn8)
              + (14097247 / 3628800) * h * (f tn8 yn8 - f tn8 zn8)
              - (43125206 / 3628800) * h * (f tn7 yn7 - f tn7 zn7)
              + (95476786 / 3628800) * h * (f tn6 yn6 - f tn6 zn6)|
        ≤ |(yn8 - zn8)
              + (14097247 / 3628800) * h * (f tn8 yn8 - f tn8 zn8)
              - (43125206 / 3628800) * h * (f tn7 yn7 - f tn7 zn7)|
          + |(95476786 / 3628800) * h * (f tn6 yn6 - f tn6 zn6)| := abs_add_le _ _
    have h4 : |(yn8 - zn8)
              + (14097247 / 3628800) * h * (f tn8 yn8 - f tn8 zn8)
              - (43125206 / 3628800) * h * (f tn7 yn7 - f tn7 zn7)
              + (95476786 / 3628800) * h * (f tn6 yn6 - f tn6 zn6)
              - (139855262 / 3628800) * h * (f tn5 yn5 - f tn5 zn5)|
        ≤ |(yn8 - zn8)
              + (14097247 / 3628800) * h * (f tn8 yn8 - f tn8 zn8)
              - (43125206 / 3628800) * h * (f tn7 yn7 - f tn7 zn7)
              + (95476786 / 3628800) * h * (f tn6 yn6 - f tn6 zn6)|
          + |(139855262 / 3628800) * h * (f tn5 yn5 - f tn5 zn5)| := abs_sub _ _
    have h5 : |(yn8 - zn8)
              + (14097247 / 3628800) * h * (f tn8 yn8 - f tn8 zn8)
              - (43125206 / 3628800) * h * (f tn7 yn7 - f tn7 zn7)
              + (95476786 / 3628800) * h * (f tn6 yn6 - f tn6 zn6)
              - (139855262 / 3628800) * h * (f tn5 yn5 - f tn5 zn5)
              + (137968480 / 3628800) * h * (f tn4 yn4 - f tn4 zn4)|
        ≤ |(yn8 - zn8)
              + (14097247 / 3628800) * h * (f tn8 yn8 - f tn8 zn8)
              - (43125206 / 3628800) * h * (f tn7 yn7 - f tn7 zn7)
              + (95476786 / 3628800) * h * (f tn6 yn6 - f tn6 zn6)
              - (139855262 / 3628800) * h * (f tn5 yn5 - f tn5 zn5)|
          + |(137968480 / 3628800) * h * (f tn4 yn4 - f tn4 zn4)| := abs_add_le _ _
    have h6 : |(yn8 - zn8)
              + (14097247 / 3628800) * h * (f tn8 yn8 - f tn8 zn8)
              - (43125206 / 3628800) * h * (f tn7 yn7 - f tn7 zn7)
              + (95476786 / 3628800) * h * (f tn6 yn6 - f tn6 zn6)
              - (139855262 / 3628800) * h * (f tn5 yn5 - f tn5 zn5)
              + (137968480 / 3628800) * h * (f tn4 yn4 - f tn4 zn4)
              - (91172642 / 3628800) * h * (f tn3 yn3 - f tn3 zn3)|
        ≤ |(yn8 - zn8)
              + (14097247 / 3628800) * h * (f tn8 yn8 - f tn8 zn8)
              - (43125206 / 3628800) * h * (f tn7 yn7 - f tn7 zn7)
              + (95476786 / 3628800) * h * (f tn6 yn6 - f tn6 zn6)
              - (139855262 / 3628800) * h * (f tn5 yn5 - f tn5 zn5)
              + (137968480 / 3628800) * h * (f tn4 yn4 - f tn4 zn4)|
          + |(91172642 / 3628800) * h * (f tn3 yn3 - f tn3 zn3)| := abs_sub _ _
    have h7 : |(yn8 - zn8)
              + (14097247 / 3628800) * h * (f tn8 yn8 - f tn8 zn8)
              - (43125206 / 3628800) * h * (f tn7 yn7 - f tn7 zn7)
              + (95476786 / 3628800) * h * (f tn6 yn6 - f tn6 zn6)
              - (139855262 / 3628800) * h * (f tn5 yn5 - f tn5 zn5)
              + (137968480 / 3628800) * h * (f tn4 yn4 - f tn4 zn4)
              - (91172642 / 3628800) * h * (f tn3 yn3 - f tn3 zn3)
              + (38833486 / 3628800) * h * (f tn2 yn2 - f tn2 zn2)|
        ≤ |(yn8 - zn8)
              + (14097247 / 3628800) * h * (f tn8 yn8 - f tn8 zn8)
              - (43125206 / 3628800) * h * (f tn7 yn7 - f tn7 zn7)
              + (95476786 / 3628800) * h * (f tn6 yn6 - f tn6 zn6)
              - (139855262 / 3628800) * h * (f tn5 yn5 - f tn5 zn5)
              + (137968480 / 3628800) * h * (f tn4 yn4 - f tn4 zn4)
              - (91172642 / 3628800) * h * (f tn3 yn3 - f tn3 zn3)|
          + |(38833486 / 3628800) * h * (f tn2 yn2 - f tn2 zn2)| := abs_add_le _ _
    have h8 : |(yn8 - zn8)
              + (14097247 / 3628800) * h * (f tn8 yn8 - f tn8 zn8)
              - (43125206 / 3628800) * h * (f tn7 yn7 - f tn7 zn7)
              + (95476786 / 3628800) * h * (f tn6 yn6 - f tn6 zn6)
              - (139855262 / 3628800) * h * (f tn5 yn5 - f tn5 zn5)
              + (137968480 / 3628800) * h * (f tn4 yn4 - f tn4 zn4)
              - (91172642 / 3628800) * h * (f tn3 yn3 - f tn3 zn3)
              + (38833486 / 3628800) * h * (f tn2 yn2 - f tn2 zn2)
              - (9664106 / 3628800) * h * (f tn1 yn1 - f tn1 zn1)|
        ≤ |(yn8 - zn8)
              + (14097247 / 3628800) * h * (f tn8 yn8 - f tn8 zn8)
              - (43125206 / 3628800) * h * (f tn7 yn7 - f tn7 zn7)
              + (95476786 / 3628800) * h * (f tn6 yn6 - f tn6 zn6)
              - (139855262 / 3628800) * h * (f tn5 yn5 - f tn5 zn5)
              + (137968480 / 3628800) * h * (f tn4 yn4 - f tn4 zn4)
              - (91172642 / 3628800) * h * (f tn3 yn3 - f tn3 zn3)
              + (38833486 / 3628800) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(9664106 / 3628800) * h * (f tn1 yn1 - f tn1 zn1)| := abs_sub _ _
    have h9 : |S| ≤ |(yn8 - zn8)
              + (14097247 / 3628800) * h * (f tn8 yn8 - f tn8 zn8)
              - (43125206 / 3628800) * h * (f tn7 yn7 - f tn7 zn7)
              + (95476786 / 3628800) * h * (f tn6 yn6 - f tn6 zn6)
              - (139855262 / 3628800) * h * (f tn5 yn5 - f tn5 zn5)
              + (137968480 / 3628800) * h * (f tn4 yn4 - f tn4 zn4)
              - (91172642 / 3628800) * h * (f tn3 yn3 - f tn3 zn3)
              + (38833486 / 3628800) * h * (f tn2 yn2 - f tn2 zn2)
              - (9664106 / 3628800) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(1070017 / 3628800) * h * (f tn yn - f tn zn)| := by
      show |_| ≤ _
      exact abs_add_le _ _
    linarith
  have htri : |S - τ| ≤ |S| + |τ| := abs_sub _ _
  calc |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 9) - zn9|
      = |S - τ| := by rw [hcalc]
    _ ≤ |S| + |τ| := htri
    _ ≤ |yn8 - zn8|
          + |(14097247 / 3628800) * h * (f tn8 yn8 - f tn8 zn8)|
          + |(43125206 / 3628800) * h * (f tn7 yn7 - f tn7 zn7)|
          + |(95476786 / 3628800) * h * (f tn6 yn6 - f tn6 zn6)|
          + |(139855262 / 3628800) * h * (f tn5 yn5 - f tn5 zn5)|
          + |(137968480 / 3628800) * h * (f tn4 yn4 - f tn4 zn4)|
          + |(91172642 / 3628800) * h * (f tn3 yn3 - f tn3 zn3)|
          + |(38833486 / 3628800) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(9664106 / 3628800) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(1070017 / 3628800) * h * (f tn yn - f tn zn)|
          + |τ| := by linarith
    _ ≤ |yn8 - zn8|
          + (14097247 / 3628800) * h * L * |yn8 - zn8|
          + (43125206 / 3628800) * h * L * |yn7 - zn7|
          + (95476786 / 3628800) * h * L * |yn6 - zn6|
          + (139855262 / 3628800) * h * L * |yn5 - zn5|
          + (137968480 / 3628800) * h * L * |yn4 - zn4|
          + (91172642 / 3628800) * h * L * |yn3 - zn3|
          + (38833486 / 3628800) * h * L * |yn2 - zn2|
          + (9664106 / 3628800) * h * L * |yn1 - zn1|
          + (1070017 / 3628800) * h * L * |yn - zn|
          + |τ| := by
        linarith [h8_abs, h7_abs, h6_abs, h5_abs, h4_abs, h3_abs, h2_abs, h1_abs, h0_abs]

/-- Max-norm one-step error recurrence for AB9 with Lipschitz constant
`L`. With `eN k := |y_k − y(t_k)|` and a 9-window max
`EN k := max (eN k, eN (k+1), …, eN (k+8))`,
`EN (n+1) ≤ (1 + h · (2231497/14175) · L) · EN n + |τ_n|`. The
`(2231497/14175)` factor is the ℓ¹-norm of the AB9 coefficient vector. -/
theorem ab9_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : ℝ) (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max (max (max (max (max (max (max
          |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
          |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|)
          |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|)
          |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|)
          |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|)
          |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|)
          |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)|)
          |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)|)
        |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)|
      ≤ (1 + h * ((2231497 / 14175) * L))
            * max (max (max (max (max (max (max (max
                  |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ n
                      - y (t₀ + (n : ℝ) * h)|
                  |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 1)
                      - y (t₀ + ((n : ℝ) + 1) * h)|)
                  |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 2)
                      - y (t₀ + ((n : ℝ) + 2) * h)|)
                  |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 3)
                      - y (t₀ + ((n : ℝ) + 3) * h)|)
                  |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 4)
                      - y (t₀ + ((n : ℝ) + 4) * h)|)
                  |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 5)
                      - y (t₀ + ((n : ℝ) + 5) * h)|)
                  |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 6)
                      - y (t₀ + ((n : ℝ) + 6) * h)|)
                  |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 7)
                      - y (t₀ + ((n : ℝ) + 7) * h)|)
                  |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 8)
                      - y (t₀ + ((n : ℝ) + 8) * h)|
        + |adamsBashforth9.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set en : ℝ := |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ n - y (t₀ + (n : ℝ) * h)|
    with hen_def
  set en1 : ℝ :=
    |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
    with hen1_def
  set en2 : ℝ :=
    |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|
    with hen2_def
  set en3 : ℝ :=
    |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|
    with hen3_def
  set en4 : ℝ :=
    |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|
    with hen4_def
  set en5 : ℝ :=
    |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 5) - y (t₀ + ((n : ℝ) + 5) * h)|
    with hen5_def
  set en6 : ℝ :=
    |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 6) - y (t₀ + ((n : ℝ) + 6) * h)|
    with hen6_def
  set en7 : ℝ :=
    |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 7) - y (t₀ + ((n : ℝ) + 7) * h)|
    with hen7_def
  set en8 : ℝ :=
    |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)|
    with hen8_def
  set en9 : ℝ :=
    |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)|
    with hen9_def
  set τabs : ℝ :=
    |adamsBashforth9.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  have hen_nn : 0 ≤ en := abs_nonneg _
  have hen1_nn : 0 ≤ en1 := abs_nonneg _
  have hen2_nn : 0 ≤ en2 := abs_nonneg _
  have hen3_nn : 0 ≤ en3 := abs_nonneg _
  have hen4_nn : 0 ≤ en4 := abs_nonneg _
  have hen5_nn : 0 ≤ en5 := abs_nonneg _
  have hen6_nn : 0 ≤ en6 := abs_nonneg _
  have hen7_nn : 0 ≤ en7 := abs_nonneg _
  have hen8_nn : 0 ≤ en8 := abs_nonneg _
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  -- One-step Lipschitz bound (from `ab9_one_step_lipschitz`).
  have hstep :
      en9 ≤ en8 + (14097247 / 3628800) * h * L * en8
                + (43125206 / 3628800) * h * L * en7
                + (95476786 / 3628800) * h * L * en6
                + (139855262 / 3628800) * h * L * en5
                + (137968480 / 3628800) * h * L * en4
                + (91172642 / 3628800) * h * L * en3
                + (38833486 / 3628800) * h * L * en2
                + (9664106 / 3628800) * h * L * en1
                + (1070017 / 3628800) * h * L * en + τabs := by
    have := ab9_one_step_lipschitz hh hf t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y hyf n
    show |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 9) - y (t₀ + ((n : ℝ) + 9) * h)|
        ≤ |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 8) - y (t₀ + ((n : ℝ) + 8) * h)|
          + (14097247 / 3628800) * h * L
              * |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 8)
                  - y (t₀ + ((n : ℝ) + 8) * h)|
          + (43125206 / 3628800) * h * L
              * |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 7)
                  - y (t₀ + ((n : ℝ) + 7) * h)|
          + (95476786 / 3628800) * h * L
              * |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 6)
                  - y (t₀ + ((n : ℝ) + 6) * h)|
          + (139855262 / 3628800) * h * L
              * |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 5)
                  - y (t₀ + ((n : ℝ) + 5) * h)|
          + (137968480 / 3628800) * h * L
              * |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 4)
                  - y (t₀ + ((n : ℝ) + 4) * h)|
          + (91172642 / 3628800) * h * L
              * |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 3)
                  - y (t₀ + ((n : ℝ) + 3) * h)|
          + (38833486 / 3628800) * h * L
              * |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 2)
                  - y (t₀ + ((n : ℝ) + 2) * h)|
          + (9664106 / 3628800) * h * L
              * |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ (n + 1)
                  - y (t₀ + ((n : ℝ) + 1) * h)|
          + (1070017 / 3628800) * h * L
              * |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ n - y (t₀ + (n : ℝ) * h)|
          + |adamsBashforth9.localTruncationError h (t₀ + (n : ℝ) * h) y|
    exact this
  set EN_n : ℝ :=
    max (max (max (max (max (max (max (max en en1) en2) en3) en4) en5) en6) en7) en8
    with hEN_n_def
  have hen_le_EN : en ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans
      (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)
  have hen1_le_EN : en1 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans
      (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)
  have hen2_le_EN : en2 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_trans (le_trans
      (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)
  have hen3_le_EN : en3 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_trans
      (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _)
  have hen4_le_EN : en4 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_trans (le_max_right _ _)
      (le_max_left _ _)) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)
  have hen5_le_EN : en5 ≤ EN_n :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_max_left _ _)) (le_max_left _ _)
  have hen6_le_EN : en6 ≤ EN_n :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hen7_le_EN : en7 ≤ EN_n :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hen8_le_EN : en8 ≤ EN_n := le_max_right _ _
  have hc8_nn : 0 ≤ (14097247 / 3628800) * h * L := by positivity
  have hc7_nn : 0 ≤ (43125206 / 3628800) * h * L := by positivity
  have hc6_nn : 0 ≤ (95476786 / 3628800) * h * L := by positivity
  have hc5_nn : 0 ≤ (139855262 / 3628800) * h * L := by positivity
  have hc4_nn : 0 ≤ (137968480 / 3628800) * h * L := by positivity
  have hc3_nn : 0 ≤ (91172642 / 3628800) * h * L := by positivity
  have hc2_nn : 0 ≤ (38833486 / 3628800) * h * L := by positivity
  have hc1_nn : 0 ≤ (9664106 / 3628800) * h * L := by positivity
  have hc0_nn : 0 ≤ (1070017 / 3628800) * h * L := by positivity
  have hEN_nn : 0 ≤ EN_n := le_trans hen_nn hen_le_EN
  have hcoef_nn : 0 ≤ h * ((2231497 / 14175) * L) := by positivity
  have hen9_bd : en9 ≤ (1 + h * ((2231497 / 14175) * L)) * EN_n + τabs := by
    have h1 : (14097247 / 3628800) * h * L * en8 ≤ (14097247 / 3628800) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen8_le_EN hc8_nn
    have h2 : (43125206 / 3628800) * h * L * en7 ≤ (43125206 / 3628800) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen7_le_EN hc7_nn
    have h3 : (95476786 / 3628800) * h * L * en6 ≤ (95476786 / 3628800) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen6_le_EN hc6_nn
    have h4 : (139855262 / 3628800) * h * L * en5 ≤ (139855262 / 3628800) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen5_le_EN hc5_nn
    have h5 : (137968480 / 3628800) * h * L * en4 ≤ (137968480 / 3628800) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen4_le_EN hc4_nn
    have h6 : (91172642 / 3628800) * h * L * en3 ≤ (91172642 / 3628800) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen3_le_EN hc3_nn
    have h7 : (38833486 / 3628800) * h * L * en2 ≤ (38833486 / 3628800) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen2_le_EN hc2_nn
    have h8 : (9664106 / 3628800) * h * L * en1 ≤ (9664106 / 3628800) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen1_le_EN hc1_nn
    have h9 : (1070017 / 3628800) * h * L * en ≤ (1070017 / 3628800) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen_le_EN hc0_nn
    have h_alg :
        EN_n + (14097247 / 3628800) * h * L * EN_n
              + (43125206 / 3628800) * h * L * EN_n
              + (95476786 / 3628800) * h * L * EN_n
              + (139855262 / 3628800) * h * L * EN_n
              + (137968480 / 3628800) * h * L * EN_n
              + (91172642 / 3628800) * h * L * EN_n
              + (38833486 / 3628800) * h * L * EN_n
              + (9664106 / 3628800) * h * L * EN_n
              + (1070017 / 3628800) * h * L * EN_n + τabs
          = (1 + h * ((2231497 / 14175) * L)) * EN_n + τabs := by ring
    linarith [hstep, hen8_le_EN, h1, h2, h3, h4, h5, h6, h7, h8, h9, h_alg.le]
  have hEN_le_grow : EN_n ≤ (1 + h * ((2231497 / 14175) * L)) * EN_n := by
    have hone : (1 : ℝ) * EN_n ≤ (1 + h * ((2231497 / 14175) * L)) * EN_n :=
      mul_le_mul_of_nonneg_right (by linarith) hEN_nn
    linarith
  have hen1_bd : en1 ≤ (1 + h * ((2231497 / 14175) * L)) * EN_n + τabs := by
    linarith [hen1_le_EN, hEN_le_grow]
  have hen2_bd : en2 ≤ (1 + h * ((2231497 / 14175) * L)) * EN_n + τabs := by
    linarith [hen2_le_EN, hEN_le_grow]
  have hen3_bd : en3 ≤ (1 + h * ((2231497 / 14175) * L)) * EN_n + τabs := by
    linarith [hen3_le_EN, hEN_le_grow]
  have hen4_bd : en4 ≤ (1 + h * ((2231497 / 14175) * L)) * EN_n + τabs := by
    linarith [hen4_le_EN, hEN_le_grow]
  have hen5_bd : en5 ≤ (1 + h * ((2231497 / 14175) * L)) * EN_n + τabs := by
    linarith [hen5_le_EN, hEN_le_grow]
  have hen6_bd : en6 ≤ (1 + h * ((2231497 / 14175) * L)) * EN_n + τabs := by
    linarith [hen6_le_EN, hEN_le_grow]
  have hen7_bd : en7 ≤ (1 + h * ((2231497 / 14175) * L)) * EN_n + τabs := by
    linarith [hen7_le_EN, hEN_le_grow]
  have hen8_bd : en8 ≤ (1 + h * ((2231497 / 14175) * L)) * EN_n + τabs := by
    linarith [hen8_le_EN, hEN_le_grow]
  exact max_le (max_le (max_le (max_le (max_le (max_le (max_le (max_le hen1_bd hen2_bd)
    hen3_bd) hen4_bd) hen5_bd) hen6_bd) hen7_bd) hen8_bd) hen9_bd

/-- Algebraic identity decomposing the AB9 local truncation residual into
two y 10th-order Taylor remainders (at `8h` and `9h`) and eight y'
9th-order Taylor remainders (at `h, 2h, …, 8h`). Pure `ring` identity. -/
private lemma ab9_residual_alg_identity
    (y0 y8 y9 d0 d1 d2 d3 d4 d5 d6 d7 d8 dd ddd dddd ddddd dddddd ddddddd
      dddddddd ddddddddd h : ℝ) :
    y9 - y8 - h * ((14097247 / 3628800) * d8 - (43125206 / 3628800) * d7
                  + (95476786 / 3628800) * d6 - (139855262 / 3628800) * d5
                  + (137968480 / 3628800) * d4 - (91172642 / 3628800) * d3
                  + (38833486 / 3628800) * d2 - (9664106 / 3628800) * d1
                  + (1070017 / 3628800) * d0)
      = (y9 - y0 - (9 * h) * d0
            - (9 * h) ^ 2 / 2 * dd
            - (9 * h) ^ 3 / 6 * ddd
            - (9 * h) ^ 4 / 24 * dddd
            - (9 * h) ^ 5 / 120 * ddddd
            - (9 * h) ^ 6 / 720 * dddddd
            - (9 * h) ^ 7 / 5040 * ddddddd
            - (9 * h) ^ 8 / 40320 * dddddddd
            - (9 * h) ^ 9 / 362880 * ddddddddd)
        - (y8 - y0 - (8 * h) * d0
            - (8 * h) ^ 2 / 2 * dd
            - (8 * h) ^ 3 / 6 * ddd
            - (8 * h) ^ 4 / 24 * dddd
            - (8 * h) ^ 5 / 120 * ddddd
            - (8 * h) ^ 6 / 720 * dddddd
            - (8 * h) ^ 7 / 5040 * ddddddd
            - (8 * h) ^ 8 / 40320 * dddddddd
            - (8 * h) ^ 9 / 362880 * ddddddddd)
        - (14097247 * h / 3628800)
            * (d8 - d0 - (8 * h) * dd
                - (8 * h) ^ 2 / 2 * ddd
                - (8 * h) ^ 3 / 6 * dddd
                - (8 * h) ^ 4 / 24 * ddddd
                - (8 * h) ^ 5 / 120 * dddddd
                - (8 * h) ^ 6 / 720 * ddddddd
                - (8 * h) ^ 7 / 5040 * dddddddd
                - (8 * h) ^ 8 / 40320 * ddddddddd)
        + (43125206 * h / 3628800)
            * (d7 - d0 - (7 * h) * dd
                - (7 * h) ^ 2 / 2 * ddd
                - (7 * h) ^ 3 / 6 * dddd
                - (7 * h) ^ 4 / 24 * ddddd
                - (7 * h) ^ 5 / 120 * dddddd
                - (7 * h) ^ 6 / 720 * ddddddd
                - (7 * h) ^ 7 / 5040 * dddddddd
                - (7 * h) ^ 8 / 40320 * ddddddddd)
        - (95476786 * h / 3628800)
            * (d6 - d0 - (6 * h) * dd
                - (6 * h) ^ 2 / 2 * ddd
                - (6 * h) ^ 3 / 6 * dddd
                - (6 * h) ^ 4 / 24 * ddddd
                - (6 * h) ^ 5 / 120 * dddddd
                - (6 * h) ^ 6 / 720 * ddddddd
                - (6 * h) ^ 7 / 5040 * dddddddd
                - (6 * h) ^ 8 / 40320 * ddddddddd)
        + (139855262 * h / 3628800)
            * (d5 - d0 - (5 * h) * dd
                - (5 * h) ^ 2 / 2 * ddd
                - (5 * h) ^ 3 / 6 * dddd
                - (5 * h) ^ 4 / 24 * ddddd
                - (5 * h) ^ 5 / 120 * dddddd
                - (5 * h) ^ 6 / 720 * ddddddd
                - (5 * h) ^ 7 / 5040 * dddddddd
                - (5 * h) ^ 8 / 40320 * ddddddddd)
        - (137968480 * h / 3628800)
            * (d4 - d0 - (4 * h) * dd
                - (4 * h) ^ 2 / 2 * ddd
                - (4 * h) ^ 3 / 6 * dddd
                - (4 * h) ^ 4 / 24 * ddddd
                - (4 * h) ^ 5 / 120 * dddddd
                - (4 * h) ^ 6 / 720 * ddddddd
                - (4 * h) ^ 7 / 5040 * dddddddd
                - (4 * h) ^ 8 / 40320 * ddddddddd)
        + (91172642 * h / 3628800)
            * (d3 - d0 - (3 * h) * dd
                - (3 * h) ^ 2 / 2 * ddd
                - (3 * h) ^ 3 / 6 * dddd
                - (3 * h) ^ 4 / 24 * ddddd
                - (3 * h) ^ 5 / 120 * dddddd
                - (3 * h) ^ 6 / 720 * ddddddd
                - (3 * h) ^ 7 / 5040 * dddddddd
                - (3 * h) ^ 8 / 40320 * ddddddddd)
        - (38833486 * h / 3628800)
            * (d2 - d0 - (2 * h) * dd
                - (2 * h) ^ 2 / 2 * ddd
                - (2 * h) ^ 3 / 6 * dddd
                - (2 * h) ^ 4 / 24 * ddddd
                - (2 * h) ^ 5 / 120 * dddddd
                - (2 * h) ^ 6 / 720 * ddddddd
                - (2 * h) ^ 7 / 5040 * dddddddd
                - (2 * h) ^ 8 / 40320 * ddddddddd)
        + (9664106 * h / 3628800)
            * (d1 - d0 - h * dd
                - h ^ 2 / 2 * ddd
                - h ^ 3 / 6 * dddd
                - h ^ 4 / 24 * ddddd
                - h ^ 5 / 120 * dddddd
                - h ^ 6 / 720 * ddddddd
                - h ^ 7 / 5040 * dddddddd
                - h ^ 8 / 40320 * ddddddddd) := by
  ring

/-- Pure algebraic identity: the sum of the ten scaled Lagrange remainder
bounds equals a fixed rational coefficient times `M · h^10`. -/
private lemma ab9_residual_bound_alg_identity (M h : ℝ) :
    M / 3628800 * (9 * h) ^ 10 + M / 3628800 * (8 * h) ^ 10
      + (14097247 * h / 3628800) * (M / 362880 * (8 * h) ^ 9)
      + (43125206 * h / 3628800) * (M / 362880 * (7 * h) ^ 9)
      + (95476786 * h / 3628800) * (M / 362880 * (6 * h) ^ 9)
      + (139855262 * h / 3628800) * (M / 362880 * (5 * h) ^ 9)
      + (137968480 * h / 3628800) * (M / 362880 * (4 * h) ^ 9)
      + (91172642 * h / 3628800) * (M / 362880 * (3 * h) ^ 9)
      + (38833486 * h / 3628800) * (M / 362880 * (2 * h) ^ 9)
      + (9664106 * h / 3628800) * (M / 362880 * h ^ 9)
      = (102509448755347 / 20575296000 : ℝ) * M * h ^ 10 := by
  ring

/-- Auxiliary triangle inequality for ten abstract terms. The concrete AB9
form is obtained by specialising the scaled summands. -/
private lemma ab9_triangle_aux
    (A B sC sD sE sF sG sH sI sJ : ℝ) :
    |A - B - sC + sD - sE + sF - sG + sH - sI + sJ|
      ≤ |A| + |B| + |sC| + |sD| + |sE| + |sF| + |sG| + |sH| + |sI| + |sJ| := by
  have h1 : |A - B - sC + sD - sE + sF - sG + sH - sI + sJ|
      ≤ |A - B - sC + sD - sE + sF - sG + sH - sI| + |sJ| := abs_add_le _ _
  have h2 : |A - B - sC + sD - sE + sF - sG + sH - sI|
      ≤ |A - B - sC + sD - sE + sF - sG + sH| + |sI| := abs_sub _ _
  have h3 : |A - B - sC + sD - sE + sF - sG + sH|
      ≤ |A - B - sC + sD - sE + sF - sG| + |sH| := abs_add_le _ _
  have h4 : |A - B - sC + sD - sE + sF - sG|
      ≤ |A - B - sC + sD - sE + sF| + |sG| := abs_sub _ _
  have h5 : |A - B - sC + sD - sE + sF|
      ≤ |A - B - sC + sD - sE| + |sF| := abs_add_le _ _
  have h6 : |A - B - sC + sD - sE|
      ≤ |A - B - sC + sD| + |sE| := abs_sub _ _
  have h7 : |A - B - sC + sD| ≤ |A - B - sC| + |sD| := abs_add_le _ _
  have h8 : |A - B - sC| ≤ |A - B| + |sC| := abs_sub _ _
  have h9 : |A - B| ≤ |A| + |B| := abs_sub _ _
  linarith

/-- Triangle inequality for the ten-term AB9 residual chunk. -/
private lemma ab9_residual_ten_term_triangle
    (A B C D E F G H I J h : ℝ) (hh : 0 ≤ h) :
    |A - B - (14097247 * h / 3628800) * C + (43125206 * h / 3628800) * D
        - (95476786 * h / 3628800) * E + (139855262 * h / 3628800) * F
        - (137968480 * h / 3628800) * G + (91172642 * h / 3628800) * H
        - (38833486 * h / 3628800) * I + (9664106 * h / 3628800) * J|
      ≤ |A| + |B| + (14097247 * h / 3628800) * |C| + (43125206 * h / 3628800) * |D|
          + (95476786 * h / 3628800) * |E| + (139855262 * h / 3628800) * |F|
          + (137968480 * h / 3628800) * |G| + (91172642 * h / 3628800) * |H|
          + (38833486 * h / 3628800) * |I| + (9664106 * h / 3628800) * |J| := by
  have hc8_nn : 0 ≤ 14097247 * h / 3628800 := by linarith
  have hc7_nn : 0 ≤ 43125206 * h / 3628800 := by linarith
  have hc6_nn : 0 ≤ 95476786 * h / 3628800 := by linarith
  have hc5_nn : 0 ≤ 139855262 * h / 3628800 := by linarith
  have hc4_nn : 0 ≤ 137968480 * h / 3628800 := by linarith
  have hc3_nn : 0 ≤ 91172642 * h / 3628800 := by linarith
  have hc2_nn : 0 ≤ 38833486 * h / 3628800 := by linarith
  have hc1_nn : 0 ≤ 9664106 * h / 3628800 := by linarith
  have habsC : |(14097247 * h / 3628800) * C| = (14097247 * h / 3628800) * |C| := by
    rw [abs_mul, abs_of_nonneg hc8_nn]
  have habsD : |(43125206 * h / 3628800) * D| = (43125206 * h / 3628800) * |D| := by
    rw [abs_mul, abs_of_nonneg hc7_nn]
  have habsE : |(95476786 * h / 3628800) * E| = (95476786 * h / 3628800) * |E| := by
    rw [abs_mul, abs_of_nonneg hc6_nn]
  have habsF : |(139855262 * h / 3628800) * F| = (139855262 * h / 3628800) * |F| := by
    rw [abs_mul, abs_of_nonneg hc5_nn]
  have habsG : |(137968480 * h / 3628800) * G| = (137968480 * h / 3628800) * |G| := by
    rw [abs_mul, abs_of_nonneg hc4_nn]
  have habsH : |(91172642 * h / 3628800) * H| = (91172642 * h / 3628800) * |H| := by
    rw [abs_mul, abs_of_nonneg hc3_nn]
  have habsI : |(38833486 * h / 3628800) * I| = (38833486 * h / 3628800) * |I| := by
    rw [abs_mul, abs_of_nonneg hc2_nn]
  have habsJ : |(9664106 * h / 3628800) * J| = (9664106 * h / 3628800) * |J| := by
    rw [abs_mul, abs_of_nonneg hc1_nn]
  have htri := ab9_triangle_aux A B
    ((14097247 * h / 3628800) * C) ((43125206 * h / 3628800) * D)
    ((95476786 * h / 3628800) * E) ((139855262 * h / 3628800) * F)
    ((137968480 * h / 3628800) * G) ((91172642 * h / 3628800) * H)
    ((38833486 * h / 3628800) * I) ((9664106 * h / 3628800) * J)
  rw [habsC, habsD, habsE, habsF, habsG, habsH, habsI, habsJ] at htri
  exact htri

/-- Combine the ten Taylor-remainder bounds into the final residual estimate.
Given abstract Taylor remainders `A,B,…,J` with bounds in terms of `M`, the
scaled triangle inequality and the bound algebraic identity, conclude
`≤ 4983 · M · h^10`. -/
private lemma ab9_residual_combine_aux
    (A B C D E F G H I J M h : ℝ) (hh : 0 ≤ h) (hMnn : 0 ≤ M)
    (hA_bd : |A| ≤ M / 3628800 * (9 * h) ^ 10)
    (hB_bd : |B| ≤ M / 3628800 * (8 * h) ^ 10)
    (hC_bd : |C| ≤ M / 362880 * (8 * h) ^ 9)
    (hD_bd : |D| ≤ M / 362880 * (7 * h) ^ 9)
    (hE_bd : |E| ≤ M / 362880 * (6 * h) ^ 9)
    (hF_bd : |F| ≤ M / 362880 * (5 * h) ^ 9)
    (hG_bd : |G| ≤ M / 362880 * (4 * h) ^ 9)
    (hH_bd : |H| ≤ M / 362880 * (3 * h) ^ 9)
    (hI_bd : |I| ≤ M / 362880 * (2 * h) ^ 9)
    (hJ_bd : |J| ≤ M / 362880 * h ^ 9) :
    |A - B - (14097247 * h / 3628800) * C + (43125206 * h / 3628800) * D
        - (95476786 * h / 3628800) * E + (139855262 * h / 3628800) * F
        - (137968480 * h / 3628800) * G + (91172642 * h / 3628800) * H
        - (38833486 * h / 3628800) * I + (9664106 * h / 3628800) * J|
      ≤ 4983 * M * h ^ 10 := by
  have htri := ab9_residual_ten_term_triangle A B C D E F G H I J h hh
  have hc8_nn : 0 ≤ 14097247 * h / 3628800 := by linarith
  have hc7_nn : 0 ≤ 43125206 * h / 3628800 := by linarith
  have hc6_nn : 0 ≤ 95476786 * h / 3628800 := by linarith
  have hc5_nn : 0 ≤ 139855262 * h / 3628800 := by linarith
  have hc4_nn : 0 ≤ 137968480 * h / 3628800 := by linarith
  have hc3_nn : 0 ≤ 91172642 * h / 3628800 := by linarith
  have hc2_nn : 0 ≤ 38833486 * h / 3628800 := by linarith
  have hc1_nn : 0 ≤ 9664106 * h / 3628800 := by linarith
  have hCbd_s : (14097247 * h / 3628800) * |C|
      ≤ (14097247 * h / 3628800) * (M / 362880 * (8 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hC_bd hc8_nn
  have hDbd_s : (43125206 * h / 3628800) * |D|
      ≤ (43125206 * h / 3628800) * (M / 362880 * (7 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hD_bd hc7_nn
  have hEbd_s : (95476786 * h / 3628800) * |E|
      ≤ (95476786 * h / 3628800) * (M / 362880 * (6 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hE_bd hc6_nn
  have hFbd_s : (139855262 * h / 3628800) * |F|
      ≤ (139855262 * h / 3628800) * (M / 362880 * (5 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hF_bd hc5_nn
  have hGbd_s : (137968480 * h / 3628800) * |G|
      ≤ (137968480 * h / 3628800) * (M / 362880 * (4 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hG_bd hc4_nn
  have hHbd_s : (91172642 * h / 3628800) * |H|
      ≤ (91172642 * h / 3628800) * (M / 362880 * (3 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hH_bd hc3_nn
  have hIbd_s : (38833486 * h / 3628800) * |I|
      ≤ (38833486 * h / 3628800) * (M / 362880 * (2 * h) ^ 9) :=
    mul_le_mul_of_nonneg_left hI_bd hc2_nn
  have hJbd_s : (9664106 * h / 3628800) * |J|
      ≤ (9664106 * h / 3628800) * (M / 362880 * h ^ 9) :=
    mul_le_mul_of_nonneg_left hJ_bd hc1_nn
  have hbound_alg := ab9_residual_bound_alg_identity M h
  have hh10_nn : 0 ≤ h ^ 10 := by positivity
  have hMh10_nn : 0 ≤ M * h ^ 10 := mul_nonneg hMnn hh10_nn
  have hslack : (102509448755347 / 20575296000 : ℝ) * M * h ^ 10
      ≤ 4983 * M * h ^ 10 := by
    rw [mul_assoc, mul_assoc (4983 : ℝ)]
    have hle : (102509448755347 / 20575296000 : ℝ) ≤ 4983 := by norm_num
    exact mul_le_mul_of_nonneg_right hle hMh10_nn
  linarith [htri, hbound_alg, hslack, hA_bd, hB_bd, hCbd_s, hDbd_s, hEbd_s,
    hFbd_s, hGbd_s, hHbd_s, hIbd_s, hJbd_s]

/-- AB9 residual at a single base point `t` is `O(M · h^10)`, where `M`
bounds the 10th derivative of the exact solution on a window covering
`[t, t + 9h]`. Decomposes the residual into ten Taylor remainders
(two y 10th-order, eight y' 9th-order). -/
private theorem ab9_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 10 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 10 y t| ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (ht4h : t + 4 * h ∈ Set.Icc a b)
    (ht5h : t + 5 * h ∈ Set.Icc a b)
    (ht6h : t + 6 * h ∈ Set.Icc a b)
    (ht7h : t + 7 * h ∈ Set.Icc a b)
    (ht8h : t + 8 * h ∈ Set.Icc a b)
    (ht9h : t + 9 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    |y (t + 9 * h) - y (t + 8 * h)
        - h * ((14097247 / 3628800) * deriv y (t + 8 * h)
              - (43125206 / 3628800) * deriv y (t + 7 * h)
              + (95476786 / 3628800) * deriv y (t + 6 * h)
              - (139855262 / 3628800) * deriv y (t + 5 * h)
              + (137968480 / 3628800) * deriv y (t + 4 * h)
              - (91172642 / 3628800) * deriv y (t + 3 * h)
              + (38833486 / 3628800) * deriv y (t + 2 * h)
              - (9664106 / 3628800) * deriv y (t + h)
              + (1070017 / 3628800) * deriv y t)|
      ≤ (4983 : ℝ) * M * h ^ 10 := by
  -- Ten Taylor remainders.
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have h5h : 0 ≤ 5 * h := by linarith
  have h6h : 0 ≤ 6 * h := by linarith
  have h7h : 0 ≤ 7 * h := by linarith
  have h8h : 0 ≤ 8 * h := by linarith
  have h9h : 0 ≤ 9 * h := by linarith
  -- R_y(8), R_y(9): y Taylor remainders at order 10.
  have hRy8 :=
    y_tenth_order_taylor_remainder hy hbnd ht ht8h h8h
  have hRy9 :=
    y_tenth_order_taylor_remainder hy hbnd ht ht9h h9h
  -- R_y'(1), …, R_y'(8): y' Taylor remainders at order 9.
  have hRyp1 :=
    derivY_ninth_order_taylor_remainder hy hbnd ht hth hh
  have hRyp2 :=
    derivY_ninth_order_taylor_remainder hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_ninth_order_taylor_remainder hy hbnd ht ht3h h3h
  have hRyp4 :=
    derivY_ninth_order_taylor_remainder hy hbnd ht ht4h h4h
  have hRyp5 :=
    derivY_ninth_order_taylor_remainder hy hbnd ht ht5h h5h
  have hRyp6 :=
    derivY_ninth_order_taylor_remainder hy hbnd ht ht6h h6h
  have hRyp7 :=
    derivY_ninth_order_taylor_remainder hy hbnd ht ht7h h7h
  have hRyp8 :=
    derivY_ninth_order_taylor_remainder hy hbnd ht ht8h h8h
  -- Abbreviations.
  set y0 := y t with hy0_def
  set y8 := y (t + 8 * h) with hy8_def
  set y9 := y (t + 9 * h) with hy9_def
  set d0 := deriv y t with hd0_def
  set d1 := deriv y (t + h) with hd1_def
  set d2 := deriv y (t + 2 * h) with hd2_def
  set d3 := deriv y (t + 3 * h) with hd3_def
  set d4 := deriv y (t + 4 * h) with hd4_def
  set d5 := deriv y (t + 5 * h) with hd5_def
  set d6 := deriv y (t + 6 * h) with hd6_def
  set d7 := deriv y (t + 7 * h) with hd7_def
  set d8 := deriv y (t + 8 * h) with hd8_def
  set dd := iteratedDeriv 2 y t with hdd_def
  set ddd := iteratedDeriv 3 y t with hddd_def
  set dddd := iteratedDeriv 4 y t with hdddd_def
  set ddddd := iteratedDeriv 5 y t with hddddd_def
  set dddddd := iteratedDeriv 6 y t with hdddddd_def
  set ddddddd := iteratedDeriv 7 y t with hddddddd_def
  set dddddddd := iteratedDeriv 8 y t with hdddddddd_def
  set ddddddddd := iteratedDeriv 9 y t with hddddddddd_def
  clear_value y0 y8 y9 d0 d1 d2 d3 d4 d5 d6 d7 d8
    dd ddd dddd ddddd dddddd ddddddd dddddddd ddddddddd
  -- Algebraic identity for the residual.
  have hLTE_eq :=
    ab9_residual_alg_identity y0 y8 y9 d0 d1 d2 d3 d4 d5 d6 d7 d8
      dd ddd dddd ddddd dddddd ddddddd dddddddd ddddddddd h
  rw [hLTE_eq]
  -- Triangle inequality (chained).
  set A := y9 - y0 - (9 * h) * d0
            - (9 * h) ^ 2 / 2 * dd
            - (9 * h) ^ 3 / 6 * ddd
            - (9 * h) ^ 4 / 24 * dddd
            - (9 * h) ^ 5 / 120 * ddddd
            - (9 * h) ^ 6 / 720 * dddddd
            - (9 * h) ^ 7 / 5040 * ddddddd
            - (9 * h) ^ 8 / 40320 * dddddddd
            - (9 * h) ^ 9 / 362880 * ddddddddd with hA_def
  set B := y8 - y0 - (8 * h) * d0
            - (8 * h) ^ 2 / 2 * dd
            - (8 * h) ^ 3 / 6 * ddd
            - (8 * h) ^ 4 / 24 * dddd
            - (8 * h) ^ 5 / 120 * ddddd
            - (8 * h) ^ 6 / 720 * dddddd
            - (8 * h) ^ 7 / 5040 * ddddddd
            - (8 * h) ^ 8 / 40320 * dddddddd
            - (8 * h) ^ 9 / 362880 * ddddddddd with hB_def
  set C := d8 - d0 - (8 * h) * dd
            - (8 * h) ^ 2 / 2 * ddd
            - (8 * h) ^ 3 / 6 * dddd
            - (8 * h) ^ 4 / 24 * ddddd
            - (8 * h) ^ 5 / 120 * dddddd
            - (8 * h) ^ 6 / 720 * ddddddd
            - (8 * h) ^ 7 / 5040 * dddddddd
            - (8 * h) ^ 8 / 40320 * ddddddddd with hC_def
  set D := d7 - d0 - (7 * h) * dd
            - (7 * h) ^ 2 / 2 * ddd
            - (7 * h) ^ 3 / 6 * dddd
            - (7 * h) ^ 4 / 24 * ddddd
            - (7 * h) ^ 5 / 120 * dddddd
            - (7 * h) ^ 6 / 720 * ddddddd
            - (7 * h) ^ 7 / 5040 * dddddddd
            - (7 * h) ^ 8 / 40320 * ddddddddd with hD_def
  set E := d6 - d0 - (6 * h) * dd
            - (6 * h) ^ 2 / 2 * ddd
            - (6 * h) ^ 3 / 6 * dddd
            - (6 * h) ^ 4 / 24 * ddddd
            - (6 * h) ^ 5 / 120 * dddddd
            - (6 * h) ^ 6 / 720 * ddddddd
            - (6 * h) ^ 7 / 5040 * dddddddd
            - (6 * h) ^ 8 / 40320 * ddddddddd with hE_def
  set F := d5 - d0 - (5 * h) * dd
            - (5 * h) ^ 2 / 2 * ddd
            - (5 * h) ^ 3 / 6 * dddd
            - (5 * h) ^ 4 / 24 * ddddd
            - (5 * h) ^ 5 / 120 * dddddd
            - (5 * h) ^ 6 / 720 * ddddddd
            - (5 * h) ^ 7 / 5040 * dddddddd
            - (5 * h) ^ 8 / 40320 * ddddddddd with hF_def
  set G := d4 - d0 - (4 * h) * dd
            - (4 * h) ^ 2 / 2 * ddd
            - (4 * h) ^ 3 / 6 * dddd
            - (4 * h) ^ 4 / 24 * ddddd
            - (4 * h) ^ 5 / 120 * dddddd
            - (4 * h) ^ 6 / 720 * ddddddd
            - (4 * h) ^ 7 / 5040 * dddddddd
            - (4 * h) ^ 8 / 40320 * ddddddddd with hG_def
  set H := d3 - d0 - (3 * h) * dd
            - (3 * h) ^ 2 / 2 * ddd
            - (3 * h) ^ 3 / 6 * dddd
            - (3 * h) ^ 4 / 24 * ddddd
            - (3 * h) ^ 5 / 120 * dddddd
            - (3 * h) ^ 6 / 720 * ddddddd
            - (3 * h) ^ 7 / 5040 * dddddddd
            - (3 * h) ^ 8 / 40320 * ddddddddd with hH_def
  set I := d2 - d0 - (2 * h) * dd
            - (2 * h) ^ 2 / 2 * ddd
            - (2 * h) ^ 3 / 6 * dddd
            - (2 * h) ^ 4 / 24 * ddddd
            - (2 * h) ^ 5 / 120 * dddddd
            - (2 * h) ^ 6 / 720 * ddddddd
            - (2 * h) ^ 7 / 5040 * dddddddd
            - (2 * h) ^ 8 / 40320 * ddddddddd with hI_def
  set J := d1 - d0 - h * dd
            - h ^ 2 / 2 * ddd
            - h ^ 3 / 6 * dddd
            - h ^ 4 / 24 * ddddd
            - h ^ 5 / 120 * dddddd
            - h ^ 6 / 720 * ddddddd
            - h ^ 7 / 5040 * dddddddd
            - h ^ 8 / 40320 * ddddddddd with hJ_def
  clear_value A B C D E F G H I J
  -- Bounds on each piece.
  have hA_bd : |A| ≤ M / 3628800 * (9 * h) ^ 10 := hRy9
  have hB_bd : |B| ≤ M / 3628800 * (8 * h) ^ 10 := hRy8
  have hC_bd : |C| ≤ M / 362880 * (8 * h) ^ 9 := hRyp8
  have hD_bd : |D| ≤ M / 362880 * (7 * h) ^ 9 := hRyp7
  have hE_bd : |E| ≤ M / 362880 * (6 * h) ^ 9 := hRyp6
  have hF_bd : |F| ≤ M / 362880 * (5 * h) ^ 9 := hRyp5
  have hG_bd : |G| ≤ M / 362880 * (4 * h) ^ 9 := hRyp4
  have hH_bd : |H| ≤ M / 362880 * (3 * h) ^ 9 := hRyp3
  have hI_bd : |I| ≤ M / 362880 * (2 * h) ^ 9 := hRyp2
  have hJ_bd : |J| ≤ M / 362880 * h ^ 9 := hRyp1
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (abs_nonneg _).trans this
  exact ab9_residual_combine_aux A B C D E F G H I J M h hh hMnn
    hA_bd hB_bd hC_bd hD_bd hE_bd hF_bd hG_bd hH_bd hI_bd hJ_bd

/-- Uniform bound on the AB9 one-step truncation residual on a finite
horizon, given a `C^10` exact solution. -/
theorem ab9_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 10 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 9) * h ≤ T →
        |adamsBashforth9.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 10 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_ten_bounded_on_Icc hy t₀ (t₀ + T + 1)
  refine ⟨(4983 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 9) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 9) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 9) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 9) * h := by nlinarith
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 4 * h ≤ ((n : ℝ) + 9) * h := by nlinarith
    linarith
  have ht5h_mem : t + 5 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 5 * h ≤ ((n : ℝ) + 9) * h := by nlinarith
    linarith
  have ht6h_mem : t + 6 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 6 * h ≤ ((n : ℝ) + 9) * h := by nlinarith
    linarith
  have ht7h_mem : t + 7 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 7 * h ≤ ((n : ℝ) + 9) * h := by nlinarith
    linarith
  have ht8h_mem : t + 8 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 8 * h ≤ ((n : ℝ) + 9) * h := by nlinarith
    linarith
  have ht9h_mem : t + 9 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 9 * h = ((n : ℝ) + 9) * h := by ring
    linarith
  -- Rewrite the LTE in textbook form.
  rw [ab9_localTruncationError_eq]
  show |y (t + 9 * h) - y (t + 8 * h)
      - h * (14097247 / 3628800 * deriv y (t + 8 * h)
              - 43125206 / 3628800 * deriv y (t + 7 * h)
              + 95476786 / 3628800 * deriv y (t + 6 * h)
              - 139855262 / 3628800 * deriv y (t + 5 * h)
              + 137968480 / 3628800 * deriv y (t + 4 * h)
              - 91172642 / 3628800 * deriv y (t + 3 * h)
              + 38833486 / 3628800 * deriv y (t + 2 * h)
              - 9664106 / 3628800 * deriv y (t + h)
              + 1070017 / 3628800 * deriv y t)|
    ≤ 4983 * M * h ^ 10
  have hreshape :
      h * (14097247 / 3628800 * deriv y (t + 8 * h)
            - 43125206 / 3628800 * deriv y (t + 7 * h)
            + 95476786 / 3628800 * deriv y (t + 6 * h)
            - 139855262 / 3628800 * deriv y (t + 5 * h)
            + 137968480 / 3628800 * deriv y (t + 4 * h)
            - 91172642 / 3628800 * deriv y (t + 3 * h)
            + 38833486 / 3628800 * deriv y (t + 2 * h)
            - 9664106 / 3628800 * deriv y (t + h)
            + 1070017 / 3628800 * deriv y t)
        = h * ((14097247 / 3628800) * deriv y (t + 8 * h)
              - (43125206 / 3628800) * deriv y (t + 7 * h)
              + (95476786 / 3628800) * deriv y (t + 6 * h)
              - (139855262 / 3628800) * deriv y (t + 5 * h)
              + (137968480 / 3628800) * deriv y (t + 4 * h)
              - (91172642 / 3628800) * deriv y (t + 3 * h)
              + (38833486 / 3628800) * deriv y (t + 2 * h)
              - (9664106 / 3628800) * deriv y (t + h)
              + (1070017 / 3628800) * deriv y t) := by ring
  rw [hreshape]
  exact ab9_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem ht4h_mem ht5h_mem ht6h_mem ht7h_mem ht8h_mem ht9h_mem hh.le

/-! #### Generic AB scalar bridge

Routes the scalar AB9 headline through the generic AB scaffold at `s = 9`. -/

/-- AB9 coefficient vector for the generic AB scaffold, ordered from the
oldest to newest sample in the nine-step window. -/
noncomputable def ab9GenericCoeff : Fin 9 → ℝ :=
  ![(1070017 : ℝ) / 3628800, -(9664106 : ℝ) / 3628800,
    (38833486 : ℝ) / 3628800, -(91172642 : ℝ) / 3628800,
    (137968480 : ℝ) / 3628800, -(139855262 : ℝ) / 3628800,
    (95476786 : ℝ) / 3628800, -(43125206 : ℝ) / 3628800,
    (14097247 : ℝ) / 3628800]

@[simp] lemma ab9GenericCoeff_zero :
    ab9GenericCoeff 0 = (1070017 : ℝ) / 3628800 := rfl

@[simp] lemma ab9GenericCoeff_one :
    ab9GenericCoeff 1 = -(9664106 : ℝ) / 3628800 := rfl

@[simp] lemma ab9GenericCoeff_two :
    ab9GenericCoeff 2 = (38833486 : ℝ) / 3628800 := rfl

@[simp] lemma ab9GenericCoeff_three :
    ab9GenericCoeff 3 = -(91172642 : ℝ) / 3628800 := rfl

@[simp] lemma ab9GenericCoeff_four :
    ab9GenericCoeff 4 = (137968480 : ℝ) / 3628800 := rfl

@[simp] lemma ab9GenericCoeff_five :
    ab9GenericCoeff 5 = -(139855262 : ℝ) / 3628800 := rfl

@[simp] lemma ab9GenericCoeff_six :
    ab9GenericCoeff 6 = (95476786 : ℝ) / 3628800 := rfl

@[simp] lemma ab9GenericCoeff_seven :
    ab9GenericCoeff 7 = -(43125206 : ℝ) / 3628800 := rfl

@[simp] lemma ab9GenericCoeff_eight :
    ab9GenericCoeff 8 = (14097247 : ℝ) / 3628800 := rfl

/-- Helper: expand `∑ i : Fin 9, f i` as nine summands. Reduces to
`Fin.sum_univ_eight` via `Fin.sum_univ_castSucc`. -/
private lemma sum_univ_nine_aux {α : Type*} [AddCommMonoid α] (f : Fin 9 → α) :
    ∑ i : Fin 9, f i
      = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_eight]
  rfl

/-- The effective Lipschitz constant for the generic AB scaffold at the
AB9 coefficient tuple is `(2231497/14175) · L`. -/
lemma abLip_ab9GenericCoeff (L : ℝ) :
    abLip 9 ab9GenericCoeff L = (2231497 / 14175) * L := by
  rw [abLip, sum_univ_nine_aux, ab9GenericCoeff_zero, ab9GenericCoeff_one,
    ab9GenericCoeff_two, ab9GenericCoeff_three, ab9GenericCoeff_four,
    ab9GenericCoeff_five, ab9GenericCoeff_six, ab9GenericCoeff_seven,
    ab9GenericCoeff_eight]
  rw [show |((1070017 : ℝ) / 3628800)| = (1070017 : ℝ) / 3628800 by norm_num,
      show |(-(9664106 : ℝ) / 3628800)| = (9664106 : ℝ) / 3628800 by norm_num,
      show |((38833486 : ℝ) / 3628800)| = (38833486 : ℝ) / 3628800 by norm_num,
      show |(-(91172642 : ℝ) / 3628800)| = (91172642 : ℝ) / 3628800 by norm_num,
      show |((137968480 : ℝ) / 3628800)| = (137968480 : ℝ) / 3628800 by norm_num,
      show |(-(139855262 : ℝ) / 3628800)| = (139855262 : ℝ) / 3628800 by norm_num,
      show |((95476786 : ℝ) / 3628800)| = (95476786 : ℝ) / 3628800 by norm_num,
      show |(-(43125206 : ℝ) / 3628800)| = (43125206 : ℝ) / 3628800 by norm_num,
      show |((14097247 : ℝ) / 3628800)| = (14097247 : ℝ) / 3628800 by norm_num]
  ring

/-- Bridge: the AB9 scalar iteration is the generic AB iteration
at `s = 9` with `α = ab9GenericCoeff` and starting samples
`![y₀, y₁, …, y₈]`. -/
lemma ab9Iter_eq_abIter
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : ℝ) (n : ℕ) :
    ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ n
      = abIter 9 ab9GenericCoeff h f t₀
          ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈] n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      show ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 0 = _
      rw [ab9Iter_zero]
      unfold abIter
      simp
    | 1 =>
      show ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 1 = _
      rw [ab9Iter_one]
      unfold abIter
      simp
    | 2 =>
      show ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 2 = _
      rw [ab9Iter_two]
      unfold abIter
      simp
    | 3 =>
      show ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 3 = _
      rw [ab9Iter_three]
      unfold abIter
      simp
    | 4 =>
      show ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 4 = _
      rw [ab9Iter_four]
      unfold abIter
      simp
    | 5 =>
      show ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 5 = _
      rw [ab9Iter_five]
      unfold abIter
      simp
    | 6 =>
      show ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 6 = _
      rw [ab9Iter_six]
      unfold abIter
      simp
    | 7 =>
      show ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 7 = _
      rw [ab9Iter_seven]
      unfold abIter
      simp
    | 8 =>
      show ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ 8 = _
      rw [ab9Iter_eight]
      unfold abIter
      simp
    | k + 9 =>
      rw [ab9Iter_succ_nine]
      rw [abIter_step (s := 9) (by norm_num)
          ab9GenericCoeff h f t₀
            ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈] k]
      rw [show (k + 9 - 1 : ℕ) = k + 8 from by omega]
      rw [sum_univ_nine_aux]
      have hval3 : ((3 : Fin 9) : ℕ) = 3 := rfl
      have hval4 : ((4 : Fin 9) : ℕ) = 4 := rfl
      have hval5 : ((5 : Fin 9) : ℕ) = 5 := rfl
      have hval6 : ((6 : Fin 9) : ℕ) = 6 := rfl
      have hval7 : ((7 : Fin 9) : ℕ) = 7 := rfl
      have hval8 : ((8 : Fin 9) : ℕ) = 8 := rfl
      simp only [ab9GenericCoeff_zero, ab9GenericCoeff_one, ab9GenericCoeff_two,
        ab9GenericCoeff_three, ab9GenericCoeff_four, ab9GenericCoeff_five,
        ab9GenericCoeff_six, ab9GenericCoeff_seven, ab9GenericCoeff_eight,
        Fin.val_zero, Fin.val_one, Fin.val_two, hval3, hval4, hval5, hval6,
        hval7, hval8, Nat.add_zero]
      rw [← ih k (by omega), ← ih (k + 1) (by omega), ← ih (k + 2) (by omega),
        ← ih (k + 3) (by omega), ← ih (k + 4) (by omega),
        ← ih (k + 5) (by omega), ← ih (k + 6) (by omega),
        ← ih (k + 7) (by omega), ← ih (k + 8) (by omega)]
      rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring,
        show ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 by push_cast; ring,
        show ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 by push_cast; ring,
        show ((k + 4 : ℕ) : ℝ) = (k : ℝ) + 4 by push_cast; ring,
        show ((k + 5 : ℕ) : ℝ) = (k : ℝ) + 5 by push_cast; ring,
        show ((k + 6 : ℕ) : ℝ) = (k : ℝ) + 6 by push_cast; ring,
        show ((k + 7 : ℕ) : ℝ) = (k : ℝ) + 7 by push_cast; ring,
        show ((k + 8 : ℕ) : ℝ) = (k : ℝ) + 8 by push_cast; ring]
      ring

/-- Bridge: the AB9 scalar truncation residual at base point `t₀ + n · h`
equals the generic AB residual at index `n`. -/
lemma ab9Residual_eq_abResidual
    (h : ℝ) (y : ℝ → ℝ) (t₀ : ℝ) (n : ℕ) :
    y (t₀ + (n : ℝ) * h + 9 * h) - y (t₀ + (n : ℝ) * h + 8 * h)
        - h * ((14097247 / 3628800) * deriv y (t₀ + (n : ℝ) * h + 8 * h)
              - (43125206 / 3628800) * deriv y (t₀ + (n : ℝ) * h + 7 * h)
              + (95476786 / 3628800) * deriv y (t₀ + (n : ℝ) * h + 6 * h)
              - (139855262 / 3628800) * deriv y (t₀ + (n : ℝ) * h + 5 * h)
              + (137968480 / 3628800) * deriv y (t₀ + (n : ℝ) * h + 4 * h)
              - (91172642 / 3628800) * deriv y (t₀ + (n : ℝ) * h + 3 * h)
              + (38833486 / 3628800) * deriv y (t₀ + (n : ℝ) * h + 2 * h)
              - (9664106 / 3628800) * deriv y (t₀ + (n : ℝ) * h + h)
              + (1070017 / 3628800) * deriv y (t₀ + (n : ℝ) * h))
      = abResidual 9 ab9GenericCoeff h y t₀ n := by
  unfold abResidual
  rw [sum_univ_nine_aux, ab9GenericCoeff_zero, ab9GenericCoeff_one,
    ab9GenericCoeff_two, ab9GenericCoeff_three, ab9GenericCoeff_four,
    ab9GenericCoeff_five, ab9GenericCoeff_six, ab9GenericCoeff_seven,
    ab9GenericCoeff_eight]
  have eA : t₀ + (n : ℝ) * h + 9 * h = t₀ + ((n + 9 : ℕ) : ℝ) * h := by
    push_cast; ring
  have eB :
      t₀ + (n : ℝ) * h + 8 * h = t₀ + ((n + 9 - 1 : ℕ) : ℝ) * h := by
    have hsub : (n + 9 - 1 : ℕ) = n + 8 := by omega
    rw [hsub]; push_cast; ring
  have eC : t₀ + (n : ℝ) * h
      = t₀ + ((n + ((0 : Fin 9) : ℕ) : ℕ) : ℝ) * h := by
    simp
  have eD : t₀ + (n : ℝ) * h + h
      = t₀ + ((n + ((1 : Fin 9) : ℕ) : ℕ) : ℝ) * h := by
    simp; ring
  have eE : t₀ + (n : ℝ) * h + 2 * h
      = t₀ + ((n + ((2 : Fin 9) : ℕ) : ℕ) : ℝ) * h := by
    simp; ring
  have eF : t₀ + (n : ℝ) * h + 3 * h
      = t₀ + ((n + ((3 : Fin 9) : ℕ) : ℕ) : ℝ) * h := by
    have : ((3 : Fin 9) : ℕ) = 3 := rfl
    rw [this]; push_cast; ring
  have eG : t₀ + (n : ℝ) * h + 4 * h
      = t₀ + ((n + ((4 : Fin 9) : ℕ) : ℕ) : ℝ) * h := by
    have : ((4 : Fin 9) : ℕ) = 4 := rfl
    rw [this]; push_cast; ring
  have eH : t₀ + (n : ℝ) * h + 5 * h
      = t₀ + ((n + ((5 : Fin 9) : ℕ) : ℕ) : ℝ) * h := by
    have : ((5 : Fin 9) : ℕ) = 5 := rfl
    rw [this]; push_cast; ring
  have eI : t₀ + (n : ℝ) * h + 6 * h
      = t₀ + ((n + ((6 : Fin 9) : ℕ) : ℕ) : ℝ) * h := by
    have : ((6 : Fin 9) : ℕ) = 6 := rfl
    rw [this]; push_cast; ring
  have eJ : t₀ + (n : ℝ) * h + 7 * h
      = t₀ + ((n + ((7 : Fin 9) : ℕ) : ℕ) : ℝ) * h := by
    have : ((7 : Fin 9) : ℕ) = 7 := rfl
    rw [this]; push_cast; ring
  have eK : t₀ + (n : ℝ) * h + 8 * h
      = t₀ + ((n + ((8 : Fin 9) : ℕ) : ℕ) : ℝ) * h := by
    have : ((8 : Fin 9) : ℕ) = 8 := rfl
    rw [this]; push_cast; ring
  rw [← eA, ← eB, ← eC, ← eD, ← eE, ← eF, ← eG, ← eH, ← eI, ← eJ, ← eK]
  ring

/-- Final AB9 global error bound on `[t₀, t₀ + T]`. Under Lipschitz `f`,
`C^10` exact solution `y` with `deriv y t = f t (y t)`, and starting
errors `|y_i - y(t_i)| ≤ ε₀` for `i = 0, 1, …, 8`, the AB9 iterate error
obeys `O(ε₀ + h^9)` on a finite horizon. -/
theorem ab9_global_error_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 10 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      ∀ {y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ ε₀ : ℝ}, 0 ≤ ε₀ →
      |y₀ - y t₀| ≤ ε₀ → |y₁ - y (t₀ + h)| ≤ ε₀ →
      |y₂ - y (t₀ + 2 * h)| ≤ ε₀ →
      |y₃ - y (t₀ + 3 * h)| ≤ ε₀ →
      |y₄ - y (t₀ + 4 * h)| ≤ ε₀ →
      |y₅ - y (t₀ + 5 * h)| ≤ ε₀ →
      |y₆ - y (t₀ + 6 * h)| ≤ ε₀ →
      |y₇ - y (t₀ + 7 * h)| ≤ ε₀ →
      |y₈ - y (t₀ + 8 * h)| ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 8) * h ≤ T →
      |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ N - y (t₀ + (N : ℝ) * h)|
        ≤ Real.exp ((2231497 / 14175) * L * T) * ε₀ + K * h ^ 9 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    ab9_local_residual_bound hy t₀ T hT
  refine ⟨T * Real.exp ((2231497 / 14175) * L * T) * C, δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
  intro h hh hδ_le y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ ε₀ hε₀
    he0_bd he1_bd he2_bd he3_bd he4_bd he5_bd he6_bd he7_bd he8_bd N hNh
  set α : Fin 9 → ℝ := ab9GenericCoeff with hα_def
  set y₀_non : Fin 9 → ℝ := ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈]
    with hy_non_def
  have hs : (1 : ℕ) ≤ 9 := by norm_num
  haveI : Nonempty (Fin 9) := ⟨⟨0, hs⟩⟩
  have hiter0 : abIter 9 α h f t₀ y₀_non 0 = y₀ := by
    unfold abIter; simp [hy_non_def]
  have hiter1 : abIter 9 α h f t₀ y₀_non 1 = y₁ := by
    unfold abIter; simp [hy_non_def]
  have hiter2 : abIter 9 α h f t₀ y₀_non 2 = y₂ := by
    unfold abIter; simp [hy_non_def]
  have hiter3 : abIter 9 α h f t₀ y₀_non 3 = y₃ := by
    unfold abIter; simp [hy_non_def]
  have hiter4 : abIter 9 α h f t₀ y₀_non 4 = y₄ := by
    unfold abIter; simp [hy_non_def]
  have hiter5 : abIter 9 α h f t₀ y₀_non 5 = y₅ := by
    unfold abIter; simp [hy_non_def]
  have hiter6 : abIter 9 α h f t₀ y₀_non 6 = y₆ := by
    unfold abIter; simp [hy_non_def]
  have hiter7 : abIter 9 α h f t₀ y₀_non 7 = y₇ := by
    unfold abIter; simp [hy_non_def]
  have hiter8 : abIter 9 α h f t₀ y₀_non 8 = y₈ := by
    unfold abIter; simp [hy_non_def]
  have hstart : abErrWindow hs α h f t₀ y₀_non y 0 ≤ ε₀ := by
    unfold abErrWindow
    apply Finset.sup'_le
    intro j _
    show abErr 9 α h f t₀ y₀_non y (0 + (j : ℕ)) ≤ ε₀
    unfold abErr
    fin_cases j
    · show |abIter 9 α h f t₀ y₀_non 0
          - y (t₀ + ((0 + (((0 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter0]
      have : ((0 + (((0 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) = 0 := by simp
      rw [this, zero_mul, add_zero]; exact he0_bd
    · show |abIter 9 α h f t₀ y₀_non 1
          - y (t₀ + ((0 + (((1 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter1]
      have : ((0 + (((1 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) = 1 := by simp
      rw [this, one_mul]; exact he1_bd
    · show |abIter 9 α h f t₀ y₀_non 2
          - y (t₀ + ((0 + (((2 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter2]
      have : ((0 + (((2 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) = 2 := by simp
      rw [this]; exact he2_bd
    · show |abIter 9 α h f t₀ y₀_non 3
          - y (t₀ + ((0 + (((3 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter3]
      have hval3 : ((3 : Fin 9) : ℕ) = 3 := rfl
      have : ((0 + (((3 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) = 3 := by
        rw [hval3]; push_cast; ring
      rw [this]; exact he3_bd
    · show |abIter 9 α h f t₀ y₀_non 4
          - y (t₀ + ((0 + (((4 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter4]
      have hval4 : ((4 : Fin 9) : ℕ) = 4 := rfl
      have : ((0 + (((4 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) = 4 := by
        rw [hval4]; push_cast; ring
      rw [this]; exact he4_bd
    · show |abIter 9 α h f t₀ y₀_non 5
          - y (t₀ + ((0 + (((5 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter5]
      have hval5 : ((5 : Fin 9) : ℕ) = 5 := rfl
      have : ((0 + (((5 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) = 5 := by
        rw [hval5]; push_cast; ring
      rw [this]; exact he5_bd
    · show |abIter 9 α h f t₀ y₀_non 6
          - y (t₀ + ((0 + (((6 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter6]
      have hval6 : ((6 : Fin 9) : ℕ) = 6 := rfl
      have : ((0 + (((6 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) = 6 := by
        rw [hval6]; push_cast; ring
      rw [this]; exact he6_bd
    · show |abIter 9 α h f t₀ y₀_non 7
          - y (t₀ + ((0 + (((7 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter7]
      have hval7 : ((7 : Fin 9) : ℕ) = 7 := rfl
      have : ((0 + (((7 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) = 7 := by
        rw [hval7]; push_cast; ring
      rw [this]; exact he7_bd
    · show |abIter 9 α h f t₀ y₀_non 8
          - y (t₀ + ((0 + (((8 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) * h)| ≤ ε₀
      rw [hiter8]
      have hval8 : ((8 : Fin 9) : ℕ) = 8 := rfl
      have : ((0 + (((8 : Fin 9) : ℕ) : ℕ) : ℕ) : ℝ) = 8 := by
        rw [hval8]; push_cast; ring
      rw [this]; exact he8_bd
  have hres_gen : ∀ n : ℕ, n < N →
      |abResidual 9 α h y t₀ n| ≤ C * h ^ (9 + 1) := by
    intro n hn_lt
    have hcast : (n : ℝ) + 9 ≤ (N : ℝ) + 8 := by
      have : (n : ℝ) + 1 ≤ (N : ℝ) := by
        exact_mod_cast Nat.lt_iff_add_one_le.mp hn_lt
      linarith
    have hn9_le : ((n : ℝ) + 9) * h ≤ T := by
      have hmul : ((n : ℝ) + 9) * h ≤ ((N : ℝ) + 8) * h :=
        mul_le_mul_of_nonneg_right hcast hh.le
      linarith
    have hres := hresidual hh hδ_le n hn9_le
    have hLTE_eq := ab9_localTruncationError_eq h (t₀ + (n : ℝ) * h) y
    have hbridge := ab9Residual_eq_abResidual h y t₀ n
    have hpow : C * h ^ (9 + 1) = C * h ^ 10 := by norm_num
    rw [hα_def, ← hbridge]
    have hreshape :
        h * ((14097247 / 3628800) * deriv y (t₀ + (n : ℝ) * h + 8 * h)
              - (43125206 / 3628800) * deriv y (t₀ + (n : ℝ) * h + 7 * h)
              + (95476786 / 3628800) * deriv y (t₀ + (n : ℝ) * h + 6 * h)
              - (139855262 / 3628800) * deriv y (t₀ + (n : ℝ) * h + 5 * h)
              + (137968480 / 3628800) * deriv y (t₀ + (n : ℝ) * h + 4 * h)
              - (91172642 / 3628800) * deriv y (t₀ + (n : ℝ) * h + 3 * h)
              + (38833486 / 3628800) * deriv y (t₀ + (n : ℝ) * h + 2 * h)
              - (9664106 / 3628800) * deriv y (t₀ + (n : ℝ) * h + h)
              + (1070017 / 3628800) * deriv y (t₀ + (n : ℝ) * h))
          = h * (14097247 / 3628800 * deriv y (t₀ + (n : ℝ) * h + 8 * h)
                - 43125206 / 3628800 * deriv y (t₀ + (n : ℝ) * h + 7 * h)
                + 95476786 / 3628800 * deriv y (t₀ + (n : ℝ) * h + 6 * h)
                - 139855262 / 3628800 * deriv y (t₀ + (n : ℝ) * h + 5 * h)
                + 137968480 / 3628800 * deriv y (t₀ + (n : ℝ) * h + 4 * h)
                - 91172642 / 3628800 * deriv y (t₀ + (n : ℝ) * h + 3 * h)
                + 38833486 / 3628800 * deriv y (t₀ + (n : ℝ) * h + 2 * h)
                - 9664106 / 3628800 * deriv y (t₀ + (n : ℝ) * h + h)
                + 1070017 / 3628800 * deriv y (t₀ + (n : ℝ) * h)) := by ring
    rw [hreshape, ← hLTE_eq]
    linarith [hres, hpow.symm.le, hpow.le]
  have hNh' : (N : ℝ) * h ≤ T := by
    have hmono : (N : ℝ) * h ≤ ((N : ℝ) + 8) * h := by
      have h1 : (N : ℝ) ≤ (N : ℝ) + 8 := by linarith
      exact mul_le_mul_of_nonneg_right h1 hh.le
    linarith
  have hgeneric :=
    ab_global_error_bound_generic (p := 9) hs α hh.le hL hC_nn hf t₀
      y₀_non y hyf hε₀ hstart N hNh' hres_gen
  rw [show abLip 9 α L = (2231497 / 14175) * L from by
    rw [hα_def]; exact abLip_ab9GenericCoeff L] at hgeneric
  have hwindow_ge : abErr 9 α h f t₀ y₀_non y N
      ≤ abErrWindow hs α h f t₀ y₀_non y N := by
    show abErr 9 α h f t₀ y₀_non y (N + ((⟨0, hs⟩ : Fin 9) : ℕ))
        ≤ abErrWindow hs α h f t₀ y₀_non y N
    unfold abErrWindow
    exact Finset.le_sup' (b := ⟨0, hs⟩)
      (f := fun j : Fin 9 => abErr 9 α h f t₀ y₀_non y (N + (j : ℕ)))
      (Finset.mem_univ _)
  have hbridge :
      abIter 9 α h f t₀ y₀_non N
        = ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ N := by
    rw [hα_def, hy_non_def]
    exact (ab9Iter_eq_abIter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ N).symm
  have habsErr :
      abErr 9 α h f t₀ y₀_non y N
        = |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ N - y (t₀ + (N : ℝ) * h)| := by
    show |abIter 9 α h f t₀ y₀_non N - y (t₀ + (N : ℝ) * h)|
        = |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ N - y (t₀ + (N : ℝ) * h)|
    rw [hbridge]
  show |ab9Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ N - y (t₀ + (N : ℝ) * h)|
      ≤ Real.exp ((2231497 / 14175) * L * T) * ε₀
        + T * Real.exp ((2231497 / 14175) * L * T) * C * h ^ 9
  linarith [hwindow_ge, hgeneric, habsErr.symm.le, habsErr.le]

end LMM
