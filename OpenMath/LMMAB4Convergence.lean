import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMABGenericConvergence

/-! ## Adams–Bashforth 4-step Convergence Chain (Iserles §1.2)

Order-4 explicit 4-step LMM convergence scaffold. Mirrors the AB3 chain
in `OpenMath.LMMAB3Convergence` at the next order. The AB4 step takes
four starting samples and combines four prior `f` evaluations. The
effective max-window Lipschitz constant is `(20/3) · L`, the residual
is `O(h^5)` and the headline global error bound is `O(ε₀ + h^4)`. -/

namespace LMM

/-- AB4 iteration with four starting samples `y₀, y₁, y₂, y₃`:
`y_{n+4} = y_{n+3} + h · ((55/24) · f_{n+3} − (59/24) · f_{n+2}
  + (37/24) · f_{n+1} − (9/24) · f_n)`. -/
noncomputable def ab4Iter
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ : ℝ) : ℕ → ℝ
  | 0 => y₀
  | 1 => y₁
  | 2 => y₂
  | 3 => y₃
  | n + 4 =>
      ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 3)
        + h * (55 / 24 * f (t₀ + ((n : ℝ) + 3) * h)
                (ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 3))
              - 59 / 24 * f (t₀ + ((n : ℝ) + 2) * h)
                (ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 2))
              + 37 / 24 * f (t₀ + ((n : ℝ) + 1) * h)
                (ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 1))
              - 9 / 24 * f (t₀ + (n : ℝ) * h)
                (ab4Iter h f t₀ y₀ y₁ y₂ y₃ n))

@[simp] lemma ab4Iter_zero
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ : ℝ) :
    ab4Iter h f t₀ y₀ y₁ y₂ y₃ 0 = y₀ := rfl

@[simp] lemma ab4Iter_one
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ : ℝ) :
    ab4Iter h f t₀ y₀ y₁ y₂ y₃ 1 = y₁ := rfl

@[simp] lemma ab4Iter_two
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ : ℝ) :
    ab4Iter h f t₀ y₀ y₁ y₂ y₃ 2 = y₂ := rfl

@[simp] lemma ab4Iter_three
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ : ℝ) :
    ab4Iter h f t₀ y₀ y₁ y₂ y₃ 3 = y₃ := rfl

lemma ab4Iter_succ_succ_succ_succ
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ : ℝ) (n : ℕ) :
    ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 4)
      = ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 3)
          + h * (55 / 24 * f (t₀ + ((n : ℝ) + 3) * h)
                  (ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 3))
                - 59 / 24 * f (t₀ + ((n : ℝ) + 2) * h)
                    (ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 2))
                + 37 / 24 * f (t₀ + ((n : ℝ) + 1) * h)
                    (ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 1))
                - 9 / 24 * f (t₀ + (n : ℝ) * h)
                    (ab4Iter h f t₀ y₀ y₁ y₂ y₃ n)) := rfl

/-- AB4 local truncation operator reduces to the textbook 4-step residual
`y(t + 4h) − y(t + 3h) − h · ((55/24) y'(t + 3h) − (59/24) y'(t + 2h)
  + (37/24) y'(t + h) − (9/24) y'(t))`. -/
theorem ab4_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    adamsBashforth4.localTruncationError h t y
      = y (t + 4 * h) - y (t + 3 * h)
          - h * (55 / 24 * deriv y (t + 3 * h)
                  - 59 / 24 * deriv y (t + 2 * h)
                  + 37 / 24 * deriv y (t + h)
                  - 9 / 24 * deriv y t) := by
  unfold localTruncationError truncationOp
  simp [adamsBashforth4, Fin.sum_univ_five, iteratedDeriv_one,
    iteratedDeriv_zero]
  ring

/-- One-step AB4 Lipschitz step: a single linearised increment of the
global error from steps `n, n+1, n+2, n+3` to `n+4`, with four Lipschitz
contributions and additive `|τ_n|`. -/
theorem ab4_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ y₁ y₂ y₃ : ℝ) (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|
      ≤ |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|
        + (55 / 24) * h * L
            * |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 3)
                - y (t₀ + ((n : ℝ) + 3) * h)|
        + (59 / 24) * h * L
            * |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 2)
                - y (t₀ + ((n : ℝ) + 2) * h)|
        + (37 / 24) * h * L
            * |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 1)
                - y (t₀ + ((n : ℝ) + 1) * h)|
        + (9 / 24) * h * L
            * |ab4Iter h f t₀ y₀ y₁ y₂ y₃ n - y (t₀ + (n : ℝ) * h)|
        + |adamsBashforth4.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set yn : ℝ := ab4Iter h f t₀ y₀ y₁ y₂ y₃ n with hyn_def
  set yn1 : ℝ := ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 1) with hyn1_def
  set yn2 : ℝ := ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 2) with hyn2_def
  set yn3 : ℝ := ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 3) with hyn3_def
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
  set τ : ℝ := adamsBashforth4.localTruncationError h tn y with hτ_def
  -- AB4 step formula.
  have hstep : ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 4)
      = yn3 + h * (55 / 24 * f tn3 yn3
                    - 59 / 24 * f tn2 yn2
                    + 37 / 24 * f tn1 yn1
                    - 9 / 24 * f tn yn) := by
    show ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 4) = _
    rw [ab4Iter_succ_succ_succ_succ]
  -- Time arithmetic.
  have htn1_h : tn + h = tn1 := by simp [htn_def, htn1_def]; ring
  have htn_2h : tn + 2 * h = tn2 := by simp [htn_def, htn2_def]; ring
  have htn_3h : tn + 3 * h = tn3 := by simp [htn_def, htn3_def]; ring
  have htn_4h : tn + 4 * h = tn4 := by simp [htn_def, htn4_def]; ring
  -- LTE residual at `tn`, expressed via `f` along the trajectory.
  have hτ_eq : τ = zn4 - zn3
        - h * (55 / 24 * f tn3 zn3 - 59 / 24 * f tn2 zn2
              + 37 / 24 * f tn1 zn1 - 9 / 24 * f tn zn) := by
    show adamsBashforth4.localTruncationError h tn y = _
    rw [ab4_localTruncationError_eq, htn1_h, htn_2h, htn_3h, htn_4h,
      hyf tn3, hyf tn2, hyf tn1, hyf tn]
  -- Algebraic decomposition of the global error increment.
  have halg : ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 4) - zn4
      = (yn3 - zn3)
        + (55 / 24) * h * (f tn3 yn3 - f tn3 zn3)
        - (59 / 24) * h * (f tn2 yn2 - f tn2 zn2)
        + (37 / 24) * h * (f tn1 yn1 - f tn1 zn1)
        - (9 / 24) * h * (f tn yn - f tn zn)
        - τ := by
    rw [hstep, hτ_eq]; ring
  -- Lipschitz bounds on the four `f` increments.
  have hLip3 : |f tn3 yn3 - f tn3 zn3| ≤ L * |yn3 - zn3| := hf tn3 yn3 zn3
  have hLip2 : |f tn2 yn2 - f tn2 zn2| ≤ L * |yn2 - zn2| := hf tn2 yn2 zn2
  have hLip1 : |f tn1 yn1 - f tn1 zn1| ≤ L * |yn1 - zn1| := hf tn1 yn1 zn1
  have hLip0 : |f tn yn - f tn zn| ≤ L * |yn - zn| := hf tn yn zn
  have h55_nn : 0 ≤ (55 / 24) * h := by linarith
  have h59_nn : 0 ≤ (59 / 24) * h := by linarith
  have h37_nn : 0 ≤ (37 / 24) * h := by linarith
  have h9_nn : 0 ≤ (9 / 24) * h := by linarith
  have h55_abs : |(55 / 24) * h * (f tn3 yn3 - f tn3 zn3)|
      ≤ (55 / 24) * h * L * |yn3 - zn3| := by
    rw [abs_mul, abs_of_nonneg h55_nn]
    calc (55 / 24) * h * |f tn3 yn3 - f tn3 zn3|
        ≤ (55 / 24) * h * (L * |yn3 - zn3|) :=
          mul_le_mul_of_nonneg_left hLip3 h55_nn
      _ = (55 / 24) * h * L * |yn3 - zn3| := by ring
  have h59_abs : |(59 / 24) * h * (f tn2 yn2 - f tn2 zn2)|
      ≤ (59 / 24) * h * L * |yn2 - zn2| := by
    rw [abs_mul, abs_of_nonneg h59_nn]
    calc (59 / 24) * h * |f tn2 yn2 - f tn2 zn2|
        ≤ (59 / 24) * h * (L * |yn2 - zn2|) :=
          mul_le_mul_of_nonneg_left hLip2 h59_nn
      _ = (59 / 24) * h * L * |yn2 - zn2| := by ring
  have h37_abs : |(37 / 24) * h * (f tn1 yn1 - f tn1 zn1)|
      ≤ (37 / 24) * h * L * |yn1 - zn1| := by
    rw [abs_mul, abs_of_nonneg h37_nn]
    calc (37 / 24) * h * |f tn1 yn1 - f tn1 zn1|
        ≤ (37 / 24) * h * (L * |yn1 - zn1|) :=
          mul_le_mul_of_nonneg_left hLip1 h37_nn
      _ = (37 / 24) * h * L * |yn1 - zn1| := by ring
  have h9_abs : |(9 / 24) * h * (f tn yn - f tn zn)|
      ≤ (9 / 24) * h * L * |yn - zn| := by
    rw [abs_mul, abs_of_nonneg h9_nn]
    calc (9 / 24) * h * |f tn yn - f tn zn|
        ≤ (9 / 24) * h * (L * |yn - zn|) :=
          mul_le_mul_of_nonneg_left hLip0 h9_nn
      _ = (9 / 24) * h * L * |yn - zn| := by ring
  -- Triangle inequality (chained five times).
  have htri :
      |(yn3 - zn3)
        + (55 / 24) * h * (f tn3 yn3 - f tn3 zn3)
        - (59 / 24) * h * (f tn2 yn2 - f tn2 zn2)
        + (37 / 24) * h * (f tn1 yn1 - f tn1 zn1)
        - (9 / 24) * h * (f tn yn - f tn zn)
        - τ|
        ≤ |yn3 - zn3|
          + |(55 / 24) * h * (f tn3 yn3 - f tn3 zn3)|
          + |(59 / 24) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(37 / 24) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(9 / 24) * h * (f tn yn - f tn zn)|
          + |τ| := by
    have h1 :
        |(yn3 - zn3)
          + (55 / 24) * h * (f tn3 yn3 - f tn3 zn3)
          - (59 / 24) * h * (f tn2 yn2 - f tn2 zn2)
          + (37 / 24) * h * (f tn1 yn1 - f tn1 zn1)
          - (9 / 24) * h * (f tn yn - f tn zn)
          - τ|
          ≤ |(yn3 - zn3)
              + (55 / 24) * h * (f tn3 yn3 - f tn3 zn3)
              - (59 / 24) * h * (f tn2 yn2 - f tn2 zn2)
              + (37 / 24) * h * (f tn1 yn1 - f tn1 zn1)
              - (9 / 24) * h * (f tn yn - f tn zn)|
            + |τ| := abs_sub _ _
    have h2 :
        |(yn3 - zn3)
          + (55 / 24) * h * (f tn3 yn3 - f tn3 zn3)
          - (59 / 24) * h * (f tn2 yn2 - f tn2 zn2)
          + (37 / 24) * h * (f tn1 yn1 - f tn1 zn1)
          - (9 / 24) * h * (f tn yn - f tn zn)|
          ≤ |(yn3 - zn3)
              + (55 / 24) * h * (f tn3 yn3 - f tn3 zn3)
              - (59 / 24) * h * (f tn2 yn2 - f tn2 zn2)
              + (37 / 24) * h * (f tn1 yn1 - f tn1 zn1)|
            + |(9 / 24) * h * (f tn yn - f tn zn)| := abs_sub _ _
    have h3 :
        |(yn3 - zn3)
          + (55 / 24) * h * (f tn3 yn3 - f tn3 zn3)
          - (59 / 24) * h * (f tn2 yn2 - f tn2 zn2)
          + (37 / 24) * h * (f tn1 yn1 - f tn1 zn1)|
          ≤ |(yn3 - zn3)
              + (55 / 24) * h * (f tn3 yn3 - f tn3 zn3)
              - (59 / 24) * h * (f tn2 yn2 - f tn2 zn2)|
            + |(37 / 24) * h * (f tn1 yn1 - f tn1 zn1)| := abs_add_le _ _
    have h4 :
        |(yn3 - zn3)
          + (55 / 24) * h * (f tn3 yn3 - f tn3 zn3)
          - (59 / 24) * h * (f tn2 yn2 - f tn2 zn2)|
          ≤ |(yn3 - zn3)
              + (55 / 24) * h * (f tn3 yn3 - f tn3 zn3)|
            + |(59 / 24) * h * (f tn2 yn2 - f tn2 zn2)| := abs_sub _ _
    have h5 :
        |(yn3 - zn3)
          + (55 / 24) * h * (f tn3 yn3 - f tn3 zn3)|
          ≤ |yn3 - zn3| + |(55 / 24) * h * (f tn3 yn3 - f tn3 zn3)| :=
      abs_add_le _ _
    linarith
  calc |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 4) - zn4|
      = |(yn3 - zn3)
          + (55 / 24) * h * (f tn3 yn3 - f tn3 zn3)
          - (59 / 24) * h * (f tn2 yn2 - f tn2 zn2)
          + (37 / 24) * h * (f tn1 yn1 - f tn1 zn1)
          - (9 / 24) * h * (f tn yn - f tn zn)
          - τ| := by rw [halg]
    _ ≤ |yn3 - zn3|
          + |(55 / 24) * h * (f tn3 yn3 - f tn3 zn3)|
          + |(59 / 24) * h * (f tn2 yn2 - f tn2 zn2)|
          + |(37 / 24) * h * (f tn1 yn1 - f tn1 zn1)|
          + |(9 / 24) * h * (f tn yn - f tn zn)|
          + |τ| := htri
    _ ≤ |yn3 - zn3|
          + (55 / 24) * h * L * |yn3 - zn3|
          + (59 / 24) * h * L * |yn2 - zn2|
          + (37 / 24) * h * L * |yn1 - zn1|
          + (9 / 24) * h * L * |yn - zn|
          + |τ| := by linarith [h55_abs, h59_abs, h37_abs, h9_abs]

/-- Max-norm one-step error recurrence for AB4 with Lipschitz constant
`L`. With `eN k := |y_k − y(t_k)|` and
`EN k := max (max (max (eN k) (eN (k+1))) (eN (k+2))) (eN (k+3))`,
`EN (n+1) ≤ (1 + h · (20/3) · L) · EN n + |τ_n|`. The `(20/3)` factor is
the ℓ¹-norm of the AB4 coefficient vector
`(55/24, 59/24, 37/24, 9/24)`. -/
theorem ab4_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ y₁ y₂ y₃ : ℝ) (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max (max
          |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
          |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|)
          |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|)
        |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|
      ≤ (1 + h * ((20 / 3) * L))
            * max (max (max
                  |ab4Iter h f t₀ y₀ y₁ y₂ y₃ n
                      - y (t₀ + (n : ℝ) * h)|
                  |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 1)
                      - y (t₀ + ((n : ℝ) + 1) * h)|)
                  |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 2)
                      - y (t₀ + ((n : ℝ) + 2) * h)|)
                  |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 3)
                      - y (t₀ + ((n : ℝ) + 3) * h)|
        + |adamsBashforth4.localTruncationError h
              (t₀ + (n : ℝ) * h) y| := by
  set en : ℝ := |ab4Iter h f t₀ y₀ y₁ y₂ y₃ n - y (t₀ + (n : ℝ) * h)|
    with hen_def
  set en1 : ℝ :=
    |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)|
    with hen1_def
  set en2 : ℝ :=
    |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)|
    with hen2_def
  set en3 : ℝ :=
    |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|
    with hen3_def
  set en4 : ℝ :=
    |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|
    with hen4_def
  set τabs : ℝ :=
    |adamsBashforth4.localTruncationError h (t₀ + (n : ℝ) * h) y|
    with hτabs_def
  have hen_nn : 0 ≤ en := abs_nonneg _
  have hen1_nn : 0 ≤ en1 := abs_nonneg _
  have hen2_nn : 0 ≤ en2 := abs_nonneg _
  have hen3_nn : 0 ≤ en3 := abs_nonneg _
  have hτ_nn : 0 ≤ τabs := abs_nonneg _
  -- One-step Lipschitz bound (from `ab4_one_step_lipschitz`).
  have hstep :
      en4 ≤ en3 + (55 / 24) * h * L * en3
                + (59 / 24) * h * L * en2
                + (37 / 24) * h * L * en1
                + (9 / 24) * h * L * en + τabs := by
    have := ab4_one_step_lipschitz hh hf t₀ y₀ y₁ y₂ y₃ y hyf n
    show |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)|
        ≤ |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|
          + (55 / 24) * h * L
              * |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 3)
                  - y (t₀ + ((n : ℝ) + 3) * h)|
          + (59 / 24) * h * L
              * |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 2)
                  - y (t₀ + ((n : ℝ) + 2) * h)|
          + (37 / 24) * h * L
              * |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 1)
                  - y (t₀ + ((n : ℝ) + 1) * h)|
          + (9 / 24) * h * L
              * |ab4Iter h f t₀ y₀ y₁ y₂ y₃ n - y (t₀ + (n : ℝ) * h)|
          + |adamsBashforth4.localTruncationError h (t₀ + (n : ℝ) * h) y|
    exact this
  set EN_n : ℝ := max (max (max en en1) en2) en3 with hEN_n_def
  have hen_le_EN : en ≤ EN_n :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hen1_le_EN : en1 ≤ EN_n :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hen2_le_EN : en2 ≤ EN_n :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hen3_le_EN : en3 ≤ EN_n := le_max_right _ _
  have h55_nn : 0 ≤ (55 / 24) * h * L := by positivity
  have h59_nn : 0 ≤ (59 / 24) * h * L := by positivity
  have h37_nn : 0 ≤ (37 / 24) * h * L := by positivity
  have h9_nn : 0 ≤ (9 / 24) * h * L := by positivity
  have hEN_nn : 0 ≤ EN_n := le_trans hen_nn hen_le_EN
  have hcoef_nn : 0 ≤ h * ((20 / 3) * L) := by positivity
  -- en4 ≤ (1 + h*(20/3*L)) * EN_n + τabs.
  have hen4_bd : en4 ≤ (1 + h * ((20 / 3) * L)) * EN_n + τabs := by
    have h1 : (55 / 24) * h * L * en3 ≤ (55 / 24) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen3_le_EN h55_nn
    have h2 : (59 / 24) * h * L * en2 ≤ (59 / 24) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen2_le_EN h59_nn
    have h3 : (37 / 24) * h * L * en1 ≤ (37 / 24) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen1_le_EN h37_nn
    have h4 : (9 / 24) * h * L * en ≤ (9 / 24) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen_le_EN h9_nn
    have h_alg :
        EN_n + (55 / 24) * h * L * EN_n
              + (59 / 24) * h * L * EN_n
              + (37 / 24) * h * L * EN_n
              + (9 / 24) * h * L * EN_n + τabs
          = (1 + h * ((20 / 3) * L)) * EN_n + τabs := by ring
    linarith [hstep, hen3_le_EN, h1, h2, h3, h4, h_alg.le]
  -- en1, en2, en3 ≤ EN_n ≤ (1 + h*(20/3*L)) * EN_n + τabs.
  have hEN_le_grow : EN_n ≤ (1 + h * ((20 / 3) * L)) * EN_n := by
    have hone : (1 : ℝ) * EN_n ≤ (1 + h * ((20 / 3) * L)) * EN_n :=
      mul_le_mul_of_nonneg_right (by linarith) hEN_nn
    linarith
  have hen1_bd : en1 ≤ (1 + h * ((20 / 3) * L)) * EN_n + τabs := by
    linarith [hen1_le_EN, hEN_le_grow]
  have hen2_bd : en2 ≤ (1 + h * ((20 / 3) * L)) * EN_n + τabs := by
    linarith [hen2_le_EN, hEN_le_grow]
  have hen3_bd : en3 ≤ (1 + h * ((20 / 3) * L)) * EN_n + τabs := by
    linarith [hen3_le_EN, hEN_le_grow]
  exact max_le (max_le (max_le hen1_bd hen2_bd) hen3_bd) hen4_bd

/-- A `C^5` function has its fifth derivative bounded on every compact
interval `[a, b]`. -/
theorem iteratedDeriv_five_bounded_on_Icc
    {y : ℝ → ℝ} (hy : ContDiff ℝ 5 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, |iteratedDeriv 5 y t| ≤ M := by
  have h_cont : Continuous (iteratedDeriv 5 y) :=
    hy.continuous_iteratedDeriv 5 (by norm_num)
  obtain ⟨M, hM⟩ :=
    IsCompact.exists_bound_of_continuousOn (CompactIccSpace.isCompact_Icc)
      h_cont.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro t ht
  exact (hM t ht).trans (le_max_left _ _)

/-- Pointwise fifth-order Taylor (Lagrange) remainder bound: if `y` is
`C^5` and `|iteratedDeriv 5 y| ≤ M` on `[a, b]`, then for `t, t + r ∈ [a, b]`
with `r ≥ 0`,
`|y(t+r) - y(t) - r·y'(t) - r²/2·y''(t) - r³/6·y'''(t) - r⁴/24·y⁽⁴⁾(t)|
  ≤ M/120 · r⁵`. -/
theorem y_fifth_order_taylor_remainder
    {y : ℝ → ℝ} (hy : ContDiff ℝ 5 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 5 y t| ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    |y (t + r) - y t - r * deriv y t
        - r ^ 2 / 2 * iteratedDeriv 2 y t
        - r ^ 3 / 6 * iteratedDeriv 3 y t
        - r ^ 4 / 24 * iteratedDeriv 4 y t|
      ≤ M / 120 * r ^ 5 := by
  by_cases hr' : r = 0
  · subst hr'; simp
  have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr')
  have htlt : t < t + r := by linarith
  have hUnique : UniqueDiffOn ℝ (Set.Icc t (t + r)) := uniqueDiffOn_Icc htlt
  have ht_mem_loc : t ∈ Set.Icc t (t + r) := Set.left_mem_Icc.mpr htlt.le
  -- Lagrange Taylor remainder at order 4 (fifth-derivative form).
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ : ∃ ξ ∈ Set.Ioo t (t + r),
      y (t + r) - taylorWithinEval y 4 (Set.Icc t (t + r)) t (t + r)
        = iteratedDeriv 5 y ξ * r ^ 5 / 120 := by
    have hcdo : ContDiffOn ℝ 5 y (Set.Icc t (t + r)) :=
      hy.contDiffOn.of_le le_rfl
    have ⟨ξ, hξ_mem, hξ_eq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 4) htlt hcdo
    refine ⟨ξ, hξ_mem, ?_⟩
    have hpow : (t + r - t) ^ 5 = r ^ 5 := by ring
    have hfact : (((4 + 1 : ℕ).factorial : ℝ)) = 120 := by
      simp [Nat.factorial]
    rw [hξ_eq, hpow, hfact]
  -- Compute the Taylor polynomial explicitly.
  have h_taylor :
      taylorWithinEval y 4 (Set.Icc t (t + r)) t (t + r)
        = y t + r * deriv y t + r ^ 2 / 2 * iteratedDeriv 2 y t
              + r ^ 3 / 6 * iteratedDeriv 3 y t
              + r ^ 4 / 24 * iteratedDeriv 4 y t := by
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
    have h0 :
        iteratedDerivWithin 0 y (Set.Icc t (t + r)) t = y t := by
      simp [iteratedDerivWithin_zero]
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero, h0, h1, h2, h3, h4]
    simp only [smul_eq_mul, Nat.factorial_zero, Nat.factorial_one,
      Nat.factorial_succ, Nat.cast_one, Nat.cast_ofNat, Nat.cast_succ,
      Nat.cast_mul, pow_zero, pow_one, mul_one, one_mul, zero_add,
      inv_one, Nat.factorial]
    ring
  -- Conclude.
  have hξ_in : ξ ∈ Set.Icc a b :=
    ⟨by linarith [hξ_mem.1, ht.1], by linarith [hξ_mem.2, htr.2]⟩
  have hbnd_ξ : |iteratedDeriv 5 y ξ| ≤ M := hbnd ξ hξ_in
  have h_eq :
      y (t + r) - y t - r * deriv y t
          - r ^ 2 / 2 * iteratedDeriv 2 y t
          - r ^ 3 / 6 * iteratedDeriv 3 y t
          - r ^ 4 / 24 * iteratedDeriv 4 y t
        = iteratedDeriv 5 y ξ * r ^ 5 / 120 := by
    have := hξ_eq
    rw [h_taylor] at this
    linarith
  rw [h_eq]
  rw [show iteratedDeriv 5 y ξ * r ^ 5 / 120
      = (iteratedDeriv 5 y ξ) * (r ^ 5 / 120) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 5 / 120)]
  calc |iteratedDeriv 5 y ξ| * (r ^ 5 / 120)
      ≤ M * (r ^ 5 / 120) :=
        mul_le_mul_of_nonneg_right hbnd_ξ (by positivity)
    _ = M / 120 * r ^ 5 := by ring

/-- Pointwise fourth-order Taylor (Lagrange) remainder bound for the
derivative: if `y` is `C^5` and `|iteratedDeriv 5 y| ≤ M` on `[a, b]`,
then for `t, t + r ∈ [a, b]` with `r ≥ 0`,
`|y'(t+r) - y'(t) - r·y''(t) - r²/2·y'''(t) - r³/6·y⁽⁴⁾(t)| ≤ M/24 · r⁴`. -/
theorem derivY_fourth_order_taylor_remainder
    {y : ℝ → ℝ} (hy : ContDiff ℝ 5 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 5 y t| ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    |deriv y (t + r) - deriv y t - r * iteratedDeriv 2 y t
        - r ^ 2 / 2 * iteratedDeriv 3 y t
        - r ^ 3 / 6 * iteratedDeriv 4 y t|
      ≤ M / 24 * r ^ 4 := by
  by_cases hr' : r = 0
  · subst hr'; simp
  have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr')
  have htlt : t < t + r := by linarith
  have hUnique : UniqueDiffOn ℝ (Set.Icc t (t + r)) := uniqueDiffOn_Icc htlt
  have ht_mem_loc : t ∈ Set.Icc t (t + r) := Set.left_mem_Icc.mpr htlt.le
  -- `deriv y` is `C^4` (since `y` is `C^5`).
  have hdy : ContDiff ℝ 4 (deriv y) := hy.deriv'
  -- Lagrange Taylor at order 3 for `deriv y` on `[t, t+r]`.
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ : ∃ ξ ∈ Set.Ioo t (t + r),
      deriv y (t + r) - taylorWithinEval (deriv y) 3 (Set.Icc t (t + r)) t (t + r)
        = iteratedDeriv 4 (deriv y) ξ * r ^ 4 / 24 := by
    have hcdo : ContDiffOn ℝ 4 (deriv y) (Set.Icc t (t + r)) :=
      hdy.contDiffOn.of_le le_rfl
    have ⟨ξ, hξ_mem, hξ_eq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 3) htlt hcdo
    refine ⟨ξ, hξ_mem, ?_⟩
    have hpow : (t + r - t) ^ 4 = r ^ 4 := by ring
    have hfact : (((3 + 1 : ℕ).factorial : ℝ)) = 24 := by
      simp [Nat.factorial]
    rw [hξ_eq, hpow, hfact]
  -- Compute the Taylor polynomial.
  have h_taylor :
      taylorWithinEval (deriv y) 3 (Set.Icc t (t + r)) t (t + r)
        = deriv y t + r * iteratedDeriv 2 y t
              + r ^ 2 / 2 * iteratedDeriv 3 y t
              + r ^ 3 / 6 * iteratedDeriv 4 y t := by
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
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
        h0, h1, h2, h3]
    simp only [smul_eq_mul, Nat.factorial_zero, Nat.factorial_one,
      Nat.factorial_succ, Nat.cast_one, Nat.cast_ofNat, Nat.cast_succ,
      Nat.cast_mul, pow_zero, pow_one, mul_one, one_mul, zero_add,
      inv_one, Nat.factorial]
    ring
  -- Bound `iteratedDeriv 4 (deriv y) ξ = iteratedDeriv 5 y ξ`.
  have hidd_eq : iteratedDeriv 4 (deriv y) = iteratedDeriv 5 y := by
    have : iteratedDeriv 5 y = iteratedDeriv 4 (deriv y) :=
      iteratedDeriv_succ' (n := 4) (f := y)
    exact this.symm
  have hξ_in : ξ ∈ Set.Icc a b :=
    ⟨by linarith [hξ_mem.1, ht.1], by linarith [hξ_mem.2, htr.2]⟩
  have hbnd_ξ : |iteratedDeriv 5 y ξ| ≤ M := hbnd ξ hξ_in
  have h_eq :
      deriv y (t + r) - deriv y t - r * iteratedDeriv 2 y t
          - r ^ 2 / 2 * iteratedDeriv 3 y t
          - r ^ 3 / 6 * iteratedDeriv 4 y t
        = iteratedDeriv 5 y ξ * r ^ 4 / 24 := by
    have hraw := hξ_eq
    rw [h_taylor, hidd_eq] at hraw
    linarith
  rw [h_eq]
  rw [show iteratedDeriv 5 y ξ * r ^ 4 / 24
      = (iteratedDeriv 5 y ξ) * (r ^ 4 / 24) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r ^ 4 / 24)]
  calc |iteratedDeriv 5 y ξ| * (r ^ 4 / 24)
      ≤ M * (r ^ 4 / 24) :=
        mul_le_mul_of_nonneg_right hbnd_ξ (by positivity)
    _ = M / 24 * r ^ 4 := by ring

/-- Pointwise AB4 truncation residual bound. The textbook AB4 residual
expands as `R_y(4) − R_y(3) − (55h/24)·R_y'(3) + (59h/24)·R_y'(2)
  − (37h/24)·R_y'(1)`, with `R_y'(0) = 0`. The combined coefficient is
`1024/120 + 243/120 + 55·81/576 + 59·16/576 + 37/576 = 57588/2880 < 20`. -/
private theorem ab4_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 5 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, |iteratedDeriv 5 y t| ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (ht4h : t + 4 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    |y (t + 4 * h) - y (t + 3 * h)
        - h * ((55 / 24) * deriv y (t + 3 * h)
              - (59 / 24) * deriv y (t + 2 * h)
              + (37 / 24) * deriv y (t + h)
              - (9 / 24) * deriv y t)|
      ≤ (20 : ℝ) * M * h ^ 5 := by
  -- Five Taylor remainders.
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  -- R_y(3): y(t+3h) Taylor remainder at order 5.
  have hRy3 :=
    y_fifth_order_taylor_remainder hy hbnd ht ht3h h3h
  -- R_y(4): y(t+4h) Taylor remainder at order 5.
  have hRy4 :=
    y_fifth_order_taylor_remainder hy hbnd ht ht4h h4h
  -- R_y'(1): y'(t+h) - y'(t) - h*y''(t) - (h²/2)*y'''(t) - (h³/6)*y⁽⁴⁾(t).
  have hRyp1 :=
    derivY_fourth_order_taylor_remainder hy hbnd ht hth hh
  -- R_y'(2): at 2h.
  have hRyp2 :=
    derivY_fourth_order_taylor_remainder hy hbnd ht ht2h h2h
  -- R_y'(3): at 3h.
  have hRyp3 :=
    derivY_fourth_order_taylor_remainder hy hbnd ht ht3h h3h
  -- Abbreviations.
  set y0 := y t with hy0_def
  set y3 := y (t + 3 * h) with hy3_def
  set y4 := y (t + 4 * h) with hy4_def
  set d0 := deriv y t with hd0_def
  set d1 := deriv y (t + h) with hd1_def
  set d2 := deriv y (t + 2 * h) with hd2_def
  set d3 := deriv y (t + 3 * h) with hd3_def
  set dd := iteratedDeriv 2 y t with hdd_def
  set ddd := iteratedDeriv 3 y t with hddd_def
  set dddd := iteratedDeriv 4 y t with hdddd_def
  -- Algebraic identity for the residual.
  have hLTE_eq :
      y4 - y3 - h * ((55 / 24) * d3 - (59 / 24) * d2
                    + (37 / 24) * d1 - (9 / 24) * d0)
        = (y4 - y0 - (4 * h) * d0
              - (4 * h) ^ 2 / 2 * dd
              - (4 * h) ^ 3 / 6 * ddd
              - (4 * h) ^ 4 / 24 * dddd)
          - (y3 - y0 - (3 * h) * d0
              - (3 * h) ^ 2 / 2 * dd
              - (3 * h) ^ 3 / 6 * ddd
              - (3 * h) ^ 4 / 24 * dddd)
          - (55 * h / 24)
              * (d3 - d0 - (3 * h) * dd
                  - (3 * h) ^ 2 / 2 * ddd
                  - (3 * h) ^ 3 / 6 * dddd)
          + (59 * h / 24)
              * (d2 - d0 - (2 * h) * dd
                  - (2 * h) ^ 2 / 2 * ddd
                  - (2 * h) ^ 3 / 6 * dddd)
          - (37 * h / 24)
              * (d1 - d0 - h * dd
                  - h ^ 2 / 2 * ddd
                  - h ^ 3 / 6 * dddd) := by ring
  rw [hLTE_eq]
  -- Triangle inequality (chained).
  set A := y4 - y0 - (4 * h) * d0
            - (4 * h) ^ 2 / 2 * dd
            - (4 * h) ^ 3 / 6 * ddd
            - (4 * h) ^ 4 / 24 * dddd with hA_def
  set B := y3 - y0 - (3 * h) * d0
            - (3 * h) ^ 2 / 2 * dd
            - (3 * h) ^ 3 / 6 * ddd
            - (3 * h) ^ 4 / 24 * dddd with hB_def
  set C := d3 - d0 - (3 * h) * dd
            - (3 * h) ^ 2 / 2 * ddd
            - (3 * h) ^ 3 / 6 * dddd with hC_def
  set D := d2 - d0 - (2 * h) * dd
            - (2 * h) ^ 2 / 2 * ddd
            - (2 * h) ^ 3 / 6 * dddd with hD_def
  set E := d1 - d0 - h * dd
            - h ^ 2 / 2 * ddd
            - h ^ 3 / 6 * dddd with hE_def
  have h55h_nn : 0 ≤ 55 * h / 24 := by linarith
  have h59h_nn : 0 ≤ 59 * h / 24 := by linarith
  have h37h_nn : 0 ≤ 37 * h / 24 := by linarith
  have habs55 : |(55 * h / 24) * C| = (55 * h / 24) * |C| := by
    rw [abs_mul, abs_of_nonneg h55h_nn]
  have habs59 : |(59 * h / 24) * D| = (59 * h / 24) * |D| := by
    rw [abs_mul, abs_of_nonneg h59h_nn]
  have habs37 : |(37 * h / 24) * E| = (37 * h / 24) * |E| := by
    rw [abs_mul, abs_of_nonneg h37h_nn]
  have htri : |A - B - (55 * h / 24) * C + (59 * h / 24) * D
                  - (37 * h / 24) * E|
      ≤ |A| + |B| + (55 * h / 24) * |C| + (59 * h / 24) * |D|
          + (37 * h / 24) * |E| := by
    have h1 : |A - B - (55 * h / 24) * C + (59 * h / 24) * D
                  - (37 * h / 24) * E|
        ≤ |A - B - (55 * h / 24) * C + (59 * h / 24) * D|
          + |(37 * h / 24) * E| := abs_sub _ _
    have h2 : |A - B - (55 * h / 24) * C + (59 * h / 24) * D|
        ≤ |A - B - (55 * h / 24) * C| + |(59 * h / 24) * D| :=
      abs_add_le _ _
    have h3 : |A - B - (55 * h / 24) * C|
        ≤ |A - B| + |(55 * h / 24) * C| := abs_sub _ _
    have h4 : |A - B| ≤ |A| + |B| := abs_sub _ _
    linarith [habs55.le, habs55.ge, habs59.le, habs59.ge,
      habs37.le, habs37.ge]
  -- Bounds on each piece.
  have hA_bd : |A| ≤ M / 120 * (4 * h) ^ 5 := hRy4
  have hB_bd : |B| ≤ M / 120 * (3 * h) ^ 5 := hRy3
  have hC_bd : |C| ≤ M / 24 * (3 * h) ^ 4 := hRyp3
  have hD_bd : |D| ≤ M / 24 * (2 * h) ^ 4 := hRyp2
  have hE_bd : |E| ≤ M / 24 * h ^ 4 := hRyp1
  -- Multiply scaled bounds.
  have h55C_bd : (55 * h / 24) * |C| ≤ (55 * h / 24) * (M / 24 * (3 * h) ^ 4) :=
    mul_le_mul_of_nonneg_left hC_bd h55h_nn
  have h59D_bd : (59 * h / 24) * |D| ≤ (59 * h / 24) * (M / 24 * (2 * h) ^ 4) :=
    mul_le_mul_of_nonneg_left hD_bd h59h_nn
  have h37E_bd : (37 * h / 24) * |E| ≤ (37 * h / 24) * (M / 24 * h ^ 4) :=
    mul_le_mul_of_nonneg_left hE_bd h37h_nn
  -- Sum of upper bounds = (1024/120 + 243/120) + 55·81/576 + 59·16/576 + 37/576
  --                    = 1267/120 + 5436/576
  --                    = 57588/2880 ≈ 19.9958...
  -- ≤ 20.
  have hbound_alg :
      M / 120 * (4 * h) ^ 5 + M / 120 * (3 * h) ^ 5
        + (55 * h / 24) * (M / 24 * (3 * h) ^ 4)
        + (59 * h / 24) * (M / 24 * (2 * h) ^ 4)
        + (37 * h / 24) * (M / 24 * h ^ 4)
        = (57588 / 2880 : ℝ) * M * h ^ 5 := by ring
  -- 57588/2880 ≤ 20 → over-estimate by 20 * M * h^5.
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (abs_nonneg _).trans this
  have hh5_nn : 0 ≤ h ^ 5 := by positivity
  have hMh5_nn : 0 ≤ M * h ^ 5 := mul_nonneg hMnn hh5_nn
  have hslack : (57588 / 2880 : ℝ) * M * h ^ 5 ≤ 20 * M * h ^ 5 := by
    have hle : (57588 / 2880 : ℝ) ≤ 20 := by norm_num
    have := mul_le_mul_of_nonneg_right hle hMh5_nn
    linarith [this]
  linarith [htri, hA_bd, hB_bd, h55C_bd, h59D_bd, h37E_bd,
    hbound_alg.le, hbound_alg.ge, hslack]

/-- Uniform bound on the AB4 one-step truncation residual on a finite
horizon, given a `C^5` exact solution. -/
theorem ab4_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 5 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 4) * h ≤ T →
        |adamsBashforth4.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 5 := by
  -- Compact sample interval `[t₀, t₀ + T + 1]` covers all `t + kh` with `k ≤ 4`.
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_five_bounded_on_Icc hy t₀ (t₀ + T + 1)
  refine ⟨(20 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 4) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 4) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 4) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 4) * h := by nlinarith
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 4 * h = ((n : ℝ) + 4) * h := by ring
    linarith
  -- Rewrite the LTE in textbook form.
  rw [ab4_localTruncationError_eq]
  show |y (t + 4 * h) - y (t + 3 * h)
      - h * (55 / 24 * deriv y (t + 3 * h)
              - 59 / 24 * deriv y (t + 2 * h)
              + 37 / 24 * deriv y (t + h)
              - 9 / 24 * deriv y t)|
    ≤ 20 * M * h ^ 5
  have hreshape :
      h * (55 / 24 * deriv y (t + 3 * h)
            - 59 / 24 * deriv y (t + 2 * h)
            + 37 / 24 * deriv y (t + h)
            - 9 / 24 * deriv y t)
        = h * ((55 / 24) * deriv y (t + 3 * h)
              - (59 / 24) * deriv y (t + 2 * h)
              + (37 / 24) * deriv y (t + h)
              - (9 / 24) * deriv y t) := by ring
  rw [hreshape]
  exact ab4_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem ht4h_mem hh.le

/-- Final AB4 global error bound on `[t₀, t₀ + T]`. Under Lipschitz `f`,
`C^5` exact solution `y` with `deriv y t = f t (y t)`, and starting
errors `|y_i - y(t_i)| ≤ ε₀` for `i = 0, 1, 2, 3`, the AB4 iterate error
obeys `O(ε₀ + h^4)` on a finite horizon. -/
theorem ab4_global_error_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 5 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      ∀ {y₀ y₁ y₂ y₃ ε₀ : ℝ}, 0 ≤ ε₀ →
      |y₀ - y t₀| ≤ ε₀ → |y₁ - y (t₀ + h)| ≤ ε₀ →
      |y₂ - y (t₀ + 2 * h)| ≤ ε₀ →
      |y₃ - y (t₀ + 3 * h)| ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 3) * h ≤ T →
      |ab4Iter h f t₀ y₀ y₁ y₂ y₃ N - y (t₀ + (N : ℝ) * h)|
        ≤ Real.exp ((20 / 3) * L * T) * ε₀ + K * h ^ 4 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    ab4_local_residual_bound hy t₀ T hT
  refine ⟨T * Real.exp ((20 / 3) * L * T) * C, δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
  intro h hh hδ_le y₀ y₁ y₂ y₃ ε₀ hε₀ he0_bd he1_bd he2_bd he3_bd N hNh
  -- Error sequence and 4-window max-norm sequence.
  set eN : ℕ → ℝ :=
    fun k => |ab4Iter h f t₀ y₀ y₁ y₂ y₃ k - y (t₀ + (k : ℝ) * h)| with heN_def
  set EN : ℕ → ℝ :=
    fun k => max (max (max (eN k) (eN (k + 1))) (eN (k + 2))) (eN (k + 3))
    with hEN_def
  have heN_nn : ∀ k, 0 ≤ eN k := fun _ => abs_nonneg _
  have hEN_nn : ∀ k, 0 ≤ EN k := fun k =>
    le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (heN_nn k)))
  -- Initial bound: EN 0 ≤ ε₀.
  have hEN0_le : EN 0 ≤ ε₀ := by
    show max (max (max (eN 0) (eN 1)) (eN 2)) (eN 3) ≤ ε₀
    refine max_le (max_le (max_le ?_ ?_) ?_) ?_
    · show |ab4Iter h f t₀ y₀ y₁ y₂ y₃ 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)| ≤ ε₀
      simpa using he0_bd
    · show |ab4Iter h f t₀ y₀ y₁ y₂ y₃ 1 - y (t₀ + ((1 : ℕ) : ℝ) * h)| ≤ ε₀
      have hcast : ((1 : ℕ) : ℝ) * h = h := by push_cast; ring
      rw [hcast]
      simpa using he1_bd
    · show |ab4Iter h f t₀ y₀ y₁ y₂ y₃ 2 - y (t₀ + ((2 : ℕ) : ℝ) * h)| ≤ ε₀
      have hcast : ((2 : ℕ) : ℝ) * h = 2 * h := by push_cast; ring
      rw [hcast]
      simpa using he2_bd
    · show |ab4Iter h f t₀ y₀ y₁ y₂ y₃ 3 - y (t₀ + ((3 : ℕ) : ℝ) * h)| ≤ ε₀
      have hcast : ((3 : ℕ) : ℝ) * h = 3 * h := by push_cast; ring
      rw [hcast]
      simpa using he3_bd
  have hLeff_nn : (0 : ℝ) ≤ (20 / 3) * L := by positivity
  -- The general recurrence: when (n + 4) * h ≤ T,
  -- EN (n+1) ≤ (1 + h*((20/3)*L)) * EN n + C * h^5.
  have hstep_general : ∀ n : ℕ, ((n : ℝ) + 4) * h ≤ T →
      EN (n + 1) ≤ (1 + h * ((20 / 3) * L)) * EN n + C * h ^ 5 := by
    intro n hnh_le
    have honestep := ab4_one_step_error_bound (h := h) (L := L)
        hh.le hL hf t₀ y₀ y₁ y₂ y₃ y hyf n
    have hres := hresidual hh hδ_le n hnh_le
    have hcast1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hcast2 : ((n + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    have hcast3 : ((n + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
    have hcast4 : ((n + 1 + 1 + 1 + 1 : ℕ) : ℝ) = (n : ℝ) + 4 := by
      push_cast; ring
    have heq_eN_n1 : eN (n + 1)
        = |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 1) - y (t₀ + ((n : ℝ) + 1) * h)| := by
      show |_ - _| = _
      rw [hcast1]
    have heq_eN_n2 : eN (n + 1 + 1)
        = |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 2) - y (t₀ + ((n : ℝ) + 2) * h)| := by
      show |_ - _| = _
      rw [hcast2]
    have heq_eN_n3 : eN (n + 1 + 1 + 1)
        = |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)| := by
      show |_ - _| = _
      rw [hcast3]
    have heq_eN_n4 : eN (n + 1 + 1 + 1 + 1)
        = |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 4) - y (t₀ + ((n : ℝ) + 4) * h)| := by
      show |_ - _| = _
      rw [hcast4]
    show max (max (max (eN (n + 1)) (eN (n + 1 + 1))) (eN (n + 1 + 1 + 1)))
            (eN (n + 1 + 1 + 1 + 1))
        ≤ (1 + h * ((20 / 3) * L))
            * max (max (max (eN n) (eN (n + 1))) (eN (n + 1 + 1)))
                (eN (n + 1 + 1 + 1))
          + C * h ^ 5
    rw [heq_eN_n1, heq_eN_n2, heq_eN_n3, heq_eN_n4]
    show max (max (max
              |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 1)
                - y (t₀ + ((n : ℝ) + 1) * h)|
              |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 2)
                - y (t₀ + ((n : ℝ) + 2) * h)|)
              |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 3)
                - y (t₀ + ((n : ℝ) + 3) * h)|)
              |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 4)
                - y (t₀ + ((n : ℝ) + 4) * h)|
        ≤ (1 + h * ((20 / 3) * L))
            * max (max (max (eN n)
                  |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 1)
                    - y (t₀ + ((n : ℝ) + 1) * h)|)
                  |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 2)
                    - y (t₀ + ((n : ℝ) + 2) * h)|)
                  |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (n + 3)
                    - y (t₀ + ((n : ℝ) + 3) * h)|
          + C * h ^ 5
    linarith [honestep, hres]
  have hexp_ge : (1 : ℝ) ≤ Real.exp ((20 / 3) * L * T) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hKnn : 0 ≤ T * Real.exp ((20 / 3) * L * T) * C :=
    mul_nonneg (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
  have hh4_nn : 0 ≤ h ^ 4 := by positivity
  have hexp_nn : 0 ≤ Real.exp ((20 / 3) * L * T) := Real.exp_nonneg _
  -- Helper: any base error ≤ ε₀ implies the headline bound.
  have hbase_to_headline : ∀ q : ℝ, q ≤ ε₀ →
      q ≤ Real.exp ((20 / 3) * L * T) * ε₀
            + T * Real.exp ((20 / 3) * L * T) * C * h ^ 4 := by
    intro q hq
    have hexp_ε₀ : ε₀ ≤ Real.exp ((20 / 3) * L * T) * ε₀ := by
      have hone : (1 : ℝ) * ε₀ ≤ Real.exp ((20 / 3) * L * T) * ε₀ :=
        mul_le_mul_of_nonneg_right hexp_ge hε₀
      linarith
    have hKh4_nn : 0 ≤ T * Real.exp ((20 / 3) * L * T) * C * h ^ 4 :=
      mul_nonneg hKnn hh4_nn
    linarith
  match N, hNh with
  | 0, _ =>
    have hbase : |ab4Iter h f t₀ y₀ y₁ y₂ y₃ 0 - y (t₀ + ((0 : ℕ) : ℝ) * h)|
        ≤ ε₀ := by simpa using he0_bd
    exact hbase_to_headline _ hbase
  | 1, _ =>
    have hbase : |ab4Iter h f t₀ y₀ y₁ y₂ y₃ 1 - y (t₀ + ((1 : ℕ) : ℝ) * h)|
        ≤ ε₀ := by
      have hcast : ((1 : ℕ) : ℝ) * h = h := by push_cast; ring
      rw [hcast]; simpa using he1_bd
    exact hbase_to_headline _ hbase
  | 2, _ =>
    have hbase : |ab4Iter h f t₀ y₀ y₁ y₂ y₃ 2 - y (t₀ + ((2 : ℕ) : ℝ) * h)|
        ≤ ε₀ := by
      have hcast : ((2 : ℕ) : ℝ) * h = 2 * h := by push_cast; ring
      rw [hcast]; simpa using he2_bd
    exact hbase_to_headline _ hbase
  | 3, _ =>
    have hbase : |ab4Iter h f t₀ y₀ y₁ y₂ y₃ 3 - y (t₀ + ((3 : ℕ) : ℝ) * h)|
        ≤ ε₀ := by
      have hcast : ((3 : ℕ) : ℝ) * h = 3 * h := by push_cast; ring
      rw [hcast]; simpa using he3_bd
    exact hbase_to_headline _ hbase
  | N' + 4, hNh =>
    -- Apply Gronwall to EN at index N'+1, then use EN_{N'+1} ≥ e_{N'+4}.
    have hcast : (((N' + 4 : ℕ) : ℝ)) = (N' : ℝ) + 4 := by push_cast; ring
    have hN_hyp : ((N' : ℝ) + 4) * h ≤ T := by
      have := hNh
      rw [hcast] at this
      linarith
    have hgronwall_step : ∀ n, n < N' + 1 →
        EN (n + 1) ≤ (1 + h * ((20 / 3) * L)) * EN n + C * h ^ (4 + 1) := by
      intro n hn_lt
      have hpow : C * h ^ (4 + 1) = C * h ^ 5 := by norm_num
      rw [hpow]
      apply hstep_general
      have hn1_le_N' : (n : ℝ) + 1 ≤ (N' : ℝ) + 1 := by
        have : (n : ℝ) ≤ (N' : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp hn_lt
        linarith
      have h_le_chain : (n : ℝ) + 4 ≤ (N' : ℝ) + 4 := by linarith
      have h_mul : ((n : ℝ) + 4) * h ≤ ((N' : ℝ) + 4) * h :=
        mul_le_mul_of_nonneg_right h_le_chain hh.le
      linarith
    have hN'1h_le_T : ((N' + 1 : ℕ) : ℝ) * h ≤ T := by
      have hcast' : ((N' + 1 : ℕ) : ℝ) = (N' : ℝ) + 1 := by push_cast; ring
      rw [hcast']
      have : (N' : ℝ) + 1 ≤ (N' : ℝ) + 4 := by linarith
      have := mul_le_mul_of_nonneg_right this hh.le
      linarith
    have hgronwall :=
      lmm_error_bound_from_local_truncation
        (h := h) (L := (20 / 3) * L) (C := C) (T := T) (p := 4)
        (e := EN) (N := N' + 1)
        hh.le hLeff_nn hC_nn (hEN_nn 0) hgronwall_step (N' + 1) le_rfl hN'1h_le_T
    -- eN (N' + 4) ≤ EN (N' + 1).
    have heN_le_EN : eN (N' + 4) ≤ EN (N' + 1) := by
      show eN (N' + 4) ≤ max (max (max (eN (N' + 1)) (eN (N' + 1 + 1)))
              (eN (N' + 1 + 2))) (eN (N' + 1 + 3))
      have heq : N' + 4 = N' + 1 + 3 := by ring
      rw [heq]
      exact le_max_right _ _
    have h_chain :
        Real.exp ((20 / 3) * L * T) * EN 0 ≤ Real.exp ((20 / 3) * L * T) * ε₀ :=
      mul_le_mul_of_nonneg_left hEN0_le hexp_nn
    show |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (N' + 4) - y (t₀ + ((N' + 4 : ℕ) : ℝ) * h)|
        ≤ Real.exp ((20 / 3) * L * T) * ε₀
          + T * Real.exp ((20 / 3) * L * T) * C * h ^ 4
    have heN_eq :
        eN (N' + 4)
          = |ab4Iter h f t₀ y₀ y₁ y₂ y₃ (N' + 4)
              - y (t₀ + ((N' + 4 : ℕ) : ℝ) * h)| := rfl
    linarith [heN_le_EN, hgronwall, h_chain, heN_eq.symm.le, heN_eq.le]

/-! ### Vector-valued Adams–Bashforth 4-step convergence chain

Vector mirror of the scalar AB4 convergence chain above, in the same
finite-dimensional normed vector setting used by the AB2 and AB3 vector chains. -/

/-- AB4 iteration in a normed vector space, with four starting samples
`y₀, y₁, y₂, y₃`:
`y_{n+4} = y_{n+3} + h • ((55/24) • f_{n+3} − (59/24) • f_{n+2}
  + (37/24) • f_{n+1} − (9/24) • f_n)`. -/
noncomputable def ab4IterVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ : E) : ℕ → E
  | 0 => y₀
  | 1 => y₁
  | 2 => y₂
  | 3 => y₃
  | n + 4 =>
      ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 3)
        + h • ((55 / 24 : ℝ) • f (t₀ + ((n : ℝ) + 3) * h)
                  (ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 3))
              - (59 / 24 : ℝ) • f (t₀ + ((n : ℝ) + 2) * h)
                  (ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 2))
              + (37 / 24 : ℝ) • f (t₀ + ((n : ℝ) + 1) * h)
                  (ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 1))
              - (9 / 24 : ℝ) • f (t₀ + (n : ℝ) * h)
                  (ab4IterVec h f t₀ y₀ y₁ y₂ y₃ n))

@[simp] lemma ab4IterVec_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ : E) :
    ab4IterVec h f t₀ y₀ y₁ y₂ y₃ 0 = y₀ := rfl

@[simp] lemma ab4IterVec_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ : E) :
    ab4IterVec h f t₀ y₀ y₁ y₂ y₃ 1 = y₁ := rfl

@[simp] lemma ab4IterVec_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ : E) :
    ab4IterVec h f t₀ y₀ y₁ y₂ y₃ 2 = y₂ := rfl

@[simp] lemma ab4IterVec_three
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ : E) :
    ab4IterVec h f t₀ y₀ y₁ y₂ y₃ 3 = y₃ := rfl

lemma ab4IterVec_succ_succ_succ_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ : E) (n : ℕ) :
    ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 4)
      = ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 3)
          + h • ((55 / 24 : ℝ) • f (t₀ + ((n : ℝ) + 3) * h)
                    (ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 3))
                - (59 / 24 : ℝ) • f (t₀ + ((n : ℝ) + 2) * h)
                    (ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 2))
                + (37 / 24 : ℝ) • f (t₀ + ((n : ℝ) + 1) * h)
                    (ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 1))
                - (9 / 24 : ℝ) • f (t₀ + (n : ℝ) * h)
                    (ab4IterVec h f t₀ y₀ y₁ y₂ y₃ n)) := rfl

/-- Textbook AB4 vector residual: the local one-step residual of the AB4
method on a smooth vector trajectory. -/
noncomputable def ab4VecResidual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) : E :=
  y (t + 4 * h) - y (t + 3 * h)
    - h • ((55 / 24 : ℝ) • deriv y (t + 3 * h)
          - (59 / 24 : ℝ) • deriv y (t + 2 * h)
          + (37 / 24 : ℝ) • deriv y (t + h)
          - (9 / 24 : ℝ) • deriv y t)

/-- The vector AB4 residual unfolds to the textbook form. -/
theorem ab4Vec_localTruncationError_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h t : ℝ) (y : ℝ → E) :
    ab4VecResidual h t y
      = y (t + 4 * h) - y (t + 3 * h)
          - h • ((55 / 24 : ℝ) • deriv y (t + 3 * h)
                - (59 / 24 : ℝ) • deriv y (t + 2 * h)
                + (37 / 24 : ℝ) • deriv y (t + h)
                - (9 / 24 : ℝ) • deriv y t) := rfl

theorem ab4Vec_one_step_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) (y₀ y₁ y₂ y₃ : E) (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 4)
        - y (t₀ + ((n : ℝ) + 4) * h)‖
      ≤ ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 3)
            - y (t₀ + ((n : ℝ) + 3) * h)‖
        + (55 / 24) * h * L
            * ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 3)
                - y (t₀ + ((n : ℝ) + 3) * h)‖
        + (59 / 24) * h * L
            * ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 2)
                - y (t₀ + ((n : ℝ) + 2) * h)‖
        + (37 / 24) * h * L
            * ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 1)
                - y (t₀ + ((n : ℝ) + 1) * h)‖
        + (9 / 24) * h * L
            * ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ n - y (t₀ + (n : ℝ) * h)‖
        + ‖ab4VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set yn : E := ab4IterVec h f t₀ y₀ y₁ y₂ y₃ n with hyn_def
  set yn1 : E := ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 1) with hyn1_def
  set yn2 : E := ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 2) with hyn2_def
  set yn3 : E := ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 3) with hyn3_def
  set tn : ℝ := t₀ + (n : ℝ) * h with htn_def
  set tn1 : ℝ := t₀ + ((n : ℝ) + 1) * h with htn1_def
  set tn2 : ℝ := t₀ + ((n : ℝ) + 2) * h with htn2_def
  set tn3 : ℝ := t₀ + ((n : ℝ) + 3) * h with htn3_def
  set tn4 : ℝ := t₀ + ((n : ℝ) + 4) * h with htn4_def
  set zn : E := y tn with hzn_def
  set zn1 : E := y tn1 with hzn1_def
  set zn2 : E := y tn2 with hzn2_def
  set zn3 : E := y tn3 with hzn3_def
  set zn4 : E := y tn4 with hzn4_def
  set τ : E := ab4VecResidual h tn y with hτ_def
  have htn1_h : tn + h = tn1 := by simp [htn_def, htn1_def]; ring
  have htn_2h : tn + 2 * h = tn2 := by simp [htn_def, htn2_def]; ring
  have htn_3h : tn + 3 * h = tn3 := by simp [htn_def, htn3_def]; ring
  have htn_4h : tn + 4 * h = tn4 := by simp [htn_def, htn4_def]; ring
  have hτ_eq :
      τ = zn4 - zn3
            - h • ((55 / 24 : ℝ) • f tn3 zn3
                  - (59 / 24 : ℝ) • f tn2 zn2
                  + (37 / 24 : ℝ) • f tn1 zn1
                  - (9 / 24 : ℝ) • f tn zn) := by
    show ab4VecResidual h tn y = _
    unfold ab4VecResidual
    rw [htn1_h, htn_2h, htn_3h, htn_4h, hyf tn3, hyf tn2, hyf tn1, hyf tn]
  have hstep : ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 4)
      = yn3 + h • ((55 / 24 : ℝ) • f tn3 yn3
                    - (59 / 24 : ℝ) • f tn2 yn2
                    + (37 / 24 : ℝ) • f tn1 yn1
                    - (9 / 24 : ℝ) • f tn yn) := by
    show ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 4) = _
    rw [ab4IterVec_succ_succ_succ_succ]
  have halg : ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 4) - zn4
      = (yn3 - zn3)
        + h • ((55 / 24 : ℝ) • (f tn3 yn3 - f tn3 zn3))
        - h • ((59 / 24 : ℝ) • (f tn2 yn2 - f tn2 zn2))
        + h • ((37 / 24 : ℝ) • (f tn1 yn1 - f tn1 zn1))
        - h • ((9 / 24 : ℝ) • (f tn yn - f tn zn))
        - τ := by
    rw [hstep, hτ_eq]
    simp only [smul_sub, smul_add]
    abel
  have hLip3 : ‖f tn3 yn3 - f tn3 zn3‖ ≤ L * ‖yn3 - zn3‖ := hf tn3 yn3 zn3
  have hLip2 : ‖f tn2 yn2 - f tn2 zn2‖ ≤ L * ‖yn2 - zn2‖ := hf tn2 yn2 zn2
  have hLip1 : ‖f tn1 yn1 - f tn1 zn1‖ ≤ L * ‖yn1 - zn1‖ := hf tn1 yn1 zn1
  have hLip0 : ‖f tn yn - f tn zn‖ ≤ L * ‖yn - zn‖ := hf tn yn zn
  have h55_nn : (0 : ℝ) ≤ 55 / 24 := by norm_num
  have h59_nn : (0 : ℝ) ≤ 59 / 24 := by norm_num
  have h37_nn : (0 : ℝ) ≤ 37 / 24 := by norm_num
  have h9_nn : (0 : ℝ) ≤ 9 / 24 := by norm_num
  have h55_norm :
      ‖h • ((55 / 24 : ℝ) • (f tn3 yn3 - f tn3 zn3))‖
        ≤ (55 / 24) * h * L * ‖yn3 - zn3‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h55_nn]
    have : h * ((55 / 24 : ℝ) * ‖f tn3 yn3 - f tn3 zn3‖)
        ≤ h * ((55 / 24 : ℝ) * (L * ‖yn3 - zn3‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip3 h55_nn
    nlinarith [this]
  have h59_norm :
      ‖h • ((59 / 24 : ℝ) • (f tn2 yn2 - f tn2 zn2))‖
        ≤ (59 / 24) * h * L * ‖yn2 - zn2‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h59_nn]
    have : h * ((59 / 24 : ℝ) * ‖f tn2 yn2 - f tn2 zn2‖)
        ≤ h * ((59 / 24 : ℝ) * (L * ‖yn2 - zn2‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip2 h59_nn
    nlinarith [this]
  have h37_norm :
      ‖h • ((37 / 24 : ℝ) • (f tn1 yn1 - f tn1 zn1))‖
        ≤ (37 / 24) * h * L * ‖yn1 - zn1‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h37_nn]
    have : h * ((37 / 24 : ℝ) * ‖f tn1 yn1 - f tn1 zn1‖)
        ≤ h * ((37 / 24 : ℝ) * (L * ‖yn1 - zn1‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip1 h37_nn
    nlinarith [this]
  have h9_norm :
      ‖h • ((9 / 24 : ℝ) • (f tn yn - f tn zn))‖
        ≤ (9 / 24) * h * L * ‖yn - zn‖ := by
    rw [norm_smul, Real.norm_of_nonneg hh,
        norm_smul, Real.norm_of_nonneg h9_nn]
    have : h * ((9 / 24 : ℝ) * ‖f tn yn - f tn zn‖)
        ≤ h * ((9 / 24 : ℝ) * (L * ‖yn - zn‖)) := by
      apply mul_le_mul_of_nonneg_left _ hh
      exact mul_le_mul_of_nonneg_left hLip0 h9_nn
    nlinarith [this]
  set A : E := yn3 - zn3 with hA_def
  set B : E := h • ((55 / 24 : ℝ) • (f tn3 yn3 - f tn3 zn3)) with hB_def
  set C : E := h • ((59 / 24 : ℝ) • (f tn2 yn2 - f tn2 zn2)) with hC_def
  set D : E := h • ((37 / 24 : ℝ) • (f tn1 yn1 - f tn1 zn1)) with hD_def
  set G : E := h • ((9 / 24 : ℝ) • (f tn yn - f tn zn)) with hG_def
  have htri : ‖A + B - C + D - G - τ‖
      ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖G‖ + ‖τ‖ := by
    have h1 : ‖A + B - C + D - G - τ‖ ≤ ‖A + B - C + D - G‖ + ‖τ‖ :=
      norm_sub_le _ _
    have h2 : ‖A + B - C + D - G‖ ≤ ‖A + B - C + D‖ + ‖G‖ :=
      norm_sub_le _ _
    have h3 : ‖A + B - C + D‖ ≤ ‖A + B - C‖ + ‖D‖ :=
      norm_add_le _ _
    have h4 : ‖A + B - C‖ ≤ ‖A + B‖ + ‖C‖ :=
      norm_sub_le _ _
    have h5 : ‖A + B‖ ≤ ‖A‖ + ‖B‖ := norm_add_le _ _
    linarith
  have hB_bd : ‖B‖ ≤ (55 / 24) * h * L * ‖yn3 - zn3‖ := by
    simpa [hB_def] using h55_norm
  have hC_bd : ‖C‖ ≤ (59 / 24) * h * L * ‖yn2 - zn2‖ := by
    simpa [hC_def] using h59_norm
  have hD_bd : ‖D‖ ≤ (37 / 24) * h * L * ‖yn1 - zn1‖ := by
    simpa [hD_def] using h37_norm
  have hG_bd : ‖G‖ ≤ (9 / 24) * h * L * ‖yn - zn‖ := by
    simpa [hG_def] using h9_norm
  have hcalc :
      ‖A + B - C + D - G - τ‖
        ≤ ‖yn3 - zn3‖
          + (55 / 24) * h * L * ‖yn3 - zn3‖
          + (59 / 24) * h * L * ‖yn2 - zn2‖
          + (37 / 24) * h * L * ‖yn1 - zn1‖
          + (9 / 24) * h * L * ‖yn - zn‖
          + ‖τ‖ := by
    have hA_norm : ‖A‖ = ‖yn3 - zn3‖ := by rw [hA_def]
    linarith [htri, hA_norm, hB_bd, hC_bd, hD_bd, hG_bd]
  calc
    ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 4) - zn4‖
        = ‖A + B - C + D - G - τ‖ := by
          rw [halg, hA_def, hB_def, hC_def, hD_def, hG_def]
    _ ≤ ‖yn3 - zn3‖
          + (55 / 24) * h * L * ‖yn3 - zn3‖
          + (59 / 24) * h * L * ‖yn2 - zn2‖
          + (37 / 24) * h * L * ‖yn1 - zn1‖
          + (9 / 24) * h * L * ‖yn - zn‖
          + ‖τ‖ := hcalc

theorem ab4Vec_one_step_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → E → E}
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (t₀ : ℝ) (y₀ y₁ y₂ y₃ : E) (y : ℝ → E)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max (max
          ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 1)
              - y (t₀ + ((n : ℝ) + 1) * h)‖
          ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 2)
              - y (t₀ + ((n : ℝ) + 2) * h)‖)
          ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 3)
              - y (t₀ + ((n : ℝ) + 3) * h)‖)
        ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 4)
            - y (t₀ + ((n : ℝ) + 4) * h)‖
      ≤ (1 + h * ((20 / 3) * L))
            * max (max (max
                  ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ n
                      - y (t₀ + (n : ℝ) * h)‖
                  ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 1)
                      - y (t₀ + ((n : ℝ) + 1) * h)‖)
                  ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 2)
                      - y (t₀ + ((n : ℝ) + 2) * h)‖)
                  ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 3)
                      - y (t₀ + ((n : ℝ) + 3) * h)‖
        + ‖ab4VecResidual h (t₀ + (n : ℝ) * h) y‖ := by
  set en : ℝ :=
    ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ n - y (t₀ + (n : ℝ) * h)‖ with hen_def
  set en1 : ℝ :=
    ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 1)
        - y (t₀ + ((n : ℝ) + 1) * h)‖ with hen1_def
  set en2 : ℝ :=
    ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 2)
        - y (t₀ + ((n : ℝ) + 2) * h)‖ with hen2_def
  set en3 : ℝ :=
    ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 3)
        - y (t₀ + ((n : ℝ) + 3) * h)‖ with hen3_def
  set en4 : ℝ :=
    ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 4)
        - y (t₀ + ((n : ℝ) + 4) * h)‖ with hen4_def
  set τabs : ℝ := ‖ab4VecResidual h (t₀ + (n : ℝ) * h) y‖ with hτabs_def
  have hen_nn : 0 ≤ en := norm_nonneg _
  have hen1_nn : 0 ≤ en1 := norm_nonneg _
  have hen2_nn : 0 ≤ en2 := norm_nonneg _
  have hen3_nn : 0 ≤ en3 := norm_nonneg _
  have hτ_nn : 0 ≤ τabs := norm_nonneg _
  have hstep :
      en4 ≤ en3 + (55 / 24) * h * L * en3
                + (59 / 24) * h * L * en2
                + (37 / 24) * h * L * en1
                + (9 / 24) * h * L * en + τabs := by
    have := ab4Vec_one_step_lipschitz hh hf t₀ y₀ y₁ y₂ y₃ y hyf n
    show ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 4)
          - y (t₀ + ((n : ℝ) + 4) * h)‖
        ≤ ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 3)
              - y (t₀ + ((n : ℝ) + 3) * h)‖
          + (55 / 24) * h * L
              * ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 3)
                  - y (t₀ + ((n : ℝ) + 3) * h)‖
          + (59 / 24) * h * L
              * ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 2)
                  - y (t₀ + ((n : ℝ) + 2) * h)‖
          + (37 / 24) * h * L
              * ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (n + 1)
                  - y (t₀ + ((n : ℝ) + 1) * h)‖
          + (9 / 24) * h * L
              * ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ n
                  - y (t₀ + (n : ℝ) * h)‖
          + ‖ab4VecResidual h (t₀ + (n : ℝ) * h) y‖
    exact this
  set EN_n : ℝ := max (max (max en en1) en2) en3 with hEN_n_def
  have hen_le_EN : en ≤ EN_n :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hen1_le_EN : en1 ≤ EN_n :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hen2_le_EN : en2 ≤ EN_n :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hen3_le_EN : en3 ≤ EN_n := le_max_right _ _
  have h55_nn : 0 ≤ (55 / 24) * h * L := by positivity
  have h59_nn : 0 ≤ (59 / 24) * h * L := by positivity
  have h37_nn : 0 ≤ (37 / 24) * h * L := by positivity
  have h9_nn : 0 ≤ (9 / 24) * h * L := by positivity
  have hEN_nn : 0 ≤ EN_n := le_trans hen_nn hen_le_EN
  have hcoef_nn : 0 ≤ h * ((20 / 3) * L) := by positivity
  have hen4_bd : en4 ≤ (1 + h * ((20 / 3) * L)) * EN_n + τabs := by
    have h1 : (55 / 24) * h * L * en3 ≤ (55 / 24) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen3_le_EN h55_nn
    have h2 : (59 / 24) * h * L * en2 ≤ (59 / 24) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen2_le_EN h59_nn
    have h3 : (37 / 24) * h * L * en1 ≤ (37 / 24) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen1_le_EN h37_nn
    have h4 : (9 / 24) * h * L * en ≤ (9 / 24) * h * L * EN_n :=
      mul_le_mul_of_nonneg_left hen_le_EN h9_nn
    have h_alg :
        EN_n + (55 / 24) * h * L * EN_n
              + (59 / 24) * h * L * EN_n
              + (37 / 24) * h * L * EN_n
              + (9 / 24) * h * L * EN_n + τabs
          = (1 + h * ((20 / 3) * L)) * EN_n + τabs := by ring
    linarith [hstep, hen3_le_EN, h1, h2, h3, h4, h_alg.le]
  have hEN_le_grow : EN_n ≤ (1 + h * ((20 / 3) * L)) * EN_n := by
    have hone : (1 : ℝ) * EN_n ≤ (1 + h * ((20 / 3) * L)) * EN_n :=
      mul_le_mul_of_nonneg_right (by linarith) hEN_nn
    linarith
  have hen1_bd : en1 ≤ (1 + h * ((20 / 3) * L)) * EN_n + τabs := by
    linarith [hen1_le_EN, hEN_le_grow]
  have hen2_bd : en2 ≤ (1 + h * ((20 / 3) * L)) * EN_n + τabs := by
    linarith [hen2_le_EN, hEN_le_grow]
  have hen3_bd : en3 ≤ (1 + h * ((20 / 3) * L)) * EN_n + τabs := by
    linarith [hen3_le_EN, hEN_le_grow]
  exact max_le (max_le (max_le hen1_bd hen2_bd) hen3_bd) hen4_bd

private theorem iteratedDeriv_five_bounded_on_Icc_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 5 y) (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 5 y t‖ ≤ M := by
  have h_cont : Continuous (iteratedDeriv 5 y) :=
    hy.continuous_iteratedDeriv 5 (by norm_num)
  obtain ⟨M, hM⟩ :=
    IsCompact.exists_bound_of_continuousOn isCompact_Icc h_cont.continuousOn
  exact ⟨max M 0, le_max_right _ _, fun t ht => (hM t ht).trans (le_max_left _ _)⟩

private theorem deriv_second_order_taylor_remainder_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {g : ℝ → E} (hg : ContDiff ℝ 3 g) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 3 g t‖ ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    ‖deriv g (t + r) - deriv g t - r • iteratedDeriv 2 g t‖
      ≤ M / 2 * r ^ 2 := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have htr_le : t ≤ t + r := by linarith
  have hdg : ContDiff ℝ 2 (deriv g) := hg.deriv'
  have h_idd2_bound :
      ∀ s ∈ Set.Icc t (t + r),
        ‖iteratedDeriv 2 g s - iteratedDeriv 2 g t‖ ≤ M * (s - t) := by
    intro s hs
    have hts : t ≤ s := hs.1
    have hdiff_idd2 : Differentiable ℝ (iteratedDeriv 2 g) :=
      hg.differentiable_iteratedDeriv 2 (by norm_num)
    have hderiv_on :
        ∀ x ∈ Set.Icc t s,
          HasDerivWithinAt (iteratedDeriv 2 g) (iteratedDeriv 3 g x)
            (Set.Icc t s) x := by
      intro x _hx
      have hxderiv : HasDerivAt (iteratedDeriv 2 g) (iteratedDeriv 3 g x) x := by
        have := (hdiff_idd2 x).hasDerivAt
        convert this using 1
        rw [iteratedDeriv_succ]
      exact hxderiv.hasDerivWithinAt
    have hbound_seg : ∀ x ∈ Set.Ico t s, ‖iteratedDeriv 3 g x‖ ≤ M := by
      intro x hx
      have hx_ab : x ∈ Set.Icc a b := by
        refine ⟨?_, ?_⟩
        · linarith [ht.1, hx.1]
        · linarith [htr.2, hs.2, hx.2]
      exact hbnd x hx_ab
    have hseg :=
      norm_image_sub_le_of_norm_deriv_le_segment'
        (f := iteratedDeriv 2 g) (f' := fun x => iteratedDeriv 3 g x)
        (a := t) (b := s) hderiv_on hbound_seg s
        (Set.right_mem_Icc.mpr hts)
    simpa using hseg
  have h_idd2_cont : Continuous (iteratedDeriv 2 g) :=
    hg.continuous_iteratedDeriv 2 (by norm_num)
  have h_idd2_int :
      IntervalIntegrable (fun s => iteratedDeriv 2 g s)
        MeasureTheory.volume t (t + r) :=
    h_idd2_cont.intervalIntegrable _ _
  have h_const_int :
      IntervalIntegrable (fun _ : ℝ => iteratedDeriv 2 g t)
        MeasureTheory.volume t (t + r) := intervalIntegrable_const
  have h_ftc :
      ∫ s in t..t + r, iteratedDeriv 2 g s = deriv g (t + r) - deriv g t := by
    have hderiv_at :
        ∀ x ∈ Set.uIcc t (t + r),
          HasDerivAt (deriv g) (iteratedDeriv 2 g x) x := by
      intro x _hx
      have hdiff : Differentiable ℝ (deriv g) := hdg.differentiable (by norm_num)
      have h1 : HasDerivAt (deriv g) (deriv (deriv g) x) x :=
        (hdiff x).hasDerivAt
      have h2 : deriv (deriv g) x = iteratedDeriv 2 g x := by
        rw [show iteratedDeriv 2 g = deriv (iteratedDeriv 1 g) from
            iteratedDeriv_succ, iteratedDeriv_one]
      rw [← h2]; exact h1
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_at h_idd2_int
  have h_residual_integral :
      deriv g (t + r) - deriv g t - r • iteratedDeriv 2 g t
        = ∫ s in t..t + r, (iteratedDeriv 2 g s - iteratedDeriv 2 g t) := by
    rw [intervalIntegral.integral_sub h_idd2_int h_const_int, h_ftc]
    simp
  have h_bound_integral :
      ‖∫ s in t..t + r, (iteratedDeriv 2 g s - iteratedDeriv 2 g t)‖
        ≤ ∫ s in t..t + r, M * (s - t) := by
    refine intervalIntegral.norm_integral_le_of_norm_le htr_le ?_ ?_
    · exact Filter.Eventually.of_forall fun s hs =>
        h_idd2_bound s ⟨hs.1.le, hs.2⟩
    · exact (by fun_prop : Continuous fun s : ℝ => M * (s - t)).intervalIntegrable _ _
  have h_integral_eval :
      ∫ s in t..t + r, M * (s - t) = M / 2 * r ^ 2 := by
    calc
      ∫ s in t..t + r, M * (s - t)
          = M * (∫ s in t..t + r, (s - t)) := by
            rw [intervalIntegral.integral_const_mul]
      _ = M / 2 * r ^ 2 := by
        simp [intervalIntegral.integral_sub, integral_id,
          intervalIntegral.integral_const]
        ring
  rw [h_residual_integral]
  exact h_bound_integral.trans_eq h_integral_eval

private theorem third_order_taylor_remainder_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {g : ℝ → E} (hg : ContDiff ℝ 3 g) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 3 g t‖ ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    ‖g (t + r) - g t - r • deriv g t - (r ^ 2 / 2) • iteratedDeriv 2 g t‖
      ≤ M / 6 * r ^ 3 := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have htr_le : t ≤ t + r := by linarith
  have h_dg_bound :
      ∀ s ∈ Set.Icc t (t + r),
        ‖deriv g s - deriv g t - (s - t) • iteratedDeriv 2 g t‖
          ≤ M / 2 * (s - t) ^ 2 := by
    intro s hs
    have hts : 0 ≤ s - t := by linarith [hs.1]
    have hs_ab : s ∈ Set.Icc a b := by
      refine ⟨?_, ?_⟩
      · linarith [ht.1, hs.1]
      · linarith [htr.2, hs.2]
    have hsplit : t + (s - t) = s := by ring
    have :=
      deriv_second_order_taylor_remainder_vec hg hbnd ht
        (by rw [hsplit]; exact hs_ab) hts
    rw [hsplit] at this
    exact this
  have hdg_cont : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  have h_dg_int :
      IntervalIntegrable (fun s => deriv g s) MeasureTheory.volume t (t + r) :=
    hdg_cont.intervalIntegrable _ _
  have h_const_int :
      IntervalIntegrable (fun _ : ℝ => deriv g t)
        MeasureTheory.volume t (t + r) := intervalIntegrable_const
  have h_lin_int :
      IntervalIntegrable (fun s : ℝ => (s - t) • iteratedDeriv 2 g t)
        MeasureTheory.volume t (t + r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h_ftc_g :
      ∫ s in t..t + r, deriv g s = g (t + r) - g t := by
    have hderiv_at :
        ∀ x ∈ Set.uIcc t (t + r),
          HasDerivAt g (deriv g x) x := by
      intro x _hx
      exact (hg.differentiable (by norm_num) x).hasDerivAt
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_at h_dg_int
  have h_lin_eval :
      ∫ s in t..t + r, (s - t) • iteratedDeriv 2 g t
        = (r ^ 2 / 2) • iteratedDeriv 2 g t := by
    rw [intervalIntegral.integral_smul_const]
    have h_int_smul :
        ∫ s in t..t + r, (s - t) = r ^ 2 / 2 := by
      simp [intervalIntegral.integral_sub, integral_id,
        intervalIntegral.integral_const]
      ring
    rw [h_int_smul]
  have h_residual_integral :
      g (t + r) - g t - r • deriv g t - (r ^ 2 / 2) • iteratedDeriv 2 g t
        = ∫ s in t..t + r,
            (deriv g s - deriv g t - (s - t) • iteratedDeriv 2 g t) := by
    rw [intervalIntegral.integral_sub
        (h_dg_int.sub h_const_int) h_lin_int,
      intervalIntegral.integral_sub h_dg_int h_const_int,
      h_ftc_g, h_lin_eval]
    have h_const_eval :
        ∫ _ in t..t + r, deriv g t = r • deriv g t := by
      rw [intervalIntegral.integral_const]
      simp
    rw [h_const_eval]
  have h_bound_integral :
      ‖∫ s in t..t + r,
          (deriv g s - deriv g t - (s - t) • iteratedDeriv 2 g t)‖
        ≤ ∫ s in t..t + r, M / 2 * (s - t) ^ 2 := by
    refine intervalIntegral.norm_integral_le_of_norm_le htr_le ?_ ?_
    · exact Filter.Eventually.of_forall fun s hs =>
        h_dg_bound s ⟨hs.1.le, hs.2⟩
    · exact (by fun_prop :
        Continuous fun s : ℝ => M / 2 * (s - t) ^ 2).intervalIntegrable _ _
  have h_integral_eval :
      ∫ s in t..t + r, M / 2 * (s - t) ^ 2 = M / 6 * r ^ 3 := by
    have h_inner : ∫ s in t..t + r, (s - t) ^ 2 = r ^ 3 / 3 := by
      have hsub :
          ∫ s in t..t + r, (s - t) ^ 2
            = ∫ s in (t - t)..(t + r - t), s ^ 2 :=
        intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 2) t
      rw [hsub]
      rw [integral_pow]
      have hzero : (t - t) = (0 : ℝ) := sub_self _
      have hr : (t + r - t) = r := by ring
      rw [hzero, hr]
      ring
    rw [intervalIntegral.integral_const_mul, h_inner]
    ring
  rw [h_residual_integral]
  exact h_bound_integral.trans_eq h_integral_eval

private theorem y_fourth_order_taylor_remainder_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 4 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 4 y t‖ ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    ‖y (t + r) - y t - r • deriv y t
        - (r ^ 2 / 2) • iteratedDeriv 2 y t
        - (r ^ 3 / 6) • iteratedDeriv 3 y t‖
      ≤ M / 24 * r ^ 4 := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have htr_le : t ≤ t + r := by linarith
  have hdy : ContDiff ℝ 3 (deriv y) := hy.deriv'
  have hbnd_d :
      ∀ s ∈ Set.Icc a b, ‖iteratedDeriv 3 (deriv y) s‖ ≤ M := by
    intro s hs
    have hidd_eq : iteratedDeriv 3 (deriv y) = iteratedDeriv 4 y := by
      have : iteratedDeriv 4 y = iteratedDeriv 3 (deriv y) :=
        iteratedDeriv_succ' (n := 3) (f := y)
      exact this.symm
    simpa [hidd_eq] using hbnd s hs
  have h_dy_bound :
      ∀ s ∈ Set.Icc t (t + r),
        ‖deriv y s - deriv y t - (s - t) • iteratedDeriv 2 y t
            - ((s - t) ^ 2 / 2) • iteratedDeriv 3 y t‖
          ≤ M / 6 * (s - t) ^ 3 := by
    intro s hs
    have hts : 0 ≤ s - t := by linarith [hs.1]
    have hs_ab : s ∈ Set.Icc a b := by
      refine ⟨?_, ?_⟩
      · linarith [ht.1, hs.1]
      · linarith [htr.2, hs.2]
    have hsplit : t + (s - t) = s := by ring
    have hrem :=
      third_order_taylor_remainder_vec hdy hbnd_d ht
        (by rw [hsplit]; exact hs_ab) hts
    have hderiv2 : deriv (deriv y) t = iteratedDeriv 2 y t := by
      rw [show iteratedDeriv 2 y = deriv (iteratedDeriv 1 y) from
          iteratedDeriv_succ, iteratedDeriv_one]
    have hiter2 : iteratedDeriv 2 (deriv y) t = iteratedDeriv 3 y t := by
      have : iteratedDeriv 3 y = iteratedDeriv 2 (deriv y) :=
        iteratedDeriv_succ' (n := 2) (f := y)
      rw [this]
    rw [hsplit] at hrem
    simpa [hderiv2, hiter2] using hrem
  have hdy_cont : Continuous (deriv y) := hy.continuous_deriv (by norm_num)
  have h_dy_int :
      IntervalIntegrable (fun s => deriv y s) MeasureTheory.volume t (t + r) :=
    hdy_cont.intervalIntegrable _ _
  have h_const_int :
      IntervalIntegrable (fun _ : ℝ => deriv y t)
        MeasureTheory.volume t (t + r) := intervalIntegrable_const
  have h_lin_int :
      IntervalIntegrable (fun s : ℝ => (s - t) • iteratedDeriv 2 y t)
        MeasureTheory.volume t (t + r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h_quad_int :
      IntervalIntegrable (fun s : ℝ => ((s - t) ^ 2 / 2) • iteratedDeriv 3 y t)
        MeasureTheory.volume t (t + r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h_ftc_y :
      ∫ s in t..t + r, deriv y s = y (t + r) - y t := by
    have hderiv_at :
        ∀ x ∈ Set.uIcc t (t + r),
          HasDerivAt y (deriv y x) x := by
      intro x _hx
      exact (hy.differentiable (by norm_num) x).hasDerivAt
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_at h_dy_int
  have h_lin_eval :
      ∫ s in t..t + r, (s - t) • iteratedDeriv 2 y t
        = (r ^ 2 / 2) • iteratedDeriv 2 y t := by
    rw [intervalIntegral.integral_smul_const]
    have h_int_smul :
        ∫ s in t..t + r, (s - t) = r ^ 2 / 2 := by
      simp [intervalIntegral.integral_sub, integral_id,
        intervalIntegral.integral_const]
      ring
    rw [h_int_smul]
  have h_quad_eval :
      ∫ s in t..t + r, ((s - t) ^ 2 / 2) • iteratedDeriv 3 y t
        = (r ^ 3 / 6) • iteratedDeriv 3 y t := by
    rw [intervalIntegral.integral_smul_const]
    have h_inner : ∫ s in t..t + r, (s - t) ^ 2 = r ^ 3 / 3 := by
      have hsub :
          ∫ s in t..t + r, (s - t) ^ 2
            = ∫ s in (t - t)..(t + r - t), s ^ 2 :=
        intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 2) t
      rw [hsub, integral_pow]
      have hzero : (t - t) = (0 : ℝ) := sub_self _
      have hr' : (t + r - t) = r := by ring
      rw [hzero, hr']
      ring
    have h_fun :
        (fun s : ℝ => (s - t) ^ 2 / 2)
          = fun s : ℝ => (1 / 2 : ℝ) * (s - t) ^ 2 := by
      funext s
      ring
    have h_int_smul :
        ∫ s in t..t + r, (s - t) ^ 2 / 2 = r ^ 3 / 6 := by
      rw [h_fun, intervalIntegral.integral_const_mul, h_inner]
      ring
    rw [h_int_smul]
  have h_residual_integral :
      y (t + r) - y t - r • deriv y t
          - (r ^ 2 / 2) • iteratedDeriv 2 y t
          - (r ^ 3 / 6) • iteratedDeriv 3 y t
        = ∫ s in t..t + r,
            (deriv y s - deriv y t - (s - t) • iteratedDeriv 2 y t
              - ((s - t) ^ 2 / 2) • iteratedDeriv 3 y t) := by
    rw [intervalIntegral.integral_sub
        ((h_dy_int.sub h_const_int).sub h_lin_int) h_quad_int,
      intervalIntegral.integral_sub (h_dy_int.sub h_const_int) h_lin_int,
      intervalIntegral.integral_sub h_dy_int h_const_int,
      h_ftc_y, h_lin_eval, h_quad_eval]
    have h_const_eval :
        ∫ _ in t..t + r, deriv y t = r • deriv y t := by
      rw [intervalIntegral.integral_const]
      simp
    rw [h_const_eval]
  have h_bound_integral :
      ‖∫ s in t..t + r,
          (deriv y s - deriv y t - (s - t) • iteratedDeriv 2 y t
            - ((s - t) ^ 2 / 2) • iteratedDeriv 3 y t)‖
        ≤ ∫ s in t..t + r, M / 6 * (s - t) ^ 3 := by
    refine intervalIntegral.norm_integral_le_of_norm_le htr_le ?_ ?_
    · exact Filter.Eventually.of_forall fun s hs =>
        h_dy_bound s ⟨hs.1.le, hs.2⟩
    · exact (by fun_prop :
        Continuous fun s : ℝ => M / 6 * (s - t) ^ 3).intervalIntegrable _ _
  have h_integral_eval :
      ∫ s in t..t + r, M / 6 * (s - t) ^ 3 = M / 24 * r ^ 4 := by
    have h_inner : ∫ s in t..t + r, (s - t) ^ 3 = r ^ 4 / 4 := by
      have hsub :
          ∫ s in t..t + r, (s - t) ^ 3
            = ∫ s in (t - t)..(t + r - t), s ^ 3 :=
        intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 3) t
      rw [hsub, integral_pow]
      have hzero : (t - t) = (0 : ℝ) := sub_self _
      have hr' : (t + r - t) = r := by ring
      rw [hzero, hr']
      ring
    rw [intervalIntegral.integral_const_mul, h_inner]
    ring
  rw [h_residual_integral]
  exact h_bound_integral.trans_eq h_integral_eval

private theorem y_fifth_order_taylor_remainder_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 5 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 5 y t‖ ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    ‖y (t + r) - y t - r • deriv y t
        - (r ^ 2 / 2) • iteratedDeriv 2 y t
        - (r ^ 3 / 6) • iteratedDeriv 3 y t
        - (r ^ 4 / 24) • iteratedDeriv 4 y t‖
      ≤ M / 120 * r ^ 5 := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have htr_le : t ≤ t + r := by linarith
  have hdy : ContDiff ℝ 4 (deriv y) := hy.deriv'
  have hbnd_d :
      ∀ s ∈ Set.Icc a b, ‖iteratedDeriv 4 (deriv y) s‖ ≤ M := by
    intro s hs
    have hidd_eq : iteratedDeriv 4 (deriv y) = iteratedDeriv 5 y := by
      have : iteratedDeriv 5 y = iteratedDeriv 4 (deriv y) :=
        iteratedDeriv_succ' (n := 4) (f := y)
      exact this.symm
    simpa [hidd_eq] using hbnd s hs
  have h_dy_bound :
      ∀ s ∈ Set.Icc t (t + r),
        ‖deriv y s - deriv y t - (s - t) • iteratedDeriv 2 y t
            - ((s - t) ^ 2 / 2) • iteratedDeriv 3 y t
            - ((s - t) ^ 3 / 6) • iteratedDeriv 4 y t‖
          ≤ M / 24 * (s - t) ^ 4 := by
    intro s hs
    have hts : 0 ≤ s - t := by linarith [hs.1]
    have hs_ab : s ∈ Set.Icc a b := by
      refine ⟨?_, ?_⟩
      · linarith [ht.1, hs.1]
      · linarith [htr.2, hs.2]
    have hsplit : t + (s - t) = s := by ring
    have hrem :=
      y_fourth_order_taylor_remainder_vec hdy hbnd_d ht
        (by rw [hsplit]; exact hs_ab) hts
    have hderiv2 : deriv (deriv y) t = iteratedDeriv 2 y t := by
      rw [show iteratedDeriv 2 y = deriv (iteratedDeriv 1 y) from
          iteratedDeriv_succ, iteratedDeriv_one]
    have hiter2 : iteratedDeriv 2 (deriv y) t = iteratedDeriv 3 y t := by
      have : iteratedDeriv 3 y = iteratedDeriv 2 (deriv y) :=
        iteratedDeriv_succ' (n := 2) (f := y)
      rw [this]
    have hiter3 : iteratedDeriv 3 (deriv y) t = iteratedDeriv 4 y t := by
      have : iteratedDeriv 4 y = iteratedDeriv 3 (deriv y) :=
        iteratedDeriv_succ' (n := 3) (f := y)
      rw [this]
    rw [hsplit] at hrem
    simpa [hderiv2, hiter2, hiter3] using hrem
  have hdy_cont : Continuous (deriv y) := hy.continuous_deriv (by norm_num)
  have h_dy_int :
      IntervalIntegrable (fun s => deriv y s) MeasureTheory.volume t (t + r) :=
    hdy_cont.intervalIntegrable _ _
  have h_const_int :
      IntervalIntegrable (fun _ : ℝ => deriv y t)
        MeasureTheory.volume t (t + r) := intervalIntegrable_const
  have h_lin_int :
      IntervalIntegrable (fun s : ℝ => (s - t) • iteratedDeriv 2 y t)
        MeasureTheory.volume t (t + r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h_quad_int :
      IntervalIntegrable (fun s : ℝ => ((s - t) ^ 2 / 2) • iteratedDeriv 3 y t)
        MeasureTheory.volume t (t + r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h_cubic_int :
      IntervalIntegrable (fun s : ℝ => ((s - t) ^ 3 / 6) • iteratedDeriv 4 y t)
        MeasureTheory.volume t (t + r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h_ftc_y :
      ∫ s in t..t + r, deriv y s = y (t + r) - y t := by
    have hderiv_at :
        ∀ x ∈ Set.uIcc t (t + r),
          HasDerivAt y (deriv y x) x := by
      intro x _hx
      exact (hy.differentiable (by norm_num) x).hasDerivAt
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_at h_dy_int
  have h_lin_eval :
      ∫ s in t..t + r, (s - t) • iteratedDeriv 2 y t
        = (r ^ 2 / 2) • iteratedDeriv 2 y t := by
    rw [intervalIntegral.integral_smul_const]
    have h_int_smul :
        ∫ s in t..t + r, (s - t) = r ^ 2 / 2 := by
      simp [intervalIntegral.integral_sub, integral_id,
        intervalIntegral.integral_const]
      ring
    rw [h_int_smul]
  have h_quad_eval :
      ∫ s in t..t + r, ((s - t) ^ 2 / 2) • iteratedDeriv 3 y t
        = (r ^ 3 / 6) • iteratedDeriv 3 y t := by
    rw [intervalIntegral.integral_smul_const]
    have h_inner : ∫ s in t..t + r, (s - t) ^ 2 = r ^ 3 / 3 := by
      have hsub :
          ∫ s in t..t + r, (s - t) ^ 2
            = ∫ s in (t - t)..(t + r - t), s ^ 2 :=
        intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 2) t
      rw [hsub, integral_pow]
      have hzero : (t - t) = (0 : ℝ) := sub_self _
      have hr' : (t + r - t) = r := by ring
      rw [hzero, hr']
      ring
    have h_fun :
        (fun s : ℝ => (s - t) ^ 2 / 2)
          = fun s : ℝ => (1 / 2 : ℝ) * (s - t) ^ 2 := by
      funext s
      ring
    have h_int_smul :
        ∫ s in t..t + r, (s - t) ^ 2 / 2 = r ^ 3 / 6 := by
      rw [h_fun, intervalIntegral.integral_const_mul, h_inner]
      ring
    rw [h_int_smul]
  have h_cubic_eval :
      ∫ s in t..t + r, ((s - t) ^ 3 / 6) • iteratedDeriv 4 y t
        = (r ^ 4 / 24) • iteratedDeriv 4 y t := by
    rw [intervalIntegral.integral_smul_const]
    have h_inner : ∫ s in t..t + r, (s - t) ^ 3 = r ^ 4 / 4 := by
      have hsub :
          ∫ s in t..t + r, (s - t) ^ 3
            = ∫ s in (t - t)..(t + r - t), s ^ 3 :=
        intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 3) t
      rw [hsub, integral_pow]
      have hzero : (t - t) = (0 : ℝ) := sub_self _
      have hr' : (t + r - t) = r := by ring
      rw [hzero, hr']
      ring
    have h_fun :
        (fun s : ℝ => (s - t) ^ 3 / 6)
          = fun s : ℝ => (1 / 6 : ℝ) * (s - t) ^ 3 := by
      funext s
      ring
    have h_int_smul :
        ∫ s in t..t + r, (s - t) ^ 3 / 6 = r ^ 4 / 24 := by
      rw [h_fun, intervalIntegral.integral_const_mul, h_inner]
      ring
    rw [h_int_smul]
  have h_residual_integral :
      y (t + r) - y t - r • deriv y t
          - (r ^ 2 / 2) • iteratedDeriv 2 y t
          - (r ^ 3 / 6) • iteratedDeriv 3 y t
          - (r ^ 4 / 24) • iteratedDeriv 4 y t
        = ∫ s in t..t + r,
            (deriv y s - deriv y t - (s - t) • iteratedDeriv 2 y t
              - ((s - t) ^ 2 / 2) • iteratedDeriv 3 y t
              - ((s - t) ^ 3 / 6) • iteratedDeriv 4 y t) := by
    rw [intervalIntegral.integral_sub
        (((h_dy_int.sub h_const_int).sub h_lin_int).sub h_quad_int) h_cubic_int,
      intervalIntegral.integral_sub
        ((h_dy_int.sub h_const_int).sub h_lin_int) h_quad_int,
      intervalIntegral.integral_sub (h_dy_int.sub h_const_int) h_lin_int,
      intervalIntegral.integral_sub h_dy_int h_const_int,
      h_ftc_y, h_lin_eval, h_quad_eval, h_cubic_eval]
    have h_const_eval :
        ∫ _ in t..t + r, deriv y t = r • deriv y t := by
      rw [intervalIntegral.integral_const]
      simp
    rw [h_const_eval]
  have h_bound_integral :
      ‖∫ s in t..t + r,
          (deriv y s - deriv y t - (s - t) • iteratedDeriv 2 y t
            - ((s - t) ^ 2 / 2) • iteratedDeriv 3 y t
            - ((s - t) ^ 3 / 6) • iteratedDeriv 4 y t)‖
        ≤ ∫ s in t..t + r, M / 24 * (s - t) ^ 4 := by
    refine intervalIntegral.norm_integral_le_of_norm_le htr_le ?_ ?_
    · exact Filter.Eventually.of_forall fun s hs =>
        h_dy_bound s ⟨hs.1.le, hs.2⟩
    · exact (by fun_prop :
        Continuous fun s : ℝ => M / 24 * (s - t) ^ 4).intervalIntegrable _ _
  have h_integral_eval :
      ∫ s in t..t + r, M / 24 * (s - t) ^ 4 = M / 120 * r ^ 5 := by
    have h_inner : ∫ s in t..t + r, (s - t) ^ 4 = r ^ 5 / 5 := by
      have hsub :
          ∫ s in t..t + r, (s - t) ^ 4
            = ∫ s in (t - t)..(t + r - t), s ^ 4 :=
        intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 4) t
      rw [hsub, integral_pow]
      have hzero : (t - t) = (0 : ℝ) := sub_self _
      have hr' : (t + r - t) = r := by ring
      rw [hzero, hr']
      ring
    rw [intervalIntegral.integral_const_mul, h_inner]
    ring
  rw [h_residual_integral]
  exact h_bound_integral.trans_eq h_integral_eval

private theorem derivY_fourth_order_taylor_remainder_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 5 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 5 y t‖ ≤ M)
    {t r : ℝ} (ht : t ∈ Set.Icc a b) (htr : t + r ∈ Set.Icc a b)
    (hr : 0 ≤ r) :
    ‖deriv y (t + r) - deriv y t - r • iteratedDeriv 2 y t
        - (r ^ 2 / 2) • iteratedDeriv 3 y t
        - (r ^ 3 / 6) • iteratedDeriv 4 y t‖
      ≤ M / 24 * r ^ 4 := by
  have hdy : ContDiff ℝ 4 (deriv y) := hy.deriv'
  have hbnd_d :
      ∀ s ∈ Set.Icc a b, ‖iteratedDeriv 4 (deriv y) s‖ ≤ M := by
    intro s hs
    have hidd_eq : iteratedDeriv 4 (deriv y) = iteratedDeriv 5 y := by
      have : iteratedDeriv 5 y = iteratedDeriv 4 (deriv y) :=
        iteratedDeriv_succ' (n := 4) (f := y)
      exact this.symm
    simpa [hidd_eq] using hbnd s hs
  have hrem := y_fourth_order_taylor_remainder_vec hdy hbnd_d ht htr hr
  have hderiv2 : deriv (deriv y) t = iteratedDeriv 2 y t := by
    rw [show iteratedDeriv 2 y = deriv (iteratedDeriv 1 y) from
        iteratedDeriv_succ, iteratedDeriv_one]
  have hiter2 : iteratedDeriv 2 (deriv y) t = iteratedDeriv 3 y t := by
    have : iteratedDeriv 3 y = iteratedDeriv 2 (deriv y) :=
      iteratedDeriv_succ' (n := 2) (f := y)
    rw [this]
  have hiter3 : iteratedDeriv 3 (deriv y) t = iteratedDeriv 4 y t := by
    have : iteratedDeriv 4 y = iteratedDeriv 3 (deriv y) :=
      iteratedDeriv_succ' (n := 3) (f := y)
    rw [this]
  simpa [hderiv2, hiter2, hiter3] using hrem

private theorem ab4Vec_pointwise_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 5 y) {a b M : ℝ}
    (hbnd : ∀ t ∈ Set.Icc a b, ‖iteratedDeriv 5 y t‖ ≤ M)
    {t h : ℝ} (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (ht4h : t + 4 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    ‖y (t + 4 * h) - y (t + 3 * h)
        - h • ((55 / 24 : ℝ) • deriv y (t + 3 * h)
              - (59 / 24 : ℝ) • deriv y (t + 2 * h)
              + (37 / 24 : ℝ) • deriv y (t + h)
              - (9 / 24 : ℝ) • deriv y t)‖
      ≤ (20 : ℝ) * M * h ^ 5 := by
  have h2h : 0 ≤ 2 * h := by linarith
  have h3h : 0 ≤ 3 * h := by linarith
  have h4h : 0 ≤ 4 * h := by linarith
  have hRy3 :=
    y_fifth_order_taylor_remainder_vec hy hbnd ht ht3h h3h
  have hRy4 :=
    y_fifth_order_taylor_remainder_vec hy hbnd ht ht4h h4h
  have hRyp1 :=
    derivY_fourth_order_taylor_remainder_vec hy hbnd ht hth hh
  have hRyp2 :=
    derivY_fourth_order_taylor_remainder_vec hy hbnd ht ht2h h2h
  have hRyp3 :=
    derivY_fourth_order_taylor_remainder_vec hy hbnd ht ht3h h3h
  set y0 : E := y t with hy0_def
  set y3 : E := y (t + 3 * h) with hy3_def
  set y4 : E := y (t + 4 * h) with hy4_def
  set d0 : E := deriv y t with hd0_def
  set d1 : E := deriv y (t + h) with hd1_def
  set d2 : E := deriv y (t + 2 * h) with hd2_def
  set d3 : E := deriv y (t + 3 * h) with hd3_def
  set dd : E := iteratedDeriv 2 y t with hdd_def
  set ddd : E := iteratedDeriv 3 y t with hddd_def
  set dddd : E := iteratedDeriv 4 y t with hdddd_def
  have hLTE_eq :
      y4 - y3 - h • ((55 / 24 : ℝ) • d3 - (59 / 24 : ℝ) • d2
                    + (37 / 24 : ℝ) • d1 - (9 / 24 : ℝ) • d0)
        = (y4 - y0 - (4 * h) • d0
              - ((4 * h) ^ 2 / 2) • dd
              - ((4 * h) ^ 3 / 6) • ddd
              - ((4 * h) ^ 4 / 24) • dddd)
          - (y3 - y0 - (3 * h) • d0
              - ((3 * h) ^ 2 / 2) • dd
              - ((3 * h) ^ 3 / 6) • ddd
              - ((3 * h) ^ 4 / 24) • dddd)
          - (55 * h / 24 : ℝ)
              • (d3 - d0 - (3 * h) • dd
                  - ((3 * h) ^ 2 / 2) • ddd
                  - ((3 * h) ^ 3 / 6) • dddd)
          + (59 * h / 24 : ℝ)
              • (d2 - d0 - (2 * h) • dd
                  - ((2 * h) ^ 2 / 2) • ddd
                  - ((2 * h) ^ 3 / 6) • dddd)
          - (37 * h / 24 : ℝ)
              • (d1 - d0 - h • dd
                  - (h ^ 2 / 2) • ddd
                  - (h ^ 3 / 6) • dddd) := by
    simp only [smul_sub, smul_add, smul_smul]
    module
  rw [hLTE_eq]
  set A : E := y4 - y0 - (4 * h) • d0
            - ((4 * h) ^ 2 / 2) • dd
            - ((4 * h) ^ 3 / 6) • ddd
            - ((4 * h) ^ 4 / 24) • dddd with hA_def
  set B : E := y3 - y0 - (3 * h) • d0
            - ((3 * h) ^ 2 / 2) • dd
            - ((3 * h) ^ 3 / 6) • ddd
            - ((3 * h) ^ 4 / 24) • dddd with hB_def
  set C : E := d3 - d0 - (3 * h) • dd
            - ((3 * h) ^ 2 / 2) • ddd
            - ((3 * h) ^ 3 / 6) • dddd with hC_def
  set D : E := d2 - d0 - (2 * h) • dd
            - ((2 * h) ^ 2 / 2) • ddd
            - ((2 * h) ^ 3 / 6) • dddd with hD_def
  set G : E := d1 - d0 - h • dd
            - (h ^ 2 / 2) • ddd
            - (h ^ 3 / 6) • dddd with hG_def
  have h55h_nn : 0 ≤ (55 * h / 24 : ℝ) := by linarith
  have h59h_nn : 0 ≤ (59 * h / 24 : ℝ) := by linarith
  have h37h_nn : 0 ≤ (37 * h / 24 : ℝ) := by linarith
  have htri :
      ‖A - B - (55 * h / 24 : ℝ) • C + (59 * h / 24 : ℝ) • D
          - (37 * h / 24 : ℝ) • G‖
        ≤ ‖A‖ + ‖B‖ + ‖(55 * h / 24 : ℝ) • C‖
            + ‖(59 * h / 24 : ℝ) • D‖
            + ‖(37 * h / 24 : ℝ) • G‖ := by
    have h1 : ‖A - B - (55 * h / 24 : ℝ) • C + (59 * h / 24 : ℝ) • D
          - (37 * h / 24 : ℝ) • G‖
        ≤ ‖A - B - (55 * h / 24 : ℝ) • C + (59 * h / 24 : ℝ) • D‖
          + ‖(37 * h / 24 : ℝ) • G‖ := norm_sub_le _ _
    have h2 : ‖A - B - (55 * h / 24 : ℝ) • C + (59 * h / 24 : ℝ) • D‖
        ≤ ‖A - B - (55 * h / 24 : ℝ) • C‖
          + ‖(59 * h / 24 : ℝ) • D‖ := norm_add_le _ _
    have h3 : ‖A - B - (55 * h / 24 : ℝ) • C‖
        ≤ ‖A - B‖ + ‖(55 * h / 24 : ℝ) • C‖ := norm_sub_le _ _
    have h4 : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
    linarith
  have hA_bd : ‖A‖ ≤ M / 120 * (4 * h) ^ 5 := hRy4
  have hB_bd : ‖B‖ ≤ M / 120 * (3 * h) ^ 5 := hRy3
  have hC_bd : ‖C‖ ≤ M / 24 * (3 * h) ^ 4 := hRyp3
  have hD_bd : ‖D‖ ≤ M / 24 * (2 * h) ^ 4 := hRyp2
  have hG_bd : ‖G‖ ≤ M / 24 * h ^ 4 := hRyp1
  have h55C_bd :
      ‖(55 * h / 24 : ℝ) • C‖
        ≤ (55 * h / 24 : ℝ) * (M / 24 * (3 * h) ^ 4) := by
    rw [norm_smul, Real.norm_of_nonneg h55h_nn]
    exact mul_le_mul_of_nonneg_left hC_bd h55h_nn
  have h59D_bd :
      ‖(59 * h / 24 : ℝ) • D‖
        ≤ (59 * h / 24 : ℝ) * (M / 24 * (2 * h) ^ 4) := by
    rw [norm_smul, Real.norm_of_nonneg h59h_nn]
    exact mul_le_mul_of_nonneg_left hD_bd h59h_nn
  have h37G_bd :
      ‖(37 * h / 24 : ℝ) • G‖
        ≤ (37 * h / 24 : ℝ) * (M / 24 * h ^ 4) := by
    rw [norm_smul, Real.norm_of_nonneg h37h_nn]
    exact mul_le_mul_of_nonneg_left hG_bd h37h_nn
  have hbound_alg :
      M / 120 * (4 * h) ^ 5 + M / 120 * (3 * h) ^ 5
        + (55 * h / 24) * (M / 24 * (3 * h) ^ 4)
        + (59 * h / 24) * (M / 24 * (2 * h) ^ 4)
        + (37 * h / 24) * (M / 24 * h ^ 4)
        = (57588 / 2880 : ℝ) * M * h ^ 5 := by ring
  have hMnn : 0 ≤ M := by
    have := hbnd t ht
    exact (norm_nonneg _).trans this
  have hh5_nn : 0 ≤ h ^ 5 := by positivity
  have hMh5_nn : 0 ≤ M * h ^ 5 := mul_nonneg hMnn hh5_nn
  have hslack : (57588 / 2880 : ℝ) * M * h ^ 5 ≤ 20 * M * h ^ 5 := by
    have hle : (57588 / 2880 : ℝ) ≤ 20 := by norm_num
    have := mul_le_mul_of_nonneg_right hle hMh5_nn
    linarith [this]
  linarith [htri, hA_bd, hB_bd, h55C_bd, h59D_bd, h37G_bd,
    hbound_alg.le, hbound_alg.ge, hslack]

theorem ab4Vec_local_residual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 5 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 4) * h ≤ T →
        ‖ab4VecResidual h (t₀ + (n : ℝ) * h) y‖
          ≤ C * h ^ 5 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_five_bounded_on_Icc_vec hy t₀ (t₀ + T + 1)
  refine ⟨(20 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 4) * h :=
        mul_le_mul_of_nonneg_right (by linarith) hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + h ≤ ((n : ℝ) + 4) * h := by nlinarith
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 4) * h := by nlinarith
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 4) * h := by nlinarith
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have h1 : (n : ℝ) * h + 4 * h = ((n : ℝ) + 4) * h := by ring
    linarith
  show ‖ab4VecResidual h t y‖ ≤ 20 * M * h ^ 5
  unfold ab4VecResidual
  exact ab4Vec_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem
    ht3h_mem ht4h_mem hh.le

/-! #### Refactor through the generic vector AB scaffold

Cycle 430 rewires the headline `ab4Vec_global_error_bound` through
`LMM.ab_global_error_bound_generic_vec` at `s = 4`, using the AB4
coefficient tuple `(-9/24, 37/24, -59/24, 55/24)`. -/

/-- AB4 coefficient vector for the generic AB scaffold:
`α 0 = -9/24`, `α 1 = 37/24`, `α 2 = -59/24`, `α 3 = 55/24`. -/
noncomputable def ab4GenericCoeff : Fin 4 → ℝ :=
  ![-(9 : ℝ) / 24, (37 : ℝ) / 24, -(59 : ℝ) / 24, (55 : ℝ) / 24]

@[simp] lemma ab4GenericCoeff_zero :
    ab4GenericCoeff 0 = -(9 : ℝ) / 24 := rfl

@[simp] lemma ab4GenericCoeff_one :
    ab4GenericCoeff 1 = (37 : ℝ) / 24 := rfl

@[simp] lemma ab4GenericCoeff_two :
    ab4GenericCoeff 2 = -(59 : ℝ) / 24 := rfl

@[simp] lemma ab4GenericCoeff_three :
    ab4GenericCoeff 3 = (55 : ℝ) / 24 := rfl

/-- The effective Lipschitz constant for the generic AB scaffold at the
AB4 coefficient tuple is `(20/3) · L`. -/
lemma abLip_ab4GenericCoeff (L : ℝ) :
    abLip 4 ab4GenericCoeff L = (20 / 3) * L := by
  rw [abLip, Fin.sum_univ_four, ab4GenericCoeff_zero, ab4GenericCoeff_one,
    ab4GenericCoeff_two, ab4GenericCoeff_three]
  rw [show |(-(9 : ℝ) / 24)| = (9 : ℝ) / 24 by norm_num,
      show |((37 : ℝ) / 24)| = (37 : ℝ) / 24 by norm_num,
      show |(-(59 : ℝ) / 24)| = (59 : ℝ) / 24 by norm_num,
      show |((55 : ℝ) / 24)| = (55 : ℝ) / 24 by norm_num]
  ring

/-- Bridge: the AB4 vector iteration is the generic vector AB iteration
at `s = 4` with `α = ab4GenericCoeff` and starting samples
`![y₀, y₁, y₂, y₃]`. -/
lemma ab4IterVec_eq_abIterVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (f : ℝ → E → E) (t₀ : ℝ) (y₀ y₁ y₂ y₃ : E) (n : ℕ) :
    ab4IterVec h f t₀ y₀ y₁ y₂ y₃ n
      = abIterVec 4 ab4GenericCoeff h f t₀ ![y₀, y₁, y₂, y₃] n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      show ab4IterVec h f t₀ y₀ y₁ y₂ y₃ 0 = _
      rw [ab4IterVec_zero]
      unfold abIterVec
      simp
    | 1 =>
      show ab4IterVec h f t₀ y₀ y₁ y₂ y₃ 1 = _
      rw [ab4IterVec_one]
      unfold abIterVec
      simp
    | 2 =>
      show ab4IterVec h f t₀ y₀ y₁ y₂ y₃ 2 = _
      rw [ab4IterVec_two]
      unfold abIterVec
      simp
    | 3 =>
      show ab4IterVec h f t₀ y₀ y₁ y₂ y₃ 3 = _
      rw [ab4IterVec_three]
      unfold abIterVec
      simp
    | k + 4 =>
      rw [ab4IterVec_succ_succ_succ_succ]
      rw [abIterVec_step (s := 4) (by norm_num)
          ab4GenericCoeff h f t₀ ![y₀, y₁, y₂, y₃] k]
      rw [show (k + 4 - 1 : ℕ) = k + 3 from by omega]
      rw [Fin.sum_univ_four]
      have hval3 : ((3 : Fin 4) : ℕ) = 3 := rfl
      simp only [ab4GenericCoeff_zero, ab4GenericCoeff_one, ab4GenericCoeff_two,
        ab4GenericCoeff_three, Fin.val_zero, Fin.val_one, Fin.val_two,
        hval3, Nat.add_zero]
      rw [← ih k (by omega), ← ih (k + 1) (by omega), ← ih (k + 2) (by omega),
        ← ih (k + 3) (by omega)]
      rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring,
        show ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 by push_cast; ring,
        show ((k + 3 : ℕ) : ℝ) = (k : ℝ) + 3 by push_cast; ring]
      rw [show (-(9 : ℝ) / 24) •
              f (t₀ + (k : ℝ) * h) (ab4IterVec h f t₀ y₀ y₁ y₂ y₃ k)
            = -((9 / 24 : ℝ) •
              f (t₀ + (k : ℝ) * h) (ab4IterVec h f t₀ y₀ y₁ y₂ y₃ k)) by
        rw [show (-(9 : ℝ) / 24) = -(9 / 24 : ℝ) by ring]
        exact neg_smul _ _]
      rw [show (-(59 : ℝ) / 24) •
              f (t₀ + ((k : ℝ) + 2) * h) (ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (k + 2))
            = -((59 / 24 : ℝ) •
              f (t₀ + ((k : ℝ) + 2) * h)
                (ab4IterVec h f t₀ y₀ y₁ y₂ y₃ (k + 2))) by
        rw [show (-(59 : ℝ) / 24) = -(59 / 24 : ℝ) by ring]
        exact neg_smul _ _]
      abel

/-- Bridge: the AB4 vector residual at base point `t₀ + n · h` equals the
generic AB vector residual at index `n`. -/
lemma ab4VecResidual_eq_abResidualVec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : ℝ) (y : ℝ → E) (t₀ : ℝ) (n : ℕ) :
    ab4VecResidual h (t₀ + (n : ℝ) * h) y
      = abResidualVec 4 ab4GenericCoeff h y t₀ n := by
  unfold ab4VecResidual abResidualVec
  rw [Fin.sum_univ_four, ab4GenericCoeff_zero, ab4GenericCoeff_one,
    ab4GenericCoeff_two, ab4GenericCoeff_three]
  -- Align time-coordinate arguments.
  have eA : t₀ + (n : ℝ) * h + 4 * h = t₀ + ((n + 4 : ℕ) : ℝ) * h := by
    push_cast; ring
  have eB :
      t₀ + (n : ℝ) * h + 3 * h = t₀ + ((n + 4 - 1 : ℕ) : ℝ) * h := by
    have hsub : (n + 4 - 1 : ℕ) = n + 3 := by omega
    rw [hsub]; push_cast; ring
  have eC : t₀ + (n : ℝ) * h
      = t₀ + ((n + ((0 : Fin 4) : ℕ) : ℕ) : ℝ) * h := by
    simp [Fin.val_zero]
  have eD : t₀ + (n : ℝ) * h + h
      = t₀ + ((n + ((1 : Fin 4) : ℕ) : ℕ) : ℝ) * h := by
    simp [Fin.val_one]; ring
  have eE : t₀ + (n : ℝ) * h + 2 * h
      = t₀ + ((n + ((2 : Fin 4) : ℕ) : ℕ) : ℝ) * h := by
    simp [Fin.val_two]; ring
  have eF : t₀ + (n : ℝ) * h + 3 * h
      = t₀ + ((n + ((3 : Fin 4) : ℕ) : ℕ) : ℝ) * h := by
    have : ((3 : Fin 4) : ℕ) = 3 := rfl
    rw [this]; push_cast; ring
  rw [← eA, ← eB, ← eC, ← eD, ← eE, ← eF]
  -- Reorder the smul expression to match the generic coefficient order.
  rw [show (-(9 : ℝ) / 24) • deriv y (t₀ + (n : ℝ) * h)
        = -((9 / 24 : ℝ) • deriv y (t₀ + (n : ℝ) * h)) by
    rw [show (-(9 : ℝ) / 24) = -(9 / 24 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (-(59 : ℝ) / 24) • deriv y (t₀ + (n : ℝ) * h + 2 * h)
        = -((59 / 24 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 2 * h)) by
    rw [show (-(59 : ℝ) / 24) = -(59 / 24 : ℝ) by ring]
    exact neg_smul _ _]
  rw [show (55 / 24 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 3 * h)
        - (59 / 24 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 2 * h)
        + (37 / 24 : ℝ) • deriv y (t₀ + (n : ℝ) * h + h)
        - (9 / 24 : ℝ) • deriv y (t₀ + (n : ℝ) * h)
        = -((9 / 24 : ℝ) • deriv y (t₀ + (n : ℝ) * h))
          + (37 / 24 : ℝ) • deriv y (t₀ + (n : ℝ) * h + h)
          + -((59 / 24 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 2 * h))
          + (55 / 24 : ℝ) • deriv y (t₀ + (n : ℝ) * h + 3 * h) by abel]

theorem ab4Vec_global_error_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {y : ℝ → E} (hy : ContDiff ℝ 5 y)
    {f : ℝ → E → E} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ (t : ℝ) (a b : E), ‖f t a - f t b‖ ≤ L * ‖a - b‖)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      ∀ {y₀ y₁ y₂ y₃ : E} {ε₀ : ℝ}, 0 ≤ ε₀ →
      ‖y₀ - y t₀‖ ≤ ε₀ → ‖y₁ - y (t₀ + h)‖ ≤ ε₀ →
      ‖y₂ - y (t₀ + 2 * h)‖ ≤ ε₀ →
      ‖y₃ - y (t₀ + 3 * h)‖ ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 3) * h ≤ T →
      ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ N - y (t₀ + (N : ℝ) * h)‖
        ≤ Real.exp ((20 / 3) * L * T) * ε₀ + K * h ^ 4 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    ab4Vec_local_residual_bound hy t₀ T hT
  refine ⟨T * Real.exp ((20 / 3) * L * T) * C, δ, ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
  intro h hh hδ_le y₀ y₁ y₂ y₃ ε₀ hε₀ he0_bd he1_bd he2_bd he3_bd N hNh
  -- Specialize the generic vector AB convergence theorem at s = 4, p = 4.
  set α : Fin 4 → ℝ := ab4GenericCoeff with hα_def
  set y₀_quad : Fin 4 → E := ![y₀, y₁, y₂, y₃] with hy_quad_def
  have hs : (1 : ℕ) ≤ 4 := by norm_num
  haveI : Nonempty (Fin 4) := ⟨⟨0, hs⟩⟩
  -- (1) Starting bound on the window-max error.
  have hiter0 : abIterVec 4 α h f t₀ y₀_quad 0 = y₀ := by
    unfold abIterVec
    simp [hy_quad_def]
  have hiter1 : abIterVec 4 α h f t₀ y₀_quad 1 = y₁ := by
    unfold abIterVec
    simp [hy_quad_def]
  have hiter2 : abIterVec 4 α h f t₀ y₀_quad 2 = y₂ := by
    unfold abIterVec
    simp [hy_quad_def]
  have hiter3 : abIterVec 4 α h f t₀ y₀_quad 3 = y₃ := by
    unfold abIterVec
    simp [hy_quad_def]
  have hstart : abErrWindowVec hs α h f t₀ y₀_quad y 0 ≤ ε₀ := by
    unfold abErrWindowVec
    apply Finset.sup'_le
    intro j _
    show abErrVec 4 α h f t₀ y₀_quad y (0 + (j : ℕ)) ≤ ε₀
    unfold abErrVec
    fin_cases j
    · show ‖abIterVec 4 α h f t₀ y₀_quad 0
          - y (t₀ + ((0 + (((0 : Fin 4) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter0]
      have : ((0 + (((0 : Fin 4) : ℕ) : ℕ) : ℕ) : ℝ) = 0 := by simp
      rw [this, zero_mul, add_zero]
      exact he0_bd
    · show ‖abIterVec 4 α h f t₀ y₀_quad 1
          - y (t₀ + ((0 + (((1 : Fin 4) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter1]
      have : ((0 + (((1 : Fin 4) : ℕ) : ℕ) : ℕ) : ℝ) = 1 := by simp
      rw [this, one_mul]
      exact he1_bd
    · show ‖abIterVec 4 α h f t₀ y₀_quad 2
          - y (t₀ + ((0 + (((2 : Fin 4) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter2]
      have : ((0 + (((2 : Fin 4) : ℕ) : ℕ) : ℕ) : ℝ) = 2 := by simp
      rw [this]
      exact he2_bd
    · show ‖abIterVec 4 α h f t₀ y₀_quad 3
          - y (t₀ + ((0 + (((3 : Fin 4) : ℕ) : ℕ) : ℕ) : ℝ) * h)‖ ≤ ε₀
      rw [hiter3]
      have hval3 : ((3 : Fin 4) : ℕ) = 3 := rfl
      have : ((0 + (((3 : Fin 4) : ℕ) : ℕ) : ℕ) : ℝ) = 3 := by
        rw [hval3]; push_cast; ring
      rw [this]
      exact he3_bd
  -- (2) Residual bound for n < N, via the bridge.
  have hres_gen : ∀ n : ℕ, n < N →
      ‖abResidualVec 4 α h y t₀ n‖ ≤ C * h ^ (4 + 1) := by
    intro n hn_lt
    have hcast : (n : ℝ) + 4 ≤ (N : ℝ) + 3 := by
      have : (n : ℝ) + 1 ≤ (N : ℝ) := by
        exact_mod_cast Nat.lt_iff_add_one_le.mp hn_lt
      linarith
    have hn4_le : ((n : ℝ) + 4) * h ≤ T := by
      have hmul : ((n : ℝ) + 4) * h ≤ ((N : ℝ) + 3) * h :=
        mul_le_mul_of_nonneg_right hcast hh.le
      linarith
    have hres := hresidual hh hδ_le n hn4_le
    have hbridge :=
      ab4VecResidual_eq_abResidualVec (E := E) h y t₀ n
    have hpow : C * h ^ (4 + 1) = C * h ^ 5 := by norm_num
    rw [hα_def, ← hbridge]
    linarith [hres, hpow.symm.le, hpow.le]
  -- (3) (N : ℝ) * h ≤ T from ((N : ℝ) + 3) * h ≤ T and 0 ≤ h.
  have hNh' : (N : ℝ) * h ≤ T := by
    have hmono : (N : ℝ) * h ≤ ((N : ℝ) + 3) * h := by
      have h1 : (N : ℝ) ≤ (N : ℝ) + 3 := by linarith
      exact mul_le_mul_of_nonneg_right h1 hh.le
    linarith
  -- (4) Apply the generic theorem.
  have hgeneric :=
    ab_global_error_bound_generic_vec hs α hh.le hL hC_nn hf t₀ y₀_quad y hyf
      hε₀ hstart N hNh' hres_gen
  -- (5) Replace abLip 4 α L with (20/3) * L.
  rw [show abLip 4 α L = (20 / 3) * L from by
    rw [hα_def]
    exact abLip_ab4GenericCoeff L] at hgeneric
  -- (6) Bound abErrVec at index N by the window-max bound.
  have hwindow_ge : abErrVec 4 α h f t₀ y₀_quad y N
      ≤ abErrWindowVec hs α h f t₀ y₀_quad y N := by
    show abErrVec 4 α h f t₀ y₀_quad y (N + ((⟨0, hs⟩ : Fin 4) : ℕ))
        ≤ abErrWindowVec hs α h f t₀ y₀_quad y N
    unfold abErrWindowVec
    exact Finset.le_sup' (b := ⟨0, hs⟩)
      (f := fun j : Fin 4 => abErrVec 4 α h f t₀ y₀_quad y (N + (j : ℕ)))
      (Finset.mem_univ _)
  -- (7) Convert abErrVec at N to ‖ab4IterVec ... N - y(...)‖ via the iter bridge.
  have hbridge :
      abIterVec 4 α h f t₀ y₀_quad N = ab4IterVec h f t₀ y₀ y₁ y₂ y₃ N := by
    rw [hα_def, hy_quad_def]
    exact (ab4IterVec_eq_abIterVec h f t₀ y₀ y₁ y₂ y₃ N).symm
  have habsErr :
      abErrVec 4 α h f t₀ y₀_quad y N
        = ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ N - y (t₀ + (N : ℝ) * h)‖ := by
    show ‖abIterVec 4 α h f t₀ y₀_quad N - y (t₀ + (N : ℝ) * h)‖
        = ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ N - y (t₀ + (N : ℝ) * h)‖
    rw [hbridge]
  -- Conclude.
  show ‖ab4IterVec h f t₀ y₀ y₁ y₂ y₃ N - y (t₀ + (N : ℝ) * h)‖
      ≤ Real.exp ((20 / 3) * L * T) * ε₀
        + T * Real.exp ((20 / 3) * L * T) * C * h ^ 4
  linarith [hwindow_ge, hgeneric, habsErr.symm.le, habsErr.le]

end LMM
