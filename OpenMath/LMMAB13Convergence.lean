import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import OpenMath.MultistepMethods
import OpenMath.AdamsMethods
import OpenMath.LMMTruncationOp
import OpenMath.LMMABGenericConvergence
import OpenMath.LMMAB12Convergence
import OpenMath.LMMAM12Convergence

/-! ## Adams-Bashforth 13-step Scalar Convergence Chain (Iserles §1.2)

Order-13 explicit 13-step Adams-Bashforth scalar convergence scaffold. The
AB13 weights were computed by exact `Fraction` integration of the Lagrange
basis on nodes `0,...,12` over `[12, 13]`; their absolute sum is
`1439788039057 / 638512875`.

The weights, ordered from `f_n` through `f_(n+12)`, are
`(703604254357, -9160551085734, 55060974662412, -202322913738370,
507140369728425, -915883387152444, 1226443086129408, -1233589244941764,
932884546055895, -524924579905150, 214696591002612, -61497552797274,
13064406523627) / 2615348736000`.

The fourteenth-order scalar Taylor helpers used here
(`y_fourteenth_order_taylor_remainder`,
`derivY_thirteenth_order_taylor_remainder`,
`iteratedDeriv_fourteen_bounded_on_Icc`) are imported from
`LMMAM12Convergence`.

The fourteenth-order residual coefficient for AB13 is approximately
`5616577262114645115720677 / 10602754543180800000 ≈ 529728.12`, slacked
upward to the integer `529729`.
-/

namespace LMM

/-! ### AB13 coefficients and iteration -/

/-- AB13 coefficient vector for the generic AB scaffold, ordered from the
oldest sample `f_n` through `f_(n+12)`. -/
noncomputable def ab13GenericCoeff : Fin 13 → ℝ :=
  ![(703604254357 : ℝ) / 2615348736000, -(9160551085734 : ℝ) / 2615348736000, (55060974662412 : ℝ) / 2615348736000, -(202322913738370 : ℝ) / 2615348736000, (507140369728425 : ℝ) / 2615348736000, -(915883387152444 : ℝ) / 2615348736000, (1226443086129408 : ℝ) / 2615348736000, -(1233589244941764 : ℝ) / 2615348736000, (932884546055895 : ℝ) / 2615348736000, -(524924579905150 : ℝ) / 2615348736000, (214696591002612 : ℝ) / 2615348736000, -(61497552797274 : ℝ) / 2615348736000, (13064406523627 : ℝ) / 2615348736000]

@[simp] lemma ab13GenericCoeff_zero :
    ab13GenericCoeff 0 = (703604254357 : ℝ) / 2615348736000 := rfl
@[simp] lemma ab13GenericCoeff_one :
    ab13GenericCoeff 1 = -(9160551085734 : ℝ) / 2615348736000 := rfl
@[simp] lemma ab13GenericCoeff_two :
    ab13GenericCoeff 2 = (55060974662412 : ℝ) / 2615348736000 := rfl
@[simp] lemma ab13GenericCoeff_three :
    ab13GenericCoeff 3 = -(202322913738370 : ℝ) / 2615348736000 := rfl
@[simp] lemma ab13GenericCoeff_four :
    ab13GenericCoeff 4 = (507140369728425 : ℝ) / 2615348736000 := rfl
@[simp] lemma ab13GenericCoeff_five :
    ab13GenericCoeff 5 = -(915883387152444 : ℝ) / 2615348736000 := rfl
@[simp] lemma ab13GenericCoeff_six :
    ab13GenericCoeff 6 = (1226443086129408 : ℝ) / 2615348736000 := rfl
@[simp] lemma ab13GenericCoeff_seven :
    ab13GenericCoeff 7 = -(1233589244941764 : ℝ) / 2615348736000 := rfl
@[simp] lemma ab13GenericCoeff_eight :
    ab13GenericCoeff 8 = (932884546055895 : ℝ) / 2615348736000 := rfl
@[simp] lemma ab13GenericCoeff_nine :
    ab13GenericCoeff 9 = -(524924579905150 : ℝ) / 2615348736000 := rfl
@[simp] lemma ab13GenericCoeff_ten :
    ab13GenericCoeff 10 = (214696591002612 : ℝ) / 2615348736000 := rfl
@[simp] lemma ab13GenericCoeff_eleven :
    ab13GenericCoeff 11 = -(61497552797274 : ℝ) / 2615348736000 := rfl
@[simp] lemma ab13GenericCoeff_twelve :
    ab13GenericCoeff 12 = (13064406523627 : ℝ) / 2615348736000 := rfl

private lemma sum_univ_thirteen_aux {α : Type*} [AddCommMonoid α] (f : Fin 13 → α) :
    ∑ j : Fin 13, f j
      = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 := by
  simp [Fin.sum_univ_succ]
  ac_rfl

/-- The AB13 absolute coefficient sum is `1439788039057/638512875`. -/
lemma abLip_ab13GenericCoeff (L : ℝ) :
    abLip 13 ab13GenericCoeff L = (1439788039057 / 638512875) * L := by
  rw [abLip, sum_univ_thirteen_aux, ab13GenericCoeff_zero, ab13GenericCoeff_one,
    ab13GenericCoeff_two, ab13GenericCoeff_three, ab13GenericCoeff_four,
    ab13GenericCoeff_five, ab13GenericCoeff_six, ab13GenericCoeff_seven,
    ab13GenericCoeff_eight, ab13GenericCoeff_nine, ab13GenericCoeff_ten,
    ab13GenericCoeff_eleven, ab13GenericCoeff_twelve]
  norm_num
  ring

/-- AB13 iteration with thirteen starting samples. -/
noncomputable def ab13Iter
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ : ℝ)
    (y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ : ℝ) : ℕ → ℝ :=
  abIter 13 ab13GenericCoeff h f t₀
    ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂]

@[simp] lemma ab13Iter_zero
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ : ℝ) :
    ab13Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ 0 = y₀ := by
  unfold ab13Iter abIter
  simp

@[simp] lemma ab13Iter_one
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ : ℝ) :
    ab13Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ 1 = y₁ := by
  unfold ab13Iter abIter
  simp

@[simp] lemma ab13Iter_two
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ : ℝ) :
    ab13Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ 2 = y₂ := by
  unfold ab13Iter abIter
  simp

@[simp] lemma ab13Iter_three
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ : ℝ) :
    ab13Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ 3 = y₃ := by
  unfold ab13Iter abIter
  simp

@[simp] lemma ab13Iter_four
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ : ℝ) :
    ab13Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ 4 = y₄ := by
  unfold ab13Iter abIter
  simp

@[simp] lemma ab13Iter_five
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ : ℝ) :
    ab13Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ 5 = y₅ := by
  unfold ab13Iter abIter
  simp

@[simp] lemma ab13Iter_six
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ : ℝ) :
    ab13Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ 6 = y₆ := by
  unfold ab13Iter abIter
  simp

@[simp] lemma ab13Iter_seven
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ : ℝ) :
    ab13Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ 7 = y₇ := by
  unfold ab13Iter abIter
  simp

@[simp] lemma ab13Iter_eight
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ : ℝ) :
    ab13Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ 8 = y₈ := by
  unfold ab13Iter abIter
  simp

@[simp] lemma ab13Iter_nine
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ : ℝ) :
    ab13Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ 9 = y₉ := by
  unfold ab13Iter abIter
  simp

@[simp] lemma ab13Iter_ten
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ : ℝ) :
    ab13Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ 10 = y₁₀ := by
  unfold ab13Iter abIter
  simp

@[simp] lemma ab13Iter_eleven
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ : ℝ) :
    ab13Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ 11 = y₁₁ := by
  unfold ab13Iter abIter
  simp

@[simp] lemma ab13Iter_twelve
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ : ℝ) :
    ab13Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ 12 = y₁₂ := by
  unfold ab13Iter abIter
  simp

lemma ab13Iter_succ_thirteen
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ : ℝ)
    (n : ℕ) :
    ab13Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ (n + 13)
      = ab13Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ (n + 12)
        + h * ∑ j : Fin 13,
            ab13GenericCoeff j *
              f (t₀ + ((n + (j : ℕ) : ℕ) : ℝ) * h)
                (ab13Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ (n + (j : ℕ))) := by
  simpa [ab13Iter] using
    (abIter_step 13 (by norm_num : 0 < 13) ab13GenericCoeff h f t₀
      ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂] n)

/-! ### Truncation residual and one-step bounds -/

/-- AB13 local truncation operator reduces to the textbook residual. -/
theorem ab13_localTruncationError_eq
    (h t : ℝ) (y : ℝ → ℝ) :
    adamsBashforth13.localTruncationError h t y
      = y (t + 13 * h) - y (t + 12 * h)
        - h * (             (13064406523627 / 2615348736000 : ℝ) * deriv y (t + 12 * h)
             - (61497552797274 / 2615348736000 : ℝ) * deriv y (t + 11 * h)
             + (214696591002612 / 2615348736000 : ℝ) * deriv y (t + 10 * h)
             - (524924579905150 / 2615348736000 : ℝ) * deriv y (t + 9 * h)
             + (932884546055895 / 2615348736000 : ℝ) * deriv y (t + 8 * h)
             - (1233589244941764 / 2615348736000 : ℝ) * deriv y (t + 7 * h)
             + (1226443086129408 / 2615348736000 : ℝ) * deriv y (t + 6 * h)
             - (915883387152444 / 2615348736000 : ℝ) * deriv y (t + 5 * h)
             + (507140369728425 / 2615348736000 : ℝ) * deriv y (t + 4 * h)
             - (202322913738370 / 2615348736000 : ℝ) * deriv y (t + 3 * h)
             + (55060974662412 / 2615348736000 : ℝ) * deriv y (t + 2 * h)
             - (9160551085734 / 2615348736000 : ℝ) * deriv y (t + h)
             + (703604254357 / 2615348736000 : ℝ) * deriv y (t)) := by
  unfold localTruncationError truncationOp
  simp [adamsBashforth13, Fin.sum_univ_succ, iteratedDeriv_one,
    iteratedDeriv_zero]
  norm_num
  ring

/-- Bridge: the AB13 scalar truncation residual at base point `t₀ + n · h`
equals the generic AB residual at index `n`. -/
lemma ab13Residual_eq_abResidual
    (h : ℝ) (y : ℝ → ℝ) (t₀ : ℝ) (n : ℕ) :
    adamsBashforth13.localTruncationError h (t₀ + (n : ℝ) * h) y
      = abResidual 13 ab13GenericCoeff h y t₀ n := by
  rw [ab13_localTruncationError_eq]
  unfold abResidual
  rw [sum_univ_thirteen_aux, ab13GenericCoeff_zero, ab13GenericCoeff_one,
    ab13GenericCoeff_two, ab13GenericCoeff_three, ab13GenericCoeff_four,
    ab13GenericCoeff_five, ab13GenericCoeff_six, ab13GenericCoeff_seven,
    ab13GenericCoeff_eight, ab13GenericCoeff_nine, ab13GenericCoeff_ten,
    ab13GenericCoeff_eleven, ab13GenericCoeff_twelve]
  norm_num
  ring_nf

/-- Generic-facing AB13 one-step Lipschitz recurrence. -/
theorem ab13_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ : ℝ)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    abErrWindow (by norm_num : (1 : ℕ) ≤ 13) ab13GenericCoeff h f t₀
        ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂] y (n + 1)
      ≤ (1 + h * ((1439788039057 / 638512875) * L))
          * abErrWindow (by norm_num : (1 : ℕ) ≤ 13) ab13GenericCoeff h f t₀
              ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂] y n
        + |adamsBashforth13.localTruncationError h (t₀ + (n : ℝ) * h) y| := by
  have hgen :=
    abIter_lipschitz_one_step (s := 13)
      (by norm_num : (1 : ℕ) ≤ 13) ab13GenericCoeff hh hL hf t₀
      ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂] y hyf n
  rw [abLip_ab13GenericCoeff L] at hgen
  rw [← ab13Residual_eq_abResidual h y t₀ n] at hgen
  exact hgen

/-- Max-window AB13 one-step error recurrence with effective constant
`(1439788039057/638512875) * L`. -/
theorem ab13_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ : ℝ)
    (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    abErrWindow (by norm_num : (1 : ℕ) ≤ 13) ab13GenericCoeff h f t₀
        ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂] y (n + 1)
      ≤ (1 + h * ((1439788039057 / 638512875) * L))
          * abErrWindow (by norm_num : (1 : ℕ) ≤ 13) ab13GenericCoeff h f t₀
              ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂] y n
        + |adamsBashforth13.localTruncationError h (t₀ + (n : ℝ) * h) y| := by
  exact ab13_one_step_lipschitz hh hL hf t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ y hyf n

/-! ### Residual algebra and pointwise bound

The pointwise residual is proved through the generic Taylor-polynomial
decomposition from `LMMTruncationOp`: the degree-13 Taylor polynomial
contribution vanishes by `adamsBashforth13_order_thirteen`, and the remaining
finite sum is bounded termwise by the value and derivative Taylor remainders. -/

private lemma taylorPolyOf_eval_thirteen (y : ℝ → ℝ) (t r : ℝ) :
    (taylorPolyOf y t 13).eval r
      = y t + r * deriv y t
        + r ^ 2 / 2 * iteratedDeriv 2 y t
        + r ^ 3 / 6 * iteratedDeriv 3 y t
        + r ^ 4 / 24 * iteratedDeriv 4 y t
        + r ^ 5 / 120 * iteratedDeriv 5 y t
        + r ^ 6 / 720 * iteratedDeriv 6 y t
        + r ^ 7 / 5040 * iteratedDeriv 7 y t
        + r ^ 8 / 40320 * iteratedDeriv 8 y t
        + r ^ 9 / 362880 * iteratedDeriv 9 y t
        + r ^ 10 / 3628800 * iteratedDeriv 10 y t
        + r ^ 11 / 39916800 * iteratedDeriv 11 y t
        + r ^ 12 / 479001600 * iteratedDeriv 12 y t
        + r ^ 13 / 6227020800 * iteratedDeriv 13 y t := by
  unfold taylorPolyOf taylorPoly
  rw [Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one]
  ring

private lemma taylorPolyOf_derivative_eval_thirteen (y : ℝ → ℝ) (t r : ℝ) :
    (taylorPolyOf y t 13).derivative.eval r
      = deriv y t
        + r * iteratedDeriv 2 y t
        + r ^ 2 / 2 * iteratedDeriv 3 y t
        + r ^ 3 / 6 * iteratedDeriv 4 y t
        + r ^ 4 / 24 * iteratedDeriv 5 y t
        + r ^ 5 / 120 * iteratedDeriv 6 y t
        + r ^ 6 / 720 * iteratedDeriv 7 y t
        + r ^ 7 / 5040 * iteratedDeriv 8 y t
        + r ^ 8 / 40320 * iteratedDeriv 9 y t
        + r ^ 9 / 362880 * iteratedDeriv 10 y t
        + r ^ 10 / 3628800 * iteratedDeriv 11 y t
        + r ^ 11 / 39916800 * iteratedDeriv 12 y t
        + r ^ 12 / 479001600 * iteratedDeriv 13 y t := by
  unfold taylorPolyOf taylorPoly
  rw [Polynomial.derivative_sum, Polynomial.eval_finset_sum]
  simp only [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul]
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one]
  ring

private lemma ab13_taylor_residual_sum_alg (Mb h : ℝ) :
    (∑ j : Fin 14,
        (|adamsBashforth13.α j| * (Mb / 87178291200 * (((j : ℕ) : ℝ) * h) ^ 14)
          + h * (|adamsBashforth13.β j| *
              (Mb / 6227020800 * (((j : ℕ) : ℝ) * h) ^ 13))))
      = (5616577262114645115720677 / 10602754543180800000 : ℝ) * Mb * h ^ 14 := by
  simp [adamsBashforth13, Fin.sum_univ_succ]
  norm_num
  ring

theorem ab13_pointwise_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 14 y) {a b Mb t h : ℝ}
    (hbnd : ∀ u ∈ Set.Icc a b, |iteratedDeriv 14 y u| ≤ Mb)
    (ht : t ∈ Set.Icc a b)
    (hth : t + h ∈ Set.Icc a b)
    (ht2h : t + 2 * h ∈ Set.Icc a b)
    (ht3h : t + 3 * h ∈ Set.Icc a b)
    (ht4h : t + 4 * h ∈ Set.Icc a b)
    (ht5h : t + 5 * h ∈ Set.Icc a b)
    (ht6h : t + 6 * h ∈ Set.Icc a b)
    (ht7h : t + 7 * h ∈ Set.Icc a b)
    (ht8h : t + 8 * h ∈ Set.Icc a b)
    (ht9h : t + 9 * h ∈ Set.Icc a b)
    (ht10h : t + 10 * h ∈ Set.Icc a b)
    (ht11h : t + 11 * h ∈ Set.Icc a b)
    (ht12h : t + 12 * h ∈ Set.Icc a b)
    (ht13h : t + 13 * h ∈ Set.Icc a b)
    (hh : 0 ≤ h) :
    |adamsBashforth13.localTruncationError h t y| ≤ (529729 : ℝ) * Mb * h ^ 14 := by
  have hmem : ∀ j : Fin 14, t + ((j : ℕ) : ℝ) * h ∈ Set.Icc a b := by
    intro j
    fin_cases j
    · simpa using ht
    · simpa [one_mul] using hth
    · simpa using ht2h
    · simpa using ht3h
    · simpa using ht4h
    · simpa using ht5h
    · simpa using ht6h
    · simpa using ht7h
    · simpa using ht8h
    · simpa using ht9h
    · simpa using ht10h
    · simpa using ht11h
    · simpa using ht12h
    · simpa using ht13h
  have hr_nn : ∀ j : Fin 14, 0 ≤ ((j : ℕ) : ℝ) * h := by
    intro j
    exact mul_nonneg (by exact_mod_cast Nat.zero_le (j : ℕ)) hh
  have hR : ∀ j : Fin 14,
      |y (t + ((j : ℕ) : ℝ) * h)
          - (taylorPolyOf y t 13).eval ((t + ((j : ℕ) : ℝ) * h) - t)|
        ≤ Mb / 87178291200 * (((j : ℕ) : ℝ) * h) ^ 14 := by
    intro j
    set r : ℝ := ((j : ℕ) : ℝ) * h with hr_def
    have hsub : t + r - t = r := by ring
    have hTaylor :=
      y_fourteenth_order_taylor_remainder hy hbnd ht
        (by simpa [hr_def] using hmem j)
        (by simpa [hr_def] using hr_nn j)
    have hleft : y (t + r) - (taylorPolyOf y t 13).eval ((t + r) - t)
        = y (t + r) - y t
          - r * deriv y t
          - r ^ 2 / 2 * iteratedDeriv 2 y t
          - r ^ 3 / 6 * iteratedDeriv 3 y t
          - r ^ 4 / 24 * iteratedDeriv 4 y t
          - r ^ 5 / 120 * iteratedDeriv 5 y t
          - r ^ 6 / 720 * iteratedDeriv 6 y t
          - r ^ 7 / 5040 * iteratedDeriv 7 y t
          - r ^ 8 / 40320 * iteratedDeriv 8 y t
          - r ^ 9 / 362880 * iteratedDeriv 9 y t
          - r ^ 10 / 3628800 * iteratedDeriv 10 y t
          - r ^ 11 / 39916800 * iteratedDeriv 11 y t
          - r ^ 12 / 479001600 * iteratedDeriv 12 y t
          - r ^ 13 / 6227020800 * iteratedDeriv 13 y t := by
      rw [hsub, taylorPolyOf_eval_thirteen]
      ring
    have hmain :
        |y (t + r) - (taylorPolyOf y t 13).eval ((t + r) - t)|
          ≤ Mb / 87178291200 * r ^ 14 := by
      rw [hleft]
      exact hTaylor
    simpa [hr_def] using hmain
  have hD : ∀ j : Fin 14,
      |deriv y (t + ((j : ℕ) : ℝ) * h)
          - (taylorPolyOf y t 13).derivative.eval ((t + ((j : ℕ) : ℝ) * h) - t)|
        ≤ Mb / 6227020800 * (((j : ℕ) : ℝ) * h) ^ 13 := by
    intro j
    set r : ℝ := ((j : ℕ) : ℝ) * h with hr_def
    have hsub : t + r - t = r := by ring
    have hTaylor :=
      derivY_thirteenth_order_taylor_remainder hy hbnd ht
        (by simpa [hr_def] using hmem j)
        (by simpa [hr_def] using hr_nn j)
    have hleft : deriv y (t + r)
          - (taylorPolyOf y t 13).derivative.eval ((t + r) - t)
        = deriv y (t + r) - deriv y t
          - r * iteratedDeriv 2 y t
          - r ^ 2 / 2 * iteratedDeriv 3 y t
          - r ^ 3 / 6 * iteratedDeriv 4 y t
          - r ^ 4 / 24 * iteratedDeriv 5 y t
          - r ^ 5 / 120 * iteratedDeriv 6 y t
          - r ^ 6 / 720 * iteratedDeriv 7 y t
          - r ^ 7 / 5040 * iteratedDeriv 8 y t
          - r ^ 8 / 40320 * iteratedDeriv 9 y t
          - r ^ 9 / 362880 * iteratedDeriv 10 y t
          - r ^ 10 / 3628800 * iteratedDeriv 11 y t
          - r ^ 11 / 39916800 * iteratedDeriv 12 y t
          - r ^ 12 / 479001600 * iteratedDeriv 13 y t := by
      rw [hsub, taylorPolyOf_derivative_eval_thirteen]
      ring
    have hmain :
        |deriv y (t + r)
            - (taylorPolyOf y t 13).derivative.eval ((t + r) - t)|
          ≤ Mb / 6227020800 * r ^ 13 := by
      rw [hleft]
      exact hTaylor
    simpa [hr_def] using hmain
  have hτeq : adamsBashforth13.localTruncationError h t y =
      ∑ j : Fin 14,
        (adamsBashforth13.α j *
            (y (t + ((j : ℕ) : ℝ) * h)
              - (taylorPolyOf y t 13).eval ((t + ((j : ℕ) : ℝ) * h) - t))
          - h * (adamsBashforth13.β j *
            (deriv y (t + ((j : ℕ) : ℝ) * h)
              - (taylorPolyOf y t 13).derivative.eval
                  ((t + ((j : ℕ) : ℝ) * h) - t)))) := by
    have hdecomp := adamsBashforth13.truncationOp_smooth_eq_taylor_residual 12 h t y
    dsimp only at hdecomp
    have hdecomp13 : adamsBashforth13.truncationOp h (fun u => y u) (fun u => deriv y u) t =
        adamsBashforth13.truncationOp h
          (fun u => (taylorPolyOf y t 13).eval (u - t))
          (fun u => (taylorPolyOf y t 13).derivative.eval (u - t)) t
        + ∑ j : Fin 14,
          (adamsBashforth13.α j *
              (y (t + ((j : ℕ) : ℝ) * h)
                - (taylorPolyOf y t 13).eval ((t + ((j : ℕ) : ℝ) * h) - t))
            - h * (adamsBashforth13.β j *
              (deriv y (t + ((j : ℕ) : ℝ) * h)
                - (taylorPolyOf y t 13).derivative.eval
                    ((t + ((j : ℕ) : ℝ) * h) - t)))) := by
      simpa [iteratedDeriv_zero, iteratedDeriv_one] using hdecomp
    have hpoly0 := adamsBashforth13.truncationOp_taylorPoly_eq_zero_of_HasOrder
      (p := 13) h t adamsBashforth13_order_thirteen (fun k u => iteratedDeriv k y u)
    have hpoly0' : adamsBashforth13.truncationOp h
        (fun u => (taylorPolyOf y t 13).eval (u - t))
        (fun u => (taylorPolyOf y t 13).derivative.eval (u - t)) t = 0 := by
      simpa [taylorPolyOf] using hpoly0
    unfold localTruncationError
    rw [show (fun u => iteratedDeriv 0 y u) = (fun u => y u) by
      funext u
      simp [iteratedDeriv_zero]]
    rw [show (fun u => iteratedDeriv 1 y u) = (fun u => deriv y u) by
      funext u
      simp [iteratedDeriv_one]]
    rw [hdecomp13, hpoly0']
    ring
  rw [hτeq]
  have hterm : ∀ j : Fin 14,
      |adamsBashforth13.α j *
            (y (t + ((j : ℕ) : ℝ) * h)
              - (taylorPolyOf y t 13).eval ((t + ((j : ℕ) : ℝ) * h) - t))
          - h * (adamsBashforth13.β j *
            (deriv y (t + ((j : ℕ) : ℝ) * h)
              - (taylorPolyOf y t 13).derivative.eval
                  ((t + ((j : ℕ) : ℝ) * h) - t)))|
        ≤ |adamsBashforth13.α j| *
            (Mb / 87178291200 * (((j : ℕ) : ℝ) * h) ^ 14)
          + h * (|adamsBashforth13.β j| *
            (Mb / 6227020800 * (((j : ℕ) : ℝ) * h) ^ 13)) := by
    intro j
    calc
      |adamsBashforth13.α j *
            (y (t + ((j : ℕ) : ℝ) * h)
              - (taylorPolyOf y t 13).eval ((t + ((j : ℕ) : ℝ) * h) - t))
          - h * (adamsBashforth13.β j *
            (deriv y (t + ((j : ℕ) : ℝ) * h)
              - (taylorPolyOf y t 13).derivative.eval
                  ((t + ((j : ℕ) : ℝ) * h) - t)))|
          ≤ |adamsBashforth13.α j *
              (y (t + ((j : ℕ) : ℝ) * h)
                - (taylorPolyOf y t 13).eval ((t + ((j : ℕ) : ℝ) * h) - t))|
            + |h * (adamsBashforth13.β j *
              (deriv y (t + ((j : ℕ) : ℝ) * h)
                - (taylorPolyOf y t 13).derivative.eval
                    ((t + ((j : ℕ) : ℝ) * h) - t)))| :=
            abs_sub _ _
      _ = |adamsBashforth13.α j| *
              |y (t + ((j : ℕ) : ℝ) * h)
                - (taylorPolyOf y t 13).eval ((t + ((j : ℕ) : ℝ) * h) - t)|
            + h * (|adamsBashforth13.β j| *
              |deriv y (t + ((j : ℕ) : ℝ) * h)
                - (taylorPolyOf y t 13).derivative.eval
                    ((t + ((j : ℕ) : ℝ) * h) - t)|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hh]
      _ ≤ |adamsBashforth13.α j| *
            (Mb / 87178291200 * (((j : ℕ) : ℝ) * h) ^ 14)
          + h * (|adamsBashforth13.β j| *
            (Mb / 6227020800 * (((j : ℕ) : ℝ) * h) ^ 13)) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left (hR j) (abs_nonneg _)
            · apply mul_le_mul_of_nonneg_left _ hh
              exact mul_le_mul_of_nonneg_left (hD j) (abs_nonneg _)
  have hsum_abs :
      |∑ j : Fin 14,
        (adamsBashforth13.α j *
            (y (t + ((j : ℕ) : ℝ) * h)
              - (taylorPolyOf y t 13).eval ((t + ((j : ℕ) : ℝ) * h) - t))
          - h * (adamsBashforth13.β j *
            (deriv y (t + ((j : ℕ) : ℝ) * h)
              - (taylorPolyOf y t 13).derivative.eval
                  ((t + ((j : ℕ) : ℝ) * h) - t))))|
        ≤ ∑ j : Fin 14,
          (|adamsBashforth13.α j| *
              (Mb / 87178291200 * (((j : ℕ) : ℝ) * h) ^ 14)
            + h * (|adamsBashforth13.β j| *
              (Mb / 6227020800 * (((j : ℕ) : ℝ) * h) ^ 13))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact Finset.sum_le_sum (fun j _ => hterm j)
  have hMbnn : 0 ≤ Mb := by
    have := hbnd t ht
    exact (abs_nonneg _).trans this
  have hMbh14_nn : 0 ≤ Mb * h ^ 14 := mul_nonneg hMbnn (by positivity)
  have hslack :
      (5616577262114645115720677 / 10602754543180800000 : ℝ) * Mb * h ^ 14
        ≤ 529729 * Mb * h ^ 14 := by
    rw [mul_assoc, mul_assoc (529729 : ℝ)]
    have hle :
        (5616577262114645115720677 / 10602754543180800000 : ℝ) ≤ 529729 := by
      norm_num
    exact mul_le_mul_of_nonneg_right hle hMbh14_nn
  have hsum_eq := ab13_taylor_residual_sum_alg Mb h
  linarith [hsum_abs, hsum_eq, hslack]

theorem ab13_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 14 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 13) * h ≤ T →
        |adamsBashforth13.localTruncationError h
            (t₀ + (n : ℝ) * h) y|
          ≤ C * h ^ 14 := by
  obtain ⟨M, hM_nn, hM⟩ :=
    iteratedDeriv_fourteen_bounded_on_Icc hy t₀ (t₀ + T + 1)
  refine ⟨(529729 : ℝ) * M, 1, by positivity, by norm_num, ?_⟩
  intro h hh _hh1 n hn
  set t : ℝ := t₀ + (n : ℝ) * h with ht_def
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have hnh_nn : 0 ≤ (n : ℝ) * h := mul_nonneg hn_nn hh.le
  have ht_mem : t ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hnh_le : (n : ℝ) * h ≤ T := by
      have h1 : (n : ℝ) * h ≤ ((n : ℝ) + 13) * h := by
        have hcoef : (n : ℝ) ≤ (n : ℝ) + 13 := by norm_num
        exact mul_le_mul_of_nonneg_right hcoef hh.le
      linarith
    linarith
  have hth_mem : t + h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hj_le : (n : ℝ) * h + 1 * h ≤ ((n : ℝ) + 13) * h := by
      nlinarith [hh.le]
    linarith
  have ht2h_mem : t + 2 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hj_le : (n : ℝ) * h + 2 * h ≤ ((n : ℝ) + 13) * h := by
      nlinarith [hh.le]
    linarith
  have ht3h_mem : t + 3 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hj_le : (n : ℝ) * h + 3 * h ≤ ((n : ℝ) + 13) * h := by
      nlinarith [hh.le]
    linarith
  have ht4h_mem : t + 4 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hj_le : (n : ℝ) * h + 4 * h ≤ ((n : ℝ) + 13) * h := by
      nlinarith [hh.le]
    linarith
  have ht5h_mem : t + 5 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hj_le : (n : ℝ) * h + 5 * h ≤ ((n : ℝ) + 13) * h := by
      nlinarith [hh.le]
    linarith
  have ht6h_mem : t + 6 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hj_le : (n : ℝ) * h + 6 * h ≤ ((n : ℝ) + 13) * h := by
      nlinarith [hh.le]
    linarith
  have ht7h_mem : t + 7 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hj_le : (n : ℝ) * h + 7 * h ≤ ((n : ℝ) + 13) * h := by
      nlinarith [hh.le]
    linarith
  have ht8h_mem : t + 8 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hj_le : (n : ℝ) * h + 8 * h ≤ ((n : ℝ) + 13) * h := by
      nlinarith [hh.le]
    linarith
  have ht9h_mem : t + 9 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hj_le : (n : ℝ) * h + 9 * h ≤ ((n : ℝ) + 13) * h := by
      nlinarith [hh.le]
    linarith
  have ht10h_mem : t + 10 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hj_le : (n : ℝ) * h + 10 * h ≤ ((n : ℝ) + 13) * h := by
      nlinarith [hh.le]
    linarith
  have ht11h_mem : t + 11 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hj_le : (n : ℝ) * h + 11 * h ≤ ((n : ℝ) + 13) * h := by
      nlinarith [hh.le]
    linarith
  have ht12h_mem : t + 12 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hj_le : (n : ℝ) * h + 12 * h ≤ ((n : ℝ) + 13) * h := by
      nlinarith [hh.le]
    linarith
  have ht13h_mem : t + 13 * h ∈ Set.Icc t₀ (t₀ + T + 1) := by
    refine ⟨by linarith, ?_⟩
    have hj_le : (n : ℝ) * h + 13 * h ≤ ((n : ℝ) + 13) * h := by
      nlinarith [hh.le]
    linarith
  exact ab13_pointwise_residual_bound hy hM ht_mem hth_mem ht2h_mem ht3h_mem ht4h_mem ht5h_mem ht6h_mem ht7h_mem ht8h_mem ht9h_mem ht10h_mem ht11h_mem ht12h_mem ht13h_mem hh.le

/-! ### Generic AB bridge and headline theorem -/

/-- Bridge: the AB13 scalar iteration is the generic AB iteration at `s = 13`. -/
lemma ab13Iter_eq_abIter
    (h : ℝ) (f : ℝ → ℝ → ℝ) (t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ : ℝ)
    (n : ℕ) :
    ab13Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ n
      = abIter 13 ab13GenericCoeff h f t₀
          ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂] n := by
  rfl

/-- Final AB13 global error bound on `[t₀, t₀ + T]`. -/
theorem ab13_global_error_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 14 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      ∀ {y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ ε₀ : ℝ}, 0 ≤ ε₀ →
      |y₀ - y t₀| ≤ ε₀ →
      |y₁ - y (t₀ + h)| ≤ ε₀ →
      |y₂ - y (t₀ + 2 * h)| ≤ ε₀ →
      |y₃ - y (t₀ + 3 * h)| ≤ ε₀ →
      |y₄ - y (t₀ + 4 * h)| ≤ ε₀ →
      |y₅ - y (t₀ + 5 * h)| ≤ ε₀ →
      |y₆ - y (t₀ + 6 * h)| ≤ ε₀ →
      |y₇ - y (t₀ + 7 * h)| ≤ ε₀ →
      |y₈ - y (t₀ + 8 * h)| ≤ ε₀ →
      |y₉ - y (t₀ + 9 * h)| ≤ ε₀ →
      |y₁₀ - y (t₀ + 10 * h)| ≤ ε₀ →
      |y₁₁ - y (t₀ + 11 * h)| ≤ ε₀ →
      |y₁₂ - y (t₀ + 12 * h)| ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 12) * h ≤ T →
      |ab13Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ N
          - y (t₀ + (N : ℝ) * h)|
        ≤ Real.exp ((1439788039057 / 638512875) * L * T) * ε₀ + K * h ^ 13 := by
  obtain ⟨C, δ, hC_nn, hδ_pos, hresidual⟩ :=
    ab13_local_residual_bound hy t₀ T hT
  refine ⟨T * Real.exp ((1439788039057 / 638512875) * L * T) * C, δ,
    ?_, hδ_pos, ?_⟩
  · exact mul_nonneg
      (mul_nonneg hT.le (Real.exp_nonneg _)) hC_nn
  intro h hh hδ_le y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ ε₀ hε₀
    he0_bd he1_bd he2_bd he3_bd he4_bd he5_bd he6_bd he7_bd he8_bd he9_bd
    he10_bd he11_bd he12_bd N hNh
  set α : Fin 13 → ℝ := ab13GenericCoeff with hα_def
  set y₀_non : Fin 13 → ℝ :=
    ![y₀, y₁, y₂, y₃, y₄, y₅, y₆, y₇, y₈, y₉, y₁₀, y₁₁, y₁₂]
    with hy_non_def
  have hs : (1 : ℕ) ≤ 13 := by norm_num
  haveI : Nonempty (Fin 13) := ⟨⟨0, hs⟩⟩
  have hstart : abErrWindow hs α h f t₀ y₀_non y 0 ≤ ε₀ := by
    unfold abErrWindow
    apply Finset.sup'_le
    intro j _
    unfold abErr
    fin_cases j <;> unfold abIter <;> simp [hy_non_def]
    · simpa using he0_bd
    · simpa using he1_bd
    · simpa using he2_bd
    · simpa using he3_bd
    · simpa using he4_bd
    · simpa using he5_bd
    · simpa using he6_bd
    · simpa using he7_bd
    · simpa using he8_bd
    · simpa using he9_bd
    · simpa using he10_bd
    · simpa using he11_bd
    · simpa using he12_bd
  have hres_gen : ∀ n : ℕ, n < N →
      |abResidual 13 α h y t₀ n| ≤ C * h ^ (13 + 1) := by
    intro n hn_lt
    have hcast : (n : ℝ) + 13 ≤ (N : ℝ) + 12 := by
      have : (n : ℝ) + 1 ≤ (N : ℝ) := by
        exact_mod_cast Nat.lt_iff_add_one_le.mp hn_lt
      linarith
    have hn13_le : ((n : ℝ) + 13) * h ≤ T := by
      have hmul : ((n : ℝ) + 13) * h ≤ ((N : ℝ) + 12) * h :=
        mul_le_mul_of_nonneg_right hcast hh.le
      linarith
    have hres := hresidual hh hδ_le n hn13_le
    rw [hα_def, ← ab13Residual_eq_abResidual h y t₀ n]
    have hpow : C * h ^ (13 + 1) = C * h ^ 14 := by norm_num
    rwa [hpow]
  have hNh' : (N : ℝ) * h ≤ T := by
    have hmono : (N : ℝ) * h ≤ ((N : ℝ) + 12) * h := by
      have h1 : (N : ℝ) ≤ (N : ℝ) + 12 := by linarith
      exact mul_le_mul_of_nonneg_right h1 hh.le
    linarith
  have hgeneric :=
    ab_global_error_bound_generic (p := 13) hs α hh.le hL hC_nn hf t₀
      y₀_non y hyf hε₀ hstart N hNh' hres_gen
  rw [show abLip 13 α L = (1439788039057 / 638512875) * L from by
    rw [hα_def]; exact abLip_ab13GenericCoeff L] at hgeneric
  have hwindow_ge : abErr 13 α h f t₀ y₀_non y N
      ≤ abErrWindow hs α h f t₀ y₀_non y N := by
    show abErr 13 α h f t₀ y₀_non y (N + ((⟨0, hs⟩ : Fin 13) : ℕ))
        ≤ abErrWindow hs α h f t₀ y₀_non y N
    unfold abErrWindow
    exact Finset.le_sup' (b := ⟨0, hs⟩)
      (f := fun j : Fin 13 => abErr 13 α h f t₀ y₀_non y (N + (j : ℕ)))
      (Finset.mem_univ _)
  have hbridge :
      abIter 13 α h f t₀ y₀_non N
        = ab13Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ N := by
    rw [hα_def, hy_non_def]
    rfl
  have habsErr :
      abErr 13 α h f t₀ y₀_non y N
        = |ab13Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ N
            - y (t₀ + (N : ℝ) * h)| := by
    show |abIter 13 α h f t₀ y₀_non N - y (t₀ + (N : ℝ) * h)|
        = |ab13Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ N
            - y (t₀ + (N : ℝ) * h)|
    rw [hbridge]
  show |ab13Iter h f t₀ y₀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ y₉ y₁₀ y₁₁ y₁₂ N
        - y (t₀ + (N : ℝ) * h)|
      ≤ Real.exp ((1439788039057 / 638512875) * L * T) * ε₀
        + T * Real.exp ((1439788039057 / 638512875) * L * T) * C * h ^ 13
  linarith [hwindow_ge, hgeneric, habsErr.symm.le, habsErr.le]

end LMM
