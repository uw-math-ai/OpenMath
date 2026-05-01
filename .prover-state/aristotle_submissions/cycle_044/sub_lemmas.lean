import Mathlib

/-!
# Cycle 044 — Aristotle submission for `thm:406C` sub-lemmas

Four targets: sub-lemma A (algebraic identity 406d), sub-lemma B
(`T_1` Lipschitz bound), sub-lemma C (`T_2` Lipschitz sum bound), and
the main theorem `globalError_recurrence_bound` (Butcher's per-term
bound, 406c-form before the `(1 − hL|β₀|)` inversion).

Sub-lemma D is a one-liner application of `lem:406B` and is closed
inline in the main file — not submitted here.

The structure / definitions below mirror
`OpenMath/Chapter4/Section404.lean` exactly, **including the
sign-corrected `IsLMMSolution` (cycle 044 fix: RHS negated to
`-h * Σ β · f`)**, so that explicit Euler `Y(m+1) = Y(m) + h f(Y(m))`
satisfies the recurrence.

Faithfulness (Butcher §400, equation (400b)):
`y_n = α_1 y_{n-1} + ⋯ + α_k y_{n-k} + h Σ_{i=0}^k β_i f(x_{n-i}, y_{n-i})`,
which rearranges to `y_n − Σ_{i=1}^k α_i y_{n-i} = h Σ β_i f`. With the
Lean normalisation `α_0 = -1` and `Σ_{i=0}^k M.α i Y_{n-i} = -h Σ M.β i f`
(the cycle-044 fix), peeling `i = 0` reproduces the textbook form.
-/

namespace OpenMath.Chapter4.Section404

structure LinearMultistepMethod (k : ℕ) where
  α : Fin (k + 1) → ℝ
  β : Fin (k + 1) → ℝ
  α_zero : α 0 = -1

def LinearMultistepMethod.IsPreconsistent {k : ℕ}
    (M : LinearMultistepMethod k) : Prop :=
  1 = ∑ i : Fin k, M.α i.succ

def LinearMultistepMethod.SatisfiesEq404b {k : ℕ}
    (M : LinearMultistepMethod k) : Prop :=
  (∑ i : Fin k, ((i : ℕ) + 1 : ℝ) * M.α i.succ) = ∑ i, M.β i

def LinearMultistepMethod.IsConsistent {k : ℕ}
    (M : LinearMultistepMethod k) : Prop :=
  M.IsPreconsistent ∧ M.SatisfiesEq404b

noncomputable def LinearMultistepMethod.localTruncationError {k : ℕ}
    (M : LinearMultistepMethod k) (y : ℝ → ℝ) (x h : ℝ) : ℝ :=
  y x
    - ∑ i : Fin k, M.α i.succ * y (x - ((i.val + 1 : ℕ) : ℝ) * h)
    - h * ∑ i : Fin (k + 1), M.β i * deriv y (x - ((i.val : ℕ) : ℝ) * h)

/-- Sign-corrected (cycle-044) IsLMMSolution: RHS is `-h * Σ β · f`. -/
def LinearMultistepMethod.IsLMMSolution {k : ℕ}
    (M : LinearMultistepMethod k) (h x₀ : ℝ) (f : ℝ → ℝ → ℝ)
    (Y : ℕ → ℝ) : Prop :=
  ∀ n : ℕ,
    (∑ i : Fin (k + 1), M.α i * Y (n + k - i.val)) =
      -h * ∑ i : Fin (k + 1), M.β i *
        f (x₀ + ((n + k - i.val : ℕ) : ℝ) * h) (Y (n + k - i.val))

def globalError (yex : ℝ → ℝ) (Y : ℕ → ℝ) (x₀ h : ℝ) (n : ℕ) : ℝ :=
  yex (x₀ + (n : ℝ) * h) - Y n

/-- **Sub-lemma A** — algebraic identity (406d). -/
theorem aristotle_globalError_decomposition {k : ℕ}
    (M : LinearMultistepMethod k)
    {f : ℝ → ℝ} {yex : ℝ → ℝ} {Y : ℕ → ℝ} {x₀ h : ℝ}
    (hyex_ode : ∀ t, deriv yex t = f (yex t))
    (hY : M.IsLMMSolution h x₀ (fun _ y => f y) Y)
    (n : ℕ) (hn : k ≤ n) :
    globalError yex Y x₀ h n
      - ∑ i : Fin k, M.α i.succ * globalError yex Y x₀ h (n - (i.val + 1))
      = h * M.β 0 * (f (yex (x₀ + (n : ℝ) * h)) - f (Y n))
        + h * (∑ i : Fin k, M.β i.succ
                * (f (yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h))
                   - f (Y (n - (i.val + 1)))))
        + M.localTruncationError yex (x₀ + (n : ℝ) * h) h := by
  sorry

/-- **Sub-lemma B** — bound on `T_1`. -/
theorem aristotle_T1_bound
    {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf_lip : LipschitzWith L.toNNReal f)
    {β₀ : ℝ} (h : ℝ) (hh : 0 ≤ h) (a b : ℝ) :
    |h * β₀ * (f a - f b)| ≤ h * L * |β₀| * |a - b| := by
  sorry

/-- **Sub-lemma C** — bound on `T_2`. -/
theorem aristotle_T2_bound {k : ℕ} (M : LinearMultistepMethod k)
    {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf_lip : LipschitzWith L.toNNReal f)
    (h : ℝ) (hh : 0 ≤ h)
    (a : Fin k → ℝ) (b : Fin k → ℝ) (Mmax : ℝ)
    (hMmax : ∀ i : Fin k, |a i - b i| ≤ Mmax) (hMmax0 : 0 ≤ Mmax) :
    |h * ∑ i : Fin k, M.β i.succ * (f (a i) - f (b i))|
      ≤ h * L * (∑ i : Fin k, |M.β i.succ|) * Mmax := by
  sorry

/-- The `lem:406B` LTE bound. (For Aristotle to use as a black box
when proving the main theorem; the actual proof lives in the project
file.) -/
theorem localTruncationError_bound {k : ℕ}
    (M : LinearMultistepMethod k) (hcons : M.IsConsistent)
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ M_bound)
    (x h : ℝ) (hh : 0 ≤ h) :
    |M.localTruncationError y x h|
      ≤ ((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
          + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
        * L * M_bound * h^2 := by
  sorry

/-- **Main theorem** — `globalError_recurrence_bound` (`thm:406C`,
partial form before the `(1 − hL|β₀|)` inversion). -/
theorem aristotle_globalError_recurrence_bound
    {k : ℕ} (M : LinearMultistepMethod k) (hcons : M.IsConsistent)
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {yex : ℝ → ℝ}
    (hyex_C1 : ContDiff ℝ 1 yex)
    (hyex_ode : ∀ t, deriv yex t = f (yex t))
    (hf_yex_bound : ∀ t, |f (yex t)| ≤ M_bound)
    {Y : ℕ → ℝ} {x₀ h : ℝ}
    (hh : 0 ≤ h)
    (hY : M.IsLMMSolution h x₀ (fun _ y => f y) Y)
    (n : ℕ) (hn : k ≤ n)
    (Mmax : ℝ) (hMmax0 : 0 ≤ Mmax)
    (hMmax : ∀ i : Fin k,
              |yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
                - Y (n - (i.val + 1))| ≤ Mmax) :
    |yex (x₀ + (n : ℝ) * h) - Y n
        - ∑ i : Fin k, M.α i.succ
            * (yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
                - Y (n - (i.val + 1)))|
      ≤ h * L * |M.β 0| * |yex (x₀ + (n : ℝ) * h) - Y n|
        + h * L * (∑ i : Fin k, |M.β i.succ|) * Mmax
        + ((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
            + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
          * L * M_bound * h^2 := by
  sorry

end OpenMath.Chapter4.Section404
