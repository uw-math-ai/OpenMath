import Mathlib

/-!
# Cycle 040 — Aristotle submission for `lem:406B` sub-lemmas

Self-contained Lean file mirroring the relevant `def:404` / `def:406A`
infrastructure from `OpenMath/Chapter4/Section404.lean`. We submit five
sub-lemmas (A–E) as `aristotle_*` theorems with their full hypotheses;
each is needed for the main theorem `localTruncationError_bound`
(`lem:406B`, the algebraically-corrected form using `β_i` instead of
`iα_i − β_i`; see the issue file
`.prover-state/issues/lem_406B_textbook_check.md`).

Sub-lemma A: pointwise norm bound on `y(x + h*ξ) − y x` for ξ ≤ 0.
Sub-lemma B: integral form of the residual `y(x) − y(x − ih) − ih y'(x)`.
Sub-lemma C: bound `|residual| ≤ (1/2) i² h² L M`.
Sub-lemma D: Lipschitz bound `|y'(x) − y'(x − ih)| ≤ ihLM`.
Sub-lemma E: algebraic decomposition of `localTruncationError` under
  consistency.
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

/-- Sub-lemma A — pointwise bound on `|y(x + h*ξ) − y x|` for ξ ≤ 0
under the IVP hypotheses `y' = f∘y` and `‖f∘y‖ ≤ M_bound`. -/
theorem aristotle_exact_solution_norm_bound
    {f : ℝ → ℝ} {M_bound : ℝ} (hM : 0 ≤ M_bound)
    {y : ℝ → ℝ}
    (hy_diff : Differentiable ℝ y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ M_bound)
    (x h : ℝ) (hh : 0 ≤ h)
    (ξ : ℝ) (hξ : ξ ≤ 0) :
    |y (x + h * ξ) - y x| ≤ h * (-ξ) * M_bound := by
  sorry

/-- Sub-lemma B — integral form for the residual
`y(x) − y(x − i*h) − i*h*y'(x)`. -/
theorem aristotle_residual_integral_form
    {f : ℝ → ℝ} {y : ℝ → ℝ}
    (hy_diff : Differentiable ℝ y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (i : ℕ) (x h : ℝ) (hh : 0 ≤ h) :
    y x - y (x - (i : ℝ) * h) - ((i : ℝ) * h) * deriv y x
      = h * ∫ ξ in (-(i : ℝ))..0, (f (y (x + h*ξ)) - f (y x)) := by
  sorry

/-- Sub-lemma C — bound on `|y(x) − y(x − i*h) − i*h*y'(x)|`. -/
theorem aristotle_residual_bound
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y : ℝ → ℝ}
    (hy_diff : Differentiable ℝ y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ M_bound)
    (i : ℕ) (x h : ℝ) (hh : 0 ≤ h) :
    |y x - y (x - (i : ℝ) * h) - ((i : ℝ) * h) * deriv y x|
      ≤ (1/2) * (i : ℝ)^2 * h^2 * L * M_bound := by
  sorry

/-- Sub-lemma D — Lipschitz bound on `|y'(x) − y'(x − i*h)|`. -/
theorem aristotle_deriv_diff_bound
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y : ℝ → ℝ}
    (hy_diff : Differentiable ℝ y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ M_bound)
    (i : ℕ) (x h : ℝ) (hh : 0 ≤ h) :
    |deriv y x - deriv y (x - (i : ℝ) * h)|
      ≤ (i : ℝ) * h * L * M_bound := by
  sorry

/-- Sub-lemma E — algebraic decomposition of `localTruncationError`
under consistency. (Algebraically corrected form using `β_i` instead
of the textbook's `iα_i − β_i`.) -/
theorem aristotle_localTruncationError_decomposition {k : ℕ}
    (M : LinearMultistepMethod k) (hcons : M.IsConsistent)
    (y : ℝ → ℝ) (x h : ℝ) :
    M.localTruncationError y x h
      = (∑ i : Fin k, M.α i.succ
          * (y x - y (x - ((i.val + 1 : ℕ) : ℝ) * h)
             - ((i.val + 1 : ℕ) : ℝ) * h * deriv y x))
        + h * ∑ i : Fin k, M.β i.succ
              * (deriv y x - deriv y (x - ((i.val + 1 : ℕ) : ℝ) * h)) := by
  sorry

end OpenMath.Chapter4.Section404
