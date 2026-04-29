import Mathlib

/-!
# Cycle 039 — Aristotle witness submission for `def:406A`

We define `LinearMultistepMethod`, `IsPreconsistent`, `SatisfiesEq404b`,
`IsConsistent`, and `localTruncationError` from Butcher §404 / §406.
The witnesses to be proven are at the bottom (the two `sorry`s).
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

/-- A constant function has vanishing local truncation error for any
preconsistent linear multistep method. -/
theorem aristotle_localTruncationError_const {k : ℕ}
    (M : LinearMultistepMethod k) (hpre : M.IsPreconsistent) (c x h : ℝ) :
    M.localTruncationError (fun _ => c) x h = 0 := by
  sorry

/-- A linear function has vanishing local truncation error for any
consistent linear multistep method. -/
theorem aristotle_localTruncationError_linear {k : ℕ}
    (M : LinearMultistepMethod k) (hcons : M.IsConsistent) (a b x h : ℝ) :
    M.localTruncationError (fun t => a * t + b) x h = 0 := by
  sorry

end OpenMath.Chapter4.Section404
