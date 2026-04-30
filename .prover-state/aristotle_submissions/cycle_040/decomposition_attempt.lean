import Mathlib

/-! Local manual attempt at proving sub-lemma E (algebraic decomposition)
self-contained for testing. -/

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

theorem decomp_test {k : ℕ}
    (M : LinearMultistepMethod k) (hcons : M.IsConsistent)
    (y : ℝ → ℝ) (x h : ℝ) :
    M.localTruncationError y x h
      = (∑ i : Fin k, M.α i.succ
          * (y x - y (x - ((i.val + 1 : ℕ) : ℝ) * h)
             - ((i.val + 1 : ℕ) : ℝ) * h * deriv y x))
        + h * ∑ i : Fin k, M.β i.succ
              * (deriv y x - deriv y (x - ((i.val + 1 : ℕ) : ℝ) * h)) := by
  obtain ⟨hpre, h404b⟩ := hcons
  have h404b' : (∑ i : Fin k, (((i.val + 1 : ℕ) : ℝ)) * M.α i.succ)
      = ∑ i : Fin (k + 1), M.β i := by
    unfold LinearMultistepMethod.SatisfiesEq404b at h404b
    convert h404b using 1
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  -- LHS: peel β-sum at i=0
  have hLHS :
      M.localTruncationError y x h
        = y x - (∑ i : Fin k, M.α i.succ * y (x - ((i.val + 1 : ℕ) : ℝ) * h))
          - h * M.β 0 * deriv y x
          - h * (∑ i : Fin k, M.β i.succ
                  * deriv y (x - ((i.val + 1 : ℕ) : ℝ) * h)) := by
    unfold LinearMultistepMethod.localTruncationError
    rw [Fin.sum_univ_succ
        (f := fun i : Fin (k + 1) => M.β i * deriv y (x - ((i.val : ℕ) : ℝ) * h))]
    simp only [Fin.val_zero, Nat.cast_zero, zero_mul, sub_zero, Fin.val_succ]
    ring
  -- RHS α-piece: distribute and use preconsistency
  have hα_dist :
      (∑ i : Fin k, M.α i.succ
          * (y x - y (x - ((i.val + 1 : ℕ) : ℝ) * h)
             - ((i.val + 1 : ℕ) : ℝ) * h * deriv y x))
        = y x - (∑ i : Fin k, M.α i.succ * y (x - ((i.val + 1 : ℕ) : ℝ) * h))
          - h * deriv y x
              * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ) := by
    have heach : ∀ i : Fin k,
        M.α i.succ
          * (y x - y (x - ((i.val + 1 : ℕ) : ℝ) * h)
             - ((i.val + 1 : ℕ) : ℝ) * h * deriv y x)
        = M.α i.succ * y x
          - M.α i.succ * y (x - ((i.val + 1 : ℕ) : ℝ) * h)
          - h * deriv y x * (((i.val + 1 : ℕ) : ℝ) * M.α i.succ) := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => heach i)]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    rw [show (∑ i : Fin k, M.α i.succ * y x)
            = (∑ i : Fin k, M.α i.succ) * y x from by rw [← Finset.sum_mul]]
    rw [show (∑ i : Fin k, h * deriv y x * (((i.val + 1 : ℕ) : ℝ) * M.α i.succ))
            = h * deriv y x
                * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ) from by
        rw [← Finset.mul_sum]]
    rw [← hpre]
    ring
  have hβ_dist :
      (∑ i : Fin k, M.β i.succ
          * (deriv y x - deriv y (x - ((i.val + 1 : ℕ) : ℝ) * h)))
        = (∑ i : Fin k, M.β i.succ) * deriv y x
          - (∑ i : Fin k, M.β i.succ
                  * deriv y (x - ((i.val + 1 : ℕ) : ℝ) * h)) := by
    have heach : ∀ i : Fin k,
        M.β i.succ
          * (deriv y x - deriv y (x - ((i.val + 1 : ℕ) : ℝ) * h))
        = M.β i.succ * deriv y x
          - M.β i.succ * deriv y (x - ((i.val + 1 : ℕ) : ℝ) * h) := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => heach i)]
    rw [Finset.sum_sub_distrib]
    rw [show (∑ i : Fin k, M.β i.succ * deriv y x)
            = (∑ i : Fin k, M.β i.succ) * deriv y x from by rw [← Finset.sum_mul]]
  rw [hLHS, hα_dist, hβ_dist, h404b']
  rw [Fin.sum_univ_succ (f := M.β)]
  simp only [Fin.val_succ]
  ring

end OpenMath.Chapter4.Section404
