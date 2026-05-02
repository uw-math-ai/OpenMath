import Mathlib

open scoped Topology

/-! # Cycle 071 — running-max + homogeneous-rescaling helpers for `thm:405A`

This file is a standalone Aristotle submission for the four sub-lemmas
needed to close Butcher's `thm:405A` (`convergent_isStable`).  All four
are pure infrastructure:

1. `runningMaxAbs_atTop_of_unbounded`: if `|y n|` is unbounded, then the
   running-max sequence `ζ n = max_{i ≤ n} |y i|` tends to `∞`.
2. `runningMaxAbs_record_above`: arbitrarily-large record indices exist
   when `y` is unbounded.
3. `IsHomogeneousSolution.const_smul` (via abstract recurrence
   skeleton `HomRec`): the homogeneous-recurrence predicate is closed
   under scalar multiplication.
4. `unbounded_homogeneous_contra`: from `ζ → ∞`, record indices, and
   `Tendsto (η m / ζ m) atTop (𝓝 0)`, derive `False`.

The first three are minor; the fourth packages the textbook contradiction.

`runningMaxAbs` is defined locally so this file is standalone (the
project version will live in `OpenMath/Chapter4/Section404.lean`).
-/

namespace AristotleCycle071

/-- Running maximum of `|y i|` over `i ≤ n`. -/
def runningMaxAbs (y : ℕ → ℝ) : ℕ → ℝ
  | 0     => |y 0|
  | n + 1 => max (runningMaxAbs y n) |y (n + 1)|

theorem runningMaxAbs_monotone (y : ℕ → ℝ) :
    Monotone (runningMaxAbs y) := by
  apply monotone_nat_of_le_succ
  intro n
  show runningMaxAbs y n ≤ runningMaxAbs y (n + 1)
  unfold runningMaxAbs
  exact le_max_left _ _

theorem runningMaxAbs_ge_abs (y : ℕ → ℝ) (n : ℕ) :
    |y n| ≤ runningMaxAbs y n := by
  cases n with
  | zero => exact le_refl _
  | succ n =>
      show |y (n + 1)| ≤ max (runningMaxAbs y n) |y (n + 1)|
      exact le_max_right _ _

/-- Sub-lemma 1: if `|y n|` is unbounded above, then `ζ` tends to `∞`. -/
theorem runningMaxAbs_atTop_of_unbounded
    {y : ℕ → ℝ} (hy : ∀ C : ℝ, ∃ n, C < |y n|) :
    Filter.Tendsto (runningMaxAbs y) Filter.atTop Filter.atTop := by
  sorry

/-- Sub-lemma 2: arbitrarily-large record indices exist. A "record" at `n`
means `|y n| = ζ n`. -/
theorem runningMaxAbs_record_above
    {y : ℕ → ℝ} (hy : ∀ C : ℝ, ∃ n, C < |y n|) (N : ℕ) :
    ∃ n, N ≤ n ∧ |y n| = runningMaxAbs y n := by
  sorry

/-- Sub-lemma 3 (abstract recurrence skeleton): if `y : ℕ → ℝ` satisfies
the homogeneous recurrence `y (m + k) = ∑ j : Fin k, α j * y (m + k - (j.val + 1))`
for every `m`, then so does `c • y`. -/
theorem hom_recurrence_const_smul
    {k : ℕ} {α : Fin (k + 1) → ℝ} {y : ℕ → ℝ}
    (hy : ∀ m : ℕ, y (m + k) =
        ∑ j : Fin k, α j.succ * y (m + k - (j.val + 1)))
    (c : ℝ) :
    ∀ m : ℕ, (c * y (m + k)) =
      ∑ j : Fin k, α j.succ * (c * y (m + k - (j.val + 1))) := by
  sorry

/-- Sub-lemma 4: the textbook contradiction.  Given a sequence `η` with
the running-max `ζ` going to ∞ and infinitely-many record indices, the
ratio `η m / ζ m` cannot tend to `0`. -/
theorem unbounded_homogeneous_contra
    {η ζ : ℕ → ℝ}
    (hζ_monotone : Monotone ζ)
    (hζ_ge : ∀ n, |η n| ≤ ζ n)
    (hζ_atTop : Filter.Tendsto ζ Filter.atTop Filter.atTop)
    (hrecord : ∀ N, ∃ n, N ≤ n ∧ |η n| = ζ n)
    (htendsto : Filter.Tendsto (fun m => η m / ζ m) Filter.atTop (nhds 0)) :
    False := by
  sorry

end AristotleCycle071
