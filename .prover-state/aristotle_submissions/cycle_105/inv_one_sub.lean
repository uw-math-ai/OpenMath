import Mathlib

/-! Cycle 105 — Aristotle batch for inverse-positivity of `(I − M)`.

Goal: prove that if a real square matrix `M` is entrywise non-negative
and `‖M‖ < 1` (operator norm), then `(I − M)` is invertible and its
inverse is also entrywise non-negative.

Mathematical justification: the Neumann series

  `(I − M)⁻¹ = ∑_{k=0}^∞ M^k`

converges absolutely whenever `‖M‖ < 1`, and each `M^k` is entrywise
non-negative (since `M ≥ 0` is preserved under matrix multiplication).
The pointwise limit of non-negative reals is non-negative, hence the
inverse is entrywise non-negative.

Mathlib infrastructure that should be relevant:

* `Mathlib.Analysis.Normed.Ring.Units` — `Units.oneSub`,
  `tsum_geometric_of_norm_lt_one`, `NormedRing.inverse_one_sub`.
* `Mathlib.Analysis.Specific.Limits.Normed` — `tsum_geometric_lt_one`.
* `Mathlib.Analysis.Matrix.Normed` — operator norm on matrices.
-/

open Matrix
open scoped BigOperators

namespace Matrix

/-- A matrix is **entrywise non-negative** if every entry satisfies
`0 ≤ M i j`. -/
def EntrywiseNonneg' {m n : Type*} (M : Matrix m n ℝ) : Prop :=
  ∀ i j, 0 ≤ M i j

/-- **Inverse positivity** for `(1 − M)` when `M` is entrywise
non-negative and has operator norm `< 1`.

This is the load-bearing lemma for `aux_515B_eta_contraction` in
Butcher §515. The textbook proof (Butcher 2008, p. 414) takes this for
granted; we prove it via the Neumann series. -/
lemma EntrywiseNonneg'.inv_one_sub_of_norm_lt_one
    {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℝ}
    (hM_nonneg : EntrywiseNonneg' M)
    (hM_norm : ‖M‖ < 1) :
    EntrywiseNonneg' ((1 : Matrix n n ℝ) - M)⁻¹ := by
  sorry

/-- Auxiliary: matrix powers preserve entrywise non-negativity. -/
lemma EntrywiseNonneg'.pow {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℝ} (hM : EntrywiseNonneg' M) (k : ℕ) :
    EntrywiseNonneg' (M ^ k) := by
  induction k with
  | zero =>
      intro i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
  | succ k ih =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg (fun l _ => mul_nonneg (ih i l) (hM l j))

/-- Auxiliary: a tsum of entrywise non-negative matrices is entrywise
non-negative (provided the sum is summable). -/
lemma EntrywiseNonneg'.tsum_pow_of_norm_lt_one
    {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℝ} (hM_nonneg : EntrywiseNonneg' M)
    (hM_norm : ‖M‖ < 1) :
    EntrywiseNonneg' (∑' k : ℕ, M ^ k) := by
  sorry

end Matrix
