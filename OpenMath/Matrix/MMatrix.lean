import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Instances.Matrix

/-!
# M-matrix infrastructure (helper file)

Helper lemmas for entrywise non-negativity of matrices, used by Butcher
§515 (and likely §530+ stability work). This file is **not** itself a
Butcher entity — it is helper infrastructure for the deferred lemma
`aux_515B_eta_contraction` (see
`.prover-state/issues/lem_515B_eta_contraction_deferred.md`).

## Scope of this cycle (105)

* Predicate `Matrix.EntrywiseNonneg`.
* Closure lemmas: addition, scalar multiplication by a non-negative
  scalar, matrix product, matrix-vector product on non-negative
  vectors, and natural-number powers.
* Concrete witnesses: zero matrix, identity matrix.

## Out of scope (deferred to cycle 106)

* Inverse positivity for `(I − M)⁻¹` when `M ≥ 0` and `‖M‖ < 1`
  (Neumann series argument).
* The actual application to `aux_515B_eta_contraction`.

## Definitional convention

`EntrywiseNonneg M` here means **componentwise** non-negativity
(`∀ i j, 0 ≤ M i j`). This is **distinct** from `Matrix.PosSemidef`
(which is spectral non-negativity via `xᵀ M x ≥ 0`). The η-contraction
proof in §515 needs the entrywise notion, not the spectral one.
-/

namespace Matrix

variable {m n p : Type*} {α : Type*}

/-- A matrix is **entrywise non-negative** if every entry satisfies
`0 ≤ M i j`. This is the componentwise order, not the Loewner /
positive-semidefinite order. -/
def EntrywiseNonneg [Zero α] [LE α] (M : Matrix m n α) : Prop :=
  ∀ i j, 0 ≤ M i j

section Zero

variable [Zero α] [Preorder α]

@[simp] lemma entrywiseNonneg_zero : (0 : Matrix m n α).EntrywiseNonneg :=
  fun _ _ => le_refl 0

end Zero

section AddCommMonoid

variable [AddCommMonoid α] [PartialOrder α] [CovariantClass α α (· + ·) (· ≤ ·)]

lemma EntrywiseNonneg.add {M N : Matrix m n α}
    (hM : M.EntrywiseNonneg) (hN : N.EntrywiseNonneg) :
    (M + N).EntrywiseNonneg := by
  intro i j
  simp only [Matrix.add_apply]
  exact add_nonneg (hM i j) (hN i j)

end AddCommMonoid

section OrderedSemiring

variable [Semiring α] [PartialOrder α] [IsOrderedRing α]

/-- The identity matrix is entrywise non-negative. -/
@[simp] lemma entrywiseNonneg_one [DecidableEq n] :
    (1 : Matrix n n α).EntrywiseNonneg := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs with h
  · exact zero_le_one
  · exact le_refl 0

/-- Scaling an entrywise-nonneg matrix by a non-negative scalar
preserves entrywise non-negativity. -/
lemma EntrywiseNonneg.smul {M : Matrix m n α} (hM : M.EntrywiseNonneg)
    {c : α} (hc : 0 ≤ c) : (c • M).EntrywiseNonneg := by
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg hc (hM i j)

/-- Matrix product of two entrywise-nonneg matrices is entrywise nonneg. -/
lemma EntrywiseNonneg.mul [Fintype n] {M : Matrix m n α} {N : Matrix n p α}
    (hM : M.EntrywiseNonneg) (hN : N.EntrywiseNonneg) :
    (M * N).EntrywiseNonneg := by
  intro i k
  rw [Matrix.mul_apply]
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hM i j) (hN j k))

/-- An entrywise-nonneg matrix sends non-negative vectors to non-negative
vectors under `mulVec`. -/
lemma EntrywiseNonneg.mulVec_nonneg [Fintype n] {M : Matrix m n α}
    (hM : M.EntrywiseNonneg) {v : n → α} (hv : ∀ j, 0 ≤ v j) :
    ∀ i, 0 ≤ (M *ᵥ v) i := by
  intro i
  rw [Matrix.mulVec, dotProduct]
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hM i j) (hv j))

/-- Natural-number powers preserve entrywise non-negativity. -/
lemma EntrywiseNonneg.pow [Fintype n] [DecidableEq n]
    {M : Matrix n n α} (hM : M.EntrywiseNonneg) :
    ∀ k : ℕ, (M ^ k).EntrywiseNonneg
  | 0 => by
      simp only [pow_zero]
      exact entrywiseNonneg_one
  | k + 1 => by
      rw [pow_succ]
      exact (EntrywiseNonneg.pow hM k).mul hM

/-- An entrywise-nonneg matrix is **monotone** as a linear operator on
componentwise-ordered vectors: `v ≤ w` (componentwise) implies
`M *ᵥ v ≤ M *ᵥ w` (componentwise).

This is the key lemma for monotone-bound propagation in the η-contraction
proof of `aux_515B_eta_contraction`. -/
lemma EntrywiseNonneg.mulVec_mono [Fintype n] {M : Matrix m n α}
    (hM : M.EntrywiseNonneg) {v w : n → α} (hvw : ∀ j, v j ≤ w j) :
    ∀ i, (M *ᵥ v) i ≤ (M *ᵥ w) i := by
  intro i
  rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct]
  exact Finset.sum_le_sum (fun j _ =>
    mul_le_mul_of_nonneg_left (hvw j) (hM i j))

/-- A finite sum of entrywise-nonneg matrices is entrywise nonneg. -/
lemma EntrywiseNonneg.sum {ι : Type*} (s : Finset ι) {f : ι → Matrix m n α}
    (hf : ∀ i ∈ s, (f i).EntrywiseNonneg) :
    (∑ i ∈ s, f i).EntrywiseNonneg := by
  intro i j
  rw [Finset.sum_apply, Finset.sum_apply]
  exact Finset.sum_nonneg (fun k hk => hf k hk i j)

end OrderedSemiring

section Witnesses

/-- Concrete witness: the 2×2 zero matrix is entrywise non-negative. -/
example : (0 : Matrix (Fin 2) (Fin 2) ℝ).EntrywiseNonneg :=
  entrywiseNonneg_zero

/-- Concrete witness: the 2×2 identity matrix is entrywise non-negative. -/
example : (1 : Matrix (Fin 2) (Fin 2) ℝ).EntrywiseNonneg :=
  entrywiseNonneg_one

/-- Concrete witness: a specific 2×2 stochastic-style matrix. -/
example : EntrywiseNonneg (!![(1/2 : ℝ), 1/2; 1/3, 2/3]) := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.cons_val_fin_one,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

end Witnesses

section InversePositivity

/-!
### Inverse positivity (Neumann series)

For an entrywise-nonneg matrix `M` over `ℝ` with operator norm `‖M‖ < 1`
(Frobenius norm here, scoped via `Matrix.Norms.Frobenius`), the inverse
`Ring.inverse (1 - M)` is entrywise non-negative. The proof goes via the
Neumann series `(1 - M)⁻¹ = ∑' k, M^k` (Mathlib's
`hasSum_geom_series_inverse`), then extracts entrywise convergence via
`Pi.hasSum` (twice, since `Matrix n n ℝ = n → n → ℝ` definitionally).

The Frobenius norm scope is opened locally so this section does not
pollute global instance resolution. Downstream consumers must open the
same scope.
-/

open scoped Matrix.Norms.Frobenius

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Inverse positivity (Neumann series)**: for an entrywise-nonneg
matrix `M` over `ℝ` with `‖M‖ < 1` (Frobenius norm), the inverse
`Ring.inverse (1 - M)` is entrywise non-negative.

This is the load-bearing M-matrix-flavored lemma used by Butcher §515's
`aux_515B_eta_contraction` (η-contraction step in the local-step error
bound). The proof realizes `(1 - M)⁻¹` as the Neumann series
`∑' k, M^k`, which converges in the normed-ring topology, and each
partial sum `M^k` is entrywise non-negative by
`EntrywiseNonneg.pow`. -/
lemma EntrywiseNonneg.inv_one_sub_of_norm_lt_one
    {M : Matrix n n ℝ} (hM : M.EntrywiseNonneg) (h_norm : ‖M‖ < 1) :
    (Ring.inverse ((1 : Matrix n n ℝ) - M)).EntrywiseNonneg := by
  intro i j
  have h_sum : HasSum (fun k => M ^ k) (Ring.inverse (1 - M)) :=
    hasSum_geom_series_inverse M h_norm
  have h_row : HasSum (fun k => (M ^ k) i) ((Ring.inverse (1 - M)) i) :=
    Pi.hasSum.mp h_sum i
  have h_entry : HasSum (fun k => (M ^ k) i j)
      ((Ring.inverse (1 - M)) i j) := Pi.hasSum.mp h_row j
  exact h_entry.nonneg (fun k => hM.pow k i j)

/-- **M-matrix comparison principle**: if `M ≥ 0` entrywise with
`‖M‖ < 1` and `(1 - M) *ᵥ v ≥ 0` componentwise, then `v ≥ 0`
componentwise.

The proof writes `v = (1 - M)⁻¹ *ᵥ ((1 - M) *ᵥ v)` (using
`Ring.inverse_mul_cancel` from `IsUnit (1 - M)`, available because
`‖M‖ < 1`), then applies the inverse-positivity lemma above together
with `EntrywiseNonneg.mulVec_nonneg`. -/
lemma EntrywiseNonneg.nonneg_of_one_sub_mulVec_nonneg
    {M : Matrix n n ℝ} (hM : M.EntrywiseNonneg) (h_norm : ‖M‖ < 1)
    {v : n → ℝ} (h : ∀ i, 0 ≤ ((1 - M) *ᵥ v) i) :
    ∀ i, 0 ≤ v i := by
  have h_unit : IsUnit ((1 : Matrix n n ℝ) - M) :=
    isUnit_one_sub_of_norm_lt_one h_norm
  have h_inv_mul : Ring.inverse ((1 : Matrix n n ℝ) - M) * (1 - M) = 1 :=
    Ring.inverse_mul_cancel _ h_unit
  have h_inv_pos : (Ring.inverse ((1 : Matrix n n ℝ) - M)).EntrywiseNonneg :=
    hM.inv_one_sub_of_norm_lt_one h_norm
  have h_apply : ∀ i, v i =
      ((Ring.inverse ((1 : Matrix n n ℝ) - M)) *ᵥ ((1 - M) *ᵥ v)) i := by
    intro i
    rw [Matrix.mulVec_mulVec, h_inv_mul, Matrix.one_mulVec]
  intro i
  rw [h_apply i]
  exact h_inv_pos.mulVec_nonneg h i

end InversePositivity

end Matrix
