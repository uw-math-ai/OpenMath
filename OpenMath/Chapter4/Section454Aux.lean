import Mathlib

/-!
# Butcher §454 — PSD/PD complex-lift helpers (Section454Aux)

Two helper lemmas for cycle 168's proof of Theorem 454A:

* `complexLift_re_dotProduct_nonneg_of_real_posSemidef`: a real PSD
  matrix lifted to ℂ via `algebraMap ℝ ℂ` has a non-negative real
  Hermitian quadratic form (with imaginary part zero).
* `complexLift_re_dotProduct_pos_of_real_posDef`: the strict
  version — a real PD matrix has strictly positive real
  Hermitian quadratic form on non-zero complex vectors.

## Proof sketch (for the prover):

For a complex vector `W : Fin n → ℂ`, decompose
`W i = (W i).re + (W i).im · I`. Set
`a i := (W i).re`, `b i := (W i).im`. Then over a real symmetric
matrix `A`,

  `star W ⬝ᵥ (A.map ι *ᵥ W) = (a ⬝ᵥ A *ᵥ a + b ⬝ᵥ A *ᵥ b : ℝ)`
                            + i · (b ⬝ᵥ A *ᵥ a - a ⬝ᵥ A *ᵥ b),

and `b ⬝ᵥ A *ᵥ a = a ⬝ᵥ A *ᵥ b` by symmetry of `A` (i.e.
`Aᵀ = A`), so the imaginary part vanishes. The real part is
`a ⬝ᵥ A *ᵥ a + b ⬝ᵥ A *ᵥ b ≥ 0` by `A.PosSemidef`.

For the strict version: `W ≠ 0` ⇒ `a ≠ 0 ∨ b ≠ 0`; take whichever
is nonzero, gets strict positivity from `A.PosDef`, and the other
gives a non-negative contribution.
-/

open scoped NNReal Topology
open Matrix Complex

namespace OpenMath.Chapter4.Section454Aux

/-
A real positive semi-definite matrix lifts to a complex matrix
whose Hermitian quadratic form has non-negative real part and zero
imaginary part.
-/
theorem complexLift_re_dotProduct_nonneg_of_real_posSemidef
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (W : Fin n → ℂ) :
    0 ≤ (star W ⬝ᵥ (A.map (algebraMap ℝ ℂ) *ᵥ W)).re ∧
    (star W ⬝ᵥ (A.map (algebraMap ℝ ℂ) *ᵥ W)).im = 0 := by
  -- Decompose W into its real and imaginary parts.
  set a : Fin n → ℝ := fun i => (W i).re
  set b : Fin n → ℝ := fun i => (W i).im;
  -- By definition of matrix multiplication and the properties of the Hermitian quadratic form, we have:
  have h_mulVec : star W ⬝ᵥ (A.map (algebraMap ℝ ℂ) *ᵥ W) = (∑ i, ∑ j, a i * A i j * a j + ∑ i, ∑ j, b i * A i j * b j) + Complex.I * (∑ i, ∑ j, b i * A i j * a j - ∑ i, ∑ j, a i * A i j * b j) := by
    simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, Finset.sum_add_distrib, mul_assoc, mul_comm, mul_left_comm, Complex.ext_iff ];
    have := hA.1; simp_all +decide [ Matrix.IsHermitian, ← Matrix.ext_iff ] ;
    exact ⟨ rfl, by rw [ ← Finset.sum_comm ] ; simp +decide [ this, mul_comm ] ; ring ⟩;
  -- Since $A$ is symmetric, we have $\sum_{i,j} b_i A_{ij} a_j = \sum_{i,j} a_i A_{ij} b_j$.
  have h_symm : ∑ i, ∑ j, b i * A i j * a j = ∑ i, ∑ j, a i * A i j * b j := by
    have := hA.1;
    rw [ ← Finset.sum_comm ] ; congr ; ext i ; congr ; ext j ; have := congr_fun ( congr_fun this j ) i ; norm_num at this ; ring;
    rw [ this ] ; ring;
  simp_all +decide [ Matrix.PosSemidef ];
  exact add_nonneg ( by simpa [ Finsupp.sum_fintype, Finset.sum_mul ] using hA.2 ( Finsupp.equivFunOnFinite.symm a ) ) ( by simpa [ Finsupp.sum_fintype, Finset.sum_mul ] using hA.2 ( Finsupp.equivFunOnFinite.symm b ) )

/-
A real positive definite matrix lifts to a complex matrix
whose Hermitian quadratic form has strictly positive real part on
non-zero complex vectors.
-/
theorem complexLift_re_dotProduct_pos_of_real_posDef
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {W : Fin n → ℂ} (hW : W ≠ 0) :
    0 < (star W ⬝ᵥ (A.map (algebraMap ℝ ℂ) *ᵥ W)).re := by
  set a : Fin n → ℝ := fun i => (W i).re
  set b : Fin n → ℝ := fun i => (W i).im
  have h_re : (star W ⬝ᵥ (A.map (algebraMap ℝ ℂ) *ᵥ W)).re =
      (a ⬝ᵥ A.mulVec a) + (b ⬝ᵥ A.mulVec b) := by
    simp +decide [Matrix.mulVec, dotProduct, Finset.sum_add_distrib,
      Complex.mul_re, Complex.mul_im]
    rfl
  rw [h_re]
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hW (funext fun i => Complex.ext
      (by simpa using congr_fun h.1 i) (by simpa using congr_fun h.2 i))
  -- Since $a$ and $b$ are real vectors, we can apply the positive definiteness of $A$ to get the strict positivity.
  have h_pos : ∀ (v : Fin n → ℝ), v ≠ 0 → 0 < dotProduct v (A.mulVec v) := by
    have := hA.2;
    intro v hv; specialize @this ( Finsupp.equivFunOnFinite.symm v ) ; simp_all +decide [ dotProduct, Matrix.mulVec, Finsupp.sum_fintype ] ;
    convert this ( by simpa [ Finsupp.ext_iff, funext_iff ] using hv ) using 1 ; simp +decide [ mul_assoc, Finset.mul_sum _ _ _ ];
  cases hab <;> [ exact add_pos_of_pos_of_nonneg ( h_pos _ ‹_› ) ( if h : b = 0 then by simp +decide [ h ] else le_of_lt ( h_pos _ h ) ) ; exact add_pos_of_nonneg_of_pos ( if h : a = 0 then by simp +decide [ h ] else le_of_lt ( h_pos _ h ) ) ( h_pos _ ‹_› ) ]

end OpenMath.Chapter4.Section454Aux