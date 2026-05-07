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

/-- A real positive semi-definite matrix lifts to a complex matrix
whose Hermitian quadratic form has non-negative real part and zero
imaginary part. -/
theorem complexLift_re_dotProduct_nonneg_of_real_posSemidef
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (W : Fin n → ℂ) :
    0 ≤ (star W ⬝ᵥ (A.map (algebraMap ℝ ℂ) *ᵥ W)).re ∧
    (star W ⬝ᵥ (A.map (algebraMap ℝ ℂ) *ᵥ W)).im = 0 := by
  sorry

/-- A real positive definite matrix lifts to a complex matrix
whose Hermitian quadratic form has strictly positive real part on
non-zero complex vectors. -/
theorem complexLift_re_dotProduct_pos_of_real_posDef
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {W : Fin n → ℂ} (hW : W ≠ 0) :
    0 < (star W ⬝ᵥ (A.map (algebraMap ℝ ℂ) *ᵥ W)).re := by
  sorry

end OpenMath.Chapter4.Section454Aux
