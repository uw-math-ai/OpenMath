import Mathlib

/-!
Focused Aristotle target: equivalence of the `P`-quadratic form with the
Euclidean norm on `Fin n → ℝ`, where `P` is real symmetric positive definite
in the quadratic-form sense.

Suggested Mathlib infrastructure to use:

* `Matrix.PosDef` (in `Mathlib.LinearAlgebra.Matrix.PosDef`): for a real matrix
  `P : Matrix (Fin n) (Fin n) ℝ`, `P.PosDef` ↔ `P.IsHermitian ∧ ∀ x ≠ 0, 0 < star x ⬝ᵥ P.mulVec x`.
  For real matrices, `star x = x` and `IsHermitian = IsSymm` (via `Pᵀ = P`).

* `Matrix.PosDef.eigenvalues_pos` (in `Mathlib.Analysis.Matrix.PosDef`):
  each eigenvalue is strictly positive.

* `Matrix.IsHermitian.spectral_theorem` / `Matrix.IsHermitian.spectralTheorem`
  for spectral decomposition of a Hermitian matrix.

Alternative: prove via compactness of the unit sphere in `EuclideanSpace ℝ (Fin n)`,
where the continuous function `x ↦ x ⬝ᵥ P.mulVec x` attains a positive minimum and
some maximum, then scale homogeneously.
-/

namespace QuadraticLyapunov

open Matrix

variable {n : ℕ}

def QFPosDef (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Pᵀ = P ∧ ∀ v : Fin n → ℝ, v ≠ 0 → 0 < v ⬝ᵥ P.mulVec v

/-- Equivalence of the `P`-quadratic form with the Euclidean form on `Fin n → ℝ`.
For positive-definite `P`, there exist `0 < c₀ ≤ c₁` such that
`c₀ · ∑ i, x i² ≤ x ⬝ᵥ P.mulVec x ≤ c₁ · ∑ i, x i²` for all `x`. -/
lemma lyapNorm_eqv {P : Matrix (Fin n) (Fin n) ℝ} (hP : QFPosDef P) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ c₀ ≤ c₁ ∧
      ∀ x : Fin n → ℝ,
        c₀ * (∑ i, (x i) ^ 2) ≤ x ⬝ᵥ P.mulVec x ∧
        x ⬝ᵥ P.mulVec x ≤ c₁ * (∑ i, (x i) ^ 2) := by
  sorry

end QuadraticLyapunov
