import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Butcher §111 — Linear systems of differential equations

This file collects entities of subsection 111 of Butcher's
*Numerical Methods for Ordinary Differential Equations* (3rd ed.).

Contents:

* `thm:111A` — `solution_superposition` (superposition principle for linear
  ODE systems).
-/

namespace OpenMath.Chapter1.Section111

open scoped Matrix
open Set Finset

/-- Butcher §111, Theorem 111A — *Superposition principle for linear systems*.

Verbatim textbook statement (Butcher 2008, p. 45):

> If `ŷ` is a solution to `dy/dx = A(x) y + φ(x)` (equation 111a) and
> `y₁, y₂, …, y_k` are solutions to `dy/dx = A(x) y` (equation 111b),
> then for any constants `α₁, α₂, …, α_k`, the function `y` given by
> `y(x) = ŷ(x) + ∑ᵢ αᵢ yᵢ(x)` is a solution to (111a).

This is a pure linearity-of-derivative fact: differentiating both sides,
`Matrix.mulVec` distributes over the inner sum and the constants `αᵢ`
factor out. Mathlib supplies all the building blocks
(`HasDerivAt.add`, `HasDerivAt.sum`, `HasDerivAt.const_smul`,
`Matrix.mulVec_add`, `Matrix.mulVec_smul`).

Signature notes:
* `s : Set ℝ` rather than `Set.Icc a b` keeps the lemma reusable; the
  intended Butcher instance is `s = Icc a b`.
* `(Fin N → ℝ)` is the codomain of solutions because `Matrix.mulVec`
  lives there directly. A `EuclideanSpace ℝ (Fin N)` wrapper can be
  added downstream if needed.
* `HasDerivAt` (not `HasDerivWithinAt`) — Butcher's "is a solution"
  is captured by pointwise differentiability on `s`. -/
theorem solution_superposition
    {N k : ℕ}
    (s : Set ℝ)
    (A : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (φ : ℝ → (Fin N → ℝ))
    (ŷ : ℝ → (Fin N → ℝ))
    (y : Fin k → ℝ → (Fin N → ℝ))
    (α : Fin k → ℝ)
    (hŷ : ∀ x ∈ s, HasDerivAt ŷ (A x *ᵥ ŷ x + φ x) x)
    (hy : ∀ i, ∀ x ∈ s, HasDerivAt (y i) (A x *ᵥ (y i) x) x) :
    ∀ x ∈ s, HasDerivAt
      (fun x => ŷ x + ∑ i, α i • y i x)
      (A x *ᵥ (ŷ x + ∑ i, α i • y i x) + φ x) x := by
  intro x hx
  -- Step 1: derivative of each scaled solution `α i • y i` is `α i • (A x *ᵥ y i x)`.
  have hαy : ∀ i : Fin k,
      HasDerivAt (fun t => α i • y i t) (α i • (A x *ᵥ (y i) x)) x := by
    intro i
    exact (hy i x hx).const_smul (α i)
  -- Step 2: derivative of the sum is the sum of the derivatives.
  have hsum_raw :
      HasDerivAt (∑ i ∈ (Finset.univ : Finset (Fin k)), fun t => α i • y i t)
        (∑ i ∈ (Finset.univ : Finset (Fin k)), α i • (A x *ᵥ (y i) x)) x :=
    HasDerivAt.sum (fun i _ => hαy i)
  have hsum_fun_eq :
      (∑ i ∈ (Finset.univ : Finset (Fin k)), fun t => α i • y i t)
        = (fun t => ∑ i, α i • y i t) := by
    funext t
    simp [Finset.sum_apply]
  rw [hsum_fun_eq] at hsum_raw
  -- Step 3: combine the derivative of `ŷ` with the derivative of `Σ αᵢ yᵢ`.
  have htot :
      HasDerivAt (fun t => ŷ t + ∑ i, α i • y i t)
        ((A x *ᵥ ŷ x + φ x) + ∑ i, α i • (A x *ᵥ (y i) x)) x :=
    (hŷ x hx).add hsum_raw
  -- Step 4: rewrite the target derivative via linearity of `Matrix.mulVec`.
  have h_dist :
      A x *ᵥ (∑ i, α i • y i x) = ∑ i, α i • (A x *ᵥ (y i) x) := by
    -- Use the linear-map version of `Matrix.mulVec` to commute with `Finset.sum`
    -- and pull out the `αᵢ` scalars.
    have hsum :
        (A x).mulVecLin (∑ i, α i • y i x)
          = ∑ i, (A x).mulVecLin (α i • y i x) :=
      map_sum (A x).mulVecLin (fun i => α i • y i x) Finset.univ
    have hsmul : ∀ i,
        (A x).mulVecLin (α i • y i x) = α i • (A x).mulVecLin (y i x) := by
      intro i
      exact (A x).mulVecLin.map_smul (α i) (y i x)
    simp_rw [Matrix.mulVecLin_apply] at hsum hsmul
    rw [hsum]
    refine Finset.sum_congr rfl ?_
    intro i _
    exact hsmul i
  -- Step 5: conclude.
  have h_target :
      A x *ᵥ (ŷ x + ∑ i, α i • y i x) + φ x
        = (A x *ᵥ ŷ x + φ x) + ∑ i, α i • (A x *ᵥ (y i) x) := by
    rw [Matrix.mulVec_add, h_dist]
    abel
  rw [h_target]
  exact htot

end OpenMath.Chapter1.Section111
