import OpenMath.Chapter3.Section370
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Butcher §357 — Algebraically stable Runge–Kutta methods (Definition 357B)

This file formalises Definition 357B from Butcher's *Numerical Methods for
Ordinary Differential Equations* (3rd ed., page 271).

## Textbook statement (Definition 357B, quoted verbatim from `def_357B.json`)

> A Runge–Kutta method `(A, b, c)` is 'algebraically stable' if
> `bᵢ > 0`, for `i = 1, 2, …, s`, and if the matrix `M`, given by
> `M = diag(b)A + A diag(b) − bbᵀ` (357d), is positive
> semi-definite.

## Faithfulness notes

* The matrix `M` of equation (357d) is **literally the same matrix** as
  Butcher's equation (370a) used to define symplecticity. We reuse
  `OpenMath.Chapter3.Section370.symplecticityMatrix` rather than
  introducing a parallel definition; symplecticity is the case `M = 0`,
  and algebraic stability is the case `M ⪰ 0` together with `b > 0`.
* `IsAlgebraicallyStable R` is the conjunction of two textbook clauses:
  componentwise positivity of `b` and `(symplecticityMatrix R).PosSemidef`.
  This matches the textbook definition verbatim with no reformulation.
* The LLM-extracted dependency graph lists `def:357B → def:357A`
  (B-stability), but Butcher's text presents algebraic stability as a
  *sufficient condition* for B/BN-stability (Burrage–Butcher), not the
  other way round. Algebraic stability is a self-contained matrix
  condition; the JSON edge is reversed and is **not** a real
  mathematical dependency for this definition.

## Concrete witness — the implicit midpoint method

The implicit midpoint method (cycle 027's `implicitMidpoint`) has
`symplecticityMatrix = 0`, so it is trivially algebraically stable:
its single weight is `1 > 0`, and the zero matrix is positive
semidefinite.
-/

namespace OpenMath.Chapter3.Section357

open OpenMath.Chapter3.Section312
open OpenMath.Chapter3.Section370

/-- Butcher §357 Definition 357B — a Runge–Kutta method `(A, b, c)` is
*algebraically stable* iff every weight `bᵢ` is strictly positive and
the symplecticity matrix `M = diag(b) A + A diag(b) − b bᵀ` (equation
(357d), the same matrix as in (370a)) is positive semidefinite. -/
def IsAlgebraicallyStable {s : ℕ} (R : RKTableau s) : Prop :=
  (∀ i, 0 < R.b i) ∧ (symplecticityMatrix R).PosSemidef

/-! ## Concrete witness — implicit midpoint -/

/-- The implicit midpoint method is algebraically stable: its single
weight is `1 > 0`, and its symplecticity matrix vanishes (cycle 027's
`implicitMidpoint_isSymplectic`), so the zero matrix is trivially
positive semidefinite. -/
theorem implicitMidpoint_isAlgebraicallyStable :
    IsAlgebraicallyStable implicitMidpoint := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    norm_num [implicitMidpoint]
  · rw [show symplecticityMatrix implicitMidpoint = 0 from
        implicitMidpoint_isSymplectic]
    exact Matrix.PosSemidef.zero

end OpenMath.Chapter3.Section357
