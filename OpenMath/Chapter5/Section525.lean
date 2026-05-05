import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.IsDiag
import OpenMath.Chapter5.Section510

/-!
# Butcher §525 — G-symplectic methods (Definition 525A)

This file formalizes the textbook predicate `IsGSymplectic`
on a `GeneralLinearMethod`.

## Textbook statement (quoted verbatim from `entities/def_525A.json`)

> A general linear method `(A, U, B, V)` is G-symplectic if there
> exists a positive semi-definite symmetric `r × r` matrix `G` and an
> `s × s` diagonal matrix `D` such that
>
>     G = Vᵀ G V,                              (525a)
>     D U = Bᵀ G V,                            (525b)
>     D A + Aᵀ D = Bᵀ G B.                     (525c)

## Faithfulness notes

* `Matrix.PosSemidef` (Mathlib, `LinearAlgebra.Matrix.PosDef`) bundles
  `IsHermitian` (which over `ℝ` is exactly symmetry) with the
  non-negative quadratic-form condition. This matches Butcher's
  "positive semi-definite symmetric" exactly.
* `Matrix.IsDiag` (Mathlib, `LinearAlgebra.Matrix.IsDiag`) is the
  predicate `∀ i j, i ≠ j → M i j = 0`, the standard textbook
  notion of a diagonal matrix.
* The predicate is purely existential over `(G, D)`: we are *not*
  characterizing G-symplecticity via a derived property (e.g.
  the stability function being unitary). The Lean predicate is
  the textbook definition letter-for-letter.

## Non-vacuity witness

`explicitEulerGLM` (the canonical `(s, r) = (1, 1)` GLM from
`Section510.lean`) is trivially G-symplectic with `G = 0` and
`D = 0`: every condition (525a)–(525c) collapses to `0 = 0`.
This establishes inhabitation of the predicate but is a
*degenerate* witness — every GLM trivially satisfies the
predicate with `G = D = 0`. Butcher's substantive non-trivial
example (eq. (525d), the explicit 2×2 method with `√3`
arithmetic) is deferred to a future cycle.
-/

namespace OpenMath.Chapter5.Section510

namespace GeneralLinearMethod

variable {s r : ℕ}

/-- **Definition 525A** — A general linear method `(A, U, B, V)` is
*G-symplectic* if there exist a positive semi-definite symmetric
`r × r` matrix `G` and an `s × s` diagonal matrix `D` such that

* (525a) `Vᵀ G V = G`,
* (525b) `D U = Bᵀ G V`,
* (525c) `D A + Aᵀ D = Bᵀ G B`.

Note that `Matrix.PosSemidef` over `ℝ` already encodes symmetry
through its `IsHermitian` component; no separate symmetry
hypothesis is needed. -/
def IsGSymplectic (M : GeneralLinearMethod s r) : Prop :=
  ∃ (G : Matrix (Fin r) (Fin r) ℝ) (D : Matrix (Fin s) (Fin s) ℝ),
    G.PosSemidef ∧ D.IsDiag ∧
    M.V.transpose * G * M.V = G ∧
    D * M.U = M.B.transpose * G * M.V ∧
    D * M.A + M.A.transpose * D = M.B.transpose * G * M.B

/-- Non-vacuity witness for `IsGSymplectic`: `explicitEulerGLM` is
trivially G-symplectic with `G = 0` and `D = 0`. Every condition
(525a)–(525c) collapses to `0 = 0`.

This is a *degenerate* witness — every GLM trivially satisfies
`IsGSymplectic` with `G = D = 0`. It establishes inhabitation of
the predicate, but does not exhibit a substantively G-symplectic
method. Butcher's intended non-trivial example is the explicit
2×2 method of equation (525d), whose witness involves `√3`
arithmetic and is deferred to a future cycle. -/
theorem explicitEulerGLM_isGSymplectic :
    explicitEulerGLM.IsGSymplectic := by
  refine ⟨0, 0, Matrix.PosSemidef.zero, Matrix.isDiag_zero, ?_, ?_, ?_⟩
  · -- Vᵀ * 0 * V = 0
    simp
  · -- 0 * U = Bᵀ * 0 * V
    simp
  · -- 0 * A + Aᵀ * 0 = Bᵀ * 0 * B
    simp

end GeneralLinearMethod

end OpenMath.Chapter5.Section510
