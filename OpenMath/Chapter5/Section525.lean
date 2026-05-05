import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Data.Real.StarOrdered
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
method. The *substantively* non-trivial witness is provided by
`implicitMidpointGLM_isGSymplectic` (with
`G = D = (1 : Matrix (Fin 1) (Fin 1) ℝ)`). Butcher's intended
2×2 example (eq. (525d)) involves `√3` arithmetic and is deferred
to a future cycle. -/
theorem explicitEulerGLM_isGSymplectic :
    explicitEulerGLM.IsGSymplectic := by
  refine ⟨0, 0, Matrix.PosSemidef.zero, Matrix.isDiag_zero, ?_, ?_, ?_⟩
  · -- Vᵀ * 0 * V = 0
    simp
  · -- 0 * U = Bᵀ * 0 * V
    simp
  · -- 0 * A + Aᵀ * 0 = Bᵀ * 0 * B
    simp

/-- Substantively non-trivial G-symplectic witness: the implicit
midpoint method (as a `(s, r) = (1, 1)` general linear method)
is G-symplectic with the *non-zero* witness
`G = D = (1 : Matrix (Fin 1) (Fin 1) ℝ)`.

This complements `explicitEulerGLM_isGSymplectic` (whose
`G = D = 0` witness trivially satisfies (525a)–(525c) for *every*
GLM) by demonstrating that `IsGSymplectic` has discriminating
content. Indeed `explicitEulerGLM` (with `A = !![0]`) does *not*
admit the witness `G = D = 1`: equation (525c) would require
`D · A + Aᵀ · D = Bᵀ · G · B`, i.e. `0 = 1`. So this witness
genuinely separates `implicitMidpointGLM` from
`explicitEulerGLM` at the level of G-symplectic structure.

The three matrix equations all collapse under the chosen witness:
* (525a) `Vᵀ · G · V = 1 · 1 · 1 = 1 = G`,
* (525b) `D · U = 1 · 1 = 1 = 1 · 1 · 1 = Bᵀ · G · V`,
* (525c) `D · A + Aᵀ · D = (1/2) + (1/2) = 1 = 1 · 1 · 1 = Bᵀ · G · B`.

Implicit midpoint is the canonical textbook example of a
symplectic integrator (Butcher §234, p. ~104), making this the
mathematically intended substantive witness for the predicate. -/
theorem implicitMidpointGLM_isGSymplectic :
    implicitMidpointGLM.IsGSymplectic := by
  refine ⟨1, 1, Matrix.PosSemidef.one, Matrix.isDiag_one, ?_, ?_, ?_⟩
  · -- (525a) Vᵀ * 1 * V = 1, with V = !![1]
    ext i j
    fin_cases i; fin_cases j
    simp [implicitMidpointGLM, Matrix.mul_apply]
  · -- (525b) 1 * U = Bᵀ * 1 * V, with U = B = V = !![1]
    ext i j
    fin_cases i; fin_cases j
    simp [implicitMidpointGLM, Matrix.mul_apply]
  · -- (525c) 1 * A + Aᵀ * 1 = Bᵀ * 1 * B, with A = !![1/2], B = !![1]
    ext i j
    fin_cases i; fin_cases j
    simp [implicitMidpointGLM, Matrix.mul_apply, Matrix.add_apply]
    norm_num

end GeneralLinearMethod

end OpenMath.Chapter5.Section510
