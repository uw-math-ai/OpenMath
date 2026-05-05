import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import OpenMath.Chapter1.Section142

/-!
# Butcher §510 — Preconsistency vector for general linear methods (Definition 510A)

This file opens Chapter 5 of the formalization. It introduces the
`GeneralLinearMethod` data structure (four matrices `A`, `U`, `B`, `V`
indexed by the number of internal stages `s` and the number of
input/output values `r`) and the `IsPreconsistent` predicate
(Definition 510A).

## Textbook statement (quoted verbatim from `entities/def_510A.json`)

> A general linear method `(A, U, B, V)` is 'preconsistent' if
> there exists a vector `u` such that
>
>     V u = u,                              (510a)
>     U u = 1.                              (510b)
>
> The vector `u` is the 'preconsistency vector'.

## Index convention

Following Butcher's §510 tableau presentation `[A | U; B | V]`, we
take the first index to be the number of internal stages `s` and the
second to be the number of input/output values `r`:

| Matrix | Type |
|---|---|
| `A` | `Matrix (Fin s) (Fin s) ℝ` |
| `U` | `Matrix (Fin s) (Fin r) ℝ` |
| `B` | `Matrix (Fin r) (Fin s) ℝ` |
| `V` | `Matrix (Fin r) (Fin r) ℝ` |

This is the convention used throughout the rest of Chapter 5
(`def:510B`, `def:510C`, `def:520A` …).

## Non-vacuity witness

`explicitEulerGLM` is the canonical `(s = 1, r = 1)` GLM realising
explicit Euler `y_{n+1} = y_n + h f(y_n)`, with `A = !![0]`,
`U = !![1]`, `B = !![1]`, `V = !![1]`. Its preconsistency vector is
`u = (fun _ => 1)`.
-/

namespace OpenMath.Chapter5.Section510

open Matrix
open scoped Matrix.Norms.Operator

/-- A general linear method (Butcher §510) with `s` internal stages
and `r` input/output values. The four constituent matrices together
specify how a single step transforms the `r`-vector of input values
and computes the `s` internal stages. -/
structure GeneralLinearMethod (s r : ℕ) where
  /-- The `s × s` block governing internal-stage interaction. -/
  A : Matrix (Fin s) (Fin s) ℝ
  /-- The `s × r` block injecting input values into internal stages. -/
  U : Matrix (Fin s) (Fin r) ℝ
  /-- The `r × s` block extracting output values from internal stages. -/
  B : Matrix (Fin r) (Fin s) ℝ
  /-- The `r × r` block governing input/output value propagation. -/
  V : Matrix (Fin r) (Fin r) ℝ

/-- **Definition 510A** — A GLM is *preconsistent* if there exists a
vector `u : Fin r → ℝ` (the *preconsistency vector*) such that
`V u = u` and `U u = 1` (the all-ones vector in `Fin s → ℝ`). -/
def GeneralLinearMethod.IsPreconsistent {s r : ℕ}
    (M : GeneralLinearMethod s r) : Prop :=
  ∃ u : Fin r → ℝ, M.V *ᵥ u = u ∧ M.U *ᵥ u = (fun _ => 1)

/-- **Definition 510C** — A GLM is *stable* if there exists a constant
`C` such that `‖M.V ^ n‖ ≤ C` for every `n : ℕ`.

This is the GLM instance of Butcher's general matrix-stability notion
(`def:142A`, `OpenMath.Chapter1.Section142.PowerBounded`), applied to
the input/output propagation matrix `V`.

Butcher (Definition 510C, p. 407): "A general linear method
`(A, U, B, V)` is *stable* if there exists a constant `C` such that,
for all `n = 1, 2, ...,`, `‖V^n‖ ≤ C`."

The textbook quantifies over `n = 1, 2, ...`, while we quantify over
all `n : ℕ` (including `n = 0`). The two formulations are equivalent:
`V^0 = 1`, so `‖V^0‖ = ‖1‖` is a fixed constant, and any bound for
`n ≥ 1` extends to `max(C, ‖1‖)` for all `n`. The full-`ℕ`
quantification matches the existing `def:142A` `PowerBounded`
signature exactly, allowing direct reuse.

The matrix norm used is `Matrix.linftyOpNormedRing`
(`Mathlib.Analysis.Matrix.Normed`), which gives
`Matrix (Fin r) (Fin r) ℝ` a `SeminormedRing` instance compatible with
`PowerBounded`. The textbook is silent on which matrix norm is used;
all matrix norms on a finite-dimensional space are equivalent up to
changing the bound `C`, so this choice is faithful (cf. the parallel
discussion in the docstring of `def:142A`). -/
def GeneralLinearMethod.IsStable {s r : ℕ}
    (M : GeneralLinearMethod s r) : Prop :=
  ∃ C : ℝ, OpenMath.Chapter1.Section142.PowerBounded C M.V

/-- **Definition 510B** — A GLM is *consistent* if it is preconsistent
with some preconsistency vector `u`, and additionally there exists a
vector `v` such that `B·𝟙 + V·v = u + v` (equation 510c).

Butcher (Definition 510B, p. 406): "A general linear method
`(A, U, B, V)` is *consistent* if it is preconsistent with
preconsistency vector `u` and there exists a vector `v` such that
`B·𝟙 + V·v = u + v`."

We existentially quantify both `u` and `v` here so that
`IsConsistent` is a self-contained predicate on the GLM. The
preconsistency conditions `V u = u` and `U u = 1` are embedded
inline (mirroring `IsPreconsistent`); this matches the textbook's
intent that the same `u` witness preconsistency and consistency
simultaneously, while still letting downstream callers extract
`IsPreconsistent` via the `IsConsistent.isPreconsistent` projection
lemma below. -/
def GeneralLinearMethod.IsConsistent {s r : ℕ}
    (M : GeneralLinearMethod s r) : Prop :=
  ∃ u v : Fin r → ℝ,
    (M.V *ᵥ u = u ∧ M.U *ᵥ u = (fun _ => 1)) ∧
    M.B *ᵥ (fun _ => 1) + M.V *ᵥ v = u + v

/-- A consistent GLM is preconsistent (the `u` witness lifts). -/
theorem GeneralLinearMethod.IsConsistent.isPreconsistent
    {s r : ℕ} {M : GeneralLinearMethod s r}
    (hC : M.IsConsistent) : M.IsPreconsistent := by
  obtain ⟨u, _, ⟨hVu, hUu⟩, _⟩ := hC
  exact ⟨u, hVu, hUu⟩

/-! ### Non-vacuity witness: explicit Euler as a `(1, 1)`-GLM -/

/-- Explicit Euler `y_{n+1} = y_n + h f(y_n)` viewed as a
`(s, r) = (1, 1)` general linear method, with `A = 0`, `U = 1`,
`B = 1`, `V = 1`. -/
def explicitEulerGLM : GeneralLinearMethod 1 1 where
  A := !![0]
  U := !![1]
  B := !![1]
  V := !![1]

/-- The all-ones vector `u = (fun _ => 1) : Fin 1 → ℝ` witnesses the
preconsistency of `explicitEulerGLM`. -/
theorem explicitEulerGLM_isPreconsistent :
    explicitEulerGLM.IsPreconsistent := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · -- V u = u: !![1] *ᵥ (fun _ => 1) = (fun _ => 1).
    funext i
    fin_cases i
    simp [explicitEulerGLM, Matrix.mulVec, dotProduct]
  · -- U u = 1: !![1] *ᵥ (fun _ => 1) = (fun _ => 1).
    funext i
    fin_cases i
    simp [explicitEulerGLM, Matrix.mulVec, dotProduct]

/-- Non-vacuity witness for `IsStable`: `explicitEulerGLM` is stable
with bound `C = 1`. Its `V` block is the `1 × 1` identity, so every
power `V^n` is the identity and has linfty operator norm `1`. -/
theorem explicitEulerGLM_isStable : explicitEulerGLM.IsStable := by
  refine ⟨1, ?_⟩
  intro n
  -- Goal: ‖explicitEulerGLM.V ^ n‖ ≤ 1
  have hV : explicitEulerGLM.V = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    fin_cases i; fin_cases j
    simp [explicitEulerGLM]
  rw [hV, one_pow]
  exact le_of_eq norm_one

/-- Non-vacuity witness for `IsConsistent`: `explicitEulerGLM` is
consistent with `u = (fun _ => 1)` and `v = (fun _ => 0)`.

Equation (510c) collapses to `B·𝟙 + V·0 = 1 + 0`, i.e. `1 = 1`,
since the 1×1 matrices `B = V = !![1]` and the all-ones / all-zeros
vectors evaluate by `simp`. -/
theorem explicitEulerGLM_isConsistent :
    explicitEulerGLM.IsConsistent := by
  refine ⟨fun _ => 1, fun _ => 0, ⟨?_, ?_⟩, ?_⟩
  · -- V·u = u
    funext i; fin_cases i
    simp [explicitEulerGLM, Matrix.mulVec, dotProduct]
  · -- U·u = 1
    funext i; fin_cases i
    simp [explicitEulerGLM, Matrix.mulVec, dotProduct]
  · -- B·𝟙 + V·v = u + v
    funext i; fin_cases i
    simp [explicitEulerGLM, dotProduct]

/-! ### Non-vacuity witness: implicit midpoint as a `(1, 1)`-GLM -/

/-- The implicit midpoint method as a `(s, r) = (1, 1)` general
linear method. The single stage `Y₁ = (h/2) f(Y₁) + y[n]` and the
output `y[n+1] = h f(Y₁) + y[n]` recover the classical implicit
midpoint rule (cf. Butcher §234 written in Runge–Kutta tableau as
`c = 1/2, A = 1/2, b = 1`, then transcribed into GLM form via the
trivial `r = 1` embedding). The GLM tableau is

```
A = !![1/2],   U = !![1]
B = !![1],     V = !![1]
```

This is a substantively non-trivial named GLM in `(s, r) = (1, 1)`:
unlike `explicitEulerGLM` (which has `A = 0`), the diagonal entry
`A = 1/2` makes the method *implicit*. It is the canonical
textbook example of a symplectic integrator and is used as a
substantive non-vacuity witness for `IsGSymplectic` (see
`implicitMidpointGLM_isGSymplectic` in
`OpenMath.Chapter5.Section525`). -/
noncomputable def implicitMidpointGLM : GeneralLinearMethod 1 1 where
  A := !![1/2]
  U := !![1]
  B := !![1]
  V := !![1]

/-- Non-vacuity witness for `IsPreconsistent`: `implicitMidpointGLM`
is preconsistent with `u = (fun _ => 1)`. The proof mirrors
`explicitEulerGLM_isPreconsistent` exactly because the `U` and `V`
blocks coincide. -/
theorem implicitMidpointGLM_isPreconsistent :
    implicitMidpointGLM.IsPreconsistent := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · funext i
    fin_cases i
    simp [implicitMidpointGLM, Matrix.mulVec, dotProduct]
  · funext i
    fin_cases i
    simp [implicitMidpointGLM, Matrix.mulVec, dotProduct]

/-- Non-vacuity witness for `IsStable`: `implicitMidpointGLM` is stable
with bound `C = 1`. Its `V` block is the `1 × 1` identity (matching
`explicitEulerGLM`), so every power `V^n` is the identity and has
linfty operator norm `1`. -/
theorem implicitMidpointGLM_isStable : implicitMidpointGLM.IsStable := by
  refine ⟨1, ?_⟩
  intro n
  have hV : implicitMidpointGLM.V = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    fin_cases i; fin_cases j
    simp [implicitMidpointGLM]
  rw [hV, one_pow]
  exact le_of_eq norm_one

/-- Non-vacuity witness for `IsConsistent`: `implicitMidpointGLM` is
consistent with `u = (fun _ => 1)` and `v = (fun _ => 0)`. The proof
mirrors `explicitEulerGLM_isConsistent` exactly because the `B`, `U`,
and `V` blocks coincide between the two GLMs. -/
theorem implicitMidpointGLM_isConsistent :
    implicitMidpointGLM.IsConsistent := by
  refine ⟨fun _ => 1, fun _ => 0, ⟨?_, ?_⟩, ?_⟩
  · funext i; fin_cases i
    simp [implicitMidpointGLM, Matrix.mulVec, dotProduct]
  · funext i; fin_cases i
    simp [implicitMidpointGLM, Matrix.mulVec, dotProduct]
  · funext i; fin_cases i
    simp [implicitMidpointGLM, dotProduct]

end OpenMath.Chapter5.Section510
