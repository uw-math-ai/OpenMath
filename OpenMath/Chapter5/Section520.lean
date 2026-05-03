import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import OpenMath.Chapter5.Section510

/-!
# Butcher §520 — Stability matrix `M(z)` of a general linear method (Definition 520A)

This file opens the stability theory of general linear methods. It
introduces the *stability matrix* `M(z) = V + z·B·(I − z·A)⁻¹·U`
(Definition 520A) by lifting the four real coefficient matrices of a
GLM to complex matrices and using Mathlib's `Matrix.inv` for the
resolvent.

## Textbook statement (quoted verbatim from `entities/def_520A.json`)

> For a general linear method `(A, U, B, V)`, the 'stability matrix'
> `M(z)` is defined by
>
>     M(z) = V + zB(I − zA)⁻¹U.

## Encoding choices

* The textbook implicitly restricts attention to `z` outside the
  spectrum of `A⁻¹` (equivalently, those `z` for which `(I − z·A)`
  is invertible). We use Mathlib's `Matrix.inv`, which agrees with
  the genuine resolvent on that domain and produces the junk value
  `0` elsewhere — the standard partial-function-via-junk-value
  pattern used throughout Mathlib (`Ring.inverse`, `Matrix.inv`).
* The four real GLM matrices are entrywise lifted to `ℂ` via the
  helper `complexify`. Since `B` and `U` are not square, we cannot
  use the bundled `RingHom.mapMatrix` for them; a plain
  `Matrix.map (Complex.ofReal ·)` is the simplest choice.

## Non-vacuity

* `stabilityMatrix_at_zero`: every GLM has `M(0) = V` (entrywise lift).
* `explicitEulerGLM_stabilityMatrix`: for the canonical
  `(s, r) = (1, 1)` explicit-Euler GLM, `M(z) = !![1 + z]`.
-/

namespace OpenMath.Chapter5.Section520

open Matrix

/-- Lift a real matrix to a complex matrix entrywise via
`Complex.ofReal`. This is a small private helper used only to state
`stabilityMatrix`. -/
def complexify {m n : Type*} (A : Matrix m n ℝ) : Matrix m n ℂ :=
  A.map (Complex.ofReal ·)

@[simp]
theorem complexify_apply {m n : Type*} (A : Matrix m n ℝ) (i : m) (j : n) :
    complexify A i j = (A i j : ℂ) := rfl

end OpenMath.Chapter5.Section520

namespace OpenMath.Chapter5.Section510

open Matrix
open OpenMath.Chapter5.Section520 (complexify)

/-- **Definition 520A** — The *stability matrix* `M(z)` of a general
linear method `(A, U, B, V)` at a complex parameter `z` is

    M(z) = V + z · B · (I − z·A)⁻¹ · U.

The matrix `(I − z·A)⁻¹` is taken via Mathlib's `Matrix.inv`
(`Matrix.NonsingularInverse`); it equals the genuine resolvent when
`(I − z·A)` is invertible, and equals `0` (the Mathlib convention)
otherwise. This is the standard partial-function-via-junk-value
encoding used throughout Mathlib for `Ring.inverse`, `Matrix.inv`,
etc.

Butcher (Definition 520A, p. 418): "For a general linear method
`(A, U, B, V)`, the 'stability matrix' `M(z)` is defined by
`M(z) = V + zB(I − zA)⁻¹U`."

The textbook implicitly restricts attention to `z` outside the
spectrum of `A⁻¹` (where `(I − z·A)` is invertible). Our encoding
matches the textbook formula on that domain and produces a
well-defined "junk" elsewhere; downstream theorems that need
invertibility (e.g. `def:520C` stability function via
`det(wI − M(z))`) will provide the appropriate hypothesis.

The declaration lives in the `OpenMath.Chapter5.Section510` namespace
(rather than the file's `Section520` namespace) so that dot notation
`M.stabilityMatrix z` works on values of type
`Section510.GeneralLinearMethod s r`. -/
noncomputable def GeneralLinearMethod.stabilityMatrix
    {s r : ℕ}
    (M : GeneralLinearMethod s r)
    (z : ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  complexify M.V +
    z • complexify M.B *
      (1 - z • complexify M.A)⁻¹ *
      complexify M.U

/-- At `z = 0`, the stability matrix collapses to the (complexified)
`V` block: `M(0) = V`. This is the simplest non-vacuity check on
`stabilityMatrix` and follows by unfolding the definition and
reducing the `z = 0` factors. -/
theorem GeneralLinearMethod.stabilityMatrix_at_zero
    {s r : ℕ}
    (M : GeneralLinearMethod s r) :
    M.stabilityMatrix 0 = complexify M.V := by
  unfold GeneralLinearMethod.stabilityMatrix
  simp

/-- Non-vacuity witness: for the explicit-Euler GLM
(`A = !![0]`, `U = B = V = !![1]`), the stability matrix is the
`1×1` complex matrix `!![1 + z]`.

Since the `A`-block is `!![0]`, we have `(1 − z·A) = 1`, so
`(1 − z·A)⁻¹ = 1`, and `M(z) = !![1] + z · !![1] · !![1] · !![1]
              = !![1 + z]`. -/
theorem explicitEulerGLM_stabilityMatrix (z : ℂ) :
    explicitEulerGLM.stabilityMatrix z = !![1 + z] := by
  -- Reduce `(1 - z • complexify A) = 1` since `A = !![0]`.
  have hA :
      (1 - z • complexify explicitEulerGLM.A)
        = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    fin_cases i; fin_cases j
    simp [explicitEulerGLM, complexify]
  unfold GeneralLinearMethod.stabilityMatrix
  rw [hA, inv_one]
  ext i j
  fin_cases i; fin_cases j
  simp [explicitEulerGLM, complexify, Matrix.mul_apply]

end OpenMath.Chapter5.Section510
