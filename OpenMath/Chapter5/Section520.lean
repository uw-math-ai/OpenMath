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
open scoped Matrix.Norms.Operator
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

/-- **Definition 520C** — The *stability function* of a general linear
method, `Φ(w, z) = det(wI − M(z))`.

Butcher (Definition 520C, p. 419): "The 'stability function' for the
method is the polynomial `Φ(w, z)` given by `Φ(w, z) = det(wI − M(z))`."

Encoding note: in general `M(z)` involves `(I − zA)⁻¹`, so `Φ` is
naturally a rational function in `z`. The textbook remark "we equally
refer to the numerator of this rational function as the stability
function" is a notational convenience, not a separate Lean definition;
we encode the literal `det(wI − M(z))` form, which is the canonical
representative on the invertibility domain. -/
noncomputable def GeneralLinearMethod.stabilityFunction
    {s r : ℕ} (M : GeneralLinearMethod s r) (w z : ℂ) : ℂ :=
  (w • (1 : Matrix (Fin r) (Fin r) ℂ) - M.stabilityMatrix z).det

/-- **Definition 520C** (continued) — The *stability region* of a
general linear method is the set of `z ∈ ℂ` for which the powers of
`M(z)` are uniformly bounded.

Butcher (Definition 520C, p. 419): "the 'stability region' is the
subset of the complex plane such that if `z` is in this subset, then
`sup_{n=1..∞} ‖M(z)^n‖ < ∞`."

We use the existential `PowerBounded` predicate from
`OpenMath.Chapter1.Section142` (a uniform `∀ k, ‖a^k‖ ≤ C` bound,
equivalent on a `SeminormedRing` to the supremum-finiteness condition
`sup_n ‖a^n‖ < ∞`). The matrix norm is the default Mathlib
`Matrix.linftyOpNormedRing` made available by
`Mathlib.Analysis.Matrix.Normed`; per the §142 docstring, the
predicate is norm-equivalence-invariant on finite-dimensional spaces
so the choice of matrix norm does not affect membership.

This is a literal re-spelling of the textbook condition, not
definition smuggling: existence of a uniform bound is equivalent to
finiteness of the supremum on a `SeminormedRing`. -/
noncomputable def GeneralLinearMethod.stabilityRegion
    {s r : ℕ} (M : GeneralLinearMethod s r) : Set ℂ :=
  { z : ℂ | ∃ C : ℝ,
      OpenMath.Chapter1.Section142.PowerBounded C (M.stabilityMatrix z) }

/-- **Definition 520C** (continued) — The *instability region* of a
general linear method is the complement of its stability region in
`ℂ`.

Butcher (Definition 520C, p. 419): "We refer to the 'instability
region' as the complement of the stability region." -/
noncomputable def GeneralLinearMethod.instabilityRegion
    {s r : ℕ} (M : GeneralLinearMethod s r) : Set ℂ :=
  (M.stabilityRegion)ᶜ

/-- Non-vacuity: at `z = 0`, the explicit-Euler stability function
collapses to `Φ(w, 0) = w − 1`.

Since `M(0) = !![1 + 0] = !![1]` for explicit Euler, the determinant
`det(wI − M(0))` reduces (1×1) to the scalar `w − 1`. -/
theorem explicitEulerGLM_stabilityFunction_at_zero (w : ℂ) :
    explicitEulerGLM.stabilityFunction w 0 = w - 1 := by
  unfold GeneralLinearMethod.stabilityFunction
  rw [explicitEulerGLM_stabilityMatrix]
  rw [Matrix.det_fin_one]
  simp

/-- Non-vacuity: `0` lies in the stability region of explicit Euler.
At `z = 0`, `M(0) = !![1] = 1`, so every power equals `1` and the
sequence of norms is uniformly bounded by `‖(1 : Matrix (Fin 1) (Fin 1) ℂ)‖`. -/
theorem explicitEulerGLM_zero_mem_stabilityRegion :
    (0 : ℂ) ∈ explicitEulerGLM.stabilityRegion := by
  refine ⟨‖(1 : Matrix (Fin 1) (Fin 1) ℂ)‖, ?_⟩
  intro k
  rw [explicitEulerGLM_stabilityMatrix]
  have hM : !![(1 : ℂ) + 0] = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j; fin_cases i; fin_cases j
    simp
  rw [hM, one_pow]

/-- **Definition 520E** — A general linear method is *A-stable* if its
stability matrix `M(z)` is power-bounded for every `z` in the (closed)
left half complex plane.

Butcher (Definition 520E, p. 419): "A general linear method is
'A-stable' if `M(z)` is power-bounded for every `z` in the left half
complex plane."

Encoding choices:

* "Power-bounded" is the existential `PowerBounded` predicate from
  `OpenMath.Chapter1.Section142` reused via membership in the
  `stabilityRegion` set defined in `def:520C`. By unfolding,
  `z ∈ M.stabilityRegion ↔ ∃ C, PowerBounded C (M.stabilityMatrix z)`,
  so this re-spelling is a literal restatement of the textbook.
* "Left half complex plane" is encoded as the closed left half-plane
  `{z : ℂ | z.re ≤ 0}`. The textbook is silent on open vs closed; the
  closed interpretation is the standard convention in stability
  theory. -/
def GeneralLinearMethod.IsAStable {s r : ℕ}
    (M : GeneralLinearMethod s r) : Prop :=
  ∀ z : ℂ, z.re ≤ 0 → z ∈ M.stabilityRegion

/-- The trivial `(s, r) = (1, 1)` GLM with all four blocks set to the
zero `1×1` matrix. This is not a Runge–Kutta or LMM in the textbook
sense — it is the simplest non-vacuity witness for A-stability:
its stability matrix `M(z) = !![0]` for every `z`, so the trivial
power bound holds uniformly. -/
def trivialZeroGLM : GeneralLinearMethod 1 1 where
  A := !![0]
  U := !![0]
  B := !![0]
  V := !![0]

/-- For the all-zero `(1,1)` GLM, the stability matrix collapses to
the `1×1` zero matrix at every `z ∈ ℂ`. -/
theorem trivialZeroGLM_stabilityMatrix (z : ℂ) :
    trivialZeroGLM.stabilityMatrix z = !![0] := by
  -- (1 - z • complexify A) = 1 since A = !![0].
  have hA :
      (1 - z • complexify trivialZeroGLM.A)
        = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    fin_cases i; fin_cases j
    simp [trivialZeroGLM, complexify]
  unfold GeneralLinearMethod.stabilityMatrix
  rw [hA, inv_one]
  ext i j
  fin_cases i; fin_cases j
  simp [trivialZeroGLM, complexify, Matrix.mul_apply]

/-- Non-vacuity witness for `IsAStable`: the `trivialZeroGLM` is
A-stable. Since `M(z) = !![0]` for every `z`, the powers
`M(z)^0 = 1`, `M(z)^k = 0` (`k ≥ 1`) are uniformly bounded by
`‖(1 : Matrix (Fin 1) (Fin 1) ℂ)‖`. -/
theorem trivialZeroGLM_isAStable : trivialZeroGLM.IsAStable := by
  intro z _hz
  refine ⟨‖(1 : Matrix (Fin 1) (Fin 1) ℂ)‖, ?_⟩
  intro k
  rw [trivialZeroGLM_stabilityMatrix]
  have h0 : (!![(0 : ℂ)] : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
    ext i j; fin_cases i; fin_cases j; simp
  rw [h0]
  cases k with
  | zero => simp
  | succ n =>
      rw [zero_pow (Nat.succ_ne_zero n), norm_zero]
      exact norm_nonneg _

end OpenMath.Chapter5.Section510
