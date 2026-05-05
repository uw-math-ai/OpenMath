import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
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

/-- **Definition 520F** — A general linear method is *L-stable* if it
is A-stable and the spectral radius of its stability matrix `M(z)`
tends to `0` as `z → ∞` in `ℂ`.

Butcher (Definition 520F, p. 419): "A general linear method is
L-stable if it is A-stable and ρ(M(∞)) = 0."

Encoding choice: the condition `ρ(M(∞)) = 0` is interpreted as
`Filter.Tendsto (fun z => spectralRadius ℂ (M(z))) (Filter.cocompact ℂ)
(𝓝 0)`. This sidesteps the issue that `M(∞)` as a literal matrix
value is only well-defined when the `A`-block is invertible (in
which case `M(∞) = V − B·A⁻¹·U`); the spectral-radius limit
formulation captures the same mathematical content without needing
a case split on invertibility, and is the formulation universally
used in the modern stiff-ODE literature (cf. Hairer–Wanner). -/
def GeneralLinearMethod.IsLStable {s r : ℕ}
    (M : GeneralLinearMethod s r) : Prop :=
  M.IsAStable ∧
  Filter.Tendsto
    (fun z : ℂ => spectralRadius ℂ (M.stabilityMatrix z))
    (Filter.cocompact ℂ)
    (nhds 0)

/-- Non-vacuity witness for `IsLStable`: the `trivialZeroGLM` is
L-stable. Since `M(z) = !![0]` for every `z` (cycle 088
`trivialZeroGLM_stabilityMatrix`), the spectral radius is
identically `0`, and `Tendsto` of a constant sequence to its
constant value is automatic. -/
theorem trivialZeroGLM_isLStable : trivialZeroGLM.IsLStable := by
  refine ⟨trivialZeroGLM_isAStable, ?_⟩
  have hfun :
      (fun z : ℂ => spectralRadius ℂ (trivialZeroGLM.stabilityMatrix z))
        = fun _ => (0 : ENNReal) := by
    funext z
    rw [trivialZeroGLM_stabilityMatrix]
    have h0 : (!![(0 : ℂ)] : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
      ext i j; fin_cases i; fin_cases j; simp
    rw [h0]
    exact spectrum.spectralRadius_zero
  rw [hfun]
  exact tendsto_const_nhds

/-- **Definition 521A** — A general linear method *has stability order* `p`
if its stability function `Φ(w, z)` satisfies
`Φ(exp(z), z) = O(z^(p+1))` as `z → 0` in `ℂ`.

Butcher (Definition 521A, p. 420): "A method with stability function
`Φ(w, z)` has 'stability order' `p*` if `Φ(exp(z), z) = O(z^{p*+1})`."

Encoding choices:

* Big-O is `Asymptotics.IsBigO` at `nhds (0 : ℂ)`. The textbook's
  `O(z^{p*+1})` is at `z → 0` in `ℂ` (since `Φ` is bivariate
  complex). Plain `nhds 0` is the right filter: for any consistent
  method `Φ(exp 0, 0) = Φ(1, 0)` is well-defined (and indeed equals
  `0` for the witness below), so there is no need for a punctured
  neighborhood `nhdsWithin 0 ({0}ᶜ)`.

* No maximality clause. The textbook says "*has stability order p* if* …"
  without demanding that `p` is the largest such integer. Adding a
  maximality clause `¬ Φ(exp z, z) = O(z^(p+2))` would be
  over-specification and would require a non-vanishing argument (e.g.
  `¬ IsBigO _ _ (· ^ 3)`) for the explicit-Euler witness, which
  Mathlib does not provide directly. Downstream uses (e.g. `thm:521B`)
  can introduce a maximality predicate when needed.

The textbook §521A also introduces an auxiliary *complexity sequence*
`ν = [ν_0, ν_1, …, ν_k]` arising from the bivariate polynomial
representation
`Φ(w, z) = Σ_{j=0..k} w^(k-j) Σ_{l=0..ν_j} α_{jl} z^j`. That apparatus
is purely a representation device used to set up `thm:521B` ("for a
given ν, what is the highest possible stability order?") and is
**deferred** to whenever `thm:521B` is tackled. It plays no role in
the primary stability-order predicate above. Encoding it here would
require re-encoding `stabilityFunction` as a `Polynomial (Polynomial ℂ)`
or a parallel polynomial representation (currently
`stabilityFunction : ℂ → ℂ → ℂ` is a function, not a polynomial), a
multi-cycle infrastructure investment justified only when `thm:521B`
is the active target.

The declaration lives in the `OpenMath.Chapter5.Section510` namespace
(rather than the file's `Section520` namespace) so that dot notation
`M.HasStabilityOrder p` works on `GeneralLinearMethod` values. -/
def GeneralLinearMethod.HasStabilityOrder {s r : ℕ}
    (M : GeneralLinearMethod s r) (p : ℕ) : Prop :=
  Asymptotics.IsBigO (nhds (0 : ℂ))
    (fun z : ℂ => M.stabilityFunction (Complex.exp z) z)
    (fun z : ℂ => z ^ (p + 1))

/-- **Theorem 520B** — Stability matrix governs one step of a GLM
applied to the linear test equation `y' = q·y` with `z = h·q`.

For the linear test equation, `f(y) = q·y` so `F = q·Y` (stage
derivatives = `q` times stage values). The GLM step
`Y = h·A·F + U·y^[n−1]`, `y^[n] = h·B·F + V·y^[n−1]` reduces, with
`z := h·q`, to `Y = z·A·Y + U·y^[n−1]` and
`y^[n] = z·B·Y + V·y^[n−1]`. Provided `(I − z·A)` is invertible,
solving the stage equation gives `Y = (I − z·A)⁻¹·U·y^[n−1]` and
substituting into the output collapses to `y^[n] = M(z)·y^[n−1]`.

Butcher (Theorem 520B, p. 397): "Let `M(z)` denote the stability
matrix for a general linear method. Then, for a linear differential
equation (520a), (520b) holds with `z = hq`."

Encoding choices:

* The textbook's `f(y) = qy` ⇒ `F = qY` substitution and `z = hq`
  parameter are pre-applied, so `hY_stage` is the post-substitution
  stage equation `Y = z·A·Y + U·yPrev` and the conclusion is
  `z·B·Y + V·yPrev = M(z)·yPrev`. This faithfully captures the
  textbook content without re-introducing the stripped `q`/`h`/`f`
  apparatus.
* `IsUnit (1 - z • complexify M.A)` is added as a hypothesis to
  surface the textbook's tacit invertibility assumption (Mathlib's
  `Matrix.inv` returns junk-zero on singular matrices, so this
  theorem is genuinely false without invertibility).
* `Y` is parameterised (rather than instantiated as
  `(I − z·A)⁻¹·U·yPrev`), letting downstream callers supply any
  stage witness satisfying the stage equation. -/
theorem GeneralLinearMethod.stabilityMatrix_linearTest_step
    {s r : ℕ} (M : GeneralLinearMethod s r) (z : ℂ)
    (h_inv : IsUnit (1 - z • complexify M.A))
    (yPrev : Fin r → ℂ) (Y : Fin s → ℂ)
    (hY_stage : Y = z • complexify M.A *ᵥ Y
                    + complexify M.U *ᵥ yPrev) :
    z • complexify M.B *ᵥ Y + complexify M.V *ᵥ yPrev
      = M.stabilityMatrix z *ᵥ yPrev := by
  -- Step 1: rearrange `hY_stage` to `(1 - z • A) *ᵥ Y = U *ᵥ yPrev`.
  have h_stage_solved :
      (1 - z • complexify M.A) *ᵥ Y = complexify M.U *ᵥ yPrev := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
    -- Goal: Y - z • complexify M.A *ᵥ Y = complexify M.U *ᵥ yPrev
    nth_rewrite 1 [hY_stage]
    abel
  -- Step 2: apply `(1 - z • A)⁻¹` on the left to recover `Y`.
  have h_det : IsUnit (1 - z • complexify M.A).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp h_inv
  have h_inv_mul :
      (1 - z • complexify M.A)⁻¹ * (1 - z • complexify M.A) = 1 :=
    Matrix.nonsing_inv_mul _ h_det
  have hY_solved :
      Y = ((1 - z • complexify M.A)⁻¹ * complexify M.U) *ᵥ yPrev := by
    have h := congrArg
      (fun w : Fin s → ℂ => (1 - z • complexify M.A)⁻¹ *ᵥ w)
      h_stage_solved
    simp only at h
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h_inv_mul,
        Matrix.one_mulVec] at h
    exact h
  -- Step 3: substitute `Y` into the output and combine.
  rw [hY_solved]
  unfold GeneralLinearMethod.stabilityMatrix
  -- Goal: z • B *ᵥ (((1 - z•A)⁻¹ * U) *ᵥ yPrev) + V *ᵥ yPrev
  --     = (V + z • B * (1 - z•A)⁻¹ * U) *ᵥ yPrev
  rw [Matrix.mulVec_mulVec, ← Matrix.smul_mulVec, ← Matrix.add_mulVec,
      add_comm]
  -- Goal (matrix-equality after `congr 1`-style):
  -- (V + z • (B * ((1-z•A)⁻¹ * U))) *ᵥ yPrev
  --   = (V + z • B * (1-z•A)⁻¹ * U) *ᵥ yPrev
  congr 2
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc]

/-- Non-vacuity: at `z = 0`, the linear-test step says
`y^[n] = V·y^[n−1]` (since `M(0) = V`). The trivial stage witness
`Y := U·y^[n−1]` satisfies the stage equation `Y = 0·A·Y + U·yPrev`
trivially, and the output `0·B·Y + V·yPrev = V·yPrev` matches
`M(0)·yPrev = V·yPrev`. -/
theorem GeneralLinearMethod.stabilityMatrix_linearTest_step_at_zero
    {s r : ℕ} (M : GeneralLinearMethod s r) (yPrev : Fin r → ℂ) :
    complexify M.V *ᵥ yPrev = M.stabilityMatrix 0 *ᵥ yPrev := by
  rw [M.stabilityMatrix_at_zero]

/-- Closed-form stability function of explicit Euler:
`Φ_explicitEuler(w, z) = w − 1 − z`.

This is the `(s, r) = (1, 1)` case of `Φ(w, z) = det(wI − M(z))` with
`M(z) = !![1 + z]` from `explicitEulerGLM_stabilityMatrix`: the `1×1`
determinant evaluates to `w − (1 + z) = w − 1 − z`. -/
theorem explicitEulerGLM_stabilityFunction (w z : ℂ) :
    explicitEulerGLM.stabilityFunction w z = w - 1 - z := by
  unfold GeneralLinearMethod.stabilityFunction
  rw [explicitEulerGLM_stabilityMatrix]
  rw [Matrix.det_fin_one]
  simp [Matrix.smul_apply]
  ring

/-- Non-vacuity witness for `HasStabilityOrder`: explicit Euler has
stability order `1`.

Computation: from `explicitEulerGLM_stabilityFunction`,
`Φ(exp z, z) = exp z − 1 − z = exp z − ∑_{i<2} z^i / i!`. Mathlib's
`Complex.exp_sub_sum_range_isBigO_pow 2` then gives the desired
`O(z^2) = O(z^(1+1))` bound at `nhds 0`. -/
theorem explicitEulerGLM_hasStabilityOrder_one :
    explicitEulerGLM.HasStabilityOrder 1 := by
  unfold GeneralLinearMethod.HasStabilityOrder
  have hΦ :
      (fun z : ℂ => explicitEulerGLM.stabilityFunction
                      (Complex.exp z) z)
        = (fun z : ℂ => Complex.exp z
            - ∑ i ∈ Finset.range 2, z ^ i / (i.factorial : ℂ)) := by
    funext z
    rw [explicitEulerGLM_stabilityFunction]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [Nat.factorial]
    ring
  rw [hΦ]
  exact Complex.exp_sub_sum_range_isBigO_pow 2

/-! ### Definition 542A — Runge–Kutta stability -/

/-- **Definition 542A** — A general linear method `(A, U, B, V)` has
*Runge–Kutta stability* (RK stability) if its characteristic polynomial
`Φ(w, z) = det(wI − M(z))` factorises as

    Φ(w, z) = w^(r−1) · (w − R(z))

for some scalar function `R : ℂ → ℂ`. The function `R` is then called
the *stability function* of the method.

Butcher (Definition 542A, p. 445): "A general linear method
`(A, U, B, V)` has 'Runge–Kutta stability' if the characteristic
polynomial given by (542a) has the form `Φ(w, z) = w^{r−1}(w − R(z))`.
For a method with Runge–Kutta stability, the rational function `R(z)`
is known as the 'stability function' of the method."

Encoding choices:

* `Φ(w, z)` is the existing `M.stabilityFunction w z` from `def:520C`,
  which is exactly `det(w·I − M(z))` (equation 542a).
* The textbook calls `R` a *rational* function. We encode `R` as a plain
  `ℂ → ℂ`: the predicate only requires the factorisation to hold, and
  rationality of `R` is a downstream consequence (see e.g. `def:551A`)
  rather than part of the definitional content. Pre-emptively forcing
  `RatFunc ℂ` would be definition smuggling on the hypothesis side.
* For `r = 0`, `r − 1 = 0` (`Nat.sub`) and the factorisation reduces to
  `Φ(w, z) = w − R(z)`. But `r = 0` means `M(z)` is the empty matrix,
  so `Φ(w, z) = det(w·1 − M(z)) = 1` is constant in `w`; the
  factorisation `1 = w − R(z)` then has no solution for `R` (varying
  `w` would force `R z` to take two distinct values). The `r = 0`
  case is therefore correctly never RK-stable, matching the textbook's
  implicit `r ≥ 1`. -/
def GeneralLinearMethod.IsRKStable {s r : ℕ}
    (M : GeneralLinearMethod s r) : Prop :=
  ∃ R : ℂ → ℂ, ∀ w z : ℂ,
    M.stabilityFunction w z = w ^ (r - 1) * (w - R z)

/-- Non-vacuity witness for `IsRKStable`: `explicitEulerGLM` has
Runge–Kutta stability with stability function `R(z) = 1 + z`.

For `r = 1`, the factorisation `Φ(w, z) = w^0 · (w − R(z)) = w − R(z)`
matches `explicitEulerGLM_stabilityFunction`'s closed form
`Φ(w, z) = w − 1 − z` with `R(z) := 1 + z`. -/
theorem explicitEulerGLM_isRKStable :
    explicitEulerGLM.IsRKStable := by
  refine ⟨fun z => 1 + z, ?_⟩
  intro w z
  rw [explicitEulerGLM_stabilityFunction]
  -- Goal: w - 1 - z = w ^ (1 - 1) * (w - (1 + z))
  simp [pow_zero]
  ring

/-! ### Definition 551A — Inherent Runge–Kutta stability -/

/-- **Definition 551A (Inherent Runge–Kutta stability).**

A general linear method `(A, U, B, V)` is *inherently Runge–Kutta
stable* if:

1. The `V` block has the form `V[0][0] = 1`, `V[i][0] = 0` for
   `i ≠ 0` (i.e. its first column is the standard basis vector
   `e₀`). This is equation (551a).
2. There exists a real `r × r` matrix `X` such that the residual
   matrices `B·A − X·B` and `B·U − X·V + V·X` are zero outside
   their first rows.

Butcher (Definition 551A, p. 460): "A general linear method
`(A, U, B, V)` is `inherently Runge–Kutta stable' if `V` is of
the form (551a) and the two matrices `BA − XB` and
`BU − XV + VX` are zero except for their first rows, where `X`
is some matrix."

Encoding choices:

* The `V`-form clause (551a) is encoded directly as
  "first column is `e₀`": `V[0][0] = 1` and `V[i][0] = 0` for
  `i ≠ 0`. The `v` row-vector and the `V̇` block remain free,
  exactly as the textbook leaves them.
* "Zero except for first rows" is encoded as
  `i ≠ 0 → (·) i j = 0` for all `j`, which is the cleanest
  faithful translation without requiring an explicit
  sub-matrix extraction.
* Method-class side-conditions from the textbook `Context` block
  (`p = q`, `s = r = p + 1`, `A` diagonally implicit, `λ ≥ 0`,
  `ρ(V̇) = 0`) describe the *family of methods studied* when
  IRK stability is discussed; they are NOT part of the
  IRK-stability *predicate* itself. Including them would be
  hypothesis smuggling.
* The `[NeZero r]` instance argument captures the textbook's
  implicit `r ≥ 1` assumption (equation 551a's block form
  `V = [[1, v], [0, V̇]]` requires at least a `1 × 1` `V`). The
  `s = 0` case is harmless: the `B·A − X·B` clause is then
  vacuously satisfied. -/
def GeneralLinearMethod.IsIRKStable {s r : ℕ} [NeZero r]
    (M : GeneralLinearMethod s r) : Prop :=
  -- (551a): V's first column is the standard basis vector e₀.
  (∀ i : Fin r, M.V i 0 = if i = 0 then 1 else 0) ∧
  ∃ X : Matrix (Fin r) (Fin r) ℝ,
    -- B·A − X·B is zero outside row 0.
    (∀ (i : Fin r) (j : Fin s), i ≠ 0 →
      (M.B * M.A - X * M.B) i j = 0) ∧
    -- B·U − X·V + V·X is zero outside row 0.
    (∀ i j : Fin r, i ≠ 0 →
      (M.B * M.U - X * M.V + M.V * X) i j = 0)

/-- Non-vacuity witness for `IsIRKStable`: `explicitEulerGLM`
(s = r = 1, V = !![1]) is inherently Runge–Kutta stable.

For `r = 1`, only the index `i = 0` exists in `Fin 1`, so the
"zero outside row 0" clauses are vacuously satisfied for any
choice of `X`. We pick `X := 0`. The `V`-form clause reduces
to `V 0 0 = 1`, which holds since `V = !![1]`. -/
theorem explicitEulerGLM_isIRKStable :
    explicitEulerGLM.IsIRKStable := by
  refine ⟨?_, ?_⟩
  · -- (551a) clause: V's first column is e₀.
    intro i
    fin_cases i
    simp [explicitEulerGLM]
  · -- ∃ X clause: pick X = 0; both residual constraints are
    -- vacuously satisfied since Fin 1 forces i = 0.
    refine ⟨0, ?_, ?_⟩
    · intro i _ hi
      exact absurd (Subsingleton.elim i 0) hi
    · intro i _ hi
      exact absurd (Subsingleton.elim i 0) hi

/-! ### Theorem 520D — Instability Region Boundary Characterization

Butcher (Theorem 520D, p. 419): "The instability region for `(A, U, B, V)`
is a subset of the set of points `z`, such that `Φ(w, z) = 0`, where
`|w| ≥ 1`. The instability region is a superset of the points defined
by `Φ(w, z) = 0`, where `|w| > 1`."

This decomposes into two inclusions about
`M.instabilityRegion = (M.stabilityRegion)ᶜ`:
1. `instabilityRegion ⊆ { z : ∃ w, |w| ≥ 1 ∧ Φ(w, z) = 0 }`
2. `instabilityRegion ⊇ { z : ∃ w, |w| > 1 ∧ Φ(w, z) = 0 }`

We route through the spectrum of `M(z)` via the bridge lemma D1
(`stabilityFunction_eq_zero_iff_mem_spectrum`): zeros of `Φ(·, z)` are
exactly the spectrum of `M.stabilityMatrix z`. From there:

* Direction (2) is direct: an eigenvalue `w` with `‖w‖ > 1` forces
  `‖w‖^n ≤ ‖M(z)^n‖ * ‖(1)‖`, contradicting power-boundedness.
* Direction (1) goes via the spectral radius: power-boundedness
  bounds `spectralRadius M(z) ≤ 1` (D3), so its contrapositive says
  unstable `z` has `spectralRadius M(z) ≥ 1` (D4); pick the
  spectrum element realising the spectral radius
  (`spectrum.exists_nnnorm_eq_spectralRadius`).
-/

section InstabilityRegion520D

variable {s r : ℕ}

/-- **Sub-lemma D1** — `Φ(w, z) = 0` iff `w` is in the spectrum of
`M.stabilityMatrix z`.

This bridges the textbook's `Φ(w, z)` (encoded as `det(w·I − M(z))`)
with Mathlib's `spectrum ℂ M(z)`. Under the field `ℂ`, both forms
coincide via `Matrix.mem_spectrum_iff_isRoot_charpoly` and
`Matrix.eval_charpoly`. -/
private theorem GeneralLinearMethod.stabilityFunction_eq_zero_iff_mem_spectrum
    (M : GeneralLinearMethod s r) (w z : ℂ) :
    M.stabilityFunction w z = 0 ↔ w ∈ spectrum ℂ (M.stabilityMatrix z) := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
  unfold GeneralLinearMethod.stabilityFunction
  have h_eq : (w • (1 : Matrix (Fin r) (Fin r) ℂ) - M.stabilityMatrix z)
              = ((Matrix.scalar (Fin r)) w - M.stabilityMatrix z) := by
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  rw [h_eq, ← Matrix.eval_charpoly]
  rfl

/-- **Sub-lemma D2 = direction (2) of thm:520D** — If the stability
matrix `M(z)` has an eigenvalue strictly outside the closed unit disc,
then `z` lies in the instability region.

Proof: from `‖w‖ > 1` and `Φ(w, z) = 0` (an eigenvalue equation by D1),
we get `w^n ∈ spectrum (M(z)^n)` for every `n`, hence
`‖w‖^n = ‖w^n‖ ≤ ‖M(z)^n‖ · ‖(1)‖`. Power-boundedness would force
`‖w‖^n` bounded, but `‖w‖ > 1` makes `‖w‖^n → ∞`, contradiction. -/
theorem GeneralLinearMethod.instabilityRegion_supseteq_outside_disc
    (M : GeneralLinearMethod s r) {z : ℂ}
    (hz : ∃ w : ℂ, 1 < ‖w‖ ∧ M.stabilityFunction w z = 0) :
    z ∈ M.instabilityRegion := by
  obtain ⟨w, hw_norm, hw_zero⟩ := hz
  have hw_mem : w ∈ spectrum ℂ (M.stabilityMatrix z) :=
    (M.stabilityFunction_eq_zero_iff_mem_spectrum w z).mp hw_zero
  -- Goal: z ∈ (M.stabilityRegion)ᶜ
  unfold GeneralLinearMethod.instabilityRegion
  rw [Set.mem_compl_iff]
  unfold GeneralLinearMethod.stabilityRegion
  rw [Set.mem_setOf_eq]
  push_neg
  intro C
  unfold OpenMath.Chapter1.Section142.PowerBounded
  push_neg
  -- For each `n`, `w^n ∈ σ(M(z)^n)`, hence `‖w‖^n ≤ ‖M(z)^n‖ · ‖1‖`.
  have hnorm_one_nn : (0 : ℝ) ≤ ‖(1 : Matrix (Fin r) (Fin r) ℂ)‖ := norm_nonneg _
  have hbound : ∀ n : ℕ,
      ‖w‖ ^ n ≤ ‖M.stabilityMatrix z ^ n‖ * ‖(1 : Matrix (Fin r) (Fin r) ℂ)‖ := by
    intro n
    have hwn_mem : w ^ n ∈ spectrum ℂ (M.stabilityMatrix z ^ n) :=
      spectrum.pow_mem_pow _ _ hw_mem
    have hnorm : ‖w ^ n‖
        ≤ ‖M.stabilityMatrix z ^ n‖ * ‖(1 : Matrix (Fin r) (Fin r) ℂ)‖ :=
      spectrum.norm_le_norm_mul_of_mem hwn_mem
    rw [norm_pow] at hnorm
    exact hnorm
  -- `‖w‖ > 1` so `‖w‖^n → ∞`; pick `n` with `‖w‖^n > C·‖1‖`.
  have htend : Filter.Tendsto (fun n : ℕ => ‖w‖ ^ n) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hw_norm
  obtain ⟨N, hN⟩ : ∃ N : ℕ,
      C * ‖(1 : Matrix (Fin r) (Fin r) ℂ)‖ + 1 ≤ ‖w‖ ^ N :=
    (Filter.tendsto_atTop_atTop.mp htend
      (C * ‖(1 : Matrix (Fin r) (Fin r) ℂ)‖ + 1)).imp fun N hN => hN N le_rfl
  refine ⟨N, ?_⟩
  -- Goal (after push_neg): `C < ‖M(z)^N‖`. Argue by contradiction.
  by_contra hMN
  push_neg at hMN
  have hbN := hbound N
  have hmul_le :
      ‖M.stabilityMatrix z ^ N‖ * ‖(1 : Matrix (Fin r) (Fin r) ℂ)‖
        ≤ C * ‖(1 : Matrix (Fin r) (Fin r) ℂ)‖ :=
    mul_le_mul_of_nonneg_right hMN hnorm_one_nn
  linarith [hbN, hmul_le, hN]

/-- **Sub-lemma D3** — If `z ∈ M.stabilityRegion`, then the spectral
radius of `M(z)` is at most `1`.

Proof outline: from `PowerBounded C (M(z))` we have `‖M(z)^k‖ ≤ C` for
all `k`. Every `μ ∈ spectrum ℂ M(z)` satisfies `‖μ‖^k = ‖μ^k‖ ≤
‖M(z)^k‖ · ‖1‖ ≤ C · ‖1‖` (via `spectrum.pow_mem_pow` and
`spectrum.norm_le_norm_mul_of_mem`). If `‖μ‖ > 1`, then
`‖μ‖^k → ∞`, contradicting the uniform bound. Hence `‖μ‖ ≤ 1` for
every `μ ∈ σ`, so `spectralRadius ≤ 1`. -/
private theorem GeneralLinearMethod.stabilityRegion_imp_spectralRadius_le_one
    (M : GeneralLinearMethod s r) {z : ℂ}
    (hz : z ∈ M.stabilityRegion) :
    spectralRadius ℂ (M.stabilityMatrix z) ≤ 1 := by
  obtain ⟨C, hC⟩ := hz
  -- spectralRadius ℂ a = ⨆ k ∈ σ a, (‖k‖₊ : ℝ≥0∞).
  refine iSup₂_le ?_
  intro μ hμ
  -- Goal: (‖μ‖₊ : ℝ≥0∞) ≤ 1.
  by_contra h_lt
  push_neg at h_lt
  -- h_lt : 1 < (‖μ‖₊ : ℝ≥0∞).
  have h_norm : 1 < ‖μ‖ := by
    have h_nn : (1 : NNReal) < ‖μ‖₊ := ENNReal.one_lt_coe_iff.mp h_lt
    exact_mod_cast h_nn
  -- Power-boundedness gives ‖μ‖^k ≤ C·‖1‖ for all k.
  have hbound : ∀ k : ℕ,
      ‖μ‖ ^ k ≤ C * ‖(1 : Matrix (Fin r) (Fin r) ℂ)‖ := by
    intro k
    have hμk : μ ^ k ∈ spectrum ℂ (M.stabilityMatrix z ^ k) :=
      spectrum.pow_mem_pow _ _ hμ
    have hnorm_le := spectrum.norm_le_norm_mul_of_mem hμk
    rw [norm_pow] at hnorm_le
    calc ‖μ‖ ^ k
        ≤ ‖M.stabilityMatrix z ^ k‖ * ‖(1 : Matrix (Fin r) (Fin r) ℂ)‖ := hnorm_le
      _ ≤ C * ‖(1 : Matrix (Fin r) (Fin r) ℂ)‖ := by
          gcongr
          exact hC k
  -- ‖μ‖ > 1 forces ‖μ‖^k → ∞, contradicting hbound.
  have htend : Filter.Tendsto (fun k : ℕ => ‖μ‖ ^ k) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt h_norm
  obtain ⟨K, hK⟩ : ∃ K : ℕ,
      C * ‖(1 : Matrix (Fin r) (Fin r) ℂ)‖ + 1 ≤ ‖μ‖ ^ K :=
    (Filter.tendsto_atTop_atTop.mp htend
      (C * ‖(1 : Matrix (Fin r) (Fin r) ℂ)‖ + 1)).imp fun K hK => hK K le_rfl
  linarith [hbound K, hK]

/-- **Sub-lemma D4** — If `z ∈ M.instabilityRegion`, then the spectral
radius of `M(z)` is at least `1`.

Proof outline: contrapositive. Assume `spectralRadius M(z) < 1`. Each
root `μ` of `minpoly ℂ M(z)` is a charpoly root (since
`minpoly ∣ charpoly`), hence in the spectrum
(`Matrix.mem_spectrum_iff_isRoot_charpoly`); so
`(‖μ‖₊ : ℝ≥0∞) ≤ spectralRadius < 1`, hence `‖μ‖ < 1`. By
`Section142.minpoly_roots_lt_one_imp_convergent`, the matrix is
convergent (`M(z)^n → 0`); a convergent sequence is norm-bounded
(`Filter.Tendsto.norm` + `bddAbove_range`), giving the
power-boundedness witness for `z ∈ M.stabilityRegion`. -/
private theorem GeneralLinearMethod.instabilityRegion_imp_spectralRadius_ge_one
    (M : GeneralLinearMethod s r) {z : ℂ}
    (hz : z ∈ M.instabilityRegion) :
    1 ≤ spectralRadius ℂ (M.stabilityMatrix z) := by
  by_contra h_lt
  push_neg at h_lt
  -- h_lt : spectralRadius ℂ M(z) < 1
  apply hz
  unfold GeneralLinearMethod.stabilityRegion
  rw [Set.mem_setOf_eq]
  -- Step 1: minpoly roots have norm < 1
  have h_minpoly :
      ∀ μ : ℂ, μ ∈ (minpoly ℂ (M.stabilityMatrix z)).roots → ‖μ‖ < 1 := by
    intro μ hμ_root
    have hμ_minpoly : (minpoly ℂ (M.stabilityMatrix z)).IsRoot μ :=
      (Polynomial.mem_roots
        (minpoly.ne_zero (Matrix.isIntegral _))).mp hμ_root
    have h_dvd : minpoly ℂ (M.stabilityMatrix z) ∣ (M.stabilityMatrix z).charpoly :=
      (M.stabilityMatrix z).minpoly_dvd_charpoly
    have hμ_charpoly : (M.stabilityMatrix z).charpoly.IsRoot μ :=
      hμ_minpoly.dvd h_dvd
    have hμ_spec : μ ∈ spectrum ℂ (M.stabilityMatrix z) :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hμ_charpoly
    have h_le : (‖μ‖₊ : ENNReal) ≤ spectralRadius ℂ (M.stabilityMatrix z) :=
      le_iSup₂ (f := fun k _ => (‖k‖₊ : ENNReal)) μ hμ_spec
    have h_lt' : (‖μ‖₊ : ENNReal) < 1 := lt_of_le_of_lt h_le h_lt
    have h_lt_nn : ‖μ‖₊ < (1 : NNReal) := ENNReal.coe_lt_one_iff.mp h_lt'
    exact_mod_cast h_lt_nn
  -- Step 2: convergent
  have h_conv :
      OpenMath.Chapter1.Section142.Convergent (M.stabilityMatrix z) :=
    OpenMath.Chapter1.Section142.minpoly_roots_lt_one_imp_convergent _ h_minpoly
  -- Step 3: convergent → power-bounded
  have h_norm_tend :
      Filter.Tendsto (fun n : ℕ => ‖M.stabilityMatrix z ^ n‖)
        Filter.atTop (nhds 0) := by
    have := h_conv.norm
    simpa using this
  obtain ⟨C, hC⟩ :
      BddAbove (Set.range (fun n : ℕ => ‖M.stabilityMatrix z ^ n‖)) :=
    h_norm_tend.bddAbove_range
  exact ⟨C, fun k => hC (Set.mem_range_self k)⟩

/-- **Theorem 520D direction (1)** — If `z` is in the instability
region, then the stability matrix `M(z)` has an eigenvalue with
`|w| ≥ 1`, equivalently `Φ(w, z) = 0`.

Proof: D4 gives `1 ≤ spectralRadius M(z)`. Pick `w ∈ spectrum`
attaining the spectral radius
(`spectrum.exists_nnnorm_eq_spectralRadius`); then `‖w‖ ≥ 1`. Apply
D1 in reverse to obtain `Φ(w, z) = 0`. -/
theorem GeneralLinearMethod.instabilityRegion_subseteq_closed_disc_zeros
    (M : GeneralLinearMethod s r) {z : ℂ}
    (hz : z ∈ M.instabilityRegion) :
    ∃ w : ℂ, 1 ≤ ‖w‖ ∧ M.stabilityFunction w z = 0 := by
  -- When `r = 0`, `Matrix (Fin 0) (Fin 0) ℂ` is a subsingleton, so
  -- `M(z)^k = 0` for all `k` and `z` is in the stability region —
  -- contradicting `hz`. Otherwise, the spectral-radius route applies.
  cases isEmpty_or_nonempty (Fin r) with
  | inl _ =>
    exfalso
    apply hz
    refine ⟨0, ?_⟩
    intro k
    have h_zero : M.stabilityMatrix z ^ k = (0 : Matrix (Fin r) (Fin r) ℂ) :=
      Subsingleton.elim _ _
    rw [h_zero, norm_zero]
  | inr _ =>
    have h_sr : 1 ≤ spectralRadius ℂ (M.stabilityMatrix z) :=
      M.instabilityRegion_imp_spectralRadius_ge_one hz
    obtain ⟨w, hw_mem, hw_eq⟩ :=
      spectrum.exists_nnnorm_eq_spectralRadius (M.stabilityMatrix z)
    refine ⟨w, ?_, ?_⟩
    · -- `(‖w‖₊ : ℝ≥0∞) = spectralRadius ≥ 1`, so `‖w‖ ≥ 1` in ℝ.
      have h1 : (1 : ENNReal) ≤ ((‖w‖₊ : NNReal) : ENNReal) := hw_eq ▸ h_sr
      have h2 : (1 : NNReal) ≤ ‖w‖₊ := ENNReal.one_le_coe_iff.mp h1
      exact_mod_cast h2
    · exact (M.stabilityFunction_eq_zero_iff_mem_spectrum w z).mpr hw_mem

end InstabilityRegion520D

end OpenMath.Chapter5.Section510
