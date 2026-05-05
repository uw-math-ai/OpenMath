import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp
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

end OpenMath.Chapter5.Section510
