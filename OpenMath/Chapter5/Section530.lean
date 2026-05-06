import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.MetricSpace.Lipschitz
import OpenMath.Chapter5.Section510

/-!
# Butcher §530 — Possible definitions of order: non-degenerate starting methods (Definition 530A)

This file opens §530 with the *generalized Runge–Kutta method* tableau
`(c, A, b₀, b)` (equation (530a)) and Definition 530A, which classifies
*starting methods* as **degenerate** or **non-degenerate** according to
whether all of their `b₀^{(i)}` coefficients vanish.

## Textbook statement (quoted verbatim from `entities/def_530A.json`)

> A starting method `S` defined by the generalized Runge–Kutta methods
> (530a), for `i = 1, 2, …, r`, is 'degenerate' if `b₀^{(i)} = 0`, for
> `i = 1, 2, …, r`, and 'non-degenerate' otherwise.

The textbook construction (Butcher §530, p. 410) writes a generalized
Runge–Kutta method in tableau form

```
        c | A
   Sᵢ = ─ ─ ─
       b₀ | bᵀ
```

with `c, b : Fin sᵢ → ℝ`, `A : Matrix (Fin sᵢ) (Fin sᵢ) ℝ`, and a single
extra scalar `b₀ ∈ ℝ`. A *starting method* `S = (S₁, …, S_r)` is then a
length-`r` tuple of such tableaux, one per input/output channel of the
underlying general linear method.

## Indexing convention

Following the Lean pattern already established in §510 (where the GLM
structure indexes input/output values by `Fin r`), we index the
constituent methods of a starting method by `Fin r` as well, so that
the textbook's `S_i` for `i = 1, …, r` corresponds to `S.method ⟨i-1, _⟩`
(0-based `Fin r`).

The number of stages `s_i` of each `S_i` is *heterogeneous* in the
textbook (each `S_i` may have its own stage count). We capture this
faithfully via a dependent function `stages : Fin r → ℕ` together with
`method : (i : Fin r) → GeneralizedRungeKuttaMethod (stages i)`.

## Non-vacuity witness

`trivialStartingMethod` is the canonical `r = 1`-method starting method
whose lone constituent `S₁` is the trivial 1-stage generalized
Runge–Kutta tableau with `b₀ = 1`. The non-vacuity witness
`trivialStartingMethod_isNonDegenerate` exhibits `i = 0` as the index
on which `b₀^{(i)} ≠ 0`, refuting degeneracy.
-/

namespace OpenMath.Chapter5.Section530

/-- **Generalized Runge–Kutta method** (Butcher §530, equation (530a)).
A tableau `(c, A, b₀, b)` with `s` internal stages, where `c, b : Fin s → ℝ`,
`A : Matrix (Fin s) (Fin s) ℝ`, and the extra scalar `b₀ : ℝ` records
the input-coefficient that distinguishes a *generalized* RK method
from a classical one. -/
structure GeneralizedRungeKuttaMethod (s : ℕ) where
  /-- The stage abscissae `c : Fin s → ℝ` (textbook's `c^{(i)}`). -/
  c : Fin s → ℝ
  /-- The stage-coupling matrix `A : Fin s × Fin s → ℝ`. -/
  A : Matrix (Fin s) (Fin s) ℝ
  /-- The scalar input weight `b₀ ∈ ℝ`. This is the coefficient whose
  vanishing for *every* constituent method defines a starting method
  to be degenerate (Definition 530A). -/
  b₀ : ℝ
  /-- The output-weight row `b : Fin s → ℝ` (textbook's `b^{(i)ᵀ}`). -/
  b : Fin s → ℝ

/-- **Starting method** (Butcher §530, p. 410). A length-`r` sequence
of generalized Runge–Kutta methods `S₁, S₂, …, S_r`, one per
input/output value of the underlying general linear method.

The number of stages `s_i = stages i` may vary with `i`; we encode this
heterogeneity faithfully via a dependent function. -/
structure StartingMethod (r : ℕ) where
  /-- Number of stages in the `i`-th constituent method `S_i`. -/
  stages : Fin r → ℕ
  /-- The `i`-th constituent generalized Runge–Kutta method. -/
  method : (i : Fin r) → GeneralizedRungeKuttaMethod (stages i)

/-- **Definition 530A (Butcher §530, p. 411).** A starting method `S`
is *degenerate* if `b₀^{(i)} = 0` for every `i = 1, …, r`.

Textbook: "A starting method `S` defined by the generalized Runge–Kutta
methods (530a), for `i = 1, 2, …, r`, is 'degenerate' if `b₀^{(i)} = 0`,
for `i = 1, 2, …, r`, and 'non-degenerate' otherwise." -/
def StartingMethod.IsDegenerate {r : ℕ} (S : StartingMethod r) : Prop :=
  ∀ i : Fin r, (S.method i).b₀ = 0

/-- **Definition 530A (Butcher §530, p. 411).** A starting method is
*non-degenerate* if it fails to be degenerate, i.e. there exists at
least one constituent method `S_i` with `b₀^{(i)} ≠ 0`. -/
def StartingMethod.IsNonDegenerate {r : ℕ} (S : StartingMethod r) : Prop :=
  ¬ S.IsDegenerate

/-- Direct unfolding: `IsNonDegenerate` is equivalent to *some* `b₀^{(i)}`
being non-zero. This is the form most useful for proving non-vacuity. -/
theorem StartingMethod.isNonDegenerate_iff_exists_b₀_ne_zero
    {r : ℕ} (S : StartingMethod r) :
    S.IsNonDegenerate ↔ ∃ i : Fin r, (S.method i).b₀ ≠ 0 := by
  unfold StartingMethod.IsNonDegenerate StartingMethod.IsDegenerate
  exact not_forall

/-! ### Non-vacuity witness: trivial 1-stage starting method

The simplest starting method has `r = 1` (a single constituent), and
that single constituent is the 1-stage generalized RK tableau
`c = 0, A = !![0], b₀ = 1, b = !![1]`. Its `b₀ = 1 ≠ 0`, so the
starting method is non-degenerate. -/

/-- The 1-stage trivial generalized Runge–Kutta tableau with
`c = 0, A = 0, b₀ = 1, b = 1`. This corresponds to a "do nothing,
inject the input directly" method whose `b₀ = 1` ensures the
non-degeneracy of any starting method using it. -/
def trivialGeneralizedRK : GeneralizedRungeKuttaMethod 1 where
  c := fun _ => 0
  A := !![0]
  b₀ := 1
  b := fun _ => 1

/-- The canonical `r = 1` starting method whose single constituent
is `trivialGeneralizedRK`. Witnesses non-vacuity of
`StartingMethod` and `IsNonDegenerate`. -/
def trivialStartingMethod : StartingMethod 1 where
  stages := fun _ => 1
  method := fun _ => trivialGeneralizedRK

/-- **Non-vacuity of `IsNonDegenerate`.** The trivial 1-method starting
method has `b₀^{(0)} = 1 ≠ 0`, so it is non-degenerate.

This closes the CLAUDE.md mandate that every new predicate be
witnessed: it shows `IsDegenerate` is genuinely refutable (so
`IsNonDegenerate` is non-vacuous) and `IsDegenerate` is genuinely
distinct from "always true". -/
theorem trivialStartingMethod_isNonDegenerate :
    trivialStartingMethod.IsNonDegenerate := by
  rw [StartingMethod.isNonDegenerate_iff_exists_b₀_ne_zero]
  refine ⟨0, ?_⟩
  show (1 : ℝ) ≠ 0
  exact one_ne_zero

/-! ### Non-vacuity of `IsDegenerate` (refutability of non-degeneracy)

To show `IsNonDegenerate` is not the trivial-true predicate, we also
exhibit a starting method that *is* degenerate: the same trivial
shape but with `b₀ = 0` everywhere. -/

/-- The 1-stage *degenerate* generalized Runge–Kutta tableau with
all coefficients zero (in particular `b₀ = 0`). -/
def zeroGeneralizedRK : GeneralizedRungeKuttaMethod 1 where
  c := fun _ => 0
  A := !![0]
  b₀ := 0
  b := fun _ => 0

/-- The `r = 1` starting method whose single constituent is
`zeroGeneralizedRK`. Witnesses non-vacuity of `IsDegenerate`. -/
def zeroStartingMethod : StartingMethod 1 where
  stages := fun _ => 1
  method := fun _ => zeroGeneralizedRK

/-- **Non-vacuity of `IsDegenerate`.** The all-zero starting method
satisfies `b₀^{(i)} = 0` for every `i`, hence is degenerate. Together
with `trivialStartingMethod_isNonDegenerate`, this confirms that the
degenerate / non-degenerate dichotomy is non-trivial. -/
theorem zeroStartingMethod_isDegenerate :
    zeroStartingMethod.IsDegenerate := by
  intro i
  fin_cases i
  rfl

/-! ### Heterogeneous-stages witness (cycle 141)

The witnesses `trivialStartingMethod` and `zeroStartingMethod` both have
`r = 1` and a constant `stages` function. To exercise the dependent
heterogeneous-stages design `stages : Fin r → ℕ` of `StartingMethod`,
we construct a 2-method starting method whose first constituent is
1-stage and whose second is 2-stage, then prove (a) it is non-degenerate
and (b) the two stage counts are unequal. The latter is the
load-bearing theorem confirming the dependent-function design is
genuinely needed: the existing constant-stages witnesses leave open
whether `stages : Fin r → ℕ` does real work. -/

/-- A 2-stage *generalized* Runge–Kutta tableau with all-zero matrix,
abscissae, and output weights but `b₀ = 2`. The non-zero `b₀ = 2`
distinguishes it from `zeroGeneralizedRK` and witnesses the second
constituent of `mixedStartingMethod`. -/
def nontrivialTwoStageGRK : GeneralizedRungeKuttaMethod 2 where
  c := ![0, 0]
  A := !![0, 0; 0, 0]
  b₀ := 2
  b := ![0, 0]

/-- The heterogeneous `Fin 2 → ℕ` stage-count function:
`stages 0 = 1`, `stages 1 = 2`. -/
def mixedStages : Fin 2 → ℕ
  | 0 => 1
  | 1 => 2

/-- The dependent constituent-method function for `mixedStartingMethod`:
the zeroth constituent is the 1-stage `trivialGeneralizedRK`, the first
is the 2-stage `nontrivialTwoStageGRK`. The dependent return type
`GeneralizedRungeKuttaMethod (mixedStages i)` reduces correctly because
`mixedStages 0 = 1` and `mixedStages 1 = 2` hold definitionally. -/
def mixedMethod : (i : Fin 2) → GeneralizedRungeKuttaMethod (mixedStages i)
  | 0 => trivialGeneralizedRK
  | 1 => nontrivialTwoStageGRK

/-- A 2-method starting method exercising the heterogeneous-stages
dependent design: `stages 0 = 1, stages 1 = 2`, with a 1-stage trivial
constituent and a 2-stage non-trivial constituent. -/
def mixedStartingMethod : StartingMethod 2 where
  stages := mixedStages
  method := mixedMethod

/-- **Non-vacuity (heterogeneous-stages witness).** `mixedStartingMethod`
is non-degenerate: its zeroth constituent has `b₀ = 1 ≠ 0`. -/
theorem mixedStartingMethod_isNonDegenerate :
    mixedStartingMethod.IsNonDegenerate := by
  rw [StartingMethod.isNonDegenerate_iff_exists_b₀_ne_zero]
  refine ⟨0, ?_⟩
  show (1 : ℝ) ≠ 0
  exact one_ne_zero

/-- **The heterogeneous-stages design is genuinely needed.**
`mixedStartingMethod.stages 0 ≠ mixedStartingMethod.stages 1`,
confirming that the dependent `stages : Fin r → ℕ` field captures
information not exposed by the existing constant-stages witnesses
`trivialStartingMethod` and `zeroStartingMethod`. -/
theorem mixedStartingMethod_stages_neq :
    mixedStartingMethod.stages 0 ≠ mixedStartingMethod.stages 1 := by
  decide

/-! ### Refutability witness at `r = 2` (cycle 141 stretch)

Parallel to `zeroStartingMethod` but at `r = 2`: a 2-method starting
method with both constituents being the all-zero 1-stage tableau,
hence degenerate. Confirms the dichotomy is non-trivial across both
`r = 1` and `r = 2` shapes. -/

/-- The `r = 2` starting method whose two constituents are both
`zeroGeneralizedRK`. Witnesses `IsDegenerate` at `r = 2`. -/
def zero2StartingMethod : StartingMethod 2 where
  stages := fun _ => 1
  method := fun _ => zeroGeneralizedRK

/-- **Non-vacuity of `IsDegenerate` at `r = 2`.** The all-zero 2-method
starting method satisfies `b₀^{(i)} = 0` for every `i : Fin 2`. -/
theorem zero2StartingMethod_isDegenerate :
    zero2StartingMethod.IsDegenerate := by
  intro i
  fin_cases i <;> rfl

/-! ### Explicit generalized Runge–Kutta methods (cycle 151, def:530B Path A Step 1)

Butcher's §530 implicitly distinguishes *explicit* generalized Runge–Kutta
methods — those whose stage equations
`Y_i = y₀ + h · Σⱼ A_{ij} · f(Y_j)` can be evaluated by direct recursion
on the stage index `i = 0, 1, …, s-1` — from *implicit* ones, which
require solving a fixed-point system. The recursion succeeds exactly
when the coefficient matrix `A` is *strictly lower triangular*:
`A i j = 0` whenever `i ≤ j` (i.e. on or above the diagonal).

The textbook does not name the predicate, but uses the property
implicitly when discussing methods like classical RK4. We capture it
here as a Lean-internal helper for def:530B, where it will gate the
"explicit-only" operators `applyStartingThenStep_explicit` and
`applyExactThenStarting_explicit` (cycle 152 target). -/

/-- **Explicitness predicate.** A generalized Runge–Kutta method is
*explicit* if its coefficient matrix `A` is strictly lower triangular:
`A i j = 0` whenever `i ≤ j`.

This is the Lean encoding of "no implicit stage equations": for an
explicit method, the stage value `Y_i` depends only on the previously
computed `Y_0, …, Y_{i-1}`, so the stages can be evaluated by direct
recursion sidestepping the fixed-point machinery required for general
(implicit) methods.

This predicate is a Lean-internal helper, not a textbook entity:
Butcher §530 uses the explicit/implicit distinction implicitly when
discussing methods like classical RK4, but does not name a separate
predicate. -/
def GeneralizedRungeKuttaMethod.IsExplicit
    {s : ℕ} (M : GeneralizedRungeKuttaMethod s) : Prop :=
  ∀ i j : Fin s, i.val ≤ j.val → M.A i j = 0

/-! #### Positive witness (vacuous): trivial 1-stage method

`trivialGeneralizedRK` has `A = !![0]`, so it is trivially explicit. -/

/-- **Non-vacuity (positive direction): the trivial 1-stage method is
explicit.** Vacuous case at `s = 1`: the only matrix entry is `A 0 0`,
which is zero in `trivialGeneralizedRK`. -/
theorem trivialGeneralizedRK_isExplicit :
    trivialGeneralizedRK.IsExplicit := by
  intro i j _
  fin_cases i; fin_cases j
  rfl

/-! #### Positive witness (non-vacuous): Heun-style 2-stage explicit method

`explicit2StageGRK` has `A = !![0, 0; 1, 0]`, with a non-trivial
strict-lower entry at `(1, 0)`. This shows `IsExplicit` admits methods
whose `A`-matrix is not identically zero — the Heun-style coupling
that distinguishes a real explicit method from the vacuous trivial
one. -/

/-- A 2-stage explicit generalized Runge–Kutta tableau with
`A = !![0, 0; 1, 0]` (Heun-style strict-lower-triangular coupling),
`b₀ = 0, b = ![1/2, 1/2], c = ![0, 1]`. The non-zero entry `A 1 0 = 1`
witnesses that `IsExplicit` does not collapse to "the matrix is zero":
a genuine non-vacuous explicit method. -/
noncomputable def explicit2StageGRK : GeneralizedRungeKuttaMethod 2 where
  c := ![0, 1]
  A := !![0, 0; 1, 0]
  b₀ := 0
  b := ![1/2, 1/2]

/-- **Non-vacuity (positive direction, non-vacuous): the Heun-style
2-stage method is explicit.** The strict-lower-triangular shape
`A = !![0, 0; 1, 0]` satisfies `A i j = 0` for all `i ≤ j`. -/
theorem explicit2StageGRK_isExplicit :
    explicit2StageGRK.IsExplicit := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [explicit2StageGRK]

/-! #### Negative witness: 2-stage implicit method

`implicit2StageGRK` has a non-zero diagonal entry `A 0 0 = 1/2`, so it
violates `IsExplicit`. Witnesses non-vacuity in the negative direction:
the predicate is genuinely refutable. -/

/-- A 2-stage *implicit* generalized Runge–Kutta tableau with
`A = !![1/2, 0; 0, 1/2]` (a non-zero diagonal, so the stage equations
are coupled fixed-point equations). Witnesses non-vacuity of the
*negation* of `IsExplicit`. -/
noncomputable def implicit2StageGRK : GeneralizedRungeKuttaMethod 2 where
  c := ![0, 0]
  A := !![1/2, 0; 0, 1/2]
  b₀ := 0
  b := ![1/2, 1/2]

/-- **Non-vacuity (negative direction): an implicit method is not
explicit.** `implicit2StageGRK` has `A 0 0 = 1/2 ≠ 0`, so it fails the
strict-lower-triangular condition at `(0, 0)`. Together with
`trivialGeneralizedRK_isExplicit` and `explicit2StageGRK_isExplicit`,
this confirms the explicit/implicit dichotomy is non-trivial. -/
theorem implicit2StageGRK_not_isExplicit :
    ¬ implicit2StageGRK.IsExplicit := by
  intro h
  have h00 := h ⟨0, by omega⟩ ⟨0, by omega⟩ (le_refl _)
  simp [implicit2StageGRK] at h00

/-! ### Stage-value recursion for explicit generalized RK methods
(cycle 152, def:530B Path A Step 2)

For an explicit generalized Runge–Kutta method `M = (c, A, b₀, b)`
with strict-lower-triangular `A`, the stage equations
`Y_j = b₀·y₀ + h·Σ_k A_{jk}·f(Y_k)` collapse from a fixed-point
system to a direct recursion in the stage index `j`: the `k ≥ j`
terms vanish (since `A j k = 0` there), so each `Y_j` depends only on
`Y_0, …, Y_{j-1}`.

The body of `explicitStageValue` does **not** require `IsExplicit`:
the recursion sums only over `k < j` regardless of `A`'s shape. The
hypothesis is needed downstream when proving this matches the
textbook's full-range stage equation form. The Lean-internal helper
operators in this section are NOT textbook entities — they are the
faithful encoding of the canonical stage-value/output formulae. -/

/-- Stage value `Y_j = b₀ · y₀ + h · Σ_{k < j} A_{jk} · f(Y_k)` of a
generalized Runge–Kutta method, defined by direct recursion on the
stage index `j` (well-founded on `j.val`, since each recursive call
sums only over `Fin j.val` whose elements are strictly less than `j.val`).

For an *explicit* method (strict-lower-triangular `A`), this matches
the textbook stage equation `Y_j = b₀·y₀ + h·Σ_k A_{jk}·f(Y_k)` since
the omitted `k ≥ j` terms have `A_{jk} = 0`. Internal helper for
`def:530B`; not a textbook entity. -/
noncomputable def GeneralizedRungeKuttaMethod.explicitStageValue
    {s : ℕ} (M : GeneralizedRungeKuttaMethod s)
    (f : ℝ → ℝ) (y₀ h : ℝ) (j : Fin s) : ℝ :=
  M.b₀ * y₀ + h * ∑ k : Fin j.val,
    M.A j ⟨k.val, by omega⟩
      * f (M.explicitStageValue f y₀ h ⟨k.val, by omega⟩)
termination_by j.val
decreasing_by exact k.isLt

/-- Scalar output of one application of an explicit generalized
Runge–Kutta method to scalar `y₀` with step `h`:
`S(y₀, h) = b₀ · y₀ + h · Σ_j b_j · f(Y_j)`,
where `Y_j` are computed by `explicitStageValue`. Internal helper for
`def:530B`; not a textbook entity. -/
noncomputable def GeneralizedRungeKuttaMethod.explicitApply
    {s : ℕ} (M : GeneralizedRungeKuttaMethod s)
    (f : ℝ → ℝ) (y₀ h : ℝ) : ℝ :=
  M.b₀ * y₀ + h * ∑ j : Fin s, M.b j * f (M.explicitStageValue f y₀ h j)

/-- For each constituent method `S_i` of a starting method `S`,
compute the scalar output of `S_i` applied to `y₀` with step `h` via
`GeneralizedRungeKuttaMethod.explicitApply`. Produces the
`Fin r → ℝ` initial-input vector consumed by the GLM step in
`applyStartingThenStep_explicit`. Internal helper for `def:530B`; not
a textbook entity. -/
noncomputable def StartingMethod.applyExplicit
    {r : ℕ} (S : StartingMethod r)
    (f : ℝ → ℝ) (y₀ h : ℝ) : Fin r → ℝ :=
  fun i => (S.method i).explicitApply f y₀ h

/-- Textbook `ES(y₀, h)` operator (Butcher §530, def:530B): advance
the exact solution `yex` by `h`, then apply each constituent `S_i`
to that scalar. Returns a `Fin r → ℝ` vector of starting-method
outputs. The `IsExplicit` hypothesis on every `S_i` marks this as
the "explicit-only" variant per `def_530B_scaffold_strategy.md`; it
is unused in the body (the recursion in `explicitStageValue` sums
only over earlier stages regardless of `A`'s shape), but downstream
order-condition proofs (cycle 153 `HasOrderRelativeTo_explicit`) will
consume the hypothesis. -/
noncomputable def applyExactThenStarting_explicit
    {r : ℕ} (S : StartingMethod r)
    (_hS : ∀ i, (S.method i).IsExplicit)
    (f : ℝ → ℝ) (yex : ℝ → ℝ) (x₀ h : ℝ) : Fin r → ℝ :=
  S.applyExplicit f (yex (x₀ + h)) h

/-! ### Non-vacuity sanity computations -/

/-- The `Fin 0` summation in the stage recursion at `j = 0` is empty,
so the stage value of any 1-stage method on its zeroth (and only)
stage reduces to `b₀ · y₀`. Helper lemma decomposing the cycle 152
sanity computations. -/
private lemma explicitStageValue_zero_of_one_stage
    (M : GeneralizedRungeKuttaMethod 1) (f : ℝ → ℝ) (y₀ h : ℝ) :
    M.explicitStageValue f y₀ h 0 = M.b₀ * y₀ := by
  rw [GeneralizedRungeKuttaMethod.explicitStageValue]
  simp

/-- For `trivialGeneralizedRK` the stage value at `j = 0` is just
`y₀`, since `b₀ = 1`. -/
private lemma trivialGeneralizedRK_explicitStageValue_zero
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    trivialGeneralizedRK.explicitStageValue f y₀ h 0 = y₀ := by
  rw [explicitStageValue_zero_of_one_stage]
  show (1 : ℝ) * y₀ = y₀
  ring

/-- For `trivialGeneralizedRK`, `explicitApply` reduces to one
explicit-Euler step `y₀ + h · f(y₀)`. -/
private lemma trivialGeneralizedRK_explicitApply
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    trivialGeneralizedRK.explicitApply f y₀ h = y₀ + h * f y₀ := by
  unfold GeneralizedRungeKuttaMethod.explicitApply
  rw [Fin.sum_univ_one, trivialGeneralizedRK_explicitStageValue_zero]
  show (trivialGeneralizedRK.b₀) * y₀
        + h * (trivialGeneralizedRK.b 0 * f y₀)
      = y₀ + h * f y₀
  show (1 : ℝ) * y₀ + h * ((1 : ℝ) * f y₀) = y₀ + h * f y₀
  ring

/-- **Non-vacuity sanity (`SE` operator on the trivial 1-stage
explicit method):** for the trivial starting method (`r = 1, b₀ = 1,
b = 1, A = 0`), `applyExplicit` reduces to `y₀ + h · f(y₀)`, i.e. one
step of explicit Euler. -/
theorem trivialStartingMethod_applyExplicit
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    trivialStartingMethod.applyExplicit f y₀ h
      = fun (_ : Fin 1) => y₀ + h * f y₀ := by
  funext i
  fin_cases i
  show trivialGeneralizedRK.explicitApply f y₀ h = y₀ + h * f y₀
  exact trivialGeneralizedRK_explicitApply f y₀ h

/-- **Non-vacuity sanity (`ES` operator):** with the trivial starting
method (whose single constituent is explicit), advancing the exact
solution `yex` by `h` then applying `S` produces
`yex(x₀ + h) + h · f(yex(x₀ + h))`, i.e. one step of explicit Euler
launched from the time-`h` exact value. -/
theorem trivialStartingMethod_applyExactThenStarting_explicit
    (f : ℝ → ℝ) (yex : ℝ → ℝ) (x₀ h : ℝ) :
    applyExactThenStarting_explicit trivialStartingMethod
        (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)
        f yex x₀ h
      = fun (_ : Fin 1) => yex (x₀ + h) + h * f (yex (x₀ + h)) := by
  unfold applyExactThenStarting_explicit
  rw [trivialStartingMethod_applyExplicit]

end OpenMath.Chapter5.Section530

/-! ### Explicit general linear methods + the `SM` operator
(cycle 152, def:530B Path A Step 2e)

This sub-section bundles a parallel `IsExplicit` predicate for GLMs
(strict-lower-triangular `A`-block) with the textbook `SM(y₀, h)`
operator: apply each `S_i` to `y₀` to produce the input vector, then
take one `M`-step. The recursion machinery mirrors
`GeneralizedRungeKuttaMethod.explicitStageValue` exactly.

The `IsExplicit` hypotheses are not used in the recursion bodies (the
sums in `explicitStageValue` only ever reference earlier stages
regardless of `A`'s shape). They mark this as the "explicit-only"
variant per `def_530B_scaffold_strategy.md` and will be consumed
downstream when proving the textbook-form stage equations from these
recursion-form bodies. -/

namespace OpenMath.Chapter5.Section510.GeneralLinearMethod

open Matrix

/-- **Explicitness predicate for general linear methods.** A GLM is
*explicit* if its internal-stage matrix `A` is strictly lower
triangular: `A i j = 0` whenever `i ≤ j`. Internal helper for
def:530B; not a textbook entity. The textbook discusses
explicit/implicit GLMs implicitly but does not name a predicate. -/
def IsExplicit {s r : ℕ}
    (M : OpenMath.Chapter5.Section510.GeneralLinearMethod s r) : Prop :=
  ∀ i j : Fin s, i.val ≤ j.val → M.A i j = 0

/-- The GLM internal stage value `Y_i = (M.U *ᵥ y_input) i + h ·
Σ_{k < i} M.A_{ik} · f(Y_k)`, defined by direct recursion on `i.val`.
Mirrors `GeneralizedRungeKuttaMethod.explicitStageValue`. Internal
helper for def:530B; not a textbook entity. -/
noncomputable def explicitStageValue {s r : ℕ}
    (M : OpenMath.Chapter5.Section510.GeneralLinearMethod s r)
    (f : ℝ → ℝ) (y_input : Fin r → ℝ) (h : ℝ) (i : Fin s) : ℝ :=
  (M.U *ᵥ y_input) i + h * ∑ k : Fin i.val,
    M.A i ⟨k.val, by omega⟩
      * f (M.explicitStageValue f y_input h ⟨k.val, by omega⟩)
termination_by i.val
decreasing_by exact k.isLt

end OpenMath.Chapter5.Section510.GeneralLinearMethod

namespace OpenMath.Chapter5.Section530

open Matrix
open OpenMath.Chapter5.Section510

/-- Textbook `SM(y₀, h)` operator (Butcher §530, def:530B): apply each
constituent `S_i` to `y₀` to produce the initial-input
`Fin r → ℝ` vector `y_input`, then take one `M`-step. The output
vector is `y_new[ℓ] = h · Σ_i M.B_{ℓi} · f(Y_i) + (M.V *ᵥ y_input) ℓ`,
where the internal stages `Y_i` are computed by
`GeneralLinearMethod.explicitStageValue`. The `IsExplicit`
hypotheses on `S` and `M` mark this as the "explicit-only" variant
per `def_530B_scaffold_strategy.md`; they are unused in the body but
will be consumed by downstream order-condition proofs. -/
noncomputable def applyStartingThenStep_explicit
    {s r : ℕ}
    (M : GeneralLinearMethod s r)
    (S : StartingMethod r)
    (_hS : ∀ i, (S.method i).IsExplicit)
    (_hM : M.IsExplicit)
    (f : ℝ → ℝ) (y₀ h : ℝ) : Fin r → ℝ :=
  let y_input := S.applyExplicit f y₀ h
  fun ℓ =>
    h * ∑ i : Fin s, M.B ℓ i * f (M.explicitStageValue f y_input h i)
      + (M.V *ᵥ y_input) ℓ

/-- **Non-vacuity (positive direction): explicit Euler GLM is
explicit.** The 1×1 `A`-block `!![0]` is vacuously strict-lower
triangular at `s = 1`. -/
theorem explicitEulerGLM_isExplicit : explicitEulerGLM.IsExplicit := by
  intro i j _
  fin_cases i; fin_cases j
  rfl

/-! ### Order relative to a starting method (cycle 153, def:530B Path A Step 3)

Definition 530B (Butcher §530, p. 432) classifies a general linear method
`M` as having *order `p` relative to* a (non-degenerate) starting method
`S` if `SM(y₀, h)` and `ES(y₀, h)` agree to within `O(h^{p+1})` as `h →
0`. The textbook definition allows `M` to be implicit; we restrict to
the explicit branch (Path A of `def_530B_scaffold_strategy.md`) so that
the operators `applyStartingThenStep_explicit` and
`applyExactThenStarting_explicit` (cycle 152) close without requiring
fixed-point machinery. The implicit Path B variant remains future work.

The `p = 0` non-vacuity witness `explicitEulerGLM_hasOrderZero_trivialStarting`
demonstrates that the predicate admits at least one substantive solution
under natural IVP hypotheses (Lipschitz `f`, exact-solution derivative
`yex' = f y₀` at `x₀`, initial value matched). -/

section OrderRelativeTo

open Asymptotics Filter

/-- **Definition 530B (Butcher §530, p. 432) — explicit-only variant.**
A general linear method `M` has *order `p`* relative to a (non-degenerate)
starting method `S` (with both `M` and every `S_i` explicit) at the
initial value problem `(f, x₀, y₀, yex)` if the difference between the
two `Fin r`-vectors

  * `SM(y₀, h)` =
    `applyStartingThenStep_explicit M S hS hM f y₀ h`
  * `ES(y₀, h)` =
    `applyExactThenStarting_explicit S hS f yex x₀ h`

is `O(h^{p+1})` componentwise as `h → 0`.

Internal helper for the explicit-only branch of def:530B per
`def_530B_scaffold_strategy.md`. The Path-B implicit variant via
fixed-point machinery remains deferred.

`HasOrderRelativeTo_explicit` does **not** itself impose
non-degeneracy of `S`; downstream consumers should pair it with an
explicit `S.IsNonDegenerate` hypothesis where needed. -/
def HasOrderRelativeTo_explicit
    {s r : ℕ}
    (M : OpenMath.Chapter5.Section510.GeneralLinearMethod s r)
    (S : StartingMethod r)
    (hS : ∀ i, (S.method i).IsExplicit)
    (hM : M.IsExplicit)
    (p : ℕ)
    (f : ℝ → ℝ) (yex : ℝ → ℝ) (x₀ y₀ : ℝ) : Prop :=
  ∀ i : Fin r,
    (fun h : ℝ =>
        applyStartingThenStep_explicit M S hS hM f y₀ h i
          - applyExactThenStarting_explicit S hS f yex x₀ h i)
      =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (p + 1))

/-- **Non-vacuity (Path A Step 3, p = 0).** The explicit Euler GLM has
order `0` relative to the trivial starting method on any IVP whose exact
solution `yex` satisfies `yex x₀ = y₀` and `HasDerivAt yex (f y₀) x₀`,
with `f` Lipschitz with constant `L`.

Witnesses that `HasOrderRelativeTo_explicit` is genuinely satisfiable on
the most degenerate non-trivial GLM × starting-method shape
`(s, r) = (1, 1)`. The `p = 0` claim corresponds to `O(h)` agreement
between SM and ES (the textbook classifies explicit Euler as order 1
relative to the canonical starting method, but proving `p = 1` requires
a `ContDiff ℝ 2 yex` hypothesis and a second-order Taylor expansion;
that refinement is deferred to a future cycle). -/
theorem explicitEulerGLM_hasOrderZero_trivialStarting
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_deriv : HasDerivAt yex (f y₀) x₀) :
    HasOrderRelativeTo_explicit explicitEulerGLM trivialStartingMethod
      (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)
      explicitEulerGLM_isExplicit
      0 f yex x₀ y₀ := by
  intro i
  fin_cases i
  -- Canonicalize the goal so that `i = 0 : Fin 1` is in the application form
  -- expected by the closed-form lemmas below.
  change (fun h : ℝ =>
        applyStartingThenStep_explicit explicitEulerGLM trivialStartingMethod
            (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)
            explicitEulerGLM_isExplicit f y₀ h 0
          - applyExactThenStarting_explicit trivialStartingMethod
              (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)
              f yex x₀ h 0)
      =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (0 + 1))
  -- Step 1a: SM[0] closed form
  have hSM : ∀ h : ℝ,
      applyStartingThenStep_explicit explicitEulerGLM trivialStartingMethod
          (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)
          explicitEulerGLM_isExplicit f y₀ h 0
        = (y₀ + h * f y₀) + h * f (y₀ + h * f y₀) := by
    intro h
    show (h * ∑ i : Fin 1,
        explicitEulerGLM.B 0 i
          * f (explicitEulerGLM.explicitStageValue f
                  (trivialStartingMethod.applyExplicit f y₀ h) h i))
        + (explicitEulerGLM.V *ᵥ trivialStartingMethod.applyExplicit f y₀ h) 0
        = _
    rw [trivialStartingMethod_applyExplicit]
    unfold OpenMath.Chapter5.Section510.GeneralLinearMethod.explicitStageValue
    simp [explicitEulerGLM, Matrix.mulVec, dotProduct]
    ring
  -- Step 1b: ES[0] closed form (cycle 152 sanity lemma)
  have hES : ∀ h : ℝ,
      applyExactThenStarting_explicit trivialStartingMethod
          (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)
          f yex x₀ h 0
        = yex (x₀ + h) + h * f (yex (x₀ + h)) := by
    intro h
    rw [trivialStartingMethod_applyExactThenStarting_explicit]
  -- Step 2: rewrite the difference into closed form
  have hcongr :
      (fun h : ℝ =>
          applyStartingThenStep_explicit explicitEulerGLM trivialStartingMethod
              (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)
              explicitEulerGLM_isExplicit f y₀ h 0
            - applyExactThenStarting_explicit trivialStartingMethod
                (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)
                f yex x₀ h 0)
        = (fun h : ℝ =>
            ((y₀ + h * f y₀) - yex (x₀ + h))
              + h * (f (y₀ + h * f y₀) - f (yex (x₀ + h)))) := by
    funext h
    rw [hSM, hES]
    ring
  rw [hcongr]
  -- Collapse `h ^ (0 + 1)` to `h`.
  have hpow : (fun h : ℝ => h ^ (0 + 1)) = (fun h : ℝ => h) := by
    funext h; simp
  rw [hpow]
  -- Step 3: T1 = (y₀ + h·f y₀) - yex(x₀+h) is o(h), hence O(h).
  have hT1 : (fun h : ℝ => (y₀ + h * f y₀) - yex (x₀ + h))
      =O[nhds (0 : ℝ)] (fun h => h) := by
    have hderiv :
        (fun h : ℝ => yex (x₀ + h) - yex x₀ - h • f y₀)
          =o[nhds (0 : ℝ)] fun h => h :=
      hasDerivAt_iff_isLittleO_nhds_zero.mp hyex_deriv
    have h1 : (fun h : ℝ => yex (x₀ + h) - y₀ - h * f y₀)
        =o[nhds (0 : ℝ)] fun h => h := by
      have := hderiv
      rw [hyex_x₀] at this
      simpa [smul_eq_mul] using this
    have h2 : (fun h : ℝ => (y₀ + h * f y₀) - yex (x₀ + h))
        =o[nhds (0 : ℝ)] fun h => h := by
      have := h1.neg_left
      refine this.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
      exact Filter.Eventually.of_forall fun h => by ring
    exact h2.isBigO
  -- Step 4: T2 = h * (f(y₀ + h·f y₀) - f(yex(x₀+h))) is O(h) via Lipschitz.
  have hT2 : (fun h : ℝ => h * (f (y₀ + h * f y₀) - f (yex (x₀ + h))))
      =O[nhds (0 : ℝ)] (fun h => h) := by
    -- The pointwise bound `|h * (f a - f b)| ≤ L * |h|` holds whenever
    -- `|y₀ + h·f y₀ - yex(x₀+h)| ≤ 1`.  Both sides of the diff tend to
    -- `y₀` as `h → 0`, so the difference tends to `0`, i.e. is eventually
    -- bounded by `1` near `h = 0`.
    have hcontA : ContinuousAt (fun h : ℝ => y₀ + h * f y₀) 0 := by
      exact (continuous_const.add (continuous_id.mul continuous_const)).continuousAt
    have hcontB : ContinuousAt (fun h : ℝ => yex (x₀ + h)) 0 := by
      have h_inner : ContinuousAt (fun h : ℝ => x₀ + h) 0 :=
        (continuous_const.add continuous_id).continuousAt
      have h_outer : ContinuousAt yex ((fun h : ℝ => x₀ + h) 0) := by
        simpa using hyex_deriv.continuousAt
      exact h_outer.comp h_inner
    have hdiff_tendsto :
        Tendsto (fun h : ℝ => y₀ + h * f y₀ - yex (x₀ + h))
          (nhds 0) (nhds 0) := by
      have htend : Tendsto (fun h : ℝ => y₀ + h * f y₀ - yex (x₀ + h))
          (nhds 0) (nhds (y₀ + (0 : ℝ) * f y₀ - yex (x₀ + 0))) :=
        (hcontA.sub hcontB).tendsto
      have h0 : y₀ + (0 : ℝ) * f y₀ - yex (x₀ + 0) = 0 := by simp [hyex_x₀]
      rw [h0] at htend
      exact htend
    have hbound : ∀ᶠ h : ℝ in nhds 0,
        |y₀ + h * f y₀ - yex (x₀ + h)| < 1 := by
      have hone : (0 : ℝ) < 1 := by norm_num
      have h_in := (Metric.tendsto_nhds.mp hdiff_tendsto) 1 hone
      filter_upwards [h_in] with h hh
      rw [Real.dist_0_eq_abs] at hh
      exact hh
    refine .of_bound (↑L) ?_
    filter_upwards [hbound] with h hh
    have hlip := hf_lip.dist_le_mul (y₀ + h * f y₀) (yex (x₀ + h))
    rw [Real.dist_eq, Real.dist_eq] at hlip
    have hLnn : (0 : ℝ) ≤ L := L.coe_nonneg
    have habsh : (0 : ℝ) ≤ |h| := abs_nonneg _
    calc ‖h * (f (y₀ + h * f y₀) - f (yex (x₀ + h)))‖
        = |h| * |f (y₀ + h * f y₀) - f (yex (x₀ + h))| := by
          rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |h| * (↑L * |y₀ + h * f y₀ - yex (x₀ + h)|) :=
          mul_le_mul_of_nonneg_left hlip habsh
      _ ≤ |h| * (↑L * 1) := by
          have hh' : |y₀ + h * f y₀ - yex (x₀ + h)| ≤ 1 := hh.le
          have : ↑L * |y₀ + h * f y₀ - yex (x₀ + h)| ≤ ↑L * 1 :=
            mul_le_mul_of_nonneg_left hh' hLnn
          exact mul_le_mul_of_nonneg_left this habsh
      _ = ↑L * ‖h‖ := by rw [Real.norm_eq_abs]; ring
  -- Step 5: combine
  exact hT1.add hT2

/-- **Non-vacuity (Path A Step 4, p = 1).** The explicit Euler GLM has
order `1` relative to the trivial starting method on any IVP whose
exact solution `yex` is `C²`, satisfies `yex x₀ = y₀`, and obeys the
genuine ODE relation `∀ x, HasDerivAt yex (f (yex x)) x`, with `f`
Lipschitz with constant `L`.

This refines `explicitEulerGLM_hasOrderZero_trivialStarting` (cycle
153, `p = 0`) by upgrading the conclusion from `O(h)` to `O(h²)`. The
extra hypotheses (`ContDiff ℝ 2 yex` and the full ODE relation,
versus cycle 153's bare `HasDerivAt yex (f y₀) x₀`) are needed for the
second-order Taylor expansion that produces the `O(h²)` bound, and
remain well within Butcher's implicit "exact solution sufficiently
regular" assumption (Butcher §531 classifies explicit Euler as a
method of order `1`).

Proof structure: decompose `SM[0] - ES[0]` into
* `T1 := (y₀ + h·f y₀) - yex(x₀+h)` — bounded `O(h²)` via the
  second-order Taylor remainder lemma `taylor_isLittleO_univ` applied
  to `yex` (using `ContDiff ℝ 2`), composed with the translation
  `h ↦ x₀ + h`.
* `T2 := h · (f(y₀ + h·f y₀) - f(yex(x₀+h)))` — bounded `O(h²)` via
  Lipschitz on `f` (the inner difference is `−T1`, hence already
  `O(h²)`; multiplying by `|h|` produces `O(h³)`, which is `O(h²)`
  near `0` because `|h|³ ≤ h²` whenever `|h| ≤ 1`). -/
theorem explicitEulerGLM_hasOrderOne_trivialStarting
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C2 : ContDiff ℝ 2 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    HasOrderRelativeTo_explicit explicitEulerGLM trivialStartingMethod
      (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)
      explicitEulerGLM_isExplicit
      1 f yex x₀ y₀ := by
  intro i
  fin_cases i
  -- Canonicalize the goal so that `i = 0 : Fin 1` is in the application form
  -- expected by the closed-form lemmas below.
  change (fun h : ℝ =>
        applyStartingThenStep_explicit explicitEulerGLM trivialStartingMethod
            (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)
            explicitEulerGLM_isExplicit f y₀ h 0
          - applyExactThenStarting_explicit trivialStartingMethod
              (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)
              f yex x₀ h 0)
      =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (1 + 1))
  -- Step 1a: SM[0] closed form (cycle 153 derivation)
  have hSM : ∀ h : ℝ,
      applyStartingThenStep_explicit explicitEulerGLM trivialStartingMethod
          (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)
          explicitEulerGLM_isExplicit f y₀ h 0
        = (y₀ + h * f y₀) + h * f (y₀ + h * f y₀) := by
    intro h
    show (h * ∑ i : Fin 1,
        explicitEulerGLM.B 0 i
          * f (explicitEulerGLM.explicitStageValue f
                  (trivialStartingMethod.applyExplicit f y₀ h) h i))
        + (explicitEulerGLM.V *ᵥ trivialStartingMethod.applyExplicit f y₀ h) 0
        = _
    rw [trivialStartingMethod_applyExplicit]
    unfold OpenMath.Chapter5.Section510.GeneralLinearMethod.explicitStageValue
    simp [explicitEulerGLM, Matrix.mulVec, dotProduct]
    ring
  -- Step 1b: ES[0] closed form
  have hES : ∀ h : ℝ,
      applyExactThenStarting_explicit trivialStartingMethod
          (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)
          f yex x₀ h 0
        = yex (x₀ + h) + h * f (yex (x₀ + h)) := by
    intro h
    rw [trivialStartingMethod_applyExactThenStarting_explicit]
  -- Step 2: rewrite the difference into closed form
  have hcongr :
      (fun h : ℝ =>
          applyStartingThenStep_explicit explicitEulerGLM trivialStartingMethod
              (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)
              explicitEulerGLM_isExplicit f y₀ h 0
            - applyExactThenStarting_explicit trivialStartingMethod
                (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)
                f yex x₀ h 0)
        = (fun h : ℝ =>
            ((y₀ + h * f y₀) - yex (x₀ + h))
              + h * (f (y₀ + h * f y₀) - f (yex (x₀ + h)))) := by
    funext h
    rw [hSM, hES]
    ring
  rw [hcongr]
  -- Collapse `h ^ (1 + 1)` to `h ^ 2`.
  have hpow : (fun h : ℝ => h ^ (1 + 1)) = (fun h : ℝ => h ^ 2) := by
    funext h; ring
  rw [hpow]
  -- Step 3: T1 = (y₀ + h·f y₀) - yex(x₀+h) is O(h²) via 2nd-order Taylor.
  have hT1 : (fun h : ℝ => (y₀ + h * f y₀) - yex (x₀ + h))
      =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ 2) := by
    -- The 2nd-order Taylor remainder bound: yex - taylor₂(yex) = o((·-x₀)²) near x₀.
    have htaylor :
        (fun x : ℝ => yex x - taylorWithinEval yex 2 Set.univ x₀ x)
          =o[nhds x₀] (fun x : ℝ => (x - x₀) ^ 2) := by
      have h := taylor_isLittleO (n := 2) (f := yex) (x₀ := x₀)
        (s := Set.univ) convex_univ (Set.mem_univ _) hyex_C2.contDiffOn
      simpa [nhdsWithin_univ] using h
    -- Closed form for the 2nd-order Taylor polynomial at the point `x₀ + h`.
    have hT_eval : ∀ h : ℝ,
        taylorWithinEval yex 2 Set.univ x₀ (x₀ + h)
          = yex x₀ + h * iteratedDeriv 1 yex x₀
              + h ^ 2 / 2 * iteratedDeriv 2 yex x₀ := by
      intro h
      rw [taylor_within_apply]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        iteratedDerivWithin_univ, iteratedDeriv_zero, Nat.factorial,
        Nat.cast_one, Nat.cast_mul, smul_eq_mul, pow_zero, pow_one,
        mul_one, one_mul, inv_one]
      ring
    -- The first iterated derivative at x₀ is f y₀ (via the ODE relation).
    have hderiv_x0 : iteratedDeriv 1 yex x₀ = f y₀ := by
      rw [iteratedDeriv_one]
      have h := (hyex_ode x₀).deriv
      rw [hyex_x₀] at h
      exact h
    -- Compose `htaylor` with the translation `h ↦ x₀ + h`.
    have htend : Filter.Tendsto (fun h : ℝ => x₀ + h) (nhds 0) (nhds x₀) := by
      have hcont : Continuous (fun h : ℝ => x₀ + h) :=
        continuous_const.add continuous_id
      simpa using hcont.tendsto 0
    have hres :
        (fun h : ℝ => yex (x₀ + h) - taylorWithinEval yex 2 Set.univ x₀ (x₀ + h))
          =o[nhds (0 : ℝ)] (fun h : ℝ => h ^ 2) := by
      have hcomp := htaylor.comp_tendsto htend
      refine hcomp.congr' (Filter.Eventually.of_forall fun _ => rfl)
        (Filter.Eventually.of_forall fun h => ?_)
      show ((x₀ + h) - x₀) ^ 2 = h ^ 2
      ring
    -- Closed-form decomposition for T1.
    have hT1_eq : (fun h : ℝ => (y₀ + h * f y₀) - yex (x₀ + h))
        = (fun h : ℝ =>
            -(yex (x₀ + h) - taylorWithinEval yex 2 Set.univ x₀ (x₀ + h))
              - h ^ 2 / 2 * iteratedDeriv 2 yex x₀) := by
      funext h
      rw [hT_eval h, hderiv_x0, hyex_x₀]
      ring
    rw [hT1_eq]
    -- The constant-times-h² term is O(h²).
    have hconst : (fun h : ℝ => h ^ 2 / 2 * iteratedDeriv 2 yex x₀)
        =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ 2) := by
      have h0 := Asymptotics.isBigO_const_mul_self
        (iteratedDeriv 2 yex x₀ / 2) (fun h : ℝ => h ^ 2) (nhds 0)
      refine h0.congr' (Filter.Eventually.of_forall fun h => ?_)
        (Filter.Eventually.of_forall fun _ => rfl)
      ring
    -- Combine: -(residual) - (const · h²) is O(h²).
    have hsum := hres.isBigO.add hconst
    refine hsum.neg_left.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
    refine Filter.Eventually.of_forall fun h => ?_
    show -((yex (x₀ + h) - taylorWithinEval yex 2 Set.univ x₀ (x₀ + h))
            + h ^ 2 / 2 * iteratedDeriv 2 yex x₀)
      = -(yex (x₀ + h) - taylorWithinEval yex 2 Set.univ x₀ (x₀ + h))
        - h ^ 2 / 2 * iteratedDeriv 2 yex x₀
    ring
  -- Step 4: T2 = h * (f(y₀+h·f y₀) - f(yex(x₀+h))) is O(h²) via Lipschitz + T1.
  have hT2 : (fun h : ℝ => h * (f (y₀ + h * f y₀) - f (yex (x₀ + h))))
      =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ 2) := by
    -- Extract a positive constant C with ‖T1(h)‖ ≤ C * ‖h²‖ eventually.
    obtain ⟨C, hCpos, hC⟩ := hT1.exists_pos
    rw [Asymptotics.isBigOWith_iff] at hC
    -- Eventual bound `|h| ≤ 1` near 0.
    have hh1 : ∀ᶠ h : ℝ in nhds 0, |h| ≤ 1 := by
      refine Filter.eventually_iff_exists_mem.mpr
        ⟨Set.Ioo (-1 : ℝ) 1, IsOpen.mem_nhds isOpen_Ioo (by norm_num),
         fun h hh => ?_⟩
      exact abs_le.mpr ⟨hh.1.le, hh.2.le⟩
    refine Asymptotics.IsBigO.of_bound (↑L * C) ?_
    filter_upwards [hC, hh1] with h hT1bound hh1bound
    -- Goal: ‖h * (f a - f b)‖ ≤ ↑L * C * ‖h^2‖
    have hLnn : (0 : ℝ) ≤ ↑L := L.coe_nonneg
    have habsh : (0 : ℝ) ≤ |h| := abs_nonneg _
    have hCnn : (0 : ℝ) ≤ C := hCpos.le
    -- Lipschitz bound on |f a - f b|.
    have hlip := hf_lip.dist_le_mul (y₀ + h * f y₀) (yex (x₀ + h))
    rw [Real.dist_eq, Real.dist_eq] at hlip
    -- Rewrite |a - b| = |-T1(h)| = |T1(h)|.
    have hab_eq : |y₀ + h * f y₀ - yex (x₀ + h)|
        = |(y₀ + h * f y₀) - yex (x₀ + h)| := rfl
    -- Rewrite hC to expose `|T1(h)|`:
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hT1bound
    -- |T1(h)| ≤ C * |h^2|
    -- Combine to bound |h * (f a - f b)|.
    have habsh2 : |h ^ 2| = h ^ 2 := abs_of_nonneg (sq_nonneg h)
    have habsh_sq : |h| ^ 2 = h ^ 2 := sq_abs h
    -- Main calculation.
    calc ‖h * (f (y₀ + h * f y₀) - f (yex (x₀ + h)))‖
        = |h| * |f (y₀ + h * f y₀) - f (yex (x₀ + h))| := by
          rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |h| * (↑L * |y₀ + h * f y₀ - yex (x₀ + h)|) :=
          mul_le_mul_of_nonneg_left hlip habsh
      _ = ↑L * (|h| * |y₀ + h * f y₀ - yex (x₀ + h)|) := by ring
      _ ≤ ↑L * (|h| * (C * |h ^ 2|)) := by
          have := mul_le_mul_of_nonneg_left hT1bound habsh
          exact mul_le_mul_of_nonneg_left this hLnn
      _ = ↑L * C * (|h| * h ^ 2) := by rw [habsh2]; ring
      _ ≤ ↑L * C * (1 * h ^ 2) := by
          have hLC : (0 : ℝ) ≤ ↑L * C := mul_nonneg hLnn hCnn
          have hh2 : (0 : ℝ) ≤ h ^ 2 := sq_nonneg h
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hh1bound hh2) hLC
      _ = ↑L * C * ‖h ^ 2‖ := by rw [Real.norm_eq_abs, habsh2]; ring
  -- Step 5: combine
  exact hT1.add hT2

end OrderRelativeTo

end OpenMath.Chapter5.Section530
