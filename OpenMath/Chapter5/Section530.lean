import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

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

end OpenMath.Chapter5.Section530
