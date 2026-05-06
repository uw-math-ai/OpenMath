import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.MetricSpace.Lipschitz
import OpenMath.Chapter5.Section510
import OpenMath.Chapter5.Section520

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

/-! ### `r = 2` starting method compatible with `padded2DEulerGLM` (cycle 156)

To pair with `padded2DEulerGLM` (whose row 1 of `V` and `B` is zero) for
a `HasOrderRelativeTo_explicit` non-vacuity witness at `r = 2`, we need
a starting method `S : StartingMethod 2` whose row-1 channel is also a
zero channel — i.e. `(S.method 1).b₀ = 0` and `(S.method 1).b = 0`,
making `S.applyExplicit f y h` return `0` at index `1`. The row-0
constituent must still satisfy non-degeneracy, so we take
`trivialGeneralizedRK` (`b₀ = 1`) at index `0`. The pairing
`mixedStartingMethod` does NOT work here: its row-1 constituent
`nontrivialTwoStageGRK` has `b₀ = 2`, breaking the desired
`Diff[1] = 0` reduction.

`padCompatMethod` and `padCompatStartingMethod` are Lean-internal
helpers (not textbook entities) — analogous to `mixedStartingMethod`
and `zeroStartingMethod`. They witness that the heterogeneous-stages
`StartingMethod` design admits non-trivial inhabitants compatible
with `padded2DEulerGLM`. -/

/-- Constituent function for `padCompatStartingMethod`: index `0`
gets `trivialGeneralizedRK` (`b₀ = 1`, exercises the active channel),
index `1` gets `zeroGeneralizedRK` (`b₀ = 0`, witnesses the inactive
channel). Both are 1-stage and explicit. -/
def padCompatMethod : (i : Fin 2) → GeneralizedRungeKuttaMethod 1
  | 0 => trivialGeneralizedRK
  | 1 => zeroGeneralizedRK

/-- A 2-method starting method (`r = 2`) that meshes with
`padded2DEulerGLM`'s zero row-1 channel: row 0 active
(`trivialGeneralizedRK`, `b₀ = 1`), row 1 inactive
(`zeroGeneralizedRK`, `b₀ = 0`). Non-degenerate at index `0`. -/
def padCompatStartingMethod : StartingMethod 2 where
  stages := fun _ => 1
  method := padCompatMethod

/-- **Non-vacuity (cycle 156).** `padCompatStartingMethod` is
non-degenerate via its index-0 constituent (`b₀ = 1 ≠ 0`). -/
theorem padCompatStartingMethod_isNonDegenerate :
    padCompatStartingMethod.IsNonDegenerate := by
  rw [StartingMethod.isNonDegenerate_iff_exists_b₀_ne_zero]
  refine ⟨0, ?_⟩
  show (1 : ℝ) ≠ 0
  exact one_ne_zero

/-- Both constituents of `padCompatStartingMethod` are explicit:
`trivialGeneralizedRK` and `zeroGeneralizedRK` both have the 1×1
zero `A`-block. -/
theorem padCompatStartingMethod_constituents_isExplicit :
    ∀ i : Fin 2, (padCompatStartingMethod.method i).IsExplicit := by
  intro i
  fin_cases i
  · exact trivialGeneralizedRK_isExplicit
  · intro a b _
    fin_cases a; fin_cases b
    rfl

/-- Constituent function for `pad3CompatStartingMethod` (cycle 159):
index `0` gets `trivialGeneralizedRK` (`b₀ = 1`, exercises the active
channel); indices `1` and `2` both get `zeroGeneralizedRK`
(`b₀ = 0`, the inactive zero channels). All three are 1-stage and
explicit. -/
def pad3CompatMethod : (i : Fin 3) → GeneralizedRungeKuttaMethod 1
  | 0 => trivialGeneralizedRK
  | 1 => zeroGeneralizedRK
  | 2 => zeroGeneralizedRK

/-- A 3-method starting method (`r = 3`, cycle 159) that meshes with
`padded3DEulerGLM`'s zero row-1 and row-2 channels: row 0 active
(`trivialGeneralizedRK`, `b₀ = 1`), rows 1 and 2 inactive
(`zeroGeneralizedRK`, `b₀ = 0`). Non-degenerate at index `0`.
Lifts cycle 156's `padCompatStartingMethod` from r = 2 to r = 3. -/
def pad3CompatStartingMethod : StartingMethod 3 where
  stages := fun _ => 1
  method := pad3CompatMethod

/-- **Non-vacuity (cycle 159).** `pad3CompatStartingMethod` is
non-degenerate via its index-0 constituent (`b₀ = 1 ≠ 0`). -/
theorem pad3CompatStartingMethod_isNonDegenerate :
    pad3CompatStartingMethod.IsNonDegenerate := by
  rw [StartingMethod.isNonDegenerate_iff_exists_b₀_ne_zero]
  refine ⟨0, ?_⟩
  show (1 : ℝ) ≠ 0
  exact one_ne_zero

/-- All three constituents of `pad3CompatStartingMethod` are
explicit: `trivialGeneralizedRK` and the two `zeroGeneralizedRK`
copies all have the 1×1 zero `A`-block. -/
theorem pad3CompatStartingMethod_constituents_isExplicit :
    ∀ i : Fin 3, (pad3CompatStartingMethod.method i).IsExplicit := by
  intro i
  fin_cases i
  · exact trivialGeneralizedRK_isExplicit
  · intro a b _
    fin_cases a; fin_cases b
    rfl
  · intro a b _
    fin_cases a; fin_cases b
    rfl

/-- Constituent function for `pad4CompatStartingMethod` (cycle 161):
index `0` gets `trivialGeneralizedRK` (`b₀ = 1`, exercises the active
channel); indices `1`, `2`, and `3` all get `zeroGeneralizedRK`
(`b₀ = 0`, the inactive zero channels). All four are 1-stage and
explicit. -/
def pad4CompatMethod : (i : Fin 4) → GeneralizedRungeKuttaMethod 1
  | 0 => trivialGeneralizedRK
  | 1 => zeroGeneralizedRK
  | 2 => zeroGeneralizedRK
  | 3 => zeroGeneralizedRK

/-- A 4-method starting method (`r = 4`, cycle 161) that meshes with
`padded4DEulerGLM`'s zero row-1, row-2, and row-3 channels: row 0
active (`trivialGeneralizedRK`, `b₀ = 1`), rows 1, 2, 3 inactive
(`zeroGeneralizedRK`, `b₀ = 0`). Non-degenerate at index `0`.
Lifts cycle 159's `pad3CompatStartingMethod` from r = 3 to r = 4. -/
def pad4CompatStartingMethod : StartingMethod 4 where
  stages := fun _ => 1
  method := pad4CompatMethod

/-- **Non-vacuity (cycle 161).** `pad4CompatStartingMethod` is
non-degenerate via its index-0 constituent (`b₀ = 1 ≠ 0`). -/
theorem pad4CompatStartingMethod_isNonDegenerate :
    pad4CompatStartingMethod.IsNonDegenerate := by
  rw [StartingMethod.isNonDegenerate_iff_exists_b₀_ne_zero]
  refine ⟨0, ?_⟩
  show (1 : ℝ) ≠ 0
  exact one_ne_zero

/-- All four constituents of `pad4CompatStartingMethod` are
explicit: `trivialGeneralizedRK` and the three `zeroGeneralizedRK`
copies all have the 1×1 zero `A`-block. -/
theorem pad4CompatStartingMethod_constituents_isExplicit :
    ∀ i : Fin 4, (pad4CompatStartingMethod.method i).IsExplicit := by
  intro i
  fin_cases i
  · exact trivialGeneralizedRK_isExplicit
  · intro a b _
    fin_cases a; fin_cases b
    rfl
  · intro a b _
    fin_cases a; fin_cases b
    rfl
  · intro a b _
    fin_cases a; fin_cases b
    rfl

/-! ### `r + 1`-method parametric starting family (cycle 162 Phase A)

Consolidates cycles 156/159/161's three hand-written `padCompat`
families into a single parametric family
`padCompatStartingMethodR (r : ℕ) : StartingMethod (r + 1)`. Index 0
gets the active `trivialGeneralizedRK` channel (`b₀ = 1`); indices
`1, …, r` are passively-decoupled `zeroGeneralizedRK` channels
(`b₀ = 0`). All `r + 1` constituents are 1-stage and explicit.

Pairs with the parametric `paddedREulerGLM r` (Section520) for the
parametric `r + 1` non-vacuity witnesses for `def:530B` and
`def:530C`. The witnesses (`HasOrderRelativeTo_explicit`) themselves
are deferred to cycle 163 Phase B.1. -/

/-- Constituent function for `padCompatStartingMethodR r` (cycle 162
Phase A): index `0` gets `trivialGeneralizedRK` (`b₀ = 1`,
exercises the active channel); indices `1, …, r` all get
`zeroGeneralizedRK` (`b₀ = 0`, the inactive zero channels).
Conceptually specialises to the existing hand-written
`padCompatMethod`/`pad3CompatMethod`/`pad4CompatMethod`
constituents at `r ∈ {1, 2, 3}`. -/
noncomputable def padCompatMethodR (r : ℕ) :
    Fin (r + 1) → GeneralizedRungeKuttaMethod 1 :=
  fun i => if i.val = 0 then trivialGeneralizedRK else zeroGeneralizedRK

/-- An `r + 1`-method starting method (cycle 162 Phase A) compatible
with `paddedREulerGLM r`'s zero row-`{1, …, r}` channels: row 0
active (`trivialGeneralizedRK`, `b₀ = 1`), rows `1, …, r` inactive
(`zeroGeneralizedRK`, `b₀ = 0`). Non-degenerate at index `0`.
Conceptually specialises to the existing hand-written
`padCompatStartingMethod`/`pad3CompatStartingMethod`/
`pad4CompatStartingMethod` at `r ∈ {1, 2, 3}`. Reconciliation
lemmas deferred to cycle 163 Phase B.3. -/
noncomputable def padCompatStartingMethodR (r : ℕ) :
    StartingMethod (r + 1) where
  stages := fun _ => 1
  method := padCompatMethodR r

/-- **Non-vacuity (cycle 162 Phase A).** `padCompatStartingMethodR r`
is non-degenerate via its index-0 constituent (`b₀ = 1 ≠ 0`).
Generalises cycles 156/159/161's `padCompatStartingMethod_isNonDegenerate`,
`pad3CompatStartingMethod_isNonDegenerate`,
`pad4CompatStartingMethod_isNonDegenerate` to all `r ≥ 0`. -/
theorem padCompatStartingMethodR_isNonDegenerate (r : ℕ) :
    (padCompatStartingMethodR r).IsNonDegenerate := by
  rw [StartingMethod.isNonDegenerate_iff_exists_b₀_ne_zero]
  refine ⟨⟨0, Nat.succ_pos r⟩, ?_⟩
  unfold padCompatStartingMethodR padCompatMethodR
  simp
  show (1 : ℝ) ≠ 0
  exact one_ne_zero

/-- All `r + 1` constituents of `padCompatStartingMethodR r` are
explicit: `trivialGeneralizedRK` and `zeroGeneralizedRK` both have
the 1×1 zero `A`-block. Generalises cycles 156/159/161's
`padCompatStartingMethod_constituents_isExplicit`,
`pad3CompatStartingMethod_constituents_isExplicit`,
`pad4CompatStartingMethod_constituents_isExplicit` to all
`r ≥ 0`. -/
theorem padCompatStartingMethodR_constituents_isExplicit (r : ℕ) :
    ∀ i : Fin (r + 1),
      ((padCompatStartingMethodR r).method i).IsExplicit := by
  intro i
  show (padCompatMethodR r i).IsExplicit
  unfold padCompatMethodR
  by_cases hi : i.val = 0
  · simp [hi]
    exact trivialGeneralizedRK_isExplicit
  · simp [hi]
    intro a b _
    fin_cases a; fin_cases b
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

/-- For `zeroGeneralizedRK` (with `b₀ = 0` and `b = 0`),
`explicitApply` reduces to the constant `0`, regardless of `f, y₀, h`.
Cycle 156 helper for the `r = 2` non-vacuity witness's row-1 channel
collapse. -/
private lemma zeroGeneralizedRK_explicitApply
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    zeroGeneralizedRK.explicitApply f y₀ h = 0 := by
  unfold GeneralizedRungeKuttaMethod.explicitApply
  rw [Fin.sum_univ_one]
  show (zeroGeneralizedRK.b₀) * y₀
        + h * (zeroGeneralizedRK.b 0
                * f (zeroGeneralizedRK.explicitStageValue f y₀ h 0)) = 0
  show (0 : ℝ) * y₀
        + h * ((0 : ℝ)
                * f (zeroGeneralizedRK.explicitStageValue f y₀ h 0)) = 0
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

/-- **Component-wise closed form for `padCompatStartingMethod.applyExplicit`
(cycle 156).** The active row-0 channel returns one explicit-Euler step
`y₀ + h · f(y₀)` (via `trivialGeneralizedRK`); the inactive row-1 channel
returns `0` (via `zeroGeneralizedRK`). -/
theorem padCompatStartingMethod_applyExplicit
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    padCompatStartingMethod.applyExplicit f y₀ h
      = ![y₀ + h * f y₀, 0] := by
  funext i
  fin_cases i
  · show trivialGeneralizedRK.explicitApply f y₀ h = y₀ + h * f y₀
    exact trivialGeneralizedRK_explicitApply f y₀ h
  · show zeroGeneralizedRK.explicitApply f y₀ h = 0
    exact zeroGeneralizedRK_explicitApply f y₀ h

/-- **Component-wise closed form for
`pad3CompatStartingMethod.applyExplicit` (cycle 159).** The active
row-0 channel returns one explicit-Euler step `y₀ + h · f(y₀)` (via
`trivialGeneralizedRK`); the inactive row-1 and row-2 channels each
return `0` (via `zeroGeneralizedRK`). Lifts cycle 156's
`padCompatStartingMethod_applyExplicit` from r = 2 to r = 3. -/
theorem pad3CompatStartingMethod_applyExplicit
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    pad3CompatStartingMethod.applyExplicit f y₀ h
      = ![y₀ + h * f y₀, 0, 0] := by
  funext i
  fin_cases i
  · show trivialGeneralizedRK.explicitApply f y₀ h = y₀ + h * f y₀
    exact trivialGeneralizedRK_explicitApply f y₀ h
  · show zeroGeneralizedRK.explicitApply f y₀ h = 0
    exact zeroGeneralizedRK_explicitApply f y₀ h
  · show zeroGeneralizedRK.explicitApply f y₀ h = 0
    exact zeroGeneralizedRK_explicitApply f y₀ h

/-- **Component-wise closed form for
`pad4CompatStartingMethod.applyExplicit` (cycle 161).** The active
row-0 channel returns one explicit-Euler step `y₀ + h · f(y₀)` (via
`trivialGeneralizedRK`); the inactive row-1, row-2, row-3 channels
each return `0` (via `zeroGeneralizedRK`). Lifts cycle 159's
`pad3CompatStartingMethod_applyExplicit` from r = 3 to r = 4. -/
theorem pad4CompatStartingMethod_applyExplicit
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    pad4CompatStartingMethod.applyExplicit f y₀ h
      = ![y₀ + h * f y₀, 0, 0, 0] := by
  funext i
  fin_cases i
  · show trivialGeneralizedRK.explicitApply f y₀ h = y₀ + h * f y₀
    exact trivialGeneralizedRK_explicitApply f y₀ h
  · show zeroGeneralizedRK.explicitApply f y₀ h = 0
    exact zeroGeneralizedRK_explicitApply f y₀ h
  · show zeroGeneralizedRK.explicitApply f y₀ h = 0
    exact zeroGeneralizedRK_explicitApply f y₀ h
  · show zeroGeneralizedRK.explicitApply f y₀ h = 0
    exact zeroGeneralizedRK_explicitApply f y₀ h

/-- **Component-wise closed form for
`padCompatStartingMethodR.applyExplicit` (cycle 162 Phase A).** The
active row-0 channel returns one explicit-Euler step `y₀ + h · f(y₀)`
(via `trivialGeneralizedRK`); the inactive rows `1, …, r` each return
`0` (via `zeroGeneralizedRK`). Generalises cycles 156/159/161's
`padCompatStartingMethod_applyExplicit`,
`pad3CompatStartingMethod_applyExplicit`,
`pad4CompatStartingMethod_applyExplicit` to all `r ≥ 0`. -/
theorem padCompatStartingMethodR_applyExplicit (r : ℕ)
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    (padCompatStartingMethodR r).applyExplicit f y₀ h
      = fun i => if i.val = 0 then y₀ + h * f y₀ else 0 := by
  funext i
  show ((padCompatStartingMethodR r).method i).explicitApply f y₀ h
        = if i.val = 0 then y₀ + h * f y₀ else 0
  show (padCompatMethodR r i).explicitApply f y₀ h
        = if i.val = 0 then y₀ + h * f y₀ else 0
  unfold padCompatMethodR
  by_cases hi : i.val = 0
  · simp [hi]
    exact trivialGeneralizedRK_explicitApply f y₀ h
  · simp [hi]
    exact zeroGeneralizedRK_explicitApply f y₀ h

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

/-- **Non-vacuity (positive direction, cycle 156): the padded
`(s, r) = (1, 2)` Euler GLM is explicit.** The 1×1 `A`-block
`!![0]` of `padded2DEulerGLM` (Section520) is vacuously
strict-lower triangular at `s = 1`. Used by the `r = 2`
non-vacuity witness `padded2DEulerGLM_hasOrderZero_padCompatStarting`
for `HasOrderRelativeTo_explicit`. -/
theorem padded2DEulerGLM_isExplicit :
    padded2DEulerGLM.IsExplicit := by
  intro i j _
  fin_cases i; fin_cases j
  rfl

/-- **Non-vacuity (positive direction, cycle 159): the 3-padded
`(s, r) = (1, 3)` Euler GLM is explicit.** The 1×1 `A`-block
`!![0]` of `padded3DEulerGLM` (Section520) is vacuously
strict-lower triangular at `s = 1`. Used by the `r = 3`
non-vacuity witnesses
`padded3DEulerGLM_hasOrderZero_pad3CompatStarting` and
`padded3DEulerGLM_hasOrderOne_pad3CompatStarting`. -/
theorem padded3DEulerGLM_isExplicit :
    padded3DEulerGLM.IsExplicit := by
  intro i j _
  fin_cases i; fin_cases j
  rfl

/-- **Non-vacuity (positive direction, cycle 161): the 4-padded
`(s, r) = (1, 4)` Euler GLM is explicit.** The 1×1 `A`-block
`!![0]` of `padded4DEulerGLM` (Section520) is vacuously
strict-lower triangular at `s = 1`. Used by the `r = 4`
non-vacuity witnesses
`padded4DEulerGLM_hasOrderZero_pad4CompatStarting` and
`padded4DEulerGLM_hasOrderOne_pad4CompatStarting`. -/
theorem padded4DEulerGLM_isExplicit :
    padded4DEulerGLM.IsExplicit := by
  intro i j _
  fin_cases i; fin_cases j
  rfl

/-- **Non-vacuity (positive direction, cycle 162 Phase A): the
parametric `(s, r + 1)` padded Euler GLM is explicit for every
`r : ℕ`.** The 1×1 `A`-block `!![0]` of `paddedREulerGLM r`
(Section520) is vacuously strict-lower triangular at `s = 1`,
identically to the four hand-written instances `explicitEulerGLM`
(`r = 0` in this indexing) and `padded{2,3,4}DEulerGLM`
(`r ∈ {1, 2, 3}`). Generalises cycles 156/159/161's
`padded{2,3,4}DEulerGLM_isExplicit` to all `r ≥ 0`. -/
theorem paddedREulerGLM_isExplicit (r : ℕ) :
    (paddedREulerGLM r).IsExplicit := by
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

/-- **(Cycle 160) Shared little-o + Lipschitz closure for explicit-Euler-style
scalar SM−ES diffs at `p = 0`.** Order-zero sibling of cycle 158's
`taylor_lipschitz_explicitEuler_orderOne_diff_isBigO`. Given an exact
solution `yex` satisfying `yex x₀ = y₀` and `HasDerivAt yex (f y₀) x₀`,
with `f` Lipschitz, the residual

  `((y₀ + h · f y₀) + h · f (y₀ + h · f y₀))`
  `  − (yex (x₀ + h) + h · f (yex (x₀ + h)))`

is `O(h)` near `0`. This is the closed-form `SM[0] − ES[0]` for the
explicit-Euler GLM × explicit-Euler stage at index `0` once the
`trivialStartingMethod` (cycle 153) and the `i = 0` channels of
`padCompatStartingMethod` (cycle 156) and `pad3CompatStartingMethod`
(cycle 159) have been algebraically reduced; extracting it as a
private helper lets all three p = 0 witnesses cite the proof verbatim.

Proof structure: split the residual into

* `T1 := (y₀ + h·f y₀) − yex(x₀+h)` — `o(h)` (hence `O(h)`) via the
  little-o characterization of `HasDerivAt` at `0`,
* `T2 := h · (f(y₀ + h·f y₀) − f(yex(x₀+h)))` — `O(h)` via the
  Lipschitz pointwise bound combined with the `|·| ≤ 1` clause
  supplied by continuity of the inner difference at `h = 0`. -/
private theorem taylor_lipschitz_explicitEuler_orderZero_diff_isBigO
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_deriv : HasDerivAt yex (f y₀) x₀) :
    (fun h : ℝ =>
        ((y₀ + h * f y₀) + h * f (y₀ + h * f y₀))
          - (yex (x₀ + h) + h * f (yex (x₀ + h))))
      =O[nhds (0 : ℝ)] (fun h : ℝ => h) := by
  -- Decompose into T1 + T2 form.
  have hsplit :
      (fun h : ℝ =>
          ((y₀ + h * f y₀) + h * f (y₀ + h * f y₀))
            - (yex (x₀ + h) + h * f (yex (x₀ + h))))
        = (fun h : ℝ =>
            ((y₀ + h * f y₀) - yex (x₀ + h))
              + h * (f (y₀ + h * f y₀) - f (yex (x₀ + h)))) := by
    funext h; ring
  rw [hsplit]
  -- T1 = (y₀ + h·f y₀) - yex(x₀+h) is o(h), hence O(h).
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
  -- T2 = h * (f(y₀ + h·f y₀) - f(yex(x₀+h))) is O(h) via Lipschitz.
  have hT2 : (fun h : ℝ => h * (f (y₀ + h * f y₀) - f (yex (x₀ + h))))
      =O[nhds (0 : ℝ)] (fun h => h) := by
    have hcontA : ContinuousAt (fun h : ℝ => y₀ + h * f y₀) 0 := by
      exact (continuous_const.add (continuous_id.mul continuous_const)).continuousAt
    have hcontB : ContinuousAt (fun h : ℝ => yex (x₀ + h)) 0 := by
      have hinner : ContinuousAt (fun h : ℝ => x₀ + h) 0 :=
        (continuous_const.add continuous_id).continuousAt
      have houter : ContinuousAt yex ((fun h : ℝ => x₀ + h) 0) := by
        simpa using hyex_deriv.continuousAt
      exact houter.comp hinner
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
      have hin := (Metric.tendsto_nhds.mp hdiff_tendsto) 1 hone
      filter_upwards [hin] with h hh
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
  -- Combine
  exact hT1.add hT2

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
  -- Step 2: rewrite SM[0] − ES[0] into the helper's input form.
  have hcongr :
      (fun h : ℝ =>
          applyStartingThenStep_explicit explicitEulerGLM trivialStartingMethod
              (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)
              explicitEulerGLM_isExplicit f y₀ h 0
            - applyExactThenStarting_explicit trivialStartingMethod
                (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)
                f yex x₀ h 0)
        = (fun h : ℝ =>
            ((y₀ + h * f y₀) + h * f (y₀ + h * f y₀))
              - (yex (x₀ + h) + h * f (yex (x₀ + h)))) := by
    funext h
    rw [hSM, hES]
  rw [hcongr]
  -- Collapse `h ^ (0 + 1)` to `h`.
  have hpow : (fun h : ℝ => h ^ (0 + 1)) = (fun h : ℝ => h) := by
    funext h; simp
  rw [hpow]
  -- Step 3: discharge via the cycle-160 shared helper.
  exact taylor_lipschitz_explicitEuler_orderZero_diff_isBigO
    hf_lip hyex_x₀ hyex_deriv

/-- **(Cycle 158) Shared Taylor + Lipschitz closure for explicit-Euler-style
scalar SM−ES diffs at `p = 1`.** Given a `C²` exact solution `yex`
satisfying the ODE `∀ x, HasDerivAt yex (f (yex x)) x` with `f` Lipschitz,
the residual

  `((y₀ + h · f y₀) + h · f (y₀ + h · f y₀))`
  `  − (yex (x₀ + h) + h · f (yex (x₀ + h)))`

is `O(h²)` near `0`. This is the closed-form `SM[0] − ES[0]` for the
explicit-Euler GLM × explicit-Euler stage at index `0` once both
`trivialStartingMethod` (cycle 154) and the `i=0` channel of
`padCompatStartingMethod` (cycle 157) have been algebraically reduced;
extracting it as a private helper lets both witnesses cite the proof
verbatim. -/
private theorem taylor_lipschitz_explicitEuler_orderOne_diff_isBigO
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C2 : ContDiff ℝ 2 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    (fun h : ℝ =>
        ((y₀ + h * f y₀) + h * f (y₀ + h * f y₀))
          - (yex (x₀ + h) + h * f (yex (x₀ + h))))
      =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ 2) := by
  -- Decompose into T1 + T2 form.
  have hsplit :
      (fun h : ℝ =>
          ((y₀ + h * f y₀) + h * f (y₀ + h * f y₀))
            - (yex (x₀ + h) + h * f (yex (x₀ + h))))
        = (fun h : ℝ =>
            ((y₀ + h * f y₀) - yex (x₀ + h))
              + h * (f (y₀ + h * f y₀) - f (yex (x₀ + h)))) := by
    funext h; ring
  rw [hsplit]
  -- T1 = (y₀ + h·f y₀) - yex(x₀+h) is O(h²) via 2nd-order Taylor.
  have hT1 : (fun h : ℝ => (y₀ + h * f y₀) - yex (x₀ + h))
      =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ 2) := by
    have htaylor :
        (fun x : ℝ => yex x - taylorWithinEval yex 2 Set.univ x₀ x)
          =o[nhds x₀] (fun x : ℝ => (x - x₀) ^ 2) := by
      have h := taylor_isLittleO (n := 2) (f := yex) (x₀ := x₀)
        (s := Set.univ) convex_univ (Set.mem_univ _) hyex_C2.contDiffOn
      simpa [nhdsWithin_univ] using h
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
    have hderiv_x0 : iteratedDeriv 1 yex x₀ = f y₀ := by
      rw [iteratedDeriv_one]
      have h := (hyex_ode x₀).deriv
      rw [hyex_x₀] at h
      exact h
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
    have hT1_eq : (fun h : ℝ => (y₀ + h * f y₀) - yex (x₀ + h))
        = (fun h : ℝ =>
            -(yex (x₀ + h) - taylorWithinEval yex 2 Set.univ x₀ (x₀ + h))
              - h ^ 2 / 2 * iteratedDeriv 2 yex x₀) := by
      funext h
      rw [hT_eval h, hderiv_x0, hyex_x₀]
      ring
    rw [hT1_eq]
    have hconst : (fun h : ℝ => h ^ 2 / 2 * iteratedDeriv 2 yex x₀)
        =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ 2) := by
      have h0 := Asymptotics.isBigO_const_mul_self
        (iteratedDeriv 2 yex x₀ / 2) (fun h : ℝ => h ^ 2) (nhds 0)
      refine h0.congr' (Filter.Eventually.of_forall fun h => ?_)
        (Filter.Eventually.of_forall fun _ => rfl)
      ring
    have hsum := hres.isBigO.add hconst
    refine hsum.neg_left.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
    refine Filter.Eventually.of_forall fun h => ?_
    show -((yex (x₀ + h) - taylorWithinEval yex 2 Set.univ x₀ (x₀ + h))
            + h ^ 2 / 2 * iteratedDeriv 2 yex x₀)
      = -(yex (x₀ + h) - taylorWithinEval yex 2 Set.univ x₀ (x₀ + h))
        - h ^ 2 / 2 * iteratedDeriv 2 yex x₀
    ring
  -- T2 = h * (f(y₀+h·f y₀) - f(yex(x₀+h))) is O(h²) via Lipschitz + T1.
  have hT2 : (fun h : ℝ => h * (f (y₀ + h * f y₀) - f (yex (x₀ + h))))
      =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ 2) := by
    obtain ⟨C, hCpos, hC⟩ := hT1.exists_pos
    rw [Asymptotics.isBigOWith_iff] at hC
    have hh1 : ∀ᶠ h : ℝ in nhds 0, |h| ≤ 1 := by
      refine Filter.eventually_iff_exists_mem.mpr
        ⟨Set.Ioo (-1 : ℝ) 1, IsOpen.mem_nhds isOpen_Ioo (by norm_num),
         fun h hh => ?_⟩
      exact abs_le.mpr ⟨hh.1.le, hh.2.le⟩
    refine Asymptotics.IsBigO.of_bound (↑L * C) ?_
    filter_upwards [hC, hh1] with h hT1bound hh1bound
    have hLnn : (0 : ℝ) ≤ ↑L := L.coe_nonneg
    have habsh : (0 : ℝ) ≤ |h| := abs_nonneg _
    have hCnn : (0 : ℝ) ≤ C := hCpos.le
    have hlip := hf_lip.dist_le_mul (y₀ + h * f y₀) (yex (x₀ + h))
    rw [Real.dist_eq, Real.dist_eq] at hlip
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hT1bound
    have habsh2 : |h ^ 2| = h ^ 2 := abs_of_nonneg (sq_nonneg h)
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
  -- Combine.
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
  -- Step 2: rewrite SM[0] − ES[0] into the helper's input form.
  have hcongr :
      (fun h : ℝ =>
          applyStartingThenStep_explicit explicitEulerGLM trivialStartingMethod
              (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)
              explicitEulerGLM_isExplicit f y₀ h 0
            - applyExactThenStarting_explicit trivialStartingMethod
                (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)
                f yex x₀ h 0)
        = (fun h : ℝ =>
            ((y₀ + h * f y₀) + h * f (y₀ + h * f y₀))
              - (yex (x₀ + h) + h * f (yex (x₀ + h)))) := by
    funext h
    rw [hSM, hES]
  rw [hcongr]
  -- Collapse `h ^ (1 + 1)` to `h ^ 2`.
  have hpow : (fun h : ℝ => h ^ (1 + 1)) = (fun h : ℝ => h ^ 2) := by
    funext h; ring
  rw [hpow]
  -- Step 3: discharge via the cycle-158 shared helper.
  exact taylor_lipschitz_explicitEuler_orderOne_diff_isBigO
    hf_lip hyex_x₀ hyex_C2 hyex_ode

/-- **Order of a general linear method (Definition 530C, Path A).**
A GLM `M` has order `p` (relative to *some* non-degenerate starting
method) if there exists `S : StartingMethod r` whose constituent
methods are all explicit and which is non-degenerate, such that
`M` has order `p` relative to `S` in the sense of
`HasOrderRelativeTo_explicit`.

Faithful to Butcher's def:530C (§530, p. 432) restricted to the
explicit branch: the textbook's "`M` has order `p`" universally
quantifies over methods (explicit + implicit); Path A captures the
explicit case. Path B (implicit) is deferred — see
`.prover-state/issues/def_530B_scaffold_strategy.md`.

The `S.IsNonDegenerate` clause is included verbatim from the
textbook ("there exists a non-degenerate starting method `S`"). -/
def HasOrder_explicit
    {s r : ℕ}
    (M : OpenMath.Chapter5.Section510.GeneralLinearMethod s r)
    (hM : M.IsExplicit)
    (p : ℕ)
    (f : ℝ → ℝ) (yex : ℝ → ℝ) (x₀ y₀ : ℝ) : Prop :=
  ∃ (S : StartingMethod r) (hS : ∀ i, (S.method i).IsExplicit),
    S.IsNonDegenerate ∧
    HasOrderRelativeTo_explicit M S hS hM p f yex x₀ y₀

/-- **Non-vacuity of `HasOrder_explicit` at `p = 0`.** Witnesses
def:530C (Path A) at the `(s, r) = (1, 1)` shape by exhibiting the
trivial starting method as the existential witness. The starting
method `trivialStartingMethod` is non-degenerate
(`trivialStartingMethod_isNonDegenerate`) and explicit
(`trivialGeneralizedRK_isExplicit`); the `HasOrderRelativeTo_explicit`
component is supplied by `explicitEulerGLM_hasOrderZero_trivialStarting`
(cycle 153). -/
theorem explicitEulerGLM_hasOrderZero
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_deriv : HasDerivAt yex (f y₀) x₀) :
    HasOrder_explicit explicitEulerGLM explicitEulerGLM_isExplicit
      0 f yex x₀ y₀ := by
  refine ⟨trivialStartingMethod,
          (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit),
          trivialStartingMethod_isNonDegenerate,
          ?_⟩
  exact explicitEulerGLM_hasOrderZero_trivialStarting hf_lip hyex_x₀ hyex_deriv

/-- **Non-vacuity of `HasOrder_explicit` at `p = 1`.** Refines
`explicitEulerGLM_hasOrderZero` to order `1` using the cycle-154
witness `explicitEulerGLM_hasOrderOne_trivialStarting`, which requires
the exact solution `yex` to be `C²` and to satisfy the genuine ODE
relation `∀ x, HasDerivAt yex (f (yex x)) x`. -/
theorem explicitEulerGLM_hasOrderOne
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C2 : ContDiff ℝ 2 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    HasOrder_explicit explicitEulerGLM explicitEulerGLM_isExplicit
      1 f yex x₀ y₀ := by
  refine ⟨trivialStartingMethod,
          (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit),
          trivialStartingMethod_isNonDegenerate,
          ?_⟩
  exact explicitEulerGLM_hasOrderOne_trivialStarting hf_lip hyex_x₀ hyex_C2 hyex_ode

/-- **`r = 2` non-vacuity (def:530B Path A, cycle 156).** The padded
`(s, r) = (1, 2)` GLM `padded2DEulerGLM` has order `0` relative to
`padCompatStartingMethod` on any IVP whose exact solution `yex`
satisfies `yex x₀ = y₀` and `HasDerivAt yex (f y₀) x₀`, with `f`
Lipschitz with constant `L`.

The row-0 channel reduces to the same explicit-Euler closed form as
the cycle 153 `(s, r) = (1, 1)` witness; the row-1 channel is
identically zero on both `SM` and `ES`. Establishes
`HasOrderRelativeTo_explicit` at non-trivial `r = 2`, complementing
cycle 153 (`r = 1`, `p = 0`) and cycle 154 (`r = 1`, `p = 1`). -/
theorem padded2DEulerGLM_hasOrderZero_padCompatStarting
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_deriv : HasDerivAt yex (f y₀) x₀) :
    HasOrderRelativeTo_explicit padded2DEulerGLM padCompatStartingMethod
      padCompatStartingMethod_constituents_isExplicit
      padded2DEulerGLM_isExplicit
      0 f yex x₀ y₀ := by
  intro i
  fin_cases i
  · -- i = 0 case: identical algebraic shape to cycle 153.
    change (fun h : ℝ =>
          applyStartingThenStep_explicit padded2DEulerGLM padCompatStartingMethod
              padCompatStartingMethod_constituents_isExplicit
              padded2DEulerGLM_isExplicit f y₀ h 0
            - applyExactThenStarting_explicit padCompatStartingMethod
                padCompatStartingMethod_constituents_isExplicit
                f yex x₀ h 0)
        =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (0 + 1))
    -- SM[0] closed form
    have hSM : ∀ h : ℝ,
        applyStartingThenStep_explicit padded2DEulerGLM padCompatStartingMethod
            padCompatStartingMethod_constituents_isExplicit
            padded2DEulerGLM_isExplicit f y₀ h 0
          = (y₀ + h * f y₀) + h * f (y₀ + h * f y₀) := by
      intro h
      show (h * ∑ i : Fin 1,
          padded2DEulerGLM.B 0 i
            * f (padded2DEulerGLM.explicitStageValue f
                    (padCompatStartingMethod.applyExplicit f y₀ h) h i))
          + (padded2DEulerGLM.V *ᵥ padCompatStartingMethod.applyExplicit f y₀ h) 0
          = _
      rw [padCompatStartingMethod_applyExplicit]
      unfold OpenMath.Chapter5.Section510.GeneralLinearMethod.explicitStageValue
      simp [padded2DEulerGLM, Matrix.mulVec, dotProduct]
      ring
    -- ES[0] closed form
    have hES : ∀ h : ℝ,
        applyExactThenStarting_explicit padCompatStartingMethod
            padCompatStartingMethod_constituents_isExplicit
            f yex x₀ h 0
          = yex (x₀ + h) + h * f (yex (x₀ + h)) := by
      intro h
      show padCompatStartingMethod.applyExplicit f (yex (x₀ + h)) h 0
          = yex (x₀ + h) + h * f (yex (x₀ + h))
      rw [padCompatStartingMethod_applyExplicit]
      rfl
    -- Rewrite SM[0] − ES[0] into the helper's input form.
    have hcongr :
        (fun h : ℝ =>
            applyStartingThenStep_explicit padded2DEulerGLM padCompatStartingMethod
                padCompatStartingMethod_constituents_isExplicit
                padded2DEulerGLM_isExplicit f y₀ h 0
              - applyExactThenStarting_explicit padCompatStartingMethod
                  padCompatStartingMethod_constituents_isExplicit
                  f yex x₀ h 0)
          = (fun h : ℝ =>
              ((y₀ + h * f y₀) + h * f (y₀ + h * f y₀))
                - (yex (x₀ + h) + h * f (yex (x₀ + h)))) := by
      funext h
      rw [hSM, hES]
    rw [hcongr]
    -- Collapse `h ^ (0 + 1)` to `h`.
    have hpow : (fun h : ℝ => h ^ (0 + 1)) = (fun h : ℝ => h) := by
      funext h; simp
    rw [hpow]
    -- Discharge via the cycle-160 shared helper.
    exact taylor_lipschitz_explicitEuler_orderZero_diff_isBigO
      hf_lip hyex_x₀ hyex_deriv
  · -- i = 1 case: SM[1] = 0, ES[1] = 0, Diff = 0.
    change (fun h : ℝ =>
          applyStartingThenStep_explicit padded2DEulerGLM padCompatStartingMethod
              padCompatStartingMethod_constituents_isExplicit
              padded2DEulerGLM_isExplicit f y₀ h 1
            - applyExactThenStarting_explicit padCompatStartingMethod
                padCompatStartingMethod_constituents_isExplicit
                f yex x₀ h 1)
        =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (0 + 1))
    have hSM1 : ∀ h : ℝ,
        applyStartingThenStep_explicit padded2DEulerGLM padCompatStartingMethod
            padCompatStartingMethod_constituents_isExplicit
            padded2DEulerGLM_isExplicit f y₀ h 1 = 0 := by
      intro h
      show (h * ∑ i : Fin 1,
          padded2DEulerGLM.B 1 i
            * f (padded2DEulerGLM.explicitStageValue f
                    (padCompatStartingMethod.applyExplicit f y₀ h) h i))
          + (padded2DEulerGLM.V *ᵥ padCompatStartingMethod.applyExplicit f y₀ h) 1
          = 0
      rw [padCompatStartingMethod_applyExplicit]
      simp [padded2DEulerGLM, Matrix.mulVec, dotProduct]
    have hES1 : ∀ h : ℝ,
        applyExactThenStarting_explicit padCompatStartingMethod
            padCompatStartingMethod_constituents_isExplicit
            f yex x₀ h 1 = 0 := by
      intro h
      show padCompatStartingMethod.applyExplicit f (yex (x₀ + h)) h 1 = 0
      rw [padCompatStartingMethod_applyExplicit]
      rfl
    have hcongr : (fun h : ℝ =>
        applyStartingThenStep_explicit padded2DEulerGLM padCompatStartingMethod
            padCompatStartingMethod_constituents_isExplicit
            padded2DEulerGLM_isExplicit f y₀ h 1
          - applyExactThenStarting_explicit padCompatStartingMethod
              padCompatStartingMethod_constituents_isExplicit
              f yex x₀ h 1) = (fun _ : ℝ => (0 : ℝ)) := by
      funext h; rw [hSM1, hES1]; ring
    rw [hcongr]
    exact Asymptotics.isBigO_zero _ _

/-- **`r = 2`, `p = 1` non-vacuity (def:530B Path A, cycle 157).** Mechanical
port of `explicitEulerGLM_hasOrderOne_trivialStarting` (cycle 154) to the
padded `(s, r) = (1, 2)` setting. The padded GLM `padded2DEulerGLM` has
order `1` relative to `padCompatStartingMethod` under the cycle-154
hypothesis pack: `f` Lipschitz, `yex` is `C²`, full ODE relation
`∀ x, HasDerivAt yex (f (yex x)) x`, and `yex x₀ = y₀`.

The row-0 channel is identical to cycle 154's Taylor + Lipschitz closure
(closed forms match exactly between the trivial and padCompat starts,
so the `T1`/`T2` algebra carries verbatim); the row-1 channel is
identically zero on both `SM` and `ES` (cycle 156 shape, with the
exponent in `h ^ _` lifted from `0 + 1` to `1 + 1`). -/
theorem padded2DEulerGLM_hasOrderOne_padCompatStarting
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C2 : ContDiff ℝ 2 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    HasOrderRelativeTo_explicit padded2DEulerGLM padCompatStartingMethod
      padCompatStartingMethod_constituents_isExplicit
      padded2DEulerGLM_isExplicit
      1 f yex x₀ y₀ := by
  intro i
  fin_cases i
  · -- i = 0 case: identical algebraic shape to cycle 154's p=1 closure.
    change (fun h : ℝ =>
          applyStartingThenStep_explicit padded2DEulerGLM padCompatStartingMethod
              padCompatStartingMethod_constituents_isExplicit
              padded2DEulerGLM_isExplicit f y₀ h 0
            - applyExactThenStarting_explicit padCompatStartingMethod
                padCompatStartingMethod_constituents_isExplicit
                f yex x₀ h 0)
        =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (1 + 1))
    -- SM[0] closed form (cycle 156 shape).
    have hSM : ∀ h : ℝ,
        applyStartingThenStep_explicit padded2DEulerGLM padCompatStartingMethod
            padCompatStartingMethod_constituents_isExplicit
            padded2DEulerGLM_isExplicit f y₀ h 0
          = (y₀ + h * f y₀) + h * f (y₀ + h * f y₀) := by
      intro h
      show (h * ∑ i : Fin 1,
          padded2DEulerGLM.B 0 i
            * f (padded2DEulerGLM.explicitStageValue f
                    (padCompatStartingMethod.applyExplicit f y₀ h) h i))
          + (padded2DEulerGLM.V *ᵥ padCompatStartingMethod.applyExplicit f y₀ h) 0
          = _
      rw [padCompatStartingMethod_applyExplicit]
      unfold OpenMath.Chapter5.Section510.GeneralLinearMethod.explicitStageValue
      simp [padded2DEulerGLM, Matrix.mulVec, dotProduct]
      ring
    -- ES[0] closed form (cycle 156 shape).
    have hES : ∀ h : ℝ,
        applyExactThenStarting_explicit padCompatStartingMethod
            padCompatStartingMethod_constituents_isExplicit
            f yex x₀ h 0
          = yex (x₀ + h) + h * f (yex (x₀ + h)) := by
      intro h
      show padCompatStartingMethod.applyExplicit f (yex (x₀ + h)) h 0
          = yex (x₀ + h) + h * f (yex (x₀ + h))
      rw [padCompatStartingMethod_applyExplicit]
      rfl
    -- Rewrite SM[0] − ES[0] into the helper's input form.
    have hcongr :
        (fun h : ℝ =>
            applyStartingThenStep_explicit padded2DEulerGLM padCompatStartingMethod
                padCompatStartingMethod_constituents_isExplicit
                padded2DEulerGLM_isExplicit f y₀ h 0
              - applyExactThenStarting_explicit padCompatStartingMethod
                  padCompatStartingMethod_constituents_isExplicit
                  f yex x₀ h 0)
          = (fun h : ℝ =>
              ((y₀ + h * f y₀) + h * f (y₀ + h * f y₀))
                - (yex (x₀ + h) + h * f (yex (x₀ + h)))) := by
      funext h
      rw [hSM, hES]
    rw [hcongr]
    -- Collapse `h ^ (1 + 1)` to `h ^ 2`.
    have hpow : (fun h : ℝ => h ^ (1 + 1)) = (fun h : ℝ => h ^ 2) := by
      funext h; ring
    rw [hpow]
    -- Discharge via the cycle-158 shared helper.
    exact taylor_lipschitz_explicitEuler_orderOne_diff_isBigO
      hf_lip hyex_x₀ hyex_C2 hyex_ode
  · -- i = 1 case: SM[1] = ES[1] = 0; the difference is identically zero.
    change (fun h : ℝ =>
          applyStartingThenStep_explicit padded2DEulerGLM padCompatStartingMethod
              padCompatStartingMethod_constituents_isExplicit
              padded2DEulerGLM_isExplicit f y₀ h 1
            - applyExactThenStarting_explicit padCompatStartingMethod
                padCompatStartingMethod_constituents_isExplicit
                f yex x₀ h 1)
        =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (1 + 1))
    have hSM1 : ∀ h : ℝ,
        applyStartingThenStep_explicit padded2DEulerGLM padCompatStartingMethod
            padCompatStartingMethod_constituents_isExplicit
            padded2DEulerGLM_isExplicit f y₀ h 1 = 0 := by
      intro h
      show (h * ∑ i : Fin 1,
          padded2DEulerGLM.B 1 i
            * f (padded2DEulerGLM.explicitStageValue f
                    (padCompatStartingMethod.applyExplicit f y₀ h) h i))
          + (padded2DEulerGLM.V *ᵥ padCompatStartingMethod.applyExplicit f y₀ h) 1
          = 0
      rw [padCompatStartingMethod_applyExplicit]
      simp [padded2DEulerGLM, Matrix.mulVec, dotProduct]
    have hES1 : ∀ h : ℝ,
        applyExactThenStarting_explicit padCompatStartingMethod
            padCompatStartingMethod_constituents_isExplicit
            f yex x₀ h 1 = 0 := by
      intro h
      show padCompatStartingMethod.applyExplicit f (yex (x₀ + h)) h 1 = 0
      rw [padCompatStartingMethod_applyExplicit]
      rfl
    have hcongr : (fun h : ℝ =>
        applyStartingThenStep_explicit padded2DEulerGLM padCompatStartingMethod
            padCompatStartingMethod_constituents_isExplicit
            padded2DEulerGLM_isExplicit f y₀ h 1
          - applyExactThenStarting_explicit padCompatStartingMethod
              padCompatStartingMethod_constituents_isExplicit
              f yex x₀ h 1) = (fun _ : ℝ => (0 : ℝ)) := by
      funext h; rw [hSM1, hES1]; ring
    rw [hcongr]
    exact Asymptotics.isBigO_zero _ _

/-- **Non-vacuity of `HasOrder_explicit` at `r = 2`, `p = 0` (cycle 156).**
Mirrors `explicitEulerGLM_hasOrderZero` shape: exhibits
`padCompatStartingMethod` as the existential witness for
`padded2DEulerGLM`. The starting method is non-degenerate
(`padCompatStartingMethod_isNonDegenerate`) and has explicit constituents
(`padCompatStartingMethod_constituents_isExplicit`); the
`HasOrderRelativeTo_explicit` component is supplied by
`padded2DEulerGLM_hasOrderZero_padCompatStarting`. -/
theorem padded2DEulerGLM_hasOrderZero
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_deriv : HasDerivAt yex (f y₀) x₀) :
    HasOrder_explicit padded2DEulerGLM padded2DEulerGLM_isExplicit
      0 f yex x₀ y₀ := by
  refine ⟨padCompatStartingMethod,
          padCompatStartingMethod_constituents_isExplicit,
          padCompatStartingMethod_isNonDegenerate,
          ?_⟩
  exact padded2DEulerGLM_hasOrderZero_padCompatStarting
          hf_lip hyex_x₀ hyex_deriv

/-- **Non-vacuity of `HasOrder_explicit` at `r = 2`, `p = 1` (cycle 157).**
Refines `padded2DEulerGLM_hasOrderZero` to `p = 1` under the cycle-154
hypothesis pack (`LipschitzWith L f`, `ContDiff ℝ 2 yex`, full ODE
relation, `yex x₀ = y₀`). The starting method is
`padCompatStartingMethod`; the `HasOrderRelativeTo_explicit` component
is supplied by `padded2DEulerGLM_hasOrderOne_padCompatStarting`. -/
theorem padded2DEulerGLM_hasOrderOne
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C2 : ContDiff ℝ 2 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    HasOrder_explicit padded2DEulerGLM padded2DEulerGLM_isExplicit
      1 f yex x₀ y₀ := by
  refine ⟨padCompatStartingMethod,
          padCompatStartingMethod_constituents_isExplicit,
          padCompatStartingMethod_isNonDegenerate,
          ?_⟩
  exact padded2DEulerGLM_hasOrderOne_padCompatStarting
          hf_lip hyex_x₀ hyex_C2 hyex_ode

/-- **`r = 3` non-vacuity (def:530B Path A, cycle 159).** The 3-padded
`(s, r) = (1, 3)` GLM `padded3DEulerGLM` has order `0` relative to
`pad3CompatStartingMethod` on any IVP whose exact solution `yex`
satisfies `yex x₀ = y₀` and `HasDerivAt yex (f y₀) x₀`, with `f`
Lipschitz with constant `L`.

The row-0 channel reduces to the same explicit-Euler closed form as
the cycle 153 `(s, r) = (1, 1)` and cycle 156 `r = 2` witnesses; the
row-1 and row-2 channels are identically zero on both `SM` and `ES`
(zero-collapse via `Asymptotics.isBigO_zero`). Lifts cycle 156's
r = 2 witness to r = 3. -/
theorem padded3DEulerGLM_hasOrderZero_pad3CompatStarting
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_deriv : HasDerivAt yex (f y₀) x₀) :
    HasOrderRelativeTo_explicit padded3DEulerGLM pad3CompatStartingMethod
      pad3CompatStartingMethod_constituents_isExplicit
      padded3DEulerGLM_isExplicit
      0 f yex x₀ y₀ := by
  intro i
  fin_cases i
  · -- i = 0 case: identical algebraic shape to cycles 153 and 156.
    change (fun h : ℝ =>
          applyStartingThenStep_explicit padded3DEulerGLM pad3CompatStartingMethod
              pad3CompatStartingMethod_constituents_isExplicit
              padded3DEulerGLM_isExplicit f y₀ h 0
            - applyExactThenStarting_explicit pad3CompatStartingMethod
                pad3CompatStartingMethod_constituents_isExplicit
                f yex x₀ h 0)
        =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (0 + 1))
    -- SM[0] closed form
    have hSM : ∀ h : ℝ,
        applyStartingThenStep_explicit padded3DEulerGLM pad3CompatStartingMethod
            pad3CompatStartingMethod_constituents_isExplicit
            padded3DEulerGLM_isExplicit f y₀ h 0
          = (y₀ + h * f y₀) + h * f (y₀ + h * f y₀) := by
      intro h
      show (h * ∑ i : Fin 1,
          padded3DEulerGLM.B 0 i
            * f (padded3DEulerGLM.explicitStageValue f
                    (pad3CompatStartingMethod.applyExplicit f y₀ h) h i))
          + (padded3DEulerGLM.V *ᵥ pad3CompatStartingMethod.applyExplicit f y₀ h) 0
          = _
      rw [pad3CompatStartingMethod_applyExplicit]
      unfold OpenMath.Chapter5.Section510.GeneralLinearMethod.explicitStageValue
      simp [padded3DEulerGLM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      ring
    -- ES[0] closed form
    have hES : ∀ h : ℝ,
        applyExactThenStarting_explicit pad3CompatStartingMethod
            pad3CompatStartingMethod_constituents_isExplicit
            f yex x₀ h 0
          = yex (x₀ + h) + h * f (yex (x₀ + h)) := by
      intro h
      show pad3CompatStartingMethod.applyExplicit f (yex (x₀ + h)) h 0
          = yex (x₀ + h) + h * f (yex (x₀ + h))
      rw [pad3CompatStartingMethod_applyExplicit]
      rfl
    -- Rewrite SM[0] − ES[0] into the helper's input form.
    have hcongr :
        (fun h : ℝ =>
            applyStartingThenStep_explicit padded3DEulerGLM pad3CompatStartingMethod
                pad3CompatStartingMethod_constituents_isExplicit
                padded3DEulerGLM_isExplicit f y₀ h 0
              - applyExactThenStarting_explicit pad3CompatStartingMethod
                  pad3CompatStartingMethod_constituents_isExplicit
                  f yex x₀ h 0)
          = (fun h : ℝ =>
              ((y₀ + h * f y₀) + h * f (y₀ + h * f y₀))
                - (yex (x₀ + h) + h * f (yex (x₀ + h)))) := by
      funext h
      rw [hSM, hES]
    rw [hcongr]
    -- Collapse `h ^ (0 + 1)` to `h`.
    have hpow : (fun h : ℝ => h ^ (0 + 1)) = (fun h : ℝ => h) := by
      funext h; simp
    rw [hpow]
    -- Discharge via the cycle-160 shared helper.
    exact taylor_lipschitz_explicitEuler_orderZero_diff_isBigO
      hf_lip hyex_x₀ hyex_deriv
  · -- i = 1 case: SM[1] = 0, ES[1] = 0, Diff = 0.
    change (fun h : ℝ =>
          applyStartingThenStep_explicit padded3DEulerGLM pad3CompatStartingMethod
              pad3CompatStartingMethod_constituents_isExplicit
              padded3DEulerGLM_isExplicit f y₀ h 1
            - applyExactThenStarting_explicit pad3CompatStartingMethod
                pad3CompatStartingMethod_constituents_isExplicit
                f yex x₀ h 1)
        =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (0 + 1))
    have hSM1 : ∀ h : ℝ,
        applyStartingThenStep_explicit padded3DEulerGLM pad3CompatStartingMethod
            pad3CompatStartingMethod_constituents_isExplicit
            padded3DEulerGLM_isExplicit f y₀ h 1 = 0 := by
      intro h
      show (h * ∑ i : Fin 1,
          padded3DEulerGLM.B 1 i
            * f (padded3DEulerGLM.explicitStageValue f
                    (pad3CompatStartingMethod.applyExplicit f y₀ h) h i))
          + (padded3DEulerGLM.V *ᵥ pad3CompatStartingMethod.applyExplicit f y₀ h) 1
          = 0
      rw [pad3CompatStartingMethod_applyExplicit]
      simp [padded3DEulerGLM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    have hES1 : ∀ h : ℝ,
        applyExactThenStarting_explicit pad3CompatStartingMethod
            pad3CompatStartingMethod_constituents_isExplicit
            f yex x₀ h 1 = 0 := by
      intro h
      show pad3CompatStartingMethod.applyExplicit f (yex (x₀ + h)) h 1 = 0
      rw [pad3CompatStartingMethod_applyExplicit]
      rfl
    have hcongr : (fun h : ℝ =>
        applyStartingThenStep_explicit padded3DEulerGLM pad3CompatStartingMethod
            pad3CompatStartingMethod_constituents_isExplicit
            padded3DEulerGLM_isExplicit f y₀ h 1
          - applyExactThenStarting_explicit pad3CompatStartingMethod
              pad3CompatStartingMethod_constituents_isExplicit
              f yex x₀ h 1) = (fun _ : ℝ => (0 : ℝ)) := by
      funext h; rw [hSM1, hES1]; ring
    rw [hcongr]
    exact Asymptotics.isBigO_zero _ _
  · -- i = 2 case: identical structure to i = 1.
    change (fun h : ℝ =>
          applyStartingThenStep_explicit padded3DEulerGLM pad3CompatStartingMethod
              pad3CompatStartingMethod_constituents_isExplicit
              padded3DEulerGLM_isExplicit f y₀ h 2
            - applyExactThenStarting_explicit pad3CompatStartingMethod
                pad3CompatStartingMethod_constituents_isExplicit
                f yex x₀ h 2)
        =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (0 + 1))
    have hSM2 : ∀ h : ℝ,
        applyStartingThenStep_explicit padded3DEulerGLM pad3CompatStartingMethod
            pad3CompatStartingMethod_constituents_isExplicit
            padded3DEulerGLM_isExplicit f y₀ h 2 = 0 := by
      intro h
      show (h * ∑ i : Fin 1,
          padded3DEulerGLM.B 2 i
            * f (padded3DEulerGLM.explicitStageValue f
                    (pad3CompatStartingMethod.applyExplicit f y₀ h) h i))
          + (padded3DEulerGLM.V *ᵥ pad3CompatStartingMethod.applyExplicit f y₀ h) 2
          = 0
      rw [pad3CompatStartingMethod_applyExplicit]
      simp [padded3DEulerGLM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    have hES2 : ∀ h : ℝ,
        applyExactThenStarting_explicit pad3CompatStartingMethod
            pad3CompatStartingMethod_constituents_isExplicit
            f yex x₀ h 2 = 0 := by
      intro h
      show pad3CompatStartingMethod.applyExplicit f (yex (x₀ + h)) h 2 = 0
      rw [pad3CompatStartingMethod_applyExplicit]
      rfl
    have hcongr : (fun h : ℝ =>
        applyStartingThenStep_explicit padded3DEulerGLM pad3CompatStartingMethod
            pad3CompatStartingMethod_constituents_isExplicit
            padded3DEulerGLM_isExplicit f y₀ h 2
          - applyExactThenStarting_explicit pad3CompatStartingMethod
              pad3CompatStartingMethod_constituents_isExplicit
              f yex x₀ h 2) = (fun _ : ℝ => (0 : ℝ)) := by
      funext h; rw [hSM2, hES2]; ring
    rw [hcongr]
    exact Asymptotics.isBigO_zero _ _

/-- **`r = 3`, `p = 1` non-vacuity (def:530B Path A, cycle 159).**
Mechanical port of `padded2DEulerGLM_hasOrderOne_padCompatStarting`
(cycle 157) to the 3-padded `(s, r) = (1, 3)` setting. The padded GLM
`padded3DEulerGLM` has order `1` relative to `pad3CompatStartingMethod`
under the cycle-154 hypothesis pack: `f` Lipschitz, `yex` is `C²`,
full ODE relation `∀ x, HasDerivAt yex (f (yex x)) x`, and
`yex x₀ = y₀`.

The row-0 channel is identical to cycle 154/157's Taylor + Lipschitz
closure (closed forms match exactly across the `padCompat` and
`pad3Compat` starts on the active row 0), and discharges via the
cycle-158 shared helper
`taylor_lipschitz_explicitEuler_orderOne_diff_isBigO` as a one-line
invocation — validating its portability to a third call site. The
row-1 and row-2 channels are identically zero on both `SM` and `ES`
(cycle 156/157 zero-collapse pattern, exponent `h ^ 2`). -/
theorem padded3DEulerGLM_hasOrderOne_pad3CompatStarting
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C2 : ContDiff ℝ 2 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    HasOrderRelativeTo_explicit padded3DEulerGLM pad3CompatStartingMethod
      pad3CompatStartingMethod_constituents_isExplicit
      padded3DEulerGLM_isExplicit
      1 f yex x₀ y₀ := by
  intro i
  fin_cases i
  · -- i = 0 case: identical algebraic shape to cycles 154 and 157.
    change (fun h : ℝ =>
          applyStartingThenStep_explicit padded3DEulerGLM pad3CompatStartingMethod
              pad3CompatStartingMethod_constituents_isExplicit
              padded3DEulerGLM_isExplicit f y₀ h 0
            - applyExactThenStarting_explicit pad3CompatStartingMethod
                pad3CompatStartingMethod_constituents_isExplicit
                f yex x₀ h 0)
        =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (1 + 1))
    -- SM[0] closed form
    have hSM : ∀ h : ℝ,
        applyStartingThenStep_explicit padded3DEulerGLM pad3CompatStartingMethod
            pad3CompatStartingMethod_constituents_isExplicit
            padded3DEulerGLM_isExplicit f y₀ h 0
          = (y₀ + h * f y₀) + h * f (y₀ + h * f y₀) := by
      intro h
      show (h * ∑ i : Fin 1,
          padded3DEulerGLM.B 0 i
            * f (padded3DEulerGLM.explicitStageValue f
                    (pad3CompatStartingMethod.applyExplicit f y₀ h) h i))
          + (padded3DEulerGLM.V *ᵥ pad3CompatStartingMethod.applyExplicit f y₀ h) 0
          = _
      rw [pad3CompatStartingMethod_applyExplicit]
      unfold OpenMath.Chapter5.Section510.GeneralLinearMethod.explicitStageValue
      simp [padded3DEulerGLM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      ring
    -- ES[0] closed form
    have hES : ∀ h : ℝ,
        applyExactThenStarting_explicit pad3CompatStartingMethod
            pad3CompatStartingMethod_constituents_isExplicit
            f yex x₀ h 0
          = yex (x₀ + h) + h * f (yex (x₀ + h)) := by
      intro h
      show pad3CompatStartingMethod.applyExplicit f (yex (x₀ + h)) h 0
          = yex (x₀ + h) + h * f (yex (x₀ + h))
      rw [pad3CompatStartingMethod_applyExplicit]
      rfl
    -- Rewrite SM[0] − ES[0] into the helper's input form.
    have hcongr :
        (fun h : ℝ =>
            applyStartingThenStep_explicit padded3DEulerGLM pad3CompatStartingMethod
                pad3CompatStartingMethod_constituents_isExplicit
                padded3DEulerGLM_isExplicit f y₀ h 0
              - applyExactThenStarting_explicit pad3CompatStartingMethod
                  pad3CompatStartingMethod_constituents_isExplicit
                  f yex x₀ h 0)
          = (fun h : ℝ =>
              ((y₀ + h * f y₀) + h * f (y₀ + h * f y₀))
                - (yex (x₀ + h) + h * f (yex (x₀ + h)))) := by
      funext h
      rw [hSM, hES]
    rw [hcongr]
    -- Collapse `h ^ (1 + 1)` to `h ^ 2`.
    have hpow : (fun h : ℝ => h ^ (1 + 1)) = (fun h : ℝ => h ^ 2) := by
      funext h; ring
    rw [hpow]
    -- Discharge via the cycle-158 shared helper.
    exact taylor_lipschitz_explicitEuler_orderOne_diff_isBigO
      hf_lip hyex_x₀ hyex_C2 hyex_ode
  · -- i = 1 case: SM[1] = ES[1] = 0; the difference is identically zero.
    change (fun h : ℝ =>
          applyStartingThenStep_explicit padded3DEulerGLM pad3CompatStartingMethod
              pad3CompatStartingMethod_constituents_isExplicit
              padded3DEulerGLM_isExplicit f y₀ h 1
            - applyExactThenStarting_explicit pad3CompatStartingMethod
                pad3CompatStartingMethod_constituents_isExplicit
                f yex x₀ h 1)
        =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (1 + 1))
    have hSM1 : ∀ h : ℝ,
        applyStartingThenStep_explicit padded3DEulerGLM pad3CompatStartingMethod
            pad3CompatStartingMethod_constituents_isExplicit
            padded3DEulerGLM_isExplicit f y₀ h 1 = 0 := by
      intro h
      show (h * ∑ i : Fin 1,
          padded3DEulerGLM.B 1 i
            * f (padded3DEulerGLM.explicitStageValue f
                    (pad3CompatStartingMethod.applyExplicit f y₀ h) h i))
          + (padded3DEulerGLM.V *ᵥ pad3CompatStartingMethod.applyExplicit f y₀ h) 1
          = 0
      rw [pad3CompatStartingMethod_applyExplicit]
      simp [padded3DEulerGLM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    have hES1 : ∀ h : ℝ,
        applyExactThenStarting_explicit pad3CompatStartingMethod
            pad3CompatStartingMethod_constituents_isExplicit
            f yex x₀ h 1 = 0 := by
      intro h
      show pad3CompatStartingMethod.applyExplicit f (yex (x₀ + h)) h 1 = 0
      rw [pad3CompatStartingMethod_applyExplicit]
      rfl
    have hcongr : (fun h : ℝ =>
        applyStartingThenStep_explicit padded3DEulerGLM pad3CompatStartingMethod
            pad3CompatStartingMethod_constituents_isExplicit
            padded3DEulerGLM_isExplicit f y₀ h 1
          - applyExactThenStarting_explicit pad3CompatStartingMethod
              pad3CompatStartingMethod_constituents_isExplicit
              f yex x₀ h 1) = (fun _ : ℝ => (0 : ℝ)) := by
      funext h; rw [hSM1, hES1]; ring
    rw [hcongr]
    exact Asymptotics.isBigO_zero _ _
  · -- i = 2 case: identical structure to i = 1.
    change (fun h : ℝ =>
          applyStartingThenStep_explicit padded3DEulerGLM pad3CompatStartingMethod
              pad3CompatStartingMethod_constituents_isExplicit
              padded3DEulerGLM_isExplicit f y₀ h 2
            - applyExactThenStarting_explicit pad3CompatStartingMethod
                pad3CompatStartingMethod_constituents_isExplicit
                f yex x₀ h 2)
        =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (1 + 1))
    have hSM2 : ∀ h : ℝ,
        applyStartingThenStep_explicit padded3DEulerGLM pad3CompatStartingMethod
            pad3CompatStartingMethod_constituents_isExplicit
            padded3DEulerGLM_isExplicit f y₀ h 2 = 0 := by
      intro h
      show (h * ∑ i : Fin 1,
          padded3DEulerGLM.B 2 i
            * f (padded3DEulerGLM.explicitStageValue f
                    (pad3CompatStartingMethod.applyExplicit f y₀ h) h i))
          + (padded3DEulerGLM.V *ᵥ pad3CompatStartingMethod.applyExplicit f y₀ h) 2
          = 0
      rw [pad3CompatStartingMethod_applyExplicit]
      simp [padded3DEulerGLM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    have hES2 : ∀ h : ℝ,
        applyExactThenStarting_explicit pad3CompatStartingMethod
            pad3CompatStartingMethod_constituents_isExplicit
            f yex x₀ h 2 = 0 := by
      intro h
      show pad3CompatStartingMethod.applyExplicit f (yex (x₀ + h)) h 2 = 0
      rw [pad3CompatStartingMethod_applyExplicit]
      rfl
    have hcongr : (fun h : ℝ =>
        applyStartingThenStep_explicit padded3DEulerGLM pad3CompatStartingMethod
            pad3CompatStartingMethod_constituents_isExplicit
            padded3DEulerGLM_isExplicit f y₀ h 2
          - applyExactThenStarting_explicit pad3CompatStartingMethod
              pad3CompatStartingMethod_constituents_isExplicit
              f yex x₀ h 2) = (fun _ : ℝ => (0 : ℝ)) := by
      funext h; rw [hSM2, hES2]; ring
    rw [hcongr]
    exact Asymptotics.isBigO_zero _ _

/-- **Non-vacuity of `HasOrder_explicit` at `r = 3`, `p = 0` (cycle 159).**
Mirrors `padded2DEulerGLM_hasOrderZero` shape: exhibits
`pad3CompatStartingMethod` as the existential witness for
`padded3DEulerGLM`. The starting method is non-degenerate
(`pad3CompatStartingMethod_isNonDegenerate`) and has explicit constituents
(`pad3CompatStartingMethod_constituents_isExplicit`); the
`HasOrderRelativeTo_explicit` component is supplied by
`padded3DEulerGLM_hasOrderZero_pad3CompatStarting`. -/
theorem padded3DEulerGLM_hasOrderZero
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_deriv : HasDerivAt yex (f y₀) x₀) :
    HasOrder_explicit padded3DEulerGLM padded3DEulerGLM_isExplicit
      0 f yex x₀ y₀ := by
  refine ⟨pad3CompatStartingMethod,
          pad3CompatStartingMethod_constituents_isExplicit,
          pad3CompatStartingMethod_isNonDegenerate,
          ?_⟩
  exact padded3DEulerGLM_hasOrderZero_pad3CompatStarting
          hf_lip hyex_x₀ hyex_deriv

/-- **Non-vacuity of `HasOrder_explicit` at `r = 3`, `p = 1` (cycle 159).**
Refines `padded3DEulerGLM_hasOrderZero` to `p = 1` under the cycle-154
hypothesis pack (`LipschitzWith L f`, `ContDiff ℝ 2 yex`, full ODE
relation, `yex x₀ = y₀`). The starting method is
`pad3CompatStartingMethod`; the `HasOrderRelativeTo_explicit` component
is supplied by `padded3DEulerGLM_hasOrderOne_pad3CompatStarting`. -/
theorem padded3DEulerGLM_hasOrderOne
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C2 : ContDiff ℝ 2 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    HasOrder_explicit padded3DEulerGLM padded3DEulerGLM_isExplicit
      1 f yex x₀ y₀ := by
  refine ⟨pad3CompatStartingMethod,
          pad3CompatStartingMethod_constituents_isExplicit,
          pad3CompatStartingMethod_isNonDegenerate,
          ?_⟩
  exact padded3DEulerGLM_hasOrderOne_pad3CompatStarting
          hf_lip hyex_x₀ hyex_C2 hyex_ode

/-- **`r = 4` non-vacuity (def:530B Path A, cycle 161).** The 4-padded
`(s, r) = (1, 4)` GLM `padded4DEulerGLM` has order `0` relative to
`pad4CompatStartingMethod` on any IVP whose exact solution `yex`
satisfies `yex x₀ = y₀` and `HasDerivAt yex (f y₀) x₀`, with `f`
Lipschitz with constant `L`.

The row-0 channel reduces to the same explicit-Euler closed form as
the cycle 153 / 156 / 159 i = 0 closures and discharges via the
cycle-160 shared helper `taylor_lipschitz_explicitEuler_orderZero_diff_isBigO`
as a one-line invocation; the row-1, row-2, and row-3 channels are
identically zero on both `SM` and `ES` (zero-collapse via
`Asymptotics.isBigO_zero`). Lifts cycle 159's r = 3 witness to r = 4
and validates the cycle-160 helper at a fourth call site. -/
theorem padded4DEulerGLM_hasOrderZero_pad4CompatStarting
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_deriv : HasDerivAt yex (f y₀) x₀) :
    HasOrderRelativeTo_explicit padded4DEulerGLM pad4CompatStartingMethod
      pad4CompatStartingMethod_constituents_isExplicit
      padded4DEulerGLM_isExplicit
      0 f yex x₀ y₀ := by
  intro i
  fin_cases i
  · -- i = 0 case: identical algebraic shape to cycles 153 / 156 / 159.
    change (fun h : ℝ =>
          applyStartingThenStep_explicit padded4DEulerGLM pad4CompatStartingMethod
              pad4CompatStartingMethod_constituents_isExplicit
              padded4DEulerGLM_isExplicit f y₀ h 0
            - applyExactThenStarting_explicit pad4CompatStartingMethod
                pad4CompatStartingMethod_constituents_isExplicit
                f yex x₀ h 0)
        =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (0 + 1))
    -- SM[0] closed form
    have hSM : ∀ h : ℝ,
        applyStartingThenStep_explicit padded4DEulerGLM pad4CompatStartingMethod
            pad4CompatStartingMethod_constituents_isExplicit
            padded4DEulerGLM_isExplicit f y₀ h 0
          = (y₀ + h * f y₀) + h * f (y₀ + h * f y₀) := by
      intro h
      show (h * ∑ i : Fin 1,
          padded4DEulerGLM.B 0 i
            * f (padded4DEulerGLM.explicitStageValue f
                    (pad4CompatStartingMethod.applyExplicit f y₀ h) h i))
          + (padded4DEulerGLM.V *ᵥ pad4CompatStartingMethod.applyExplicit f y₀ h) 0
          = _
      rw [pad4CompatStartingMethod_applyExplicit]
      unfold OpenMath.Chapter5.Section510.GeneralLinearMethod.explicitStageValue
      simp [padded4DEulerGLM, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
      ring
    -- ES[0] closed form
    have hES : ∀ h : ℝ,
        applyExactThenStarting_explicit pad4CompatStartingMethod
            pad4CompatStartingMethod_constituents_isExplicit
            f yex x₀ h 0
          = yex (x₀ + h) + h * f (yex (x₀ + h)) := by
      intro h
      show pad4CompatStartingMethod.applyExplicit f (yex (x₀ + h)) h 0
          = yex (x₀ + h) + h * f (yex (x₀ + h))
      rw [pad4CompatStartingMethod_applyExplicit]
      rfl
    -- Rewrite SM[0] − ES[0] into the helper's input form.
    have hcongr :
        (fun h : ℝ =>
            applyStartingThenStep_explicit padded4DEulerGLM pad4CompatStartingMethod
                pad4CompatStartingMethod_constituents_isExplicit
                padded4DEulerGLM_isExplicit f y₀ h 0
              - applyExactThenStarting_explicit pad4CompatStartingMethod
                  pad4CompatStartingMethod_constituents_isExplicit
                  f yex x₀ h 0)
          = (fun h : ℝ =>
              ((y₀ + h * f y₀) + h * f (y₀ + h * f y₀))
                - (yex (x₀ + h) + h * f (yex (x₀ + h)))) := by
      funext h
      rw [hSM, hES]
    rw [hcongr]
    -- Collapse `h ^ (0 + 1)` to `h`.
    have hpow : (fun h : ℝ => h ^ (0 + 1)) = (fun h : ℝ => h) := by
      funext h; simp
    rw [hpow]
    -- Discharge via the cycle-160 shared helper.
    exact taylor_lipschitz_explicitEuler_orderZero_diff_isBigO
      hf_lip hyex_x₀ hyex_deriv
  · -- i = 1 case: SM[1] = 0, ES[1] = 0, Diff = 0.
    change (fun h : ℝ =>
          applyStartingThenStep_explicit padded4DEulerGLM pad4CompatStartingMethod
              pad4CompatStartingMethod_constituents_isExplicit
              padded4DEulerGLM_isExplicit f y₀ h 1
            - applyExactThenStarting_explicit pad4CompatStartingMethod
                pad4CompatStartingMethod_constituents_isExplicit
                f yex x₀ h 1)
        =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (0 + 1))
    have hSM1 : ∀ h : ℝ,
        applyStartingThenStep_explicit padded4DEulerGLM pad4CompatStartingMethod
            pad4CompatStartingMethod_constituents_isExplicit
            padded4DEulerGLM_isExplicit f y₀ h 1 = 0 := by
      intro h
      show (h * ∑ i : Fin 1,
          padded4DEulerGLM.B 1 i
            * f (padded4DEulerGLM.explicitStageValue f
                    (pad4CompatStartingMethod.applyExplicit f y₀ h) h i))
          + (padded4DEulerGLM.V *ᵥ pad4CompatStartingMethod.applyExplicit f y₀ h) 1
          = 0
      rw [pad4CompatStartingMethod_applyExplicit]
      simp [padded4DEulerGLM, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    have hES1 : ∀ h : ℝ,
        applyExactThenStarting_explicit pad4CompatStartingMethod
            pad4CompatStartingMethod_constituents_isExplicit
            f yex x₀ h 1 = 0 := by
      intro h
      show pad4CompatStartingMethod.applyExplicit f (yex (x₀ + h)) h 1 = 0
      rw [pad4CompatStartingMethod_applyExplicit]
      rfl
    have hcongr : (fun h : ℝ =>
        applyStartingThenStep_explicit padded4DEulerGLM pad4CompatStartingMethod
            pad4CompatStartingMethod_constituents_isExplicit
            padded4DEulerGLM_isExplicit f y₀ h 1
          - applyExactThenStarting_explicit pad4CompatStartingMethod
              pad4CompatStartingMethod_constituents_isExplicit
              f yex x₀ h 1) = (fun _ : ℝ => (0 : ℝ)) := by
      funext h; rw [hSM1, hES1]; ring
    rw [hcongr]
    exact Asymptotics.isBigO_zero _ _
  · -- i = 2 case: identical structure to i = 1.
    change (fun h : ℝ =>
          applyStartingThenStep_explicit padded4DEulerGLM pad4CompatStartingMethod
              pad4CompatStartingMethod_constituents_isExplicit
              padded4DEulerGLM_isExplicit f y₀ h 2
            - applyExactThenStarting_explicit pad4CompatStartingMethod
                pad4CompatStartingMethod_constituents_isExplicit
                f yex x₀ h 2)
        =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (0 + 1))
    have hSM2 : ∀ h : ℝ,
        applyStartingThenStep_explicit padded4DEulerGLM pad4CompatStartingMethod
            pad4CompatStartingMethod_constituents_isExplicit
            padded4DEulerGLM_isExplicit f y₀ h 2 = 0 := by
      intro h
      show (h * ∑ i : Fin 1,
          padded4DEulerGLM.B 2 i
            * f (padded4DEulerGLM.explicitStageValue f
                    (pad4CompatStartingMethod.applyExplicit f y₀ h) h i))
          + (padded4DEulerGLM.V *ᵥ pad4CompatStartingMethod.applyExplicit f y₀ h) 2
          = 0
      rw [pad4CompatStartingMethod_applyExplicit]
      simp [padded4DEulerGLM, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    have hES2 : ∀ h : ℝ,
        applyExactThenStarting_explicit pad4CompatStartingMethod
            pad4CompatStartingMethod_constituents_isExplicit
            f yex x₀ h 2 = 0 := by
      intro h
      show pad4CompatStartingMethod.applyExplicit f (yex (x₀ + h)) h 2 = 0
      rw [pad4CompatStartingMethod_applyExplicit]
      rfl
    have hcongr : (fun h : ℝ =>
        applyStartingThenStep_explicit padded4DEulerGLM pad4CompatStartingMethod
            pad4CompatStartingMethod_constituents_isExplicit
            padded4DEulerGLM_isExplicit f y₀ h 2
          - applyExactThenStarting_explicit pad4CompatStartingMethod
              pad4CompatStartingMethod_constituents_isExplicit
              f yex x₀ h 2) = (fun _ : ℝ => (0 : ℝ)) := by
      funext h; rw [hSM2, hES2]; ring
    rw [hcongr]
    exact Asymptotics.isBigO_zero _ _
  · -- i = 3 case: identical structure to i = 1, 2.
    change (fun h : ℝ =>
          applyStartingThenStep_explicit padded4DEulerGLM pad4CompatStartingMethod
              pad4CompatStartingMethod_constituents_isExplicit
              padded4DEulerGLM_isExplicit f y₀ h 3
            - applyExactThenStarting_explicit pad4CompatStartingMethod
                pad4CompatStartingMethod_constituents_isExplicit
                f yex x₀ h 3)
        =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (0 + 1))
    have hSM3 : ∀ h : ℝ,
        applyStartingThenStep_explicit padded4DEulerGLM pad4CompatStartingMethod
            pad4CompatStartingMethod_constituents_isExplicit
            padded4DEulerGLM_isExplicit f y₀ h 3 = 0 := by
      intro h
      show (h * ∑ i : Fin 1,
          padded4DEulerGLM.B 3 i
            * f (padded4DEulerGLM.explicitStageValue f
                    (pad4CompatStartingMethod.applyExplicit f y₀ h) h i))
          + (padded4DEulerGLM.V *ᵥ pad4CompatStartingMethod.applyExplicit f y₀ h) 3
          = 0
      rw [pad4CompatStartingMethod_applyExplicit]
      simp [padded4DEulerGLM, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    have hES3 : ∀ h : ℝ,
        applyExactThenStarting_explicit pad4CompatStartingMethod
            pad4CompatStartingMethod_constituents_isExplicit
            f yex x₀ h 3 = 0 := by
      intro h
      show pad4CompatStartingMethod.applyExplicit f (yex (x₀ + h)) h 3 = 0
      rw [pad4CompatStartingMethod_applyExplicit]
      rfl
    have hcongr : (fun h : ℝ =>
        applyStartingThenStep_explicit padded4DEulerGLM pad4CompatStartingMethod
            pad4CompatStartingMethod_constituents_isExplicit
            padded4DEulerGLM_isExplicit f y₀ h 3
          - applyExactThenStarting_explicit pad4CompatStartingMethod
              pad4CompatStartingMethod_constituents_isExplicit
              f yex x₀ h 3) = (fun _ : ℝ => (0 : ℝ)) := by
      funext h; rw [hSM3, hES3]; ring
    rw [hcongr]
    exact Asymptotics.isBigO_zero _ _

/-- **`r = 4`, `p = 1` non-vacuity (def:530B Path A, cycle 161).**
Mechanical port of `padded3DEulerGLM_hasOrderOne_pad3CompatStarting`
(cycle 159) to the 4-padded `(s, r) = (1, 4)` setting. The padded GLM
`padded4DEulerGLM` has order `1` relative to `pad4CompatStartingMethod`
under the cycle-154 hypothesis pack: `f` Lipschitz, `yex` is `C²`,
full ODE relation `∀ x, HasDerivAt yex (f (yex x)) x`, and
`yex x₀ = y₀`.

The row-0 channel is identical to cycle 154/157/159's Taylor +
Lipschitz closure (closed forms match exactly across the
`padCompat` / `pad3Compat` / `pad4Compat` starts on the active
row 0), and discharges via the cycle-158 shared helper
`taylor_lipschitz_explicitEuler_orderOne_diff_isBigO` as a one-line
invocation — validating its portability to a fourth call site. The
row-1, row-2, and row-3 channels are identically zero on both `SM`
and `ES` (cycle 156/157/159 zero-collapse pattern, exponent
`h ^ 2`). -/
theorem padded4DEulerGLM_hasOrderOne_pad4CompatStarting
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C2 : ContDiff ℝ 2 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    HasOrderRelativeTo_explicit padded4DEulerGLM pad4CompatStartingMethod
      pad4CompatStartingMethod_constituents_isExplicit
      padded4DEulerGLM_isExplicit
      1 f yex x₀ y₀ := by
  intro i
  fin_cases i
  · -- i = 0 case: identical algebraic shape to cycles 154 / 157 / 159.
    change (fun h : ℝ =>
          applyStartingThenStep_explicit padded4DEulerGLM pad4CompatStartingMethod
              pad4CompatStartingMethod_constituents_isExplicit
              padded4DEulerGLM_isExplicit f y₀ h 0
            - applyExactThenStarting_explicit pad4CompatStartingMethod
                pad4CompatStartingMethod_constituents_isExplicit
                f yex x₀ h 0)
        =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (1 + 1))
    -- SM[0] closed form
    have hSM : ∀ h : ℝ,
        applyStartingThenStep_explicit padded4DEulerGLM pad4CompatStartingMethod
            pad4CompatStartingMethod_constituents_isExplicit
            padded4DEulerGLM_isExplicit f y₀ h 0
          = (y₀ + h * f y₀) + h * f (y₀ + h * f y₀) := by
      intro h
      show (h * ∑ i : Fin 1,
          padded4DEulerGLM.B 0 i
            * f (padded4DEulerGLM.explicitStageValue f
                    (pad4CompatStartingMethod.applyExplicit f y₀ h) h i))
          + (padded4DEulerGLM.V *ᵥ pad4CompatStartingMethod.applyExplicit f y₀ h) 0
          = _
      rw [pad4CompatStartingMethod_applyExplicit]
      unfold OpenMath.Chapter5.Section510.GeneralLinearMethod.explicitStageValue
      simp [padded4DEulerGLM, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
      ring
    -- ES[0] closed form
    have hES : ∀ h : ℝ,
        applyExactThenStarting_explicit pad4CompatStartingMethod
            pad4CompatStartingMethod_constituents_isExplicit
            f yex x₀ h 0
          = yex (x₀ + h) + h * f (yex (x₀ + h)) := by
      intro h
      show pad4CompatStartingMethod.applyExplicit f (yex (x₀ + h)) h 0
          = yex (x₀ + h) + h * f (yex (x₀ + h))
      rw [pad4CompatStartingMethod_applyExplicit]
      rfl
    -- Rewrite SM[0] − ES[0] into the helper's input form.
    have hcongr :
        (fun h : ℝ =>
            applyStartingThenStep_explicit padded4DEulerGLM pad4CompatStartingMethod
                pad4CompatStartingMethod_constituents_isExplicit
                padded4DEulerGLM_isExplicit f y₀ h 0
              - applyExactThenStarting_explicit pad4CompatStartingMethod
                  pad4CompatStartingMethod_constituents_isExplicit
                  f yex x₀ h 0)
          = (fun h : ℝ =>
              ((y₀ + h * f y₀) + h * f (y₀ + h * f y₀))
                - (yex (x₀ + h) + h * f (yex (x₀ + h)))) := by
      funext h
      rw [hSM, hES]
    rw [hcongr]
    -- Collapse `h ^ (1 + 1)` to `h ^ 2`.
    have hpow : (fun h : ℝ => h ^ (1 + 1)) = (fun h : ℝ => h ^ 2) := by
      funext h; ring
    rw [hpow]
    -- Discharge via the cycle-158 shared helper.
    exact taylor_lipschitz_explicitEuler_orderOne_diff_isBigO
      hf_lip hyex_x₀ hyex_C2 hyex_ode
  · -- i = 1 case: SM[1] = ES[1] = 0; the difference is identically zero.
    change (fun h : ℝ =>
          applyStartingThenStep_explicit padded4DEulerGLM pad4CompatStartingMethod
              pad4CompatStartingMethod_constituents_isExplicit
              padded4DEulerGLM_isExplicit f y₀ h 1
            - applyExactThenStarting_explicit pad4CompatStartingMethod
                pad4CompatStartingMethod_constituents_isExplicit
                f yex x₀ h 1)
        =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (1 + 1))
    have hSM1 : ∀ h : ℝ,
        applyStartingThenStep_explicit padded4DEulerGLM pad4CompatStartingMethod
            pad4CompatStartingMethod_constituents_isExplicit
            padded4DEulerGLM_isExplicit f y₀ h 1 = 0 := by
      intro h
      show (h * ∑ i : Fin 1,
          padded4DEulerGLM.B 1 i
            * f (padded4DEulerGLM.explicitStageValue f
                    (pad4CompatStartingMethod.applyExplicit f y₀ h) h i))
          + (padded4DEulerGLM.V *ᵥ pad4CompatStartingMethod.applyExplicit f y₀ h) 1
          = 0
      rw [pad4CompatStartingMethod_applyExplicit]
      simp [padded4DEulerGLM, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    have hES1 : ∀ h : ℝ,
        applyExactThenStarting_explicit pad4CompatStartingMethod
            pad4CompatStartingMethod_constituents_isExplicit
            f yex x₀ h 1 = 0 := by
      intro h
      show pad4CompatStartingMethod.applyExplicit f (yex (x₀ + h)) h 1 = 0
      rw [pad4CompatStartingMethod_applyExplicit]
      rfl
    have hcongr : (fun h : ℝ =>
        applyStartingThenStep_explicit padded4DEulerGLM pad4CompatStartingMethod
            pad4CompatStartingMethod_constituents_isExplicit
            padded4DEulerGLM_isExplicit f y₀ h 1
          - applyExactThenStarting_explicit pad4CompatStartingMethod
              pad4CompatStartingMethod_constituents_isExplicit
              f yex x₀ h 1) = (fun _ : ℝ => (0 : ℝ)) := by
      funext h; rw [hSM1, hES1]; ring
    rw [hcongr]
    exact Asymptotics.isBigO_zero _ _
  · -- i = 2 case: identical structure to i = 1.
    change (fun h : ℝ =>
          applyStartingThenStep_explicit padded4DEulerGLM pad4CompatStartingMethod
              pad4CompatStartingMethod_constituents_isExplicit
              padded4DEulerGLM_isExplicit f y₀ h 2
            - applyExactThenStarting_explicit pad4CompatStartingMethod
                pad4CompatStartingMethod_constituents_isExplicit
                f yex x₀ h 2)
        =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (1 + 1))
    have hSM2 : ∀ h : ℝ,
        applyStartingThenStep_explicit padded4DEulerGLM pad4CompatStartingMethod
            pad4CompatStartingMethod_constituents_isExplicit
            padded4DEulerGLM_isExplicit f y₀ h 2 = 0 := by
      intro h
      show (h * ∑ i : Fin 1,
          padded4DEulerGLM.B 2 i
            * f (padded4DEulerGLM.explicitStageValue f
                    (pad4CompatStartingMethod.applyExplicit f y₀ h) h i))
          + (padded4DEulerGLM.V *ᵥ pad4CompatStartingMethod.applyExplicit f y₀ h) 2
          = 0
      rw [pad4CompatStartingMethod_applyExplicit]
      simp [padded4DEulerGLM, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    have hES2 : ∀ h : ℝ,
        applyExactThenStarting_explicit pad4CompatStartingMethod
            pad4CompatStartingMethod_constituents_isExplicit
            f yex x₀ h 2 = 0 := by
      intro h
      show pad4CompatStartingMethod.applyExplicit f (yex (x₀ + h)) h 2 = 0
      rw [pad4CompatStartingMethod_applyExplicit]
      rfl
    have hcongr : (fun h : ℝ =>
        applyStartingThenStep_explicit padded4DEulerGLM pad4CompatStartingMethod
            pad4CompatStartingMethod_constituents_isExplicit
            padded4DEulerGLM_isExplicit f y₀ h 2
          - applyExactThenStarting_explicit pad4CompatStartingMethod
              pad4CompatStartingMethod_constituents_isExplicit
              f yex x₀ h 2) = (fun _ : ℝ => (0 : ℝ)) := by
      funext h; rw [hSM2, hES2]; ring
    rw [hcongr]
    exact Asymptotics.isBigO_zero _ _
  · -- i = 3 case: identical structure to i = 1, 2.
    change (fun h : ℝ =>
          applyStartingThenStep_explicit padded4DEulerGLM pad4CompatStartingMethod
              pad4CompatStartingMethod_constituents_isExplicit
              padded4DEulerGLM_isExplicit f y₀ h 3
            - applyExactThenStarting_explicit pad4CompatStartingMethod
                pad4CompatStartingMethod_constituents_isExplicit
                f yex x₀ h 3)
        =O[nhds (0 : ℝ)] (fun h : ℝ => h ^ (1 + 1))
    have hSM3 : ∀ h : ℝ,
        applyStartingThenStep_explicit padded4DEulerGLM pad4CompatStartingMethod
            pad4CompatStartingMethod_constituents_isExplicit
            padded4DEulerGLM_isExplicit f y₀ h 3 = 0 := by
      intro h
      show (h * ∑ i : Fin 1,
          padded4DEulerGLM.B 3 i
            * f (padded4DEulerGLM.explicitStageValue f
                    (pad4CompatStartingMethod.applyExplicit f y₀ h) h i))
          + (padded4DEulerGLM.V *ᵥ pad4CompatStartingMethod.applyExplicit f y₀ h) 3
          = 0
      rw [pad4CompatStartingMethod_applyExplicit]
      simp [padded4DEulerGLM, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    have hES3 : ∀ h : ℝ,
        applyExactThenStarting_explicit pad4CompatStartingMethod
            pad4CompatStartingMethod_constituents_isExplicit
            f yex x₀ h 3 = 0 := by
      intro h
      show pad4CompatStartingMethod.applyExplicit f (yex (x₀ + h)) h 3 = 0
      rw [pad4CompatStartingMethod_applyExplicit]
      rfl
    have hcongr : (fun h : ℝ =>
        applyStartingThenStep_explicit padded4DEulerGLM pad4CompatStartingMethod
            pad4CompatStartingMethod_constituents_isExplicit
            padded4DEulerGLM_isExplicit f y₀ h 3
          - applyExactThenStarting_explicit pad4CompatStartingMethod
              pad4CompatStartingMethod_constituents_isExplicit
              f yex x₀ h 3) = (fun _ : ℝ => (0 : ℝ)) := by
      funext h; rw [hSM3, hES3]; ring
    rw [hcongr]
    exact Asymptotics.isBigO_zero _ _

/-- **Non-vacuity of `HasOrder_explicit` at `r = 4`, `p = 0` (cycle 161).**
Mirrors `padded3DEulerGLM_hasOrderZero` shape: exhibits
`pad4CompatStartingMethod` as the existential witness for
`padded4DEulerGLM`. The starting method is non-degenerate
(`pad4CompatStartingMethod_isNonDegenerate`) and has explicit constituents
(`pad4CompatStartingMethod_constituents_isExplicit`); the
`HasOrderRelativeTo_explicit` component is supplied by
`padded4DEulerGLM_hasOrderZero_pad4CompatStarting`. -/
theorem padded4DEulerGLM_hasOrderZero
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_deriv : HasDerivAt yex (f y₀) x₀) :
    HasOrder_explicit padded4DEulerGLM padded4DEulerGLM_isExplicit
      0 f yex x₀ y₀ := by
  refine ⟨pad4CompatStartingMethod,
          pad4CompatStartingMethod_constituents_isExplicit,
          pad4CompatStartingMethod_isNonDegenerate,
          ?_⟩
  exact padded4DEulerGLM_hasOrderZero_pad4CompatStarting
          hf_lip hyex_x₀ hyex_deriv

/-- **Non-vacuity of `HasOrder_explicit` at `r = 4`, `p = 1` (cycle 161).**
Refines `padded4DEulerGLM_hasOrderZero` to `p = 1` under the cycle-154
hypothesis pack (`LipschitzWith L f`, `ContDiff ℝ 2 yex`, full ODE
relation, `yex x₀ = y₀`). The starting method is
`pad4CompatStartingMethod`; the `HasOrderRelativeTo_explicit` component
is supplied by `padded4DEulerGLM_hasOrderOne_pad4CompatStarting`. -/
theorem padded4DEulerGLM_hasOrderOne
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C2 : ContDiff ℝ 2 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    HasOrder_explicit padded4DEulerGLM padded4DEulerGLM_isExplicit
      1 f yex x₀ y₀ := by
  refine ⟨pad4CompatStartingMethod,
          pad4CompatStartingMethod_constituents_isExplicit,
          pad4CompatStartingMethod_isNonDegenerate,
          ?_⟩
  exact padded4DEulerGLM_hasOrderOne_pad4CompatStarting
          hf_lip hyex_x₀ hyex_C2 hyex_ode

/-! ### Cycle 163 Phase B.1 — parametric `r`-indexed witnesses

Two parametric `HasOrderRelativeTo_explicit` theorems indexed by
`r : ℕ`, replacing the four hand-written `r ∈ {1, 2, 3, 4}` ×
`p ∈ {0, 1}` pairs (cycles 153/155/156/157/159/161) with two
parametric proofs. The `i.val = 0` channel is the substantive
Taylor + Lipschitz closure (cycle 158/160 helpers); the `i.val ≠ 0`
channels collapse to identically zero. -/

/-- Row-0 entries of `paddedREulerGLM r`'s `U` block evaluate
indicator-style: column `j` is `1` iff `j.val = 0`, and `0` otherwise.
Internal helper for cycle 163 Phase B.1. -/
private lemma paddedREulerGLM_U_apply (r : ℕ) (j : Fin (r + 1)) :
    (paddedREulerGLM r).U 0 j = if j.val = 0 then (1 : ℝ) else 0 :=
  rfl

/-- `B`-block entries of `paddedREulerGLM r` evaluate indicator-style:
row `i` is `1` iff `i.val = 0`, and `0` otherwise (the only column is
`0 : Fin 1`). Internal helper for cycle 163 Phase B.1. -/
private lemma paddedREulerGLM_B_apply (r : ℕ) (i : Fin (r + 1))
    (k : Fin 1) :
    (paddedREulerGLM r).B i k = if i.val = 0 then (1 : ℝ) else 0 :=
  rfl

/-- `V`-block entries of `paddedREulerGLM r` evaluate indicator-style:
the entry at `(i, j)` is `1` iff both `i.val = 0` and `j.val = 0`, and
`0` otherwise. Internal helper for cycle 163 Phase B.1. -/
private lemma paddedREulerGLM_V_apply (r : ℕ) (i j : Fin (r + 1)) :
    (paddedREulerGLM r).V i j =
      if i.val = 0 ∧ j.val = 0 then (1 : ℝ) else 0 :=
  rfl

/-- The dot product `(paddedREulerGLM r).U *ᵥ v` at the single row 0
collapses to `v 0`: the indicator `if j.val = 0 then 1 else 0` selects
exactly the index `0 : Fin (r + 1)`. Internal helper for cycle 163
Phase B.1. -/
private lemma paddedREulerGLM_U_mulVec_zero (r : ℕ)
    (v : Fin (r + 1) → ℝ) :
    ((paddedREulerGLM r).U *ᵥ v) 0 = v 0 := by
  show ∑ j : Fin (r + 1), (paddedREulerGLM r).U 0 j * v j = v 0
  rw [Finset.sum_eq_single (0 : Fin (r + 1))]
  · rw [paddedREulerGLM_U_apply]
    simp
  · intro j _ hj
    have hjval : j.val ≠ 0 := fun hv => hj (Fin.ext hv)
    rw [paddedREulerGLM_U_apply]
    simp [hjval]
  · intro hcontra
    exact absurd (Finset.mem_univ _) hcontra

/-- The dot product `(paddedREulerGLM r).V *ᵥ v` at row `i` collapses
to `v 0` if `i.val = 0` and to `0` otherwise: the indicator
`if i.val = 0 ∧ j.val = 0 then 1 else 0` selects exactly the index
`0 : Fin (r + 1)` in the `i.val = 0` channel and is identically zero
in the `i.val ≠ 0` channels. Internal helper for cycle 163
Phase B.1. -/
private lemma paddedREulerGLM_V_mulVec_apply (r : ℕ)
    (v : Fin (r + 1) → ℝ) (i : Fin (r + 1)) :
    ((paddedREulerGLM r).V *ᵥ v) i =
      if i.val = 0 then v 0 else 0 := by
  show ∑ j : Fin (r + 1), (paddedREulerGLM r).V i j * v j
        = if i.val = 0 then v 0 else 0
  by_cases hi : i.val = 0
  · rw [if_pos hi]
    rw [Finset.sum_eq_single (0 : Fin (r + 1))]
    · rw [paddedREulerGLM_V_apply]
      simp [hi]
    · intro j _ hj
      have hjval : j.val ≠ 0 := fun hv => hj (Fin.ext hv)
      rw [paddedREulerGLM_V_apply]
      simp [hi, hjval]
    · intro hcontra
      exact absurd (Finset.mem_univ _) hcontra
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j _
    rw [paddedREulerGLM_V_apply]
    simp [hi]

/-- `paddedREulerGLM r`'s internal stage value at the single stage
`0 : Fin 1` collapses to `(U *ᵥ y_input) 0 = y_input 0` (the `Fin 0`
sum in the recursion body is empty). Internal helper for cycle 163
Phase B.1. -/
private lemma paddedREulerGLM_explicitStageValue_zero (r : ℕ)
    (f : ℝ → ℝ) (y_input : Fin (r + 1) → ℝ) (h : ℝ) :
    (paddedREulerGLM r).explicitStageValue f y_input h 0 = y_input 0 := by
  unfold OpenMath.Chapter5.Section510.GeneralLinearMethod.explicitStageValue
  simp [paddedREulerGLM_U_mulVec_zero]

/-- `applyStartingThenStep_explicit` against `paddedREulerGLM r` and
`padCompatStartingMethodR r` collapses componentwise: the row-0 channel
returns the closed-form two-Euler-step `(y₀ + h·f y₀) + h · f(y₀ + h·f y₀)`,
and rows `1, …, r` return identically `0` (passive zero channels).
Internal helper for cycle 163 Phase B.1; the form is identical for
both `p = 0` and `p = 1` witnesses. -/
private lemma paddedREulerGLM_applyStartingThenStep_explicit_apply
    (r : ℕ) (f : ℝ → ℝ) (y₀ h : ℝ) (i : Fin (r + 1)) :
    applyStartingThenStep_explicit (paddedREulerGLM r)
        (padCompatStartingMethodR r)
        (padCompatStartingMethodR_constituents_isExplicit r)
        (paddedREulerGLM_isExplicit r) f y₀ h i
      = if i.val = 0 then
          (y₀ + h * f y₀) + h * f (y₀ + h * f y₀)
        else 0 := by
  show (h * ∑ k : Fin 1,
        (paddedREulerGLM r).B i k
          * f ((paddedREulerGLM r).explicitStageValue f
                  ((padCompatStartingMethodR r).applyExplicit f y₀ h) h k))
      + ((paddedREulerGLM r).V
            *ᵥ (padCompatStartingMethodR r).applyExplicit f y₀ h) i
      = if i.val = 0 then (y₀ + h * f y₀) + h * f (y₀ + h * f y₀) else 0
  rw [padCompatStartingMethodR_applyExplicit]
  rw [Fin.sum_univ_one]
  rw [paddedREulerGLM_B_apply]
  rw [paddedREulerGLM_explicitStageValue_zero]
  rw [paddedREulerGLM_V_mulVec_apply]
  by_cases hi : i.val = 0
  · simp [hi]; ring
  · simp [hi]

/-- `applyExactThenStarting_explicit` against `padCompatStartingMethodR r`
collapses componentwise: the row-0 channel returns the closed form
`yex(x₀ + h) + h · f(yex(x₀ + h))`, and rows `1, …, r` return
identically `0`. Internal helper for cycle 163 Phase B.1. -/
private lemma paddedREulerGLM_applyExactThenStarting_explicit_apply
    (r : ℕ) (f : ℝ → ℝ) (yex : ℝ → ℝ) (x₀ h : ℝ) (i : Fin (r + 1)) :
    applyExactThenStarting_explicit (padCompatStartingMethodR r)
        (padCompatStartingMethodR_constituents_isExplicit r)
        f yex x₀ h i
      = if i.val = 0 then
          yex (x₀ + h) + h * f (yex (x₀ + h))
        else 0 := by
  show (padCompatStartingMethodR r).applyExplicit f (yex (x₀ + h)) h i
      = if i.val = 0 then yex (x₀ + h) + h * f (yex (x₀ + h)) else 0
  rw [padCompatStartingMethodR_applyExplicit]

/-- **`def:530B` Path A, parametric `p = 0` non-vacuity (cycle 163
Phase B.1).** For every `r : ℕ`, the parametric padded Euler GLM
`paddedREulerGLM r` has order `0` relative to the parametric padded
starting method `padCompatStartingMethodR r` on any IVP whose exact
solution `yex` satisfies `yex x₀ = y₀` and
`HasDerivAt yex (f y₀) x₀`, with `f` Lipschitz with constant `L`.

Subsumes the four hand-written `r ∈ {1, 2, 3, 4}` instances
(cycles 153/156/159/161): the row-0 (active) channel discharges via
the cycle 160 shared helper
`taylor_lipschitz_explicitEuler_orderZero_diff_isBigO`; rows
`1, …, r` (passive zero channels) collapse via
`Asymptotics.isBigO_zero`. -/
theorem paddedREulerGLM_hasOrderZero_padCompatStartingR (r : ℕ)
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_deriv : HasDerivAt yex (f y₀) x₀) :
    HasOrderRelativeTo_explicit
      (paddedREulerGLM r) (padCompatStartingMethodR r)
      (padCompatStartingMethodR_constituents_isExplicit r)
      (paddedREulerGLM_isExplicit r)
      0 f yex x₀ y₀ := by
  intro i
  by_cases hi : i.val = 0
  · -- i.val = 0 channel: substantive Taylor + Lipschitz closure.
    have hcongr :
        (fun h : ℝ =>
            applyStartingThenStep_explicit (paddedREulerGLM r)
                (padCompatStartingMethodR r)
                (padCompatStartingMethodR_constituents_isExplicit r)
                (paddedREulerGLM_isExplicit r) f y₀ h i
              - applyExactThenStarting_explicit
                  (padCompatStartingMethodR r)
                  (padCompatStartingMethodR_constituents_isExplicit r)
                  f yex x₀ h i)
          = (fun h : ℝ =>
              ((y₀ + h * f y₀) + h * f (y₀ + h * f y₀))
                - (yex (x₀ + h) + h * f (yex (x₀ + h)))) := by
      funext h
      rw [paddedREulerGLM_applyStartingThenStep_explicit_apply,
          paddedREulerGLM_applyExactThenStarting_explicit_apply]
      simp [hi]
    rw [hcongr]
    -- Collapse `h ^ (0 + 1)` to `h`.
    have hpow : (fun h : ℝ => h ^ (0 + 1)) = (fun h : ℝ => h) := by
      funext h; simp
    rw [hpow]
    -- Discharge via the cycle-160 shared helper.
    exact taylor_lipschitz_explicitEuler_orderZero_diff_isBigO
      hf_lip hyex_x₀ hyex_deriv
  · -- i.val ≠ 0 channel: SM[i] = ES[i] = 0; Diff = 0.
    have hcongr :
        (fun h : ℝ =>
            applyStartingThenStep_explicit (paddedREulerGLM r)
                (padCompatStartingMethodR r)
                (padCompatStartingMethodR_constituents_isExplicit r)
                (paddedREulerGLM_isExplicit r) f y₀ h i
              - applyExactThenStarting_explicit
                  (padCompatStartingMethodR r)
                  (padCompatStartingMethodR_constituents_isExplicit r)
                  f yex x₀ h i)
          = (fun _ : ℝ => (0 : ℝ)) := by
      funext h
      rw [paddedREulerGLM_applyStartingThenStep_explicit_apply,
          paddedREulerGLM_applyExactThenStarting_explicit_apply]
      simp [hi]
    rw [hcongr]
    exact Asymptotics.isBigO_zero _ _

/-- **`def:530B` Path A, parametric `p = 1` non-vacuity (cycle 163
Phase B.1).** For every `r : ℕ`, the parametric padded Euler GLM
`paddedREulerGLM r` has order `1` relative to the parametric padded
starting method `padCompatStartingMethodR r` under the cycle-154
hypothesis pack: `f` Lipschitz, `yex` is `C²`, full ODE relation
`∀ x, HasDerivAt yex (f (yex x)) x`, and `yex x₀ = y₀`.

Subsumes the four hand-written `r ∈ {1, 2, 3, 4}` instances
(cycles 155/157/159/161): the row-0 (active) channel discharges via
the cycle 158 shared helper
`taylor_lipschitz_explicitEuler_orderOne_diff_isBigO`; rows
`1, …, r` (passive zero channels) collapse via
`Asymptotics.isBigO_zero`. -/
theorem paddedREulerGLM_hasOrderOne_padCompatStartingR (r : ℕ)
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C2 : ContDiff ℝ 2 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    HasOrderRelativeTo_explicit
      (paddedREulerGLM r) (padCompatStartingMethodR r)
      (padCompatStartingMethodR_constituents_isExplicit r)
      (paddedREulerGLM_isExplicit r)
      1 f yex x₀ y₀ := by
  intro i
  by_cases hi : i.val = 0
  · -- i.val = 0 channel: substantive Taylor + Lipschitz closure.
    have hcongr :
        (fun h : ℝ =>
            applyStartingThenStep_explicit (paddedREulerGLM r)
                (padCompatStartingMethodR r)
                (padCompatStartingMethodR_constituents_isExplicit r)
                (paddedREulerGLM_isExplicit r) f y₀ h i
              - applyExactThenStarting_explicit
                  (padCompatStartingMethodR r)
                  (padCompatStartingMethodR_constituents_isExplicit r)
                  f yex x₀ h i)
          = (fun h : ℝ =>
              ((y₀ + h * f y₀) + h * f (y₀ + h * f y₀))
                - (yex (x₀ + h) + h * f (yex (x₀ + h)))) := by
      funext h
      rw [paddedREulerGLM_applyStartingThenStep_explicit_apply,
          paddedREulerGLM_applyExactThenStarting_explicit_apply]
      simp [hi]
    rw [hcongr]
    -- Collapse `h ^ (1 + 1)` to `h ^ 2`.
    have hpow : (fun h : ℝ => h ^ (1 + 1)) = (fun h : ℝ => h ^ 2) := by
      funext h; ring
    rw [hpow]
    -- Discharge via the cycle-158 shared helper.
    exact taylor_lipschitz_explicitEuler_orderOne_diff_isBigO
      hf_lip hyex_x₀ hyex_C2 hyex_ode
  · -- i.val ≠ 0 channel: SM[i] = ES[i] = 0; Diff = 0.
    have hcongr :
        (fun h : ℝ =>
            applyStartingThenStep_explicit (paddedREulerGLM r)
                (padCompatStartingMethodR r)
                (padCompatStartingMethodR_constituents_isExplicit r)
                (paddedREulerGLM_isExplicit r) f y₀ h i
              - applyExactThenStarting_explicit
                  (padCompatStartingMethodR r)
                  (padCompatStartingMethodR_constituents_isExplicit r)
                  f yex x₀ h i)
          = (fun _ : ℝ => (0 : ℝ)) := by
      funext h
      rw [paddedREulerGLM_applyStartingThenStep_explicit_apply,
          paddedREulerGLM_applyExactThenStarting_explicit_apply]
      simp [hi]
    rw [hcongr]
    exact Asymptotics.isBigO_zero _ _

/-- **`def:530C` parametric `p = 0` non-vacuity (cycle 163 Phase B.2).**
For every `r : ℕ`, the parametric padded Euler GLM `paddedREulerGLM r`
has order `0` (in the existential `HasOrder_explicit` sense) under the
cycle-153 hypothesis pack. Exhibits `padCompatStartingMethodR r` as
the existential witness; non-degeneracy and explicit-constituent status
are supplied by the cycle 162 helpers
`padCompatStartingMethodR_isNonDegenerate` and
`padCompatStartingMethodR_constituents_isExplicit`; the
`HasOrderRelativeTo_explicit` component is supplied by
`paddedREulerGLM_hasOrderZero_padCompatStartingR`. Subsumes the four
hand-written `r ∈ {1, 2, 3, 4}` instances. -/
theorem paddedREulerGLM_hasOrderZero (r : ℕ)
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_deriv : HasDerivAt yex (f y₀) x₀) :
    HasOrder_explicit (paddedREulerGLM r) (paddedREulerGLM_isExplicit r)
      0 f yex x₀ y₀ := by
  refine ⟨padCompatStartingMethodR r,
          padCompatStartingMethodR_constituents_isExplicit r,
          padCompatStartingMethodR_isNonDegenerate r,
          ?_⟩
  exact paddedREulerGLM_hasOrderZero_padCompatStartingR r
          hf_lip hyex_x₀ hyex_deriv

/-- **`def:530C` parametric `p = 1` non-vacuity (cycle 163 Phase B.2).**
For every `r : ℕ`, the parametric padded Euler GLM `paddedREulerGLM r`
has order `1` (in the existential `HasOrder_explicit` sense) under the
cycle-154 hypothesis pack. Exhibits `padCompatStartingMethodR r` as
the existential witness; the `HasOrderRelativeTo_explicit` component
is supplied by `paddedREulerGLM_hasOrderOne_padCompatStartingR`.
Subsumes the four hand-written `r ∈ {1, 2, 3, 4}` instances. -/
theorem paddedREulerGLM_hasOrderOne (r : ℕ)
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C2 : ContDiff ℝ 2 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    HasOrder_explicit (paddedREulerGLM r) (paddedREulerGLM_isExplicit r)
      1 f yex x₀ y₀ := by
  refine ⟨padCompatStartingMethodR r,
          padCompatStartingMethodR_constituents_isExplicit r,
          padCompatStartingMethodR_isNonDegenerate r,
          ?_⟩
  exact paddedREulerGLM_hasOrderOne_padCompatStartingR r
          hf_lip hyex_x₀ hyex_C2 hyex_ode

end OrderRelativeTo

end OpenMath.Chapter5.Section530
