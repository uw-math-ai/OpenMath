import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
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

/-! ## Definition 530B — Order relative to a starting method

This section opens Definition 530B (Butcher §530, p. 432):

> Consider a general linear method `M` and a non-degenerate starting
> method `S`. The method `M` has order `p` relative to `S` if the
> results found from `SM` and `ES` agree to within `O(h^{p+1})`.

### Notation (Butcher §530, p. 411)

* `SM` — the vector of results obtained by **first** applying the
  starting method `S` to a scalar input value `y₀ ≈ y(x₀)` to produce
  `r` initial approximations, **then** carrying out one step of `M`
  with stepsize `h`.
* `ES` — the vector of approximations obtained by **first** advancing
  the *exact* solution forward by time `h` to obtain `y(x₀ + h)`,
  **then** applying each constituent method `Sᵢ` of `S` to that
  scalar.

Both `SM(y₀, h)` and `ES(y₀, h)` are `Fin r → ℝ` vectors, and the
textbook's "agree to within `O(h^{p+1})`" means
`‖SM(y₀, h) − ES(y₀, h)‖ = O(h^{p+1})` as `h → 0`.

### Sorry-first scaffold (cycle 149)

The two operators `applyStartingThenStep` (the textbook `SM`) and
`applyExactThenStarting` (the textbook `ES`) are introduced as
`noncomputable def`s with `sorry` bodies. Computing them faithfully
requires:

* For `SM`: solving the (in general implicit) stage equations of each
  constituent generalized Runge–Kutta method `Sᵢ` to produce the
  initial vector, then applying the GLM step formula
  `Y = A·η·D + U·ξ`, `y_out = B·η·D + V·ξ`. Both pieces involve
  multivariate fixed-point arguments that are out of scope for a
  scaffold cycle.
* For `ES`: evaluating the exact-solution flow `y(x₀ + h)` and then
  running each `Sᵢ` on that scalar, with the same implicit-stage
  caveat.

The cycle 149 deliverable bar is: predicate compiles, non-vacuity
witness exists (sorry-first OK). Cycle 150+ closes the operator
bodies and the witness. The sorry locus is documented in
`.prover-state/task_results/cycle_149.md`.
-/

section OrderRelativeToStartingMethod

open OpenMath.Chapter5.Section510

variable {s r : ℕ}

/-- **Textbook `SM`** (Butcher §530, p. 411). The vector of results
obtained by first applying starting method `S` to scalar `y₀` (yielding
an `r`-vector of initial approximations), then carrying out one step
of GLM `M` with stepsize `h`.

Sorry-first scaffold (cycle 149): the body is deferred. The textbook
quantities are:

* `Sᵢ(y₀, h) = b₀⁽ⁱ⁾ · y₀ + h · ∑ⱼ b⁽ⁱ⁾ⱼ · f(Yⱼ⁽ⁱ⁾)` for each
  `i = 1, …, r`, where the stages `Yⱼ⁽ⁱ⁾` solve
  `Yⱼ⁽ⁱ⁾ = y₀ + h · ∑ₖ A⁽ⁱ⁾ⱼₖ · f(Yₖ⁽ⁱ⁾)`.
* Then one M-step on the `r`-vector input `(S₁(y₀,h), …, S_r(y₀,h))`
  via the GLM tableau `(A, U, B, V)`. -/
noncomputable def applyStartingThenStep
    (M : GeneralLinearMethod s r) (S : StartingMethod r)
    (f : ℝ → ℝ) (y₀ h : ℝ) : Fin r → ℝ :=
  sorry

/-- **Textbook `ES`** (Butcher §530, p. 411). The vector of
approximations obtained by first advancing the exact solution by time
`h` from `x₀` to obtain `yex(x₀ + h)`, then applying each constituent
`Sᵢ` of the starting method `S` to that scalar.

Sorry-first scaffold (cycle 149): the body is deferred. The textbook
quantity at index `i` is `Sᵢ(yex(x₀ + h), h)`; see
`applyStartingThenStep` for the stage-evaluation formula. -/
noncomputable def applyExactThenStarting
    (S : StartingMethod r) (yex : ℝ → ℝ) (x₀ h : ℝ) : Fin r → ℝ :=
  sorry

/-- **Definition 530B (Butcher §530, p. 432).**
A general linear method `M` has *order `p` relative to a non-degenerate
starting method `S`* if, for every autonomous ODE `y' = f(y)` with
exact solution `yex` satisfying `yex(x₀) = y₀`, the difference
`SM(y₀, h) − ES(y₀, h)` is `O(h^{p+1})` as `h → 0`.

Textbook (verbatim from `entities/def_530B.json`):

> Consider a general linear method `M` and a non-degenerate starting
> method `S`. The method `M` has order `p` relative to `S` if the
> results found from `SM` and `ES` agree to within `O(h^{p+1})`.

### Encoding choices

* The non-degeneracy hypothesis `_hS : S.IsNonDegenerate` is included
  to match the textbook's "Consider a general linear method `M` and
  a non-degenerate starting method `S`" — degenerate `S` is excluded
  from the definition's scope. The hypothesis does not enter the
  predicate body; downstream theorems can use it as needed.
* The differential-equation context is encoded by quantifying over
  the right-hand side `f : ℝ → ℝ` (autonomous scalar ODE), the exact
  solution `yex : ℝ → ℝ`, the initial time `x₀`, and the initial
  value `y₀`, with hypotheses `yex x₀ = y₀` and
  `∀ t, HasDerivAt yex (f (yex t)) t` pinning `yex` as the exact
  solution to `yex' = f ∘ yex` with the prescribed initial condition.
* The "agree to `O(h^{p+1})`" condition is encoded as
  `Asymptotics.IsBigO` at the filter `nhds (0 : ℝ)` of the difference
  vector `SM − ES : Fin r → ℝ` against the comparison function
  `h ↦ h^{p+1} : ℝ`. The `Fin r → ℝ` codomain has its standard
  product norm via `Pi.normedAddCommGroup`, so the Big-O comparison
  is well-formed. -/
def HasOrderRelativeTo
    (M : GeneralLinearMethod s r) (S : StartingMethod r)
    (_hS : S.IsNonDegenerate) (p : ℕ) : Prop :=
  ∀ (f : ℝ → ℝ) (yex : ℝ → ℝ) (x₀ y₀ : ℝ),
    yex x₀ = y₀ → (∀ t, HasDerivAt yex (f (yex t)) t) →
    Asymptotics.IsBigO (nhds (0 : ℝ))
      (fun h : ℝ =>
        applyStartingThenStep M S f y₀ h
          - applyExactThenStarting S yex x₀ h)
      (fun h : ℝ => h ^ (p + 1))

/-- **Non-vacuity (sorry-first, cycle 149).** The explicit-Euler GLM
has order `0` relative to the trivial starting method.

This witness is intentionally chosen as the most degenerate non-trivial
shape: `(s, r) = (1, 1)` GLM and `r = 1` starting method, with `p = 0`
(the weakest possible order claim — agreement to `O(h)`). It is
sorry'd in cycle 149 because the bodies of `applyStartingThenStep` and
`applyExactThenStarting` are themselves sorry'd; once those are closed
in a future cycle, this witness becomes a one- or two-line argument
(both sides equal `y₀` at `h = 0`, so the difference is continuous and
vanishes at `0`, giving the Big-O bound trivially). -/
theorem explicitEulerGLM_hasOrderZero_trivialStarting :
    HasOrderRelativeTo explicitEulerGLM trivialStartingMethod
      trivialStartingMethod_isNonDegenerate 0 := by
  sorry

end OrderRelativeToStartingMethod

end OpenMath.Chapter5.Section530
