# Issue: def:530B sorry-first scaffold not viable as single-cycle deliverable

## Blocker

Definition 530B (Butcher §530, p. 432) — "method `M` has order `p`
relative to a non-degenerate starting method `S` if the results found
from `SM` and `ES` agree to within `O(h^{p+1})`" — requires defining
two operators:

* `applyStartingThenStep` (textbook `SM`): apply each constituent
  generalized RK method `Sᵢ` to scalar `y₀` to produce `r` initial
  approximations, then carry out one GLM step.
* `applyExactThenStarting` (textbook `ES`): advance the exact
  solution by time `h`, then apply each `Sᵢ` to that scalar.

Both operator bodies require **multivariate fixed-point arguments**
to solve the implicit stage equations of each `Sᵢ`. They are NOT
decomposable into named sub-helpers — they are indivisible
fixed-point computations.

Cycle 149 attempted a sorry-first scaffold:

* `noncomputable def applyStartingThenStep` with `sorry` body.
* `noncomputable def applyExactThenStarting` with `sorry` body.
* `def HasOrderRelativeTo` (the predicate, no sorry).
* `theorem explicitEulerGLM_hasOrderZero_trivialStarting` non-vacuity
  witness with `sorry` body (depends on the operator-body sorries).

Sorry count went 0 → 3 (regression −2). Cycle 150 rolled back per
the cycle 138 → cycle 139 precedent (which rolled back the sorry'd
general-n statement of thm:550A added in cycle 138).

## Context

The cycle 149 scaffold was structurally sound — the predicate
encodes Butcher's "agree to within `O(h^{p+1})`" verbatim via
`Asymptotics.IsBigO (nhds (0 : ℝ))` of the difference vector
`SM(y₀, h) - ES(y₀, h) : Fin r → ℝ` against `h^{p+1}`. The
non-vacuity witness was for the most degenerate non-trivial shape:
`(s, r) = (1, 1)` explicit Euler GLM × `r = 1` trivial starting
method, claiming order `p = 0`. Once the operator bodies close, the
witness becomes a one- or two-line argument (both sides equal `y₀`
at `h = 0`, so the difference is continuous and vanishes at `0`).

The structural problem: **the sorry-first workflow assumes the
to-be-closed body decomposes into named sub-lemmas that can be
proved one-by-one**. The cycle-149 operator bodies do not — they
are atomic fixed-point computations.

## What was tried

* Cycle 149 worker wrote the four sorry-first declarations in
  `OpenMath/Chapter5/Section530.lean` (lines ~327-400 in cycle
  149's file state) plus three new imports
  (`Mathlib.Analysis.Asymptotics.Defs`,
  `Mathlib.Analysis.Calculus.Deriv.Basic`,
  `OpenMath.Chapter5.Section510`).
* Cycle 149 worker's own analysis: closure needs Path A
  (explicit-only restricted operators, ~2-3 cycles) or Path B
  (general implicit via fixed-point, ~3-5 cycles).

## Possible solutions

### Path A — Explicit-only operators with `IsExplicit` predicate

Restrict to the explicit case where `A^{(i)}` is strictly lower
triangular for every constituent method `Sᵢ`. Then the stage
equations `Yⱼ = y₀ + h · Σₖ A^{(i)}ⱼₖ · f(Yₖ)` are not implicit —
they can be evaluated by direct recursion on `j = 0, 1, …, sᵢ-1`.

Plan:
1. Cycle N: introduce `def IsExplicit (M : GeneralizedRungeKuttaMethod s) : Prop`
   capturing strict-lower-triangular `A`. Witness: `trivialGeneralizedRK`,
   `nontrivialTwoStageGRK` are explicit; build a non-explicit
   counterexample (e.g. implicit-midpoint-style with `A 0 0 = 1/2`).
2. Cycle N+1: define `applyStartingThenStep_explicit` and
   `applyExactThenStarting_explicit` with hypothesis
   `∀ i, IsExplicit (S.method i)`. Body: direct recursion on stage
   index — each stage's `Y_j` is a `Finset.sum` over already-computed
   stages `Y_0, …, Y_{j-1}`.
3. Cycle N+2: define `HasOrderRelativeTo_explicit` and prove the
   non-vacuity witness for explicit Euler × trivialStartingMethod.

Total: ~2-3 cycles. Limitation: does not capture implicit methods
(e.g. backward Euler from cycle 142, implicit midpoint from cycle
135). Future cycles would need a separate definitional path for
implicit methods if those become target entities.

### Path B — General implicit via `ContractingWith` / `Function.IsFixedPt`

Use Mathlib's fixed-point machinery. The stage equation
`Y = y₀·𝟙 + h · A · F(Y)` (where `F y j = f y` componentwise) is a
fixed point of the map `T(Y) = y₀·𝟙 + h · A · F(Y)`. For sufficiently
small `h` and Lipschitz `f`, `T` is a contraction; uniqueness +
existence follow from Banach.

Plan:
1. Cycle N: introduce a Lipschitz hypothesis on `f`. Use
   `ContractingWith.fixedPoint` to define
   `stageVector : ℝ → ℝ → (Fin s → ℝ) → Fin s → ℝ`.
2. Cycle N+1: extend to `Sᵢ(y₀, h)` then to `applyStartingThenStep`.
3. Cycle N+2: define `applyExactThenStarting` (similar but the input
   is `yex(x₀ + h)` instead of `y₀`, and there's an additional
   exact-flow application step).
4. Cycle N+3: prove `HasOrderRelativeTo` non-vacuity for explicit
   Euler × trivialStartingMethod. This requires a Taylor expansion
   argument; the `O(h)` bound is straightforward but Lean
   formalization is non-trivial.
5. Cycle N+4: optional — prove order `p = 1` for explicit Euler
   relative to trivialStartingMethod (the textbook claim).

Total: ~3-5 cycles. Captures both explicit and implicit methods.
Heavy on `Asymptotics` / `HasDerivAt` / `Continuous` machinery.

## Closure remark on the non-vacuity witness

Once the operator bodies close (Path A or B), the cycle 149 witness
`explicitEulerGLM_hasOrderZero_trivialStarting` is essentially
mechanical:

* Explicit Euler GLM has `(s, r) = (1, 1)` with `b₀ = 1, b = 1, A = 0`
  → `M`-step is `y_out = y_in + h·f(y_in)`.
* `trivialStartingMethod` is `r = 1` with the trivial 1-stage
  generalized RK `b₀ = 1, b = 1, A = 0` → `S`-application is
  `y_out = y_in + h·f(y_in)`.
* Composing: `SM(y₀, h)` first applies `S` to `y₀` giving
  `y₀ + h·f(y₀)`, then takes one `M`-step: but the `M`-step of an
  `r = 1` GLM on the `r`-vector `(y₀ + h·f(y₀))` reuses that scalar
  — so `SM(y₀, h) = (y₀ + h·f(y₀))` as a `Fin 1 → ℝ` vector.
* `ES(y₀, h)` first advances `yex` by `h` to `yex(x₀ + h)`, then
  applies `S` to that scalar: `S(yex(x₀+h), h) = yex(x₀+h) + h·f(yex(x₀+h))`.
* Difference: `SM - ES = (y₀ + h·f(y₀)) - (yex(x₀+h) + h·f(yex(x₀+h)))`.
* By `yex(x₀) = y₀` and `yex' = f ∘ yex`, Taylor:
  `yex(x₀+h) = y₀ + h·f(y₀) + O(h²)`. So
  `SM - ES = -O(h²) + h·(f(y₀) - f(yex(x₀+h)))`. The second term
  is `h · O(h)` (by Lipschitz `f` × `yex(x₀+h) - y₀ = O(h)`), so
  `SM - ES = O(h²)`, dominating the required `O(h^{0+1}) = O(h)`.

This closed-form analysis suggests the witness is genuine (not
vacuous) once operators close — it's not the case that
`HasOrderRelativeTo` always trivially holds for all `M, S, p`.

## Cycle plan

* **Cycle 150**: rollback (this issue file documents the rollback
  rationale). No further def:530B work.
* **Cycle 151**: Path A Step 1 — `IsExplicit` predicate +
  non-vacuity witnesses landed (axiom-clean, no sorries). See update
  below.
* **Cycle 152**: Path A Step 2 (planned) — define
  `applyStartingThenStep_explicit` and `applyExactThenStarting_explicit`
  with hypothesis `∀ i, IsExplicit (S.method i)`. Body via direct
  recursion on stage index using `Finset.sum` over already-computed
  earlier stages. Estimated ~80-120 LOC.
* **Cycle 153** (planned): Path A Step 3 — define
  `HasOrderRelativeTo_explicit` and prove the trivial-IVP non-vacuity
  witness for explicit Euler × `trivialStartingMethod` with order
  `p = 0`. Estimated ~50-80 LOC.

## Cycle 151 update — Path A Step 1 complete

Path A Step 1 landed in
`OpenMath/Chapter5/Section530.lean` (cycle 151):

* `def GeneralizedRungeKuttaMethod.IsExplicit` — strict-lower-triangular
  predicate `∀ i j, i.val ≤ j.val → A i j = 0`. Captures "no implicit
  stage equations".
* `theorem trivialGeneralizedRK_isExplicit` — positive (vacuous, s = 1)
  witness.
* `noncomputable def explicit2StageGRK` (Heun-style
  `A = !![0,0;1,0]`) + `theorem explicit2StageGRK_isExplicit` —
  positive (non-vacuous, s = 2) witness with a genuine non-zero
  strict-lower entry.
* `noncomputable def implicit2StageGRK` (`A 0 0 = 1/2`) +
  `theorem implicit2StageGRK_not_isExplicit` — negative witness,
  exhibiting the predicate is genuinely refutable.

All three theorems verified axiom-clean
(`propext, Classical.choice, Quot.sound` only) via `lean_verify`.

Step 2 target for cycle 152 is the explicit-only operators. Direct
recursion on stage index (no fixed-point machinery needed) leveraging
the strict-lower-triangular `A` from `IsExplicit`.

## Cycle 152 update — Path A Step 2 complete (2a–2f + 2e)

Path A Step 2 landed in `OpenMath/Chapter5/Section530.lean` (cycle
152), axiom-clean, sorry count remained 0.

### GRK-side recursion + operators (Steps 2a–2d)

* `noncomputable def GeneralizedRungeKuttaMethod.explicitStageValue` —
  WF recursion on `j.val`, body
  `b₀·y₀ + h·Σ_{k < j} A_{jk}·f(Y_k)`. Termination by `j.val`,
  `decreasing_by exact k.isLt` (no `simp_wf` needed).
* `noncomputable def GeneralizedRungeKuttaMethod.explicitApply` —
  closed-form output `b₀·y₀ + h·Σ_j b_j·f(Y_j)`.
* `noncomputable def StartingMethod.applyExplicit` — per-constituent
  lift to a `Fin r → ℝ` initial-input vector.
* `noncomputable def applyExactThenStarting_explicit` — textbook
  `ES` operator, with unused `_hS : ∀ i, IsExplicit (S.method i)`
  hypothesis marking the explicit-only variant.

### GLM-side recursion + operator (Step 2e)

Lives in a re-opened
`namespace OpenMath.Chapter5.Section510.GeneralLinearMethod` block
(Lean rejects cross-namespace `def Foo.X` declarations from inside
a third namespace). Imports
`OpenMath.Chapter5.Section510` (no cycle introduced).

* `def GeneralLinearMethod.IsExplicit` — strict-lower-triangular
  `A`-block.
* `noncomputable def GeneralLinearMethod.explicitStageValue` —
  same WF recursion shape as the GRK version, with
  `(M.U *ᵥ y_input) i` as the base term instead of `M.b₀ · y₀`.
* `noncomputable def applyStartingThenStep_explicit` (in
  `Section530`'s namespace) — textbook `SM` operator with
  unused `_hS, _hM` IsExplicit hypotheses.

### Sanity computations (Step 2f)

Three private helpers (`explicitStageValue_zero_of_one_stage`,
`trivialGeneralizedRK_explicitStageValue_zero`,
`trivialGeneralizedRK_explicitApply`) decompose the closed-form
reductions, then the public:

* `theorem trivialStartingMethod_applyExplicit` — full `SE` reduction
  to `(fun _ => y₀ + h * f y₀)`.
* `theorem trivialStartingMethod_applyExactThenStarting_explicit` —
  `ES` reduction to
  `(fun _ => yex(x₀+h) + h * f(yex(x₀+h)))`.
* `theorem explicitEulerGLM_isExplicit` — vacuous (s = 1) GLM
  IsExplicit witness; ready for cycle 153 consumption.

### Verification

* `lake env lean OpenMath/Chapter5/Section530.lean` exits 0.
* `lake build OpenMath.Chapter5.Section530` succeeds.
* `grep -c sorry` → 0.
* `lean_verify` axiom-clean on all three new theorems.

### Notes for cycle 153

* The `SM` half of the cycle 153 witness goal can reuse
  `trivialGeneralizedRK_explicitApply` directly; the `ES` half is
  already proved.
* The `_hS`, `_hM` IsExplicit hypotheses on the operators are
  currently unused. They will be consumed when proving
  textbook-form stage equations from the recursion-form bodies
  (likely as part of the `HasOrderRelativeTo_explicit` proof).
* File grew from 360 → 573 lines (+213 LOC, slightly above the
  strategy's 150-LOC target but within its 200-LOC abort threshold).
  Concentrated in Step 2e GLM-side block.

## Cycle 153 update — Path A Step 3 complete

Path A Step 3 landed in `OpenMath/Chapter5/Section530.lean` (cycle
153), axiom-clean, sorry count remained 0.

### Predicate `HasOrderRelativeTo_explicit`

* `def HasOrderRelativeTo_explicit M S hS hM p f yex x₀ y₀` —
  componentwise `=O[nhds (0:ℝ)] (fun h => h ^ (p+1))` on the SM−ES
  diff, where SM = `applyStartingThenStep_explicit` and ES =
  `applyExactThenStarting_explicit` (cycle 152 operators). The
  predicate does NOT itself impose `S.IsNonDegenerate`; downstream
  callers add it at the use site.
* New imports: `Mathlib.Analysis.Asymptotics.Defs`,
  `Mathlib.Analysis.Calculus.Deriv.Basic`,
  `Mathlib.Topology.MetricSpace.Lipschitz`.

### `p = 0` non-vacuity witness

* `theorem explicitEulerGLM_hasOrderZero_trivialStarting` — under
  `LipschitzWith L f`, `HasDerivAt yex (f y₀) x₀`, `yex x₀ = y₀`,
  the SM−ES diff is `O(h)` componentwise. Proof outline:
  1. **Closed forms**: `hSM` reduces SM[0] to
     `(y₀ + h·f y₀) + h·f(y₀ + h·f y₀)` via
     `unfold OpenMath.Chapter5.Section510.GeneralLinearMethod.explicitStageValue`
     and `simp [explicitEulerGLM, Matrix.mulVec, dotProduct]`. `hES`
     reuses `trivialStartingMethod_applyExactThenStarting_explicit`.
  2. **T1 + T2 decomposition**: rewrite SM[0]−ES[0] as
     `T1(h) + T2(h)` where T1 = `(y₀ + h·f y₀) − yex(x₀+h)` and
     T2 = `h · (f(y₀ + h·f y₀) − f(yex(x₀+h)))`.
  3. **T1 = O(h)**: `hasDerivAt_iff_isLittleO_nhds_zero.mp` of
     `hyex_deriv` gives the canonical little-o; rewrite via
     `hyex_x₀` and `smul_eq_mul`; negate via `IsLittleO.neg_left`;
     promote to `IsBigO` via `IsLittleO.isBigO`.
  4. **T2 = O(h)**: bound `|h · (f a − f b)| ≤ L · |h|` whenever
     `|a − b| ≤ 1`. Continuity of `a, b` at 0 with `a(0) = b(0) = y₀`
     gives the eventual `< 1` bound (via
     `Metric.tendsto_nhds.mp + Real.dist_0_eq_abs`). Closure via
     `IsBigO.of_bound (↑L) ?_` + `LipschitzWith.dist_le_mul`.
  5. **Combine**: `hT1.add hT2`, then `simp` collapses
     `h ^ (0 + 1)` → `h`.

### Verification

* `lake env lean OpenMath/Chapter5/Section530.lean` exits 0.
* `lake build OpenMath.Chapter5.Section530` succeeds.
* `grep -c sorry` → 0.
* `lean_verify
  OpenMath.Chapter5.Section530.explicitEulerGLM_hasOrderZero_trivialStarting`
  → `[propext, Classical.choice, Quot.sound]` only.

### Notes for cycle 154+

* **Stretch refinement**: `p = 1` witness via `ContDiff ℝ 2 yex` +
  second-order Taylor remainder around `x₀` would match Butcher's
  textbook classification of explicit Euler as order 1 relative to
  the canonical starting method. Estimated +50–100 LOC.
* **Path B (implicit branch)**: still deferred. Requires
  `ContractingWith` / `Function.IsFixedPt` infrastructure for the
  stage-equation system when `A` is not strictly lower-triangular.
* File grew 573 → 776 LOC (+203 LOC), slightly above the strategy's
  80-LOC target but the closed-form algebra in `hSM` plus the
  IsBigO bookkeeping in T2 were unavoidable.

## Cycle 154 update — Path A Step 4 complete (`p = 1`)

The "stretch refinement" listed above is now landed. `p = 1` witness
`explicitEulerGLM_hasOrderOne_trivialStarting` lives in
`OpenMath/Chapter5/Section530.lean` immediately after the cycle-153
`p = 0` witness, axiom-clean (`[propext, Classical.choice, Quot.sound]`).

### Statement signature

```lean
theorem explicitEulerGLM_hasOrderOne_trivialStarting
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C2 : ContDiff ℝ 2 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    HasOrderRelativeTo_explicit explicitEulerGLM trivialStartingMethod
      (fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)
      explicitEulerGLM_isExplicit
      1 f yex x₀ y₀
```

Hypothesis upgrades from cycle 153:
1. `HasDerivAt yex (f y₀) x₀` (point-only) → `∀ x, HasDerivAt yex (f (yex x)) x` (genuine ODE).
2. `ContDiff ℝ 2 yex` newly added (needed for second-order Taylor).

Both upgrades are well within Butcher's implicit "exact solution
sufficiently regular" assumption.

### Proof recipe (concrete)

1. **Cycle-153 boilerplate** (intro, fin_cases, change, hSM/hES
   closed forms, hcongr, hpow). Identical to cycle 153 modulo
   `h ^ (1+1)` → `h^2` collapse via `ring`.
2. **T1 = O(h²)** via Taylor:
   * `htaylor := taylor_isLittleO (n := 2) convex_univ (Set.mem_univ _) hyex_C2.contDiffOn`
     after `simpa [nhdsWithin_univ]`.
   * `hT_eval` evaluates `taylorWithinEval yex 2 Set.univ x₀ (x₀+h)`
     via `taylor_within_apply` + `simp_only` with
     `Finset.sum_range_succ`, `iteratedDerivWithin_univ`,
     `iteratedDeriv_zero`, `Nat.factorial`, `smul_eq_mul`,
     `pow_zero`, `pow_one`, `mul_one`, `one_mul`, `inv_one`,
     followed by `ring`.
   * `hderiv_x0 : iteratedDeriv 1 yex x₀ = f y₀` via
     `iteratedDeriv_one` + `(hyex_ode x₀).deriv` + `hyex_x₀`.
   * Compose `htaylor` with `h ↦ x₀ + h` via `IsLittleO.comp_tendsto`,
     `congr'` away the `((x₀+h) - x₀)^2 = h^2` conversion.
   * Decompose `T1 = -(yex(x₀+h) - taylor₂(x₀+h)) - (h²/2)·iteratedDeriv 2 yex x₀`,
     bound the constant-times-h² term with
     `Asymptotics.isBigO_const_mul_self`, sum + negate.
3. **T2 = O(h²)** via Lipschitz + T1:
   * `obtain ⟨C, hCpos, hC⟩ := hT1.exists_pos`, then
     `Asymptotics.isBigOWith_iff` to expose the absolute bound.
   * Eventual `|h| ≤ 1` via `Set.Ioo (-1) 1` open-set argument.
   * Calc chain: `|h · (f a − f b)| ≤ |h| · L · |a − b| = |h| · L · |T1|
     ≤ |h| · L · C · h² ≤ L · C · h²` (last step uses `|h| ≤ 1`).
4. **Combine**: `hT1.add hT2`.

### Verification

* `lake env lean OpenMath/Chapter5/Section530.lean` exits 0.
* `grep -c sorry OpenMath/Chapter5/Section530.lean` → 0.
* `lean_verify
  OpenMath.Chapter5.Section530.explicitEulerGLM_hasOrderOne_trivialStarting`
  → `[propext, Classical.choice, Quot.sound]` only.
* Cycle-153 theorem still axiom-clean (rename was α-equivalent).
* File grew 776 → 989 LOC (+213 LOC).
* New imports: `Mathlib.Analysis.Calculus.Taylor`,
  `Mathlib.Analysis.Calculus.IteratedDeriv.Defs`.

### Cycle 155+ stretch

* **Path B (implicit branch)** still deferred — same blocker as before.
* Step 5 candidates: broaden the `(M × S, p)` coverage matrix with a
  `padded2DEulerGLM × mixedStartingMethod` witness (cycles 133/141)
  to non-trivial `r = 2` indexing; or pivot to `def:530C` (variants
  of order) if planner judges it tractable as a Path A consequence.

## Cross-reference

`def:530B` blocks (per dependency graph):
* `def:530C` (variants of order)
* §530+ order-condition theorems (cycle-by-cycle as planner targets
  them).

## Cycle 158 update — refactor of cycles 154+157 i=0 closures

Extracted the Taylor + Lipschitz machinery shared by the cycle 154 and
cycle 157 (i=0 channel) Path-A witnesses into a single private helper
`taylor_lipschitz_explicitEuler_orderOne_diff_isBigO` placed
immediately before `explicitEulerGLM_hasOrderOne_trivialStarting`.
Its conclusion is the closed-form `SM[0] − ES[0] =O[nhds 0] (h ↦ h²)`
in the shape that both witnesses reach after their algebraic closed-
form rewrites for SM[0] and ES[0]:

```
((y₀ + h · f y₀) + h · f (y₀ + h · f y₀))
  − (yex (x₀ + h) + h · f (yex (x₀ + h)))
=O[nhds 0] (fun h => h ^ 2)
```

Both witnesses now apply the helper as a one-liner after their
SM[0]/ES[0] rewrites and an `h^(1+1) = h^2` collapse. The cycle
156/157 i=1 channel (zero-collapse via `Asymptotics.isBigO_zero`)
remains untouched.

### Outcome
* `lake env lean OpenMath/Chapter5/Section530.lean` and
  `lake env lean OpenMath/Chapter5.lean` both exit 0.
* `grep -c sorry OpenMath/Chapter5/Section530.lean` → 0 (unchanged).
* All four affected theorems remain axiom-clean
  (`[propext, Classical.choice, Quot.sound]`):
  - `taylor_lipschitz_explicitEuler_orderOne_diff_isBigO` (new)
  - `explicitEulerGLM_hasOrderOne_trivialStarting` (refactored)
  - `padded2DEulerGLM_hasOrderOne_padCompatStarting` (refactored)
  - `padded2DEulerGLM_hasOrderOne` (def:530C wrapper, transitive)
* Cycle 153/155/156 theorems untouched and remain axiom-clean.
* File LOC: 1600 → 1524 (−76 LOC).
* Path A status of def:530B/C: still `[~]`. Path B (implicit) remains
  deferred — `lean_status.json` does NOT change this cycle.

### What the helper unblocks for future cycles
* A future Path-A witness at `r = 3` or `(s, r) = (k, 1)` for `k > 1`
  whose `i = 0` channel reduces to the same explicit-Euler shape can
  apply the helper as a one-line corollary instead of porting the
  ~140 LOC Taylor + Lipschitz body.
* A `p = 2` parametric variant (Taylor at degree 3 + matching
  hypothesis pack) would be a clean cycle 159+ refactor on top of
  this helper, generalising it over the Taylor degree once a second
  use-case appears.

## Cycle 159 update — r = 3 non-vacuity witnesses landed

Lifted the cycle 156/157 r = 2 padded-Euler Path-A non-vacuity grid
to r = 3, mirroring the cycle 156 → cycle 157 lift. New artefacts:

### In `OpenMath/Chapter5/Section520.lean`
* `padded3DEulerGLM : GeneralLinearMethod 1 3` — the 3-row padded
  explicit-Euler GLM (`A = !![0]`, `U = !![1, 0, 0]`,
  `B = !![1; 0; 0]`, `V = !![1, 0, 0; 0, 0, 0; 0, 0, 0]`). Lifts
  cycle 133's `padded2DEulerGLM` from r = 2 to r = 3. No new
  Section520 corollaries (`IsRKStable`, `IsIRKStable`, A-stability
  negative witness, etc.) added — out of scope this cycle.

### In `OpenMath/Chapter5/Section530.lean`
* `pad3CompatMethod : Fin 3 → GeneralizedRungeKuttaMethod 1` — index
  0 is `trivialGeneralizedRK` (active channel, b₀ = 1); indices 1
  and 2 are `zeroGeneralizedRK` (inactive zero channels).
* `pad3CompatStartingMethod : StartingMethod 3` — wraps
  `pad3CompatMethod` with `stages = fun _ => 1`. Meshes with
  `padded3DEulerGLM`'s row-1 and row-2 zero channels.
* `pad3CompatStartingMethod_isNonDegenerate` — non-degenerate at
  index 0 via `b₀ = 1 ≠ 0` (uses
  `StartingMethod.isNonDegenerate_iff_exists_b₀_ne_zero`).
* `pad3CompatStartingMethod_constituents_isExplicit` — three-arm
  `fin_cases i` proof: index 0 cites `trivialGeneralizedRK_isExplicit`;
  indices 1 and 2 close the 1×1 strict-lower-triangular condition
  vacuously via `intro a b _; fin_cases a; fin_cases b; rfl`.
* `padded3DEulerGLM_isExplicit` — `A = !![0]` is vacuously
  strict-lower-triangular at `s = 1`.
* `pad3CompatStartingMethod_applyExplicit` — three-component closed
  form: `![y₀ + h * f y₀, 0, 0]`. Index 0 cites
  `trivialGeneralizedRK_explicitApply`; indices 1 and 2 cite the
  cycle 156 private helper `zeroGeneralizedRK_explicitApply`.
* `padded3DEulerGLM_hasOrderZero_pad3CompatStarting` (p = 0,
  cycle 159 substantive deliverable). Three-arm `fin_cases i` proof:
  - **i = 0 channel**: identical to cycle 156's i = 0 channel — SM[0]
    and ES[0] reduce to the cycle-153 explicit-Euler closed form
    `(y₀ + h·f y₀) + h·f(y₀ + h·f y₀)` and `yex(x₀+h) + h·f(yex(x₀+h))`;
    T1 + T2 decomposition (T1 little-o(h) via `HasDerivAt`, T2 O(h)
    via Lipschitz + continuity-driven eventual `|·| ≤ 1`).
  - **i = 1 channel**: SM[1] = ES[1] = 0; close by
    `Asymptotics.isBigO_zero`.
  - **i = 2 channel**: identical to i = 1.
* `padded3DEulerGLM_hasOrderOne_pad3CompatStarting` (p = 1,
  cycle 159 substantive deliverable + cycle 158 portability
  validation). Three-arm `fin_cases i` proof:
  - **i = 0 channel**: SM[0] / ES[0] closed-form rewrites identical
    to cycle 157's i = 0 closure; an `h^(1+1) = h^2` collapse; then a
    one-line `exact taylor_lipschitz_explicitEuler_orderOne_diff_isBigO
      hf_lip hyex_x₀ hyex_C2 hyex_ode`. This is the third call site
    for the cycle 158 helper, validating its portability.
  - **i = 1 channel**: SM[1] = ES[1] = 0; zero-collapse with
    exponent `h^(1+1)`, identical structure to cycle 157's i = 1.
  - **i = 2 channel**: identical to i = 1.
* `padded3DEulerGLM_hasOrderZero` (def:530C wrapper, p = 0) —
  4-line existential closure exhibiting `pad3CompatStartingMethod` as
  the witness, citing `pad3CompatStartingMethod_isNonDegenerate`,
  `pad3CompatStartingMethod_constituents_isExplicit`, and
  `padded3DEulerGLM_hasOrderZero_pad3CompatStarting`.
* `padded3DEulerGLM_hasOrderOne` (def:530C wrapper, p = 1) —
  analogous to the p = 0 wrapper.

### Outcome
* `lake env lean OpenMath/Chapter5/Section520.lean` exits 0.
* `lake env lean OpenMath/Chapter5/Section530.lean` exits 0.
* `lake env lean OpenMath/Chapter5.lean` exits 0.
* `grep -c sorry OpenMath/Chapter5/Section520.lean` → 0 (unchanged).
* `grep -c sorry OpenMath/Chapter5/Section530.lean` → 0 (unchanged).
* All eight new theorems axiom-clean
  (`[propext, Classical.choice, Quot.sound]`):
  - `padded3DEulerGLM_isExplicit`
  - `pad3CompatStartingMethod_isNonDegenerate`
  - `pad3CompatStartingMethod_constituents_isExplicit`
  - `pad3CompatStartingMethod_applyExplicit`
  - `padded3DEulerGLM_hasOrderZero_pad3CompatStarting`
  - `padded3DEulerGLM_hasOrderOne_pad3CompatStarting`
  - `padded3DEulerGLM_hasOrderZero`
  - `padded3DEulerGLM_hasOrderOne`
* No regression on cycle 153/154/155/156/157/158 theorems —
  re-verified axiom-clean.
* `lean_status.json` updated: `def:530B` and `def:530C` cycle bumped
  from 157 to 159; both remain `partial` (Path B implicit branch
  still deferred).
* Path A status of def:530B/C: still `[~]`. Path B (implicit) remains
  deferred per the unchanged blockers above.

### What r = 3 unblocks for future cycles
* Generalising the cycle 158 helper over the Taylor degree (a p = 2
  parametric helper) becomes a cleaner refactor with the helper now
  validated at three call sites.
* Higher-order GLM order witnesses (a substantive p ≥ 2 witness
  requires a higher-order GLM such as RK2 or midpoint, since explicit
  Euler is a 1st-order method whose SM−ES diff is genuinely O(h²),
  NOT O(h³)).
* The shape of the r = 3 lift suggests an `r`-parametric padded GLM
  family `paddedRDEulerGLM (r : ℕ)` could be defined, with all
  current witnesses replaced by `r`-induction; this is a multi-cycle
  refactor.

## Cycle 160 update — shared T1+T2 helper landed at p = 0

### What changed
* Extracted the cycle-153 inline T1+T2 closure (used verbatim by
  cycles 153, 156, and 159 at the i = 0 channel) into a new private
  helper `taylor_lipschitz_explicitEuler_orderZero_diff_isBigO`,
  placed before `explicitEulerGLM_hasOrderZero_trivialStarting` in
  `OpenMath/Chapter5/Section530.lean`.
* Helper signature mirrors cycle 158's `..._orderOne_diff_isBigO`:
  takes `hf_lip`, `hyex_x₀`, `hyex_deriv : HasDerivAt yex (f y₀) x₀`,
  and produces
  `((y₀ + h·f y₀) + h·f (y₀ + h·f y₀))
   − (yex (x₀ + h) + h·f (yex (x₀ + h)))  =O[nhds 0] (fun h => h)`.
* Refactored three call sites to discharge with a one-liner after
  SM[0]/ES[0] closed-form rewrites and the `h^(0+1) = h` collapse:
  - `explicitEulerGLM_hasOrderZero_trivialStarting` (cycle 153)
  - `padded2DEulerGLM_hasOrderZero_padCompatStarting` (cycle 156,
    i = 0 channel only — i = 1 zero-collapse untouched)
  - `padded3DEulerGLM_hasOrderZero_pad3CompatStarting` (cycle 159,
    i = 0 channel only — i = 1, i = 2 zero-collapse untouched)
* Cycle 158's p = 1 helper and its three call sites
  (cycles 154/157/159 i = 0) untouched; re-verified axiom-clean to
  confirm no upstream breakage.

### Outcome
* `lake env lean OpenMath/Chapter5/Section530.lean` exits 0.
* `lake env lean OpenMath/Chapter5.lean` exits 0.
* `grep -c sorry OpenMath/Chapter5/Section530.lean` → 0 (unchanged).
* All thirteen affected theorems axiom-clean
  (`[propext, Classical.choice, Quot.sound]`):
  - new helper `taylor_lipschitz_explicitEuler_orderZero_diff_isBigO`
  - cycle 158 helper `taylor_lipschitz_explicitEuler_orderOne_diff_isBigO`
  - `explicitEulerGLM_hasOrderZero_trivialStarting`
  - `explicitEulerGLM_hasOrderOne_trivialStarting`
  - `padded2DEulerGLM_hasOrderZero_padCompatStarting`
  - `padded2DEulerGLM_hasOrderOne_padCompatStarting`
  - `padded3DEulerGLM_hasOrderZero_pad3CompatStarting`
  - `padded3DEulerGLM_hasOrderOne_pad3CompatStarting`
  - all six def:530C wrappers (`explicitEulerGLM_hasOrder{Zero,One}`,
    `padded2DEulerGLM_hasOrder{Zero,One}`,
    `padded3DEulerGLM_hasOrder{Zero,One}`)
* File 2034 → 1951 LOC (−83 LOC).
* Tautology-scanner regex
  `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$` clean.

### What cycles 158 + 160 together unblock
* The i = 0 explicit-Euler channel at p ∈ {0, 1} now factors through
  exactly two parametric helpers (one per Taylor degree). Any future
  r-extension reduces to one-line invocations on the i = 0 channel,
  with the r-parametric machinery (closed-form SM[i]/ES[i] expansions
  and zero-collapse on i ≥ 1) being the only per-r work.
* An r-parametric padded GLM family
  `paddedRDEulerGLM (r : ℕ)` would replace cycles 153/156/159's
  three pairs of HasOrderRelativeTo witnesses with a single pair of
  inductive theorems. The two helpers extracted in cycles 158 and 160
  remain the i = 0 base case.
* A future Taylor-degree-parametric helper covering p ∈ ℕ (using
  `taylor_isLittleO` at degree `p + 1`) would unify the two helpers
  in cycles 158 and 160 into one. The two-helper shape is sufficient
  for current Path A non-vacuity at p ∈ {0, 1}.

### Path B status (unchanged)
* Path B (implicit method via `ContractingWith` /
  `Function.IsFixedPt`) remains deferred per the original
  multi-cycle infrastructure plan above.

## Cycle 161 update — r = 4 non-vacuity witnesses landed

### What changed
* Added `padded4DEulerGLM` `(s, r) = (1, 4)` to
  `OpenMath/Chapter5/Section520.lean` — V matrix `!![1, 0, 0, 0; 0,
  0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]`, with row 0 the active
  explicit-Euler channel and rows 1, 2, 3 zero channels (passively
  decoupled). Lifts cycle 159's `padded3DEulerGLM` to r = 4 by the
  same row-padding scheme.
* Added `pad4CompatMethod`, `pad4CompatStartingMethod`, and four
  axiom-clean support theorems to `OpenMath/Chapter5/Section530.lean`:
  - `pad4CompatStartingMethod_isNonDegenerate` (b₀ ≠ 0 at index 0)
  - `pad4CompatStartingMethod_constituents_isExplicit` (all four
    constituents have 1×1 zero `A`-block)
  - `padded4DEulerGLM_isExplicit` (1×1 zero `A`-block)
  - `pad4CompatStartingMethod_applyExplicit` (closed form
    `![y₀ + h·f y₀, 0, 0, 0]`, mirroring cycle 159's r = 3 closed
    form with one extra zero entry).
* Added two new `HasOrderRelativeTo_explicit` witnesses at r = 4
  (Path A):
  - `padded4DEulerGLM_hasOrderZero_pad4CompatStarting` (p = 0;
    i = 0 channel = one-line invocation of cycle-160 helper after
    SM[0]/ES[0] closed-form rewrites and `h^(0+1) = h` collapse;
    rows 1, 2, 3 = zero-collapse via `Asymptotics.isBigO_zero`)
  - `padded4DEulerGLM_hasOrderOne_pad4CompatStarting` (p = 1;
    i = 0 channel = one-line invocation of cycle-158 helper after
    closed-form rewrites and `h^(1+1) = h^2` collapse; rows 1, 2,
    3 = zero-collapse).
* Added two def:530C wrappers `padded4DEulerGLM_hasOrderZero` (p=0)
  and `padded4DEulerGLM_hasOrderOne` (p=1), exhibiting
  `pad4CompatStartingMethod` as the existential witness and citing
  the new HasOrderRelativeTo witnesses.

### Outcome
* `lake env lean OpenMath/Chapter5/Section520.lean` exits 0.
* `lake env lean OpenMath/Chapter5/Section530.lean` exits 0.
* `lake env lean OpenMath/Chapter5.lean` exits 0.
* `grep -c sorry OpenMath/Chapter5/Section{520,530}.lean` → 0
  (unchanged).
* All nine new declarations axiom-clean
  (`[propext, Classical.choice, Quot.sound]`):
  - `OpenMath.Chapter5.Section510.padded4DEulerGLM` (definition)
  - `pad4CompatStartingMethod_isNonDegenerate`
  - `pad4CompatStartingMethod_constituents_isExplicit`
  - `padded4DEulerGLM_isExplicit`
  - `pad4CompatStartingMethod_applyExplicit`
  - `padded4DEulerGLM_hasOrderZero_pad4CompatStarting`
  - `padded4DEulerGLM_hasOrderOne_pad4CompatStarting`
  - `padded4DEulerGLM_hasOrderZero` (def:530C wrapper)
  - `padded4DEulerGLM_hasOrderOne` (def:530C wrapper)
* Tautology-scanner regex
  `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$` clean.

### What cycle 161 establishes
* Path A non-vacuity grid for `def:530B`/`def:530C` now stands at
  r ∈ {1, 2, 3, 4} × p ∈ {0, 1} — saturated through r = 4. Eight
  axiom-clean HasOrderRelativeTo witnesses and eight axiom-clean
  HasOrder wrappers across the grid.
* Cycle 158's `taylor_lipschitz_explicitEuler_orderOne_diff_isBigO`
  helper validated at a fourth call site (cycles 154, 157, 159, 161).
* Cycle 160's `taylor_lipschitz_explicitEuler_orderZero_diff_isBigO`
  helper validated at a fourth call site (cycles 153, 156, 159, 161).
* The r = 4 lift is mechanical port territory: each new r adds
  ≈300 LOC of duplication, but the i = 0 channel is now uniformly
  one-line per (r, p) pair, with only the r-row Fin index in the
  zero-collapse closures varying.
* Four-data-point baseline (r ∈ {1, 2, 3, 4}) is now in place,
  enabling cycle 162+ to commit to an r-parametric refactor
  (`paddedRDEulerGLM (r : ℕ)`) that replaces these four pairs with
  a single inductive pair of HasOrderRelativeTo theorems.

### Path B status (unchanged)
* Path B (implicit method via `ContractingWith` /
  `Function.IsFixedPt`) remains deferred per the original
  multi-cycle infrastructure plan above.

## Cycle 162 update: r-parametric refactor (Phase A landed)

### Context
Cycles 156–161 alternated r-extensions and helper-extraction
refactors on `def:530B`/`def:530C` Path A (six consecutive cycles).
The cycle 161 worker explicitly flagged "diminishing returns on
r = 5": each additional hand-written r-lift adds ≈300 LOC of
duplication with no new mathematical content. The cycle 162
strategy committed to **option 1** (r-parametric refactor, Phase A
only) over **option 2** (pivot to a fresh entity), as the
highest-confidence single-cycle deliverable.

### What cycle 162 landed
* **Section520** — parametric padded GLM family
  `paddedREulerGLM (r : ℕ) : GeneralLinearMethod 1 (r + 1)` placed
  immediately after `padded4DEulerGLM`. Body uses `Matrix.of` with
  index-0 conditional active entries:
  ```
  A := !![0]
  U := Matrix.of fun (_ : Fin 1) (j : Fin (r + 1)) =>
         if j.val = 0 then 1 else 0
  B := Matrix.of fun (i : Fin (r + 1)) (_ : Fin 1) =>
         if i.val = 0 then 1 else 0
  V := Matrix.of fun (i j : Fin (r + 1)) =>
         if i.val = 0 ∧ j.val = 0 then 1 else 0
  ```
  Conceptually specialises to `explicitEulerGLM` (`r = 0`),
  `padded2DEulerGLM` (`r = 1`), `padded3DEulerGLM` (`r = 2`),
  `padded4DEulerGLM` (`r = 3`); reconciliation lemmas are Phase B.3
  work.
* **Section530** — parametric starting family:
  - `padCompatMethodR (r : ℕ) : Fin (r + 1) → GeneralizedRungeKuttaMethod 1`
    `:= fun i => if i.val = 0 then trivialGeneralizedRK else zeroGeneralizedRK`,
  - `padCompatStartingMethodR (r : ℕ) : StartingMethod (r + 1)`
    with `stages := fun _ => 1` and `method := padCompatMethodR r`.
* **Four basic structure lemmas** (all axiom-clean):
  - `paddedREulerGLM_isExplicit (r : ℕ)` — vacuous closure on the
    1×1 `A`-block (mirrors `padded4DEulerGLM_isExplicit`).
  - `padCompatStartingMethodR_isNonDegenerate (r : ℕ)` — witness
    `⟨0, Nat.succ_pos r⟩` with `b₀ = 1` from `trivialGeneralizedRK`,
    via `StartingMethod.isNonDegenerate_iff_exists_b₀_ne_zero`.
  - `padCompatStartingMethodR_constituents_isExplicit (r : ℕ)` —
    case-split on `i.val = 0`: index 0 cites
    `trivialGeneralizedRK_isExplicit`, `i ≠ 0` closes vacuously on
    the 1×1 `A`-block of `zeroGeneralizedRK`.
  - `padCompatStartingMethodR_applyExplicit (r : ℕ) (f : ℝ → ℝ) (h y₀ : ℝ)`
    — closed form `fun i => if i.val = 0 then y₀ + h * f y₀ else 0`,
    discharged via `by_cases hi : i.val = 0` then citing
    `trivialGeneralizedRK_explicitApply` (cycle 152) at index 0 and
    private `zeroGeneralizedRK_explicitApply` (cycle 156) elsewhere.

### Outcome
* `lake env lean OpenMath/Chapter5/Section520.lean` exits 0.
* `lake env lean OpenMath/Chapter5/Section530.lean` exits 0.
* `lake env lean OpenMath/Chapter5.lean` exits 0.
* `grep -c sorry OpenMath/Chapter5/Section{520,530}.lean` → 0
  (unchanged).
* All four new theorems axiom-clean
  (`[propext, Classical.choice, Quot.sound]`):
  - `OpenMath.Chapter5.Section530.paddedREulerGLM_isExplicit`
  - `OpenMath.Chapter5.Section530.padCompatStartingMethodR_isNonDegenerate`
  - `OpenMath.Chapter5.Section530.padCompatStartingMethodR_constituents_isExplicit`
  - `OpenMath.Chapter5.Section530.padCompatStartingMethodR_applyExplicit`
* The new definitions (`paddedREulerGLM`, `padCompatMethodR`,
  `padCompatStartingMethodR`) compile and elaborate cleanly.

### Phase B (deferred to cycle 163)

* **Phase B.1** — parametric witnesses
  `paddedREulerGLM_hasOrderZero_padCompatStartingR (r : ℕ)` and
  `_hasOrderOne_padCompatStartingR (r : ℕ)`. Closure pattern:
  case-split on `i.val = 0`. At `i.val = 0`, one-line invocation
  of cycle 158/160's Taylor + Lipschitz helpers after the standard
  SM[0]/ES[0] closed-form rewrites. At `i.val ≠ 0`, zero-collapse
  via `Asymptotics.isBigO_zero` (the `applyExplicit` closed form
  yields 0; `paddedREulerGLM r`'s row-i-active-channel is also 0
  because the `B` and `V` rows for `i ≥ 1` are zero). Estimated
  ~150–250 LOC for both.
* **Phase B.2** — parametric `def:530C` wrappers
  `paddedREulerGLM_hasOrderZero (r : ℕ)` and `_hasOrderOne (r : ℕ)`,
  trivial corollaries citing Phase B.1 with
  `padCompatStartingMethodR r` as the existential witness and
  `padCompatStartingMethodR_isNonDegenerate r` for the
  non-degeneracy clause.
* **Phase B.3** (optional / stretch) — reconciliation lemmas
  `paddedREulerGLM_zero_eq_explicitEulerGLM`,
  `paddedREulerGLM_one_eq_padded2DEulerGLM`,
  `paddedREulerGLM_two_eq_padded3DEulerGLM`,
  `paddedREulerGLM_three_eq_padded4DEulerGLM`. The `Matrix.of`
  body vs `!![..]` body unfold differently, so these likely close
  by `ext + simp` / `decide` rather than `rfl`. Ship only if they
  close cleanly; do not block on them.

After Phase B lands cleanly, the planner pivots to a fresh entity
(see cycle 162 strategy's backup pivot candidate list:
`def:451A` G-stable, `def:422B` underlying one-step method,
`def:442A` principal sheet, `thm:535A` underlying one-step method
(GLM), `thm:541A` types of DIMSIM methods).

### What cycle 162 establishes
* The r-parametric infrastructure for `def:530B`/`def:530C` Path A
  is now in place. Future r-extensions of the structural side
  (definitions and basic lemmas) require zero new code: any
  needed concrete instance follows by specialising the parametric
  family at a numeral.
* The hand-written `r ∈ {1, 2, 3, 4}` instances coexist with the
  parametric family. Cycle 163 (Phase B.3) can ship reconciliation
  lemmas; if those close cleanly, cycle 164+ can begin retiring
  the hand-written instances — but this is downstream cleanup,
  not blocking.
