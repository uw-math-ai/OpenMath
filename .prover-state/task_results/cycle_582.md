# Cycle 582 Results

## Worked on

Backlog item #6 — Butcher §111: closed-form solution of linear systems
of ODEs `y'(x) = A · y(x), y(x₀) = y₀`. New file `OpenMath/LinearODE.lean`.

## Approach

Per the planner's pivot away from the §38 convolution layer, set up a
sorry-first scaffold with three core deliverables:

1. `closedFormSolution`: the closed-form `exp((x − x₀) • A) *ᵥ y₀`.
2. `closedFormSolution_initial`: matches the initial condition.
3. `closedFormSolution_hasDerivAt`: derivative `A *ᵥ y(x)`.
4. `exp_smul_add`: one-parameter group law for `exp(s • A)`.

## Result

**SUCCESS — all four declarations closed, zero sorries.**

- `closedFormSolution_initial`: closed by `simp [closedFormSolution]`
  (chains through `sub_self`, `zero_smul`, `NormedSpace.exp_zero`,
  `Matrix.one_mulVec`).
- `exp_smul_add`: `rw [add_smul]` then `NormedSpace.exp_add_of_commute`
  with the commute proof
  `((Commute.refl A).smul_left s).smul_right t`.
- `closedFormSolution_hasDerivAt`: chained
  - `hasDerivAt_exp_smul_const' (𝕂 := ℝ)` (Mathlib lemma giving
    `(d/dt) exp(t • A) = A * exp(t • A)`),
  - `HasDerivAt.scomp` with `t ↦ t − x₀` (derivative 1) for the
    inner translation,
  - and a small helper `mulVecRightCLM y₀ : Matrix →L[ℝ] (Fin n → ℝ)`
    (right multiplication by a fixed vector, packaged as a continuous
    linear map via `LinearMap.toContinuousLinearMap`) composed via
    `HasFDerivAt.comp_hasDerivAt`,
  - finishing with `← Matrix.mulVec_mulVec` to reshape
    `(A * exp(...)) *ᵥ y₀` into `A *ᵥ (exp(...) *ᵥ y₀)`.

## Aristotle usage

Submitted scaffolds were prepared in
`.prover-state/aristotle_scaffolds/cycle_582/{initial,exp_smul_add,derivAt,exp_smul_helper,all}.lean`.
Submission attempts hit HTTP 429 (rate limit) on the first request and
the queue was full of carry-over §38 / §384 jobs from prior cycles.
Per strategy guidance ("if all jobs hit 429 at submission time, do not
retry the same submissions; close manually"), pivoted to manual
closure. All three sorries closed manually using Lean LSP
`lean_multi_attempt`.

## Dead ends

- Tried `simp [Matrix.smul_mulVec_assoc]` for the `map_smul'` field of
  the helper linear map — the lemma is named `Matrix.smul_mulVec`
  (no `_assoc` suffix). Direct `Matrix.smul_mulVec c M y` works.
- Initially used `NormedSpace.hasDerivAt_exp_smul_const'` and
  `h_exp.scomp` / `.comp_hasDerivAt` via dot notation. The lemma is
  in the root namespace (not `NormedSpace`), and dot notation through
  `HasDerivAt = HasDerivAtFilter ... 𝓝` does not project methods like
  `scomp` / `comp_hasDerivAt`. Fixed by calling them as
  `HasDerivAt.scomp` / `HasFDerivAt.comp_hasDerivAt` directly.
- Needed to add `Mathlib.Analysis.Calculus.Deriv.Comp` and
  `Mathlib.Analysis.Calculus.FDeriv.Comp` imports — `MatrixExponential`
  alone does not pull in the chain rule for derivatives.

## Discovery

- The Mathlib `Matrix` exponential lives at `NormedSpace.exp`
  (re-exported via `open Matrix NormedSpace`); the linfty operator
  norm instances must be opened via `open scoped Matrix.Norms.Operator`
  for `NormedRing`/`NormedAlgebra` typeclass resolution.
- `hasDerivAt_exp_smul_const'` (with the prime, giving the `x * exp(t • x)`
  ordering on the right) is the key lemma for matrix-valued exponential
  derivatives — Mathlib does not directly expose `(d/dt) exp((t − x₀) • A)`,
  so the chain rule via `HasDerivAt.scomp` with the affine shift is the
  canonical move.
- `HasDerivAt.scomp` takes `x` explicitly as its first argument
  (`(x : 𝕜)`), per the variable-block annotation in
  `Mathlib/Analysis/Calculus/Deriv/Comp.lean`.

## Suggested next approach

§111 is now landed. Per the planner's "Side note for the planner",
the next §38 cycle should be a **planning cycle** that designs the
augmented `bSeriesConv` (Butcher-aug convolution with empty-forest
scalars), picks the empty-forest convention, and writes a sorry-first
scaffold with an associativity sanity check at depth ≤ 2. Do not allow
a one-cycle full redefinition + associativity attempt — cycle 581 shows
that ends in a revert.

For continued §1xx progress, plausible follow-ups:
- §112 / §113 — non-autonomous linear systems, variation-of-parameters.
- A `closedFormSolution` lemma showing it solves the non-homogeneous
  IVP with a forcing term.
- Strengthen the §111 file with `closedFormSolution_eq_picardSolution`
  bridging to `OpenMath.PicardLindelof`.
