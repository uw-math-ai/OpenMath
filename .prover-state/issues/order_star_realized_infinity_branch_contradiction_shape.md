# Issue: Exact theorem shape for the realized infinity-branch analytic contradiction

## Blocker
After cycle 278, the remaining gap below
`ConcreteRationalApproxToExp R data` is no longer a generic topology lemma.
The live file now has the branch-extraction helpers and the connected-image
crossing lemma needed to pass from:

- one support point with `‖R z * exp (-z)‖ < 1`,
- one support point with `1 < ‖R z * exp (-z)‖`,

to a support point with `‖R z * exp (-z)‖ = 1`.

So the actual blocker is now narrower: derive the theorem-local analytic
hypotheses used in the cycle-278 scratch contradictions from the concrete
rational approximation `R` under study, without pushing that content back into
`IsRationalApproxToExp` and without redesigning the live seam.

## Context
- `OpenMath/OrderStars.lean` still keeps the public/live boundary unchanged:
  - `RealizedDownArrowInfinityBranch`
  - `RealizedUpArrowInfinityBranch`
  - `NoRealizedDownArrowInfinityBranch`
  - `NoRealizedUpArrowInfinityBranch`
  - `RealizesInfinityBranchGerms`
  - `ConcreteRationalApproxToExp`
  - `noArrowsEscapeToInfinity_of_concreteRationalApprox`
  - `thm_355D_of_concreteRationalApprox`
  - `thm_355E'_of_concreteRationalApprox`
- cycle 278 added only small helper infrastructure directly supporting the
  contradiction work:
  - `mem_orderWeb_of_mem_globalOrderArrowBranch_support`
  - `exists_mem_support_norm_gt_of_escapesEveryClosedBall`
  - `exists_mem_inter_rayConeNearOrigin_of_branchTracksRayNearOrigin`
  - `exists_mem_support_unit_level_of_connected_orderWeb_branch`
- The new scratch batch is:
  - `.prover-state/aristotle/cycle_278/01_realizedDownArrowInfinityBranch_contradiction.lean`
  - `.prover-state/aristotle/cycle_278/02_realizedUpArrowInfinityBranch_contradiction.lean`
  - `.prover-state/aristotle/cycle_278/03_concreteRationalApproxToExp_builder.lean`

## What was tried
- Wrote the required cycle-278 scratch files first, with theorem-local analytic
  hypotheses only.
- Submitted a fresh Aristotle batch:
  - `3187363b-ba74-497e-a8c9-966db1aa874f`
  - `6e6eb7ac-2bc5-4667-9411-f1ca5f8e2f8b`
  - `85dab4bf-8050-4378-9cac-b875e9ef491c`
- Waited once for 30 minutes, then refreshed once.
- All three projects finished `COMPLETE_WITH_ERRORS`.
- Inspected the returned artifacts. None were directly incorporable because each
  Aristotle output rebuilt a parallel `OpenMath/OrderStars.lean` interface; the
  builder job also changed the semantics enough that the contradiction became an
  artifact of the fabricated interface rather than a proof about the live one.
- Manually checked the remaining Lean-side helper step. The connectedness
  crossing lemma closes in the live file via
  `IsPreconnected.intermediate_value`, so that part is no longer speculative.

## Exact theorem signatures tried
The down-arrow scratch contradiction stabilized at:

```lean
theorem cycle278_realizedDownArrowInfinityBranch_contradiction
    (R : ℂ → ℂ)
    (hcont : Continuous (fun z => ‖R z * exp (-z)‖))
    (hzero_not_mem_down_support :
      ∀ branch : RealizedDownArrowInfinityBranch R,
        (0 : ℂ) ∉ branch.branch.toGlobalOrderArrowBranch.support)
    (hno_nonzero_unit_points_on_orderWeb :
      ∀ z : ℂ, z ≠ 0 → z ∈ orderWeb R → ‖R z * exp (-z)‖ = 1 → False)
    (hlocal_minus_near_down :
      ∀ θ : ℝ, IsDownArrowDir R θ →
        ∃ aperture > 0, ∃ radius > 0,
          ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
            ‖R z * exp (-z)‖ < 1)
    (hfar_plus_on_orderWeb :
      ∃ radius > 0, ∀ z : ℂ, z ∈ orderWeb R → radius ≤ ‖z‖ →
        1 < ‖R z * exp (-z)‖)
    (branch : RealizedDownArrowInfinityBranch R) :
    False
```

The up-arrow scratch contradiction stabilized at the same shape with the local
and far-field inequalities reversed:

```lean
theorem cycle278_realizedUpArrowInfinityBranch_contradiction
    (R : ℂ → ℂ)
    (hcont : Continuous (fun z => ‖R z * exp (-z)‖))
    (hzero_not_mem_up_support :
      ∀ branch : RealizedUpArrowInfinityBranch R,
        (0 : ℂ) ∉ branch.branch.toGlobalOrderArrowBranch.support)
    (hno_nonzero_unit_points_on_orderWeb :
      ∀ z : ℂ, z ≠ 0 → z ∈ orderWeb R → ‖R z * exp (-z)‖ = 1 → False)
    (hlocal_plus_near_up :
      ∀ θ : ℝ, IsUpArrowDir R θ →
        ∃ aperture > 0, ∃ radius > 0,
          ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
            1 < ‖R z * exp (-z)‖)
    (hfar_minus_on_orderWeb :
      ∃ radius > 0, ∀ z : ℂ, z ∈ orderWeb R → radius ≤ ‖z‖ →
        ‖R z * exp (-z)‖ < 1)
    (branch : RealizedUpArrowInfinityBranch R) :
    False
```

And the combined scratch builder used exactly those same theorem-local
hypotheses to construct `ConcreteRationalApproxToExp R data`.

## Which local helper lemmas closed
- `mem_orderWeb_of_mem_globalOrderArrowBranch_support`
- `exists_mem_support_norm_gt_of_escapesEveryClosedBall`
- `exists_mem_inter_rayConeNearOrigin_of_branchTracksRayNearOrigin`
- `exists_mem_support_unit_level_of_connected_orderWeb_branch`

## Which part still failed
- No theorem currently derives the cycle-278 theorem-local hypotheses above from
  the concrete rational approximation `R`.
- In particular, the following assumptions are still not justified from live
  mathematics in the repo:
  - exclusion of `0` from realized branch support,
  - exclusion of nonzero unit-level points on `orderWeb R`,
  - local cone sign control around realized down/up tangents,
  - far-field sign control on large `orderWeb R` points.

## Possible solutions
- Derive the cycle-278 local/far-field sign hypotheses from the concrete
  asymptotics of the actual rational approximation `R`, then reuse the scratch
  contradiction shape without changing the public seam.
- Re-evaluate whether `hzero_not_mem_*_support` and
  `hno_nonzero_unit_points_on_orderWeb` are mathematically natural consequences
  of the intended branch representation, or whether the concrete contradiction
  should be stated with a slightly different nondegeneracy hypothesis.
- Keep further work scratch-local until the minimal justified theorem-local
  hypothesis list is known; do not move these assumptions into
  `IsRationalApproxToExp` and do not redesign `ConcreteRationalApproxToExp`.
