# Issue: Exact theorem shape for the realized infinity-branch analytic contradiction

## Blocker
After cycle 277, the live theorem boundary below `thm_355D` / `thm_355E'` is now
explicitly:
- `ConcreteRationalApproxToExp R data`
- `noArrowsEscapeToInfinity_of_concreteRationalApprox`
- `thm_355D_of_concreteRationalApprox`
- `thm_355E'_of_concreteRationalApprox`

So the remaining gap is no longer bookkeeping. What is still missing is the
analytic theorem that proves `ConcreteRationalApproxToExp R data` for the
concrete rational approximation `R` under study. The abstract hypothesis
`IsRationalApproxToExp data` still cannot express that input, because it does not
mention `R` at all.

## Context
- `OpenMath/OrderStars.lean` now has:
  - `NoRealizedDownArrowInfinityBranch`
  - `NoRealizedUpArrowInfinityBranch`
  - `downArrowsAtInfinity_eq_zero_of_noRealizedDownArrowInfinityBranch`
  - `upArrowsAtInfinity_eq_zero_of_noRealizedUpArrowInfinityBranch`
  - `noArrowsEscapeToInfinity_of_noRealizedArrowInfinityBranches`
  - helper corollaries
    `thm_355D_of_realizedInfinityBranchGerms` and
    `thm_355E'_of_realizedInfinityBranchGerms`
- cycle 277 added the minimal concrete boundary:
  - `ConcreteRationalApproxToExp`
  - `noArrowsEscapeToInfinity_of_concreteRationalApprox`
  - `thm_355D_of_concreteRationalApprox`
  - `thm_355E'_of_concreteRationalApprox`
- So the remaining theorem is now visibly branch-level and `R`-dependent: the
  concrete analytic geometry of the rational approximation must imply the two
  fields of `ConcreteRationalApproxToExp R data`.
- Cycle-276 Aristotle scratch jobs confirmed the same point:
  - the two branch contradiction jobs could only report blockage once the
    `R`-dependent analytic hypothesis was left as an opaque placeholder;
  - the combined corollary job was not incorporable because it tried to repair the
    missing context by fabricating placeholder module changes outside the live
    boundary.

## What was tried
- Added the explicit branch-level contradiction hypotheses and proved the finite
  witness-elimination reduction from `RealizesInfinityBranchGerms R data` to
  `NoArrowsEscapeToInfinity data`.
- Added the live concrete wrapper
  `ConcreteRationalApproxToExp R data` containing exactly the two branch
  contradiction fields already isolated in the cycle-276 seam.
- Proved the new concrete corollaries
  `noArrowsEscapeToInfinity_of_concreteRationalApprox`,
  `thm_355D_of_concreteRationalApprox`, and
  `thm_355E'_of_concreteRationalApprox`.
- Isolated three Aristotle scratch files under
  `.prover-state/aristotle/cycle_276/`:
  - down-arrow contradiction,
  - up-arrow contradiction,
  - combined no-escape corollary.
- In scratch, used a placeholder `IsConcreteRationalApproxToExp R data` to expose
  the missing `R`-dependent analytic input explicitly.

## Possible solutions
- Prove branch-witness contradiction theorems of the form:
  `theorem realizedDownArrowInfinityBranch_contradiction
      (R : ℂ → ℂ) (data : OrderArrowTerminationData)
      (hconcrete : ConcreteRationalApproxToExp R data)
      (branch : RealizedDownArrowInfinityBranch R) : False`
  and analogously for the up-arrow case.
- Or, more directly, prove the two fields required by
  `ConcreteRationalApproxToExp R data` from the concrete analytic hypotheses on
  the rational approximation `R`, then reuse the new concrete corollaries
  unchanged.
