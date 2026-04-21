# Issue: Exact theorem shape for the realized infinity-branch analytic contradiction

## Blocker
After cycle 276, the bookkeeping gap below `thm_355D` / `thm_355E'` is no longer
`NoArrowsEscapeToInfinity data` itself. The live file now reduces that statement to
the branch-level impossibility of `RealizedDownArrowInfinityBranch R` and
`RealizedUpArrowInfinityBranch R`.

What still has no honest theorem statement is the analytic input that rules out
those realized escaping branches for a concrete rational approximation `R`. The
existing abstract hypothesis `IsRationalApproxToExp data` cannot express this,
because it does not mention `R` at all.

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
- So the remaining theorem is now visibly branch-level:
  a realized escaping branch should contradict the concrete analytic geometry of
  the rational approximation itself.
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
- Isolated three Aristotle scratch files under
  `.prover-state/aristotle/cycle_276/`:
  - down-arrow contradiction,
  - up-arrow contradiction,
  - combined no-escape corollary.
- In scratch, used a placeholder `IsConcreteRationalApproxToExp R data` to expose
  the missing `R`-dependent analytic input explicitly.

## Possible solutions
- Introduce one minimal theorem-level hypothesis or structure outside
  `IsRationalApproxToExp data`, for example a relation like
  `ConcreteRationalApproxToExp R data`, whose content is specifically the analytic
  bridge from the concrete rational approximation `R` to the realized order-web
  branches.
- State the next real theorem in branch-witness form:
  `theorem realizedDownArrowInfinityBranch_contradiction
      (R : ℂ → ℂ) (data : OrderArrowTerminationData)
      (hconcrete : ConcreteRationalApproxToExp R data)
      (branch : RealizedDownArrowInfinityBranch R) : False`
  and analogously for the up-arrow case.
- Derive `NoRealizedDownArrowInfinityBranch R` /
  `NoRealizedUpArrowInfinityBranch R` from those contradiction theorems and then
  reuse the cycle-276 reduction lemmas unchanged.
