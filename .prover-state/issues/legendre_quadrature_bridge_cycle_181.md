# Issue: Legendre quadrature proof still missing orthogonality/remainder bridge

## Blocker
`OpenMath/Legendre.lean` now has a direct bridge theorem from the recursive
`shiftedLegendreP` to Mathlib's mapped `Polynomial.shiftedLegendre`, but the
two remaining sorries still need the actual Gaussian quadrature argument:

- `gaussLegendre_B_double`
- `gaussLegendreNodes_of_B_double`

The missing step is not the sign convention anymore. It is the current
repository-level packaging of:
1. division of `X^(s+j)` by the mapped shifted Legendre polynomial,
2. vanishing of the defect term by orthogonality,
3. conversion back to the tableau quadrature sum.

## Context
- New theorem in [OpenMath/Legendre.lean](/mmfs1/gscratch/amath/mathai/OpenMath/OpenMath/Legendre.lean):
  `shiftedLegendreP_eq_eval_map_shiftedLegendre`
- Existing helpers:
  [OpenMath/ShiftedLegendreDivision.lean](/mmfs1/gscratch/amath/mathai/OpenMath/OpenMath/ShiftedLegendreDivision.lean)
  and
  [OpenMath/LegendreHelpers.lean](/mmfs1/gscratch/amath/mathai/OpenMath/OpenMath/LegendreHelpers.lean)
- Remaining sorries compile, but only as placeholders.

## What was tried
- Reused older Aristotle bridge outputs from cycles 175 and 179.
- Confirmed stale CI report and recompiled current `OpenMath/Legendre.lean`.
- Adapted the recursive bridge proof into the current file and verified it compiles.
- Reviewed older Aristotle outputs for `gaussLegendre_B_double` / converse, but they targeted incompatible older infrastructure.

## Possible solutions
- Derive a direct theorem:
  `HasGaussLegendreNodes -> eval mapped shiftedLegendre = 0`
  from the new bridge theorem, then combine it with `monomial_div_mod_shiftedLegendre`.
- Turn `orthogonality_sum_zero` into the exact coefficient/integral lemma needed for the defect term in `gaussLegendre_B_double`.
- For the converse theorem, either:
  1. prove the node polynomial is orthogonal to all lower monomials and hence proportional to the shifted Legendre polynomial, or
  2. specialize the argument first to small `s` if a general proof remains expensive.
