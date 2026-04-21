# Issue: Exact coincidence exclusion needs `R`-specific input

## Blocker
The live contradiction seam is now reduced all the way to the exact statement

- `∀ z : ℂ, z ≠ 0 → z ∈ orderWeb R → R z = exp z → False`.

Cycle 284 also added a live wrapper theorem
`concreteRationalApproxToExp_of_realizedArrowInfinityBranch_contradictions_of_no_nonzero_eq_exp`
so this exact-coincidence exclusion can be fed into the contradiction package
without reintroducing the older unit-level formulation.

But the current seam still quantifies over an arbitrary `R : ℂ → ℂ`, and the
existing local asymptotic / cone-control / branch hypotheses do not control the
global zero set of `fun z => exp z - R z`. So the remaining exclusion theorem
cannot come from the present generic interface alone.

## Context
- Live file: `OpenMath/OrderStars.lean`
- Relevant live theorems:
  - `eq_one_of_mem_orderWeb_of_norm_eq_one`
  - `eq_exp_of_mem_orderWeb_of_norm_eq_one`
  - `no_nonzero_unit_points_on_orderWeb_iff_no_nonzero_eq_exp`
  - `realizedDownArrowInfinityBranch_contradiction_of_no_nonzero_eq_exp`
  - `realizedUpArrowInfinityBranch_contradiction_of_no_nonzero_eq_exp`
  - `concreteRationalApproxToExp_of_realizedArrowInfinityBranch_contradictions_of_no_nonzero_eq_exp`
- The old contradiction input
  `‖R z * exp (-z)‖ = 1 → False`
  has already been reduced to exact coincidence `R z = exp z` on `orderWeb R`.
- The remaining missing content is therefore not norm bookkeeping anymore; it is
  a concrete theorem about nonzero zeros of `exp - R`.

## What was tried
- Searched `OpenMath/OrderStars.lean`, `OpenMath/Pade.lean`, and the local
  contradiction seam for any existing theorem controlling nonzero coincidence
  points of `R` with `exp`; none was found.
- Added the exact-coincidence wrapper theorems so the live seam now accepts the
  sharpened hypothesis directly and recompiled `OpenMath/OrderStars.lean`.
- Checked whether the sharpened statement might be derivable from the current
  arbitrary-`R` interface anyway. It is not:
  the local asymptotic lemmas only control behavior near `0`, the cone lemmas
  only control specific tangential sectors, and the branch contradictions only
  consume a global coincidence-exclusion theorem rather than produce one.
- Ran a numerical sanity check on one concrete rational approximation already in
  the file, `backwardEulerR z = (1 - z)⁻¹`. It has a nonzero solution of
  `backwardEulerR z = exp z` near
  `z ≈ -4.06479569417 - 58.03240937970 i`
  with residual about `7e-82`.

## Possible solutions
- State the target concrete rational approximation `R` explicitly at this seam
  and prove a theorem about the nonzero zero set of `exp - R`.
- Import or prove a Padé-specific global nondegeneracy theorem strong enough to
  exclude nonzero coincidence points on `orderWeb R`.
- Keep using the new exact-coincidence wrapper seam, but supply the missing
  exclusion as an explicit theorem-local hypothesis until the actual concrete
  `R`-specific theorem exists.
