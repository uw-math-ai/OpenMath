# Issue: Nonzero order-web `R z = exp z` coincidences block unit-level exclusion

## Blocker
The concrete contradiction input

- `∀ z : ℂ, z ≠ 0 → z ∈ orderWeb R → ‖R z * exp (-z)‖ = 1 → False`

is now reduced in live code to the sharper statement

- `∀ z : ℂ, z ≠ 0 → z ∈ orderWeb R → R z = exp z → False`.

This is the first still-unjustified concrete hypothesis I could isolate cleanly in
cycle 283. The current live `OrderStars.lean` hypotheses provide local asymptotic
control near `0` and branch-local cone sign control, but they do not provide any
global theorem excluding nonzero coincidence points of `R` with `exp` on the
positive-real order web.

## Context
- Live file: `OpenMath/OrderStars.lean`
- New cycle-283 lemmas:
  - `eq_one_of_mem_orderWeb_of_norm_eq_one`
  - `eq_exp_of_mem_orderWeb_of_norm_eq_one`
  - `no_nonzero_unit_points_on_orderWeb_iff_no_nonzero_eq_exp`
- These show:
  - on `orderWeb R`, unit norm means `R z * exp (-z) = 1`,
  - hence the contradiction input is equivalent to forbidding nonzero points of
    `orderWeb R` where `R z = exp z`.

So the remaining gap is no longer about norms or positivity bookkeeping; it is a
global coincidence-exclusion theorem for the concrete rational approximation `R`.

## What was tried
- Inspected the live contradiction seam around
  `realizedDownArrowInfinityBranch_contradiction`,
  `realizedUpArrowInfinityBranch_contradiction`, and
  `concreteRationalApproxToExp_of_realizedArrowInfinityBranch_contradictions`.
- Rejected the three mandated Aristotle result bundles because they either:
  - targeted the already-refuted inverse bridge
    `IsDownArrowDir`/`IsUpArrowDir -> exp (I * (p + 1) * θ) = ±1`,
  - rebuilt a parallel `OpenMath/OrderStars.lean` interface,
  - or reproved cone-control material outside the live seam.
- Added the cycle-283 helper lemmas above and recompiled
  `OpenMath/OrderStars.lean`.
- Looked for a derivation of the new exact coincidence statement from the current
  concrete inputs already present in the file. Nothing live currently controls the
  nonzero zero-set of `fun z => exp z - R z` on `orderWeb R`.

## Possible solutions
- Prove a global theorem for the concrete Padé/rational approximation under study
  excluding nonzero solutions of `R z = exp z` on `orderWeb R`.
- If that theorem naturally lives outside the contradiction seam, add a small
  theorem-local bridge back to
  `no_nonzero_unit_points_on_orderWeb_iff_no_nonzero_eq_exp`.
- Only after this is available, revisit whether the separate `0 ∉ support`
  hypotheses are genuinely next, or whether they can be discharged from the same
  concrete nondegeneracy package.
