# Issue: Concrete Padé target for the order-star seam is not stated

## Blocker
`ConcreteRationalApproxToExp R data` is now the live seam for feeding
`thm_355D_of_concreteRationalApprox` and `thm_355E'_of_concreteRationalApprox`,
but there is still no theorem in the live development that chooses an actual
concrete `R`.

The search result is:
- `ConcreteRationalApproxToExp`
- `thm_355D_of_concreteRationalApprox`
- `thm_355E'_of_concreteRationalApprox`

all occur only in `OpenMath/OrderStars.lean`.

Separately, `OpenMath/Pade.lean` owns the actual Padé family `padeR` and the
Padé/A-stability theorem family, but it does not import `OpenMath/OrderStars`.
No file under `OpenMath/` imports `OpenMath/OrderStars` at all. So the concrete
consumer of the order-star seam has not yet been stated.

## Context
- `OpenMath/OrderStars.lean` now has a ready abstract-to-concrete seam:
  - `ConcreteRationalApproxToExp`
  - `concreteRationalApproxToExp_of_realizedArrowInfinityBranch_contradictions_of_no_nonzero_eq_exp`
  - `thm_355D_of_concreteRationalApprox`
  - `thm_355E'_of_concreteRationalApprox`
- `OpenMath/Pade.lean` defines:
  - `padeR`
  - the low-degree Padé specializations
  - the Padé A-stability/L-stability catalog
- `OpenMath/Pade.lean` currently proves the Padé-side story without using the
  order-star seam.
- The concrete examples already inside `OpenMath/OrderStars.lean`
  (`forwardEulerR`, `backwardEulerR`, `trapezoidalR`) are geometric examples,
  not live consumers of `ConcreteRationalApproxToExp R data`.
- `backwardEulerR` is already known to have a nonzero solution of
  `backwardEulerR z = exp z`, so it cannot be used as the target of the cycle-284
  exact-coincidence exclusion.

## What was tried
- Searched the live codebase for any consumer of
  `thm_355D_of_concreteRationalApprox` / `thm_355E'_of_concreteRationalApprox`.
- Searched for any file that imports `OpenMath/OrderStars`.
- Re-read the concrete seam in `OpenMath/OrderStars.lean` and the Padé-side
  theorem family in `OpenMath/Pade.lean`.
- Checked whether an existing concrete stability function in `OrderStars.lean`
  could honestly serve as the intended target; it cannot.

## Possible solutions
- State the first concrete consumer on the Padé side, in `OpenMath/Pade.lean`
  or in a new adjacent file imported by it, with a theorem-local choice
  `R := padeR n d`.
- That theorem must also provide the matching bookkeeping object
  `data : OrderArrowTerminationData` plus the bridge hypotheses
  `IsPadeApproxToExp data` and `RealizesInfinityBranchGerms (padeR n d) data`.
- The first genuinely missing analytic input for that concrete `R` is still:
  `∀ z : ℂ, z ≠ 0 → z ∈ orderWeb (padeR n d) → padeR n d z = exp z → False`.
- Only after that concrete coincidence-exclusion theorem exists should the next
  remaining concrete hypotheses be revisited:
  `0 ∉` realized branch support, local cone `< 1` / `> 1` control, and far-field
  sign control on large order-web points.
