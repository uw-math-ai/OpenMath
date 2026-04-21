# Issue: Padé no-escape seam now reduces to unit-level order-web exclusion plus sign feeders

## Blocker
After cycle 303, `OpenMath/PadeOrderStars.lean` no longer threads the derived
exact-coincidence statement

`∀ z ≠ 0, z ∈ orderWeb (padeR n d) → padeR n d z = exp z → False`

as a primitive input. The live Padé seam now asks directly for the smaller
primitive field

`∀ z ≠ 0, z ∈ orderWeb (padeR n d) → ‖padeR n d z * exp (-z)‖ = 1 → False`

together with the local/far sign-control inputs.

No live theorem currently produces that unit-level exclusion or the sign-control
package for `padeR n d`, so `PadeRConcreteNoEscapeInput` still cannot be built
from existing Padé interfaces alone.

## Context
- Live file:
  - `OpenMath/PadeOrderStars.lean`
- Repaired boundary:
  - `concreteRationalApproxToExp_of_padeR`
  - `PadeRConcreteNoEscapeInput`
  - `padeRConcreteNoEscapeInput_of_realizesInfinityBranchGerms`
- Abstract consumer:
  - `OpenMath/OrderStars.lean`
  - `concreteRationalApproxToExp_of_realizedArrowInfinityBranch_contradictions`

Cycle 303 changed the Padé-local bundle so it matches the primitive
`OrderStars` contradiction boundary. The remaining missing inputs are now:
- nonzero unit-level exclusion on `orderWeb (padeR n d)`
- local minus cone control near down-arrow directions
- local plus cone control near up-arrow directions
- far-field plus sign on `orderWeb (padeR n d)`
- far-field minus sign on `orderWeb (padeR n d)`

The zero-support exclusion fields were not targeted this cycle because the live
branch-adjoining lemmas already show they are not derivable from the realized
branch interface alone.

## What was tried
- Audited the live dependency chain around:
  - `thm_355D_of_padeR`
  - `thm_355E'_of_padeR`
  - `ConcreteRationalApproxToExp`
  - `PadeRConcreteNoEscapeInput`
- Replaced the Padé-local primitive hypothesis `no_nonzero_eq_exp` with the
  smaller primitive hypothesis `no_nonzero_unit_points_on_orderWeb`.
- Added only a derived helper theorem
  `PadeRConcreteNoEscapeInput.no_nonzero_eq_exp`, proved from the existing
  `OrderStars` equivalence theorem.
- Re-read `OpenMath/OrderStars.lean` for generic local cone lemmas.
  The available cone lemmas all require a leading-term error bound
  `‖R z * exp (-z) - (1 - C z^(p+1))‖ ≤ K ‖z‖^(p+2)`, not just continuity.
- Submitted five Aristotle scratch jobs for the next feeder candidates:
  - `a43ef8ad-0287-465f-8571-8d96f644745d`
  - `c91e5315-67f7-4c21-a19a-2c0f7d4c952c`
  - `0bb82e67-8c95-4d67-a17e-4d9a4a669414`
  - `f5fce893-2d9c-4ea5-b1eb-fd61f4b47d8d`
  - `a7da198e-c81f-4722-8819-aa113ae19781`
  A first refresh still showed all five jobs in `QUEUED`.

## Possible solutions
- Derive a Padé-side leading-term estimate for
  `padeR n d z * exp (-z)` from `OpenMath/Pade.lean`
  (`pade_approximation_order`, `padePhiErrorConst`,
  `expTaylor_exp_neg_local_norm_bound`) and then instantiate the generic
  `OrderStars` local cone lemmas.
- Separate the unit-level exclusion problem from the sign-control package:
  first determine the smallest true restriction on `(n,d)` under which
  nonzero unit-level order-web points are impossible, instead of promoting the
  current exploratory `n + d > 0` Aristotle statement into live code.
- If the far-field sign statements are too strong globally, narrow them to the
  actual class of escaping branches they are meant to contradict before adding
  any new live theorem.
