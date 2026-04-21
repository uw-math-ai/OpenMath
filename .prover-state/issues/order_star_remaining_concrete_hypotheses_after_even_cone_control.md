# Issue: Remaining concrete contradiction inputs after even-angle cone control

## Blocker
Cycle 279 proved one live theorem-local cone-control lemma:

- `local_minus_near_even_angle_of_pos_errorConst`

But the live contradiction below `ConcreteRationalApproxToExp` is still blocked
because that is only one branch-local analytic input. The contradiction still
needs the remaining local cone cases, the nonzero/unit-level obstruction, the
far-field sign input, and a bridge from generic realized tangent directions to
the 355B even/odd angle families.

## Context
- Live file: `OpenMath/OrderStars.lean`
- Newly proved live lemma:
  - `local_minus_near_even_angle_of_pos_errorConst`
- Existing live helper layer from cycle 278 remains available:
  - `mem_orderWeb_of_mem_globalOrderArrowBranch_support`
  - `exists_mem_support_norm_gt_of_escapesEveryClosedBall`
  - `exists_mem_inter_rayConeNearOrigin_of_branchTracksRayNearOrigin`
  - `exists_mem_support_unit_level_of_connected_orderWeb_branch`
- The live seam is still unchanged:
  - `RealizedDownArrowInfinityBranch`
  - `RealizedUpArrowInfinityBranch`
  - `RealizesInfinityBranchGerms`
  - `ConcreteRationalApproxToExp`

## What was tried
- Rejected the three cycle-278 Aristotle bundles again because they rebuilt a
  parallel `OpenMath/OrderStars.lean`.
- Proved the even-angle / `C > 0` local cone-control lemma manually in the live file.
- Submitted five new cycle-279 Aristotle scratch jobs focused on the remaining
  cone-control and contradiction subgoals.
- After the required 30-minute wait and single refresh:
  - two contradiction jobs completed with errors and were rejected because they
    again fabricated a parallel `OpenMath/OrderStars.lean` with witness fields,
  - three local-cone jobs were still `IN_PROGRESS` at the one allowed check.

## Minimal theorem statement now appearing sufficient
The local theorem that still looks like the right generic bridge is:

```lean
∀ θ : ℝ, IsDownArrowDir R θ →
  ∃ aperture > 0, ∃ radius > 0,
    ∀ z : ℂ, z ∈ rayConeNearOrigin θ aperture radius →
      ‖R z * exp (-z)‖ < 1
```

and similarly the up-arrow analogue with `1 < ‖R z * exp (-z)‖`.

Cycle 279 only proved one concrete instance of that scheme, not the fully
generic tangent form.

## Possible solutions
- Prove the three remaining parity/sign cone-control lemmas first:
  - even-angle / `C < 0`
  - odd-angle / `C < 0`
  - odd-angle / `C > 0`
- Then prove a classification theorem turning a generic
  `IsDownArrowDir R θ` / `IsUpArrowDir R θ` into the appropriate 355B angle case.
- Only after that, return to the unit-level and far-field contradiction inputs.
- Keep rejecting any Aristotle artifact that:
  - introduces a parallel `OpenMath/OrderStars.lean`,
  - redefines `orderWeb` as the unit-level locus,
  - adds witness-style branch fields not present in the live seam.
