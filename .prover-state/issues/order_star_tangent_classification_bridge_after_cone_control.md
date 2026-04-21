# Issue: Missing tangent-classification bridge after the cone-control layer

## Blocker
Cycle 280 leaves `OpenMath/OrderStars.lean` with all four concrete local
cone-control lemmas proved, but the realized infinity-branch contradiction still
needs the generic theorem-local bridge

- `∀ θ, IsDownArrowDir R θ → ∃ aperture > 0, ∃ radius > 0, ... < 1`
- `∀ θ, IsUpArrowDir R θ → ∃ aperture > 0, ∃ radius > 0, ... > 1`

The file does not yet contain a theorem classifying an arbitrary realized
`IsDownArrowDir R θ` / `IsUpArrowDir R θ` into one of the discrete 355B
even/odd angle families.

## Context
- Live concrete cone lemmas now available:
  - `local_minus_near_even_angle_of_pos_errorConst`
  - `local_plus_near_even_angle_of_neg_errorConst`
  - `local_plus_near_odd_angle_of_pos_errorConst`
  - `local_minus_near_odd_angle_of_neg_errorConst`
- Existing exact-ray 355B theorems:
  - `arrow_up_of_neg_errorConst`
  - `arrow_down_of_pos_errorConst`
  - `arrow_down_of_neg_errorConst_odd`
  - `arrow_up_of_pos_errorConst_odd`
- Realized branch structures still store only:
  - `tangentAngle : ℝ`
  - `tangentDown : IsDownArrowDir R tangentAngle` or
  - `tangentUp : IsUpArrowDir R tangentAngle`
- The contradiction shape from
  `.prover-state/issues/order_star_realized_infinity_branch_contradiction_shape.md`
  expects the generic local bridge, not just the four concrete angle lemmas.

## What was tried
- Searched the repo for an existing inverse/classification theorem for
  `IsDownArrowDir` / `IsUpArrowDir`; none exists.
- Checked the live exact-ray theorems and the cycle-280 Aristotle bundles.
  They only provide forward implications from concrete angle/sign data to
  arrow orientation.
- Proved the remaining three live cone lemmas anyway, so the only missing step
  is now the generic dispatch from a realized tangent direction to one of those
  concrete cone lemmas.

## Possible solutions
- Prove a theorem-local inverse classification from the asymptotic main term
  `1 - C * z^(p+1)`:
  if `θ` is an arrow direction, then `exp (I * (p + 1) * θ)` must be `±1`,
  so `θ` is congruent to an even or odd 355B angle modulo `2π / (p + 1)`.
- Package that classification directly in the final contradiction-ready form,
  so a `RealizedDownArrowInfinityBranch` immediately yields local `< 1` cone
  control and a `RealizedUpArrowInfinityBranch` immediately yields local `> 1`
  cone control.
- If the inverse classification is too long to prove next, keep it as an
  explicit theorem-local hypothesis of the contradiction theorem. Do not move it
  into `IsRationalApproxToExp` and do not redesign the branch structures.
