# Cycle 603 Results

## Worked on
Split the depth-3 augmented associativity ladder out of
`OpenMath/ButcherGroup/Section386Aug.lean` into
`OpenMath/ButcherGroup/Section386Aug/DepthThree.lean`.

## Approach
Moved the cycle 600/602 depth-3 block into the new submodule:
`forestSum_cons_node_pair_depth_one`,
`forestSum_cons_node_singleton_node_singleton_depth_one`,
both compact depth-3 cons recurrences, both compact depth-3 expansion
lemmas, `shift_pair_agg`, `shift_singleton_node_singleton_agg`,
`shift_one_agg`, `shift_node_singleton_agg`, the four
`forestSum_assoc_three_*_head` lemmas, `forestSum_assoc_depth_three`,
and `mul_assoc_at_node_depth_three_children`.

Added imports in the new file for `Mathlib`, `OpenMath.RungeKutta`,
`OpenMath.OrderConditions`, `OpenMath.ButcherGroup.Core`,
`OpenMath.ButcherGroup.Section386Conv`, and
`OpenMath.ButcherGroup.Section386Aug`. Added
`OpenMath.ButcherGroup.Section386Aug.DepthThree` to the
`OpenMath/ButcherGroup.lean` umbrella import list.

Because the moved block crossed a file boundary, exposed the minimal
upstream helper interface it consumes: `order_le_one_iff`,
`AugSeries.shiftBy`, `AugSeries.shiftBy_node`, `forestSum`,
`forestSum_cons_depth_one_compact`,
`forestSum_cons_node_singleton_depth_one_compact`,
`bSeriesConvAug_node_cons_depth_one_expand_compact`, and
`bSeriesConvAug_node_cons_node_singleton_depth_one_expand_compact`.
No proof bodies were changed.

## Result
SUCCESS.

Line counts:
- Before: `OpenMath/ButcherGroup/Section386Aug.lean` had 3012 lines.
- After: `OpenMath/ButcherGroup/Section386Aug.lean` has 1807 lines.
- New: `OpenMath/ButcherGroup/Section386Aug/DepthThree.lean` has 1218 lines.
- Umbrella: `OpenMath/ButcherGroup.lean` has 2968 lines.

Verification:
- `lake env lean OpenMath/ButcherGroup/Section386Aug.lean` passed.
- `lake env lean OpenMath/ButcherGroup/Section386Aug/DepthThree.lean` passed.
- `lake env lean OpenMath/ButcherGroup.lean` passed.
- `lake build` passed.
- `rg -n "sorry" OpenMath/ButcherGroup/Section386Aug.lean OpenMath/ButcherGroup/Section386Aug/DepthThree.lean` returned no matches.
- A scratch visibility check importing only `OpenMath.ButcherGroup`
  successfully `#check`ed
  `ButcherTableau.mul_assoc_at_node_depth_three_children`.

## Dead ends
The first compile of `DepthThree.lean` failed because the planned cut
depended on helpers that were `private` inside `Section386Aug.lean`.
This was resolved by making only the cross-module helper interface
non-private.

After `lake env lean OpenMath/ButcherGroup/Section386Aug.lean`, the
new module still saw the old `.olean`; building
`OpenMath.ButcherGroup.Section386Aug` refreshed the imported artifact.

## Discovery
The depth-3 ladder is cohesive, but it depends on the depth-1/2 compact
forest-sum API and on `AugSeries.shiftBy`. Those helpers need to remain
visible for future depth submodules.

The relocated file produces the same existing unused-simp-argument
warnings in its moved proof block, but the build succeeds.

## Suggested next approach
Resume the depth-4 ladder using the smaller split structure. Start from
cohort enumeration via `BTree.order_le_four_iff` and mirror the cycle
598/599/600/602 pattern. If the depth-4 cohort family is large, prefer a
sibling `OpenMath/ButcherGroup/Section386Aug/DepthFour.lean` rather than
growing `DepthThree.lean` aggressively.
