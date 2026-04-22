# Issue: odd radius-phase zero set still needs the clopen-to-crossing contradiction

## Blocker
The only live `sorry` remains:

```lean
padeR_odd_downArrowConnectedRadiusPhaseZeroSet_of_neg_errorConst
```

This still asks for one connected subset of the true odd radius-phase zero set
whose first-coordinate projection is all of `Set.Icc (0 : ℝ) δ`.

Cycle 339 added the compact separation seam:
- `exists_clopen_separating_closed_sets_of_component_images_disjoint`
- `exists_clopen_of_no_connected_subset_meeting_both`

So the remaining missing content is no longer the component packaging itself.
It is the contradiction step that turns a hypothetical clopen split of the
compact zero set into an impossible zero-free perturbation.

## Context
- File: `OpenMath/PadeOrderStars.lean`
- Current live sorry line after cycle-339 edits: around line 1957
- Already available analytic input:
  - `padeR_odd_downArrowUniformRadiusPhaseStrip_of_neg_errorConst`
  - positive real part on a small odd strip
  - opposite imaginary signs on the two fixed phase edges
- Already available compact-topology input from cycle 339:
  - compact clopen separation for disjoint connected-component images
  - conversion from “no connected subset meets both closed sets” to such a
    clopen split

## What was tried
- Triaged the six ready Aristotle bundles requested by the planner and rejected
  all of them under the live transplant filter.
- Added the two compact clopen-separation helpers above the live theorem.
- Submitted five focused cycle-339 Aristotle jobs on:
  - generic rectangle crossing,
  - connected-component projection,
  - triangle crossing,
  - direct live theorem,
  - direct component-projection specialization.
- After the single allowed wait and single refresh:
  - three jobs were still `IN_PROGRESS`
  - one direct theorem job rebuilt the interface with `padeR := exp`
  - one projection job failed immediately on an import issue

## Possible solutions
- Finish a rectangle-crossing theorem on a compact rectangle subtype:
  1. assume the zero set admits a clopen split separating the left and right
     zero traces,
  2. use Urysohn/Tietze-style separation to build a continuous scalar
     perturbation,
  3. show the perturbed function has no zeros,
  4. contradict the bottom/top sign IVT on each vertical slice.
- Or prove the same contradiction directly on the true wedge
  `{p | p.1 ∈ Icc 0 δ ∧ p.2 ∈ Icc (-p.1) p.1}` once sloping-edge signs
  `F(r,-r)` and `F(r,r)` are available.
- If the fixed-strip route is kept, an additional argument is still needed to
  recover the actual odd geometry `p.2 ∈ Icc (-p.1) p.1`; a plain rectangle
  crossing result by itself does not close the live theorem.
