# Issue: Padé up-arrow connected-component meet input is still missing

## Blocker
The up-arrow side is not ready for the same pure-wrapper packaging that now
exists for the down-arrow side.

The first missing live theorem surface is an up-arrow analogue of
`PadeRUpArrowOrderWebConnectedComponentMeetInput`, or equivalently the first
sign-specific producers that would feed it. Without that, there is nothing to
compose into:

- `PadeRDownArrowConnectedRayConeSupportInput`
- `PadeRDownArrowRayTrackingSupportInput`
- `PadeRDownArrowBranchTrackingInput`

on the up-arrow side.

## Context
The new down-arrow wrapper chain in `OpenMath/PadeOrderStars.lean` is purely
compositional because these source theorems already exist:

- `padeRDownArrowOrderWebConnectedComponentMeetInput_of_pos_errorConst`
- `padeRDownArrowOrderWebConnectedComponentMeetInput_of_neg_errorConst`

Those, in turn, are backed by live same-component continuation theorems:

- `padeR_even_downArrowOrderWebSameComponentContinuation_of_pos_errorConst`
- `padeR_odd_downArrowOrderWebSameComponentContinuation_of_neg_errorConst`

By contrast, the live up-arrow surface currently stops much earlier. The file
has:

- `padeR_upArrowDir_of_neg_errorConst`
- `padeR_upArrowDir_of_pos_errorConst_oddAngle`
- `padeR_exists_upArrowDir`
- `padeR_exists_globalUpArrowBranch_of_upArrowsAtInfinity_pos_of_exists_upArrowDir`

but no theorem matching either of these forms:

- `padeR_*_upArrowOrderWebSameComponentContinuation_*`
- `padeRUpArrowOrderWebConnectedComponentMeetInput_of_*`

There is therefore no existing theorem to wrap into an up-arrow
connected-ray-cone support input.

## What was tried
- Searched `OpenMath/PadeOrderStars.lean` for up-arrow
  connected-component/continuation/meet theorems.
- Confirmed that the only connected-component cone-meeting infrastructure is
  down-arrow-specific.
- Checked whether the existing up-arrow direction and global-branch theorems
  already imply the missing input; they do not, because they do not provide
  ray-cone meeting inside a single connected component near the origin.

## Possible solutions
- Add the first sign-specific up-arrow continuation theorems mirroring the
  down-arrow pair:
  - an even-angle continuation theorem for negative error constant
  - an odd-angle continuation theorem for positive error constant
- Package those into sign-specific producers of
  `PadeRUpArrowOrderWebConnectedComponentMeetInput`.
- Only after that will an up-arrow mirror of the new down-arrow wrapper chain
  be a one-line constructor composition.
