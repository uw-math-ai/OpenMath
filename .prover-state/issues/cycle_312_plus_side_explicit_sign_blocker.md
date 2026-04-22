# Issue: Cycle 312 plus-side explicit-sign cone blocker

## Blocker
The explicit-sign up-cone analogue
`local_plus_near_of_errorConst_cos_neg`
was not landed this cycle. The minus-side theorem under
`0 < C * cos ((p + 1) * θ)` now compiles, but the positive-outside-the-unit-disk
companion still needs a clean pointwise helper extraction and should not be
forced through the false `IsUpArrowDir` symmetric-cone route.

## Context
Cycle 311 already showed that the live feeder shape

```lean
IsDownArrowDir (padeR n d) θ -> symmetric cone with ‖·‖ < 1
IsUpArrowDir   (padeR n d) θ -> symmetric cone with 1 < ‖·‖
```

is false at zero-cosine rays. In cycle 312, the honest replacement was started
on the live seam by adding:

- `OrderStars.local_minus_near_of_errorConst_cos_pos`
- `PadeOrderStars.padeR_local_minus_near_of_errorConst_cos_pos`

The missing companion would require the same explicit-sign style with
`padePhiErrorConst n d * cos (...) < 0`, not a recovery of sign information from
`IsUpArrowDir`.

## What was tried
- Added sorry-first skeletons for both generic explicit-sign lemmas and both Padé wrappers.
- Compiled the sorry-first state and submitted five Aristotle jobs:
  - `1c721556-f3bd-4c2c-b2d3-0326c9ed053e` for the generic minus lemma
  - `f263e639-f9f4-44bc-aba9-3b887cd953de` for the generic plus lemma
  - `6a55a267-c191-4568-9693-6209ede901f7` for the Padé minus wrapper
  - `e235e25f-8143-482e-bdbf-02f53a529719` for the Padé plus wrapper
  - `8418c228-9454-4df1-ad83-a77ab02d64a7` for the cone-margin helper
- Waited once for 30 minutes and refreshed once.
- Incorporated the completed wrapper proof shape only where it matched the live interface.
- Split the generic minus proof into a private pointwise helper to stay below the heartbeat ceiling.
- Removed the unfinished plus-side additions rather than leaving a `sorry` in the live files.

## Possible solutions
- Mirror the landed minus-side helper structure with a second pointwise helper that applies
  `main_plus_bound_of_re_neg` instead of `main_minus_bound_of_re_pos`.
- When reviving the plus-side theorem, keep the hypothesis explicit:
  `C * Real.cos ((↑(p + 1) : ℝ) * θ) < 0`.
- After both explicit-sign feeders exist, weaken the downstream
  `PadeRConcreteNoEscapeInput.local_minus_near_down` /
  `.local_plus_near_up` seam to explicit sign-margin or one-sided wedge inputs,
  rather than trying to recover those facts from `IsDownArrowDir` / `IsUpArrowDir`.
