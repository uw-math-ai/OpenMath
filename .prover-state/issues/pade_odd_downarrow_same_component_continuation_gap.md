# Issue: odd down-arrow continuation still needs a concrete strip-to-support bridge

## Blocker
The live blocker in `OpenMath/PadeOrderStars.lean` is now exactly:

```lean
padeR_odd_downArrowOrderWebSameComponentContinuation_of_neg_errorConst
```

at line 1784.

Cycle 335 removed the old generic bridge/selector scaffold because it was dead
code once the even case was refactored away from it. The remaining obstacle is
purely the concrete odd-angle case.

## Context
- The even case is solved directly:
  the exact positive real ray already lies in `orderWeb (padeR n d)` for all
  sufficiently small radii, so one connected component meets every small cone
  around `θ = 0`.
- The odd case still needs an honest connected-support construction near

```lean
θ0 = Real.pi / ((↑(n + d) + 1) : ℝ).
```

- The existing live infrastructure already provides:
  - `padeR_exp_neg_re_pos_of_small_norm`
  - `padeR_odd_downArrowArcEndpointSigns_of_neg_errorConst`
  - `padeR_odd_downArrowArcPhaseBridge_of_neg_errorConst`
- What is still missing is the upgrade from endpoint signs on short arcs to one
  connected subset of the order web meeting every sufficiently small cone.

## What was tried
- Triaged the ready cycle-334 Aristotle bundles first and rejected them for the
  known interface-changing failure modes.
- Refactored the live file to bypass the abstract bridge/selector path.
- Added a direct exact-ray proof for the even same-component continuation.
- Submitted five focused cycle-335 Aristotle jobs on the odd concrete route:
  uniform strip, connected zero set, selector extraction, connected support,
  and the final odd theorem.
- After the required single 30-minute wait and single refresh:
  - two jobs completed with unusable outputs
  - three jobs remained in progress

## Why the current odd seam is still hard
- Endpoint sign control on each fixed-radius arc is enough to get at least one
  zero of the imaginary part on that arc, but it does not by itself package
  those zeros into a connected support in `ℂ`.
- The old abstract zero-set/selector scaffold was too coarse because it tried to
  solve the full generic bridge problem; after the cycle-335 refactor, only the
  concrete odd-angle version remains.
- A usable proof likely needs one of these concrete steps:
  1. a genuine odd-angle uniform strip theorem over a radius interval
  2. a theorem turning that strip into a connected radius-phase zero set with
     full radius projection
  3. a direct support/path construction from an explicit selector

## Possible solutions
- Prove the odd uniform strip first, matching the cycle-335 Aristotle input
  `01_uniformRadiusPhaseStrip_oddDownArrow.lean`.
- If that lands, derive a connected radius-phase zero set before attempting any
  selector theorem.
- If selector extraction remains too hard, bypass it and prove a connected
  order-web support directly from the strip data plus a concrete phase choice.
