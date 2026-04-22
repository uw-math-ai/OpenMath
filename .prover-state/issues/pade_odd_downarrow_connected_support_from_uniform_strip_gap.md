# Issue: odd down-arrow connected support still lacks the strip-to-support step

## Blocker
The only remaining live sorry in `OpenMath/PadeOrderStars.lean` is now the
specialized helper

```lean
padeR_odd_downArrowConnectedRayConeSupport_of_neg_errorConst
```

which asks for

```lean
Nonempty
  (PadeRConnectedRayConeOrderWebSupport n d
    (Real.pi / ((↑(n + d) + 1) : ℝ)))
```

This is strictly smaller than the old public continuation theorem, but it still
requires one connected subset of `orderWeb (padeR n d)` meeting every
sufficiently small cone around the odd angle.

## Context
- Cycle 336 proved the new local theorem
  `padeR_odd_downArrowUniformRadiusPhaseStrip_of_neg_errorConst`.
- The old odd endpoint-sign theorem is now just a corollary of that uniform
  strip.
- The public continuation theorem is already reduced to the connected-support
  helper above.
- What is still missing is not any further sign estimate; it is the topological
  step from the family of strip witnesses to one connected support in `ℂ`.

## What was tried
- Checked the ready Aristotle bundles first; all reusable-looking files were
  stale, interface-changing, or based on fake local definitions / sidecar files.
- Proved the uniform strip directly in the live file.
- Tried to see whether one fixed `(δ, η)` strip could be enough to solve the
  live theorem.

## Why that fixed-strip route fails
- A fixed strip only controls phases inside `[-η, η]`.
- The live theorem needs one fixed connected support that meets
  `rayConeNearOrigin θ0 aperture radius` for every smaller `aperture > 0`.
- So even a connected support extracted from one strip would not obviously meet
  all smaller apertures unless it also comes with a genuine continuation /
  nesting argument as `η → 0`.

## Possible solutions
- Prove a direct odd-only theorem turning the whole family of uniform strips
  (one for each small `η`) into a connected support meeting every cone.
- Or first build an odd-only connected radius-phase zero set with full radius
  projection and then map it into `ℂ`, avoiding any generic selector layer.
