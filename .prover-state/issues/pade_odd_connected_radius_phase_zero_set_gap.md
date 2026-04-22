# Issue: odd down-arrow radius-phase zero set still needs the crossing argument

## Blocker
The only remaining live `sorry` in `OpenMath/PadeOrderStars.lean` is now:

```lean
padeR_odd_downArrowConnectedRadiusPhaseZeroSet_of_neg_errorConst
```

This helper asks for:
- `∃ δ > 0, ∃ Z : Set (ℝ × ℝ)`
- `IsConnected Z`
- every `p ∈ Z` satisfies the actual odd local geometry
  `p.1 ∈ Icc (0 : ℝ) δ` and `p.2 ∈ Icc (-p.1) p.1`
- the corresponding complex point
  `w = p.1 * exp ((θ0 + p.2) I)` has
  `Im (padeR n d w * exp (-w)) = 0` and `Re > 0`
- `Prod.fst '' Z` contains all of `Icc (0 : ℝ) δ`

The downstream theorem
`padeR_odd_downArrowSameComponentRadiusPhaseBound_of_neg_errorConst`
is now proved from this helper, so the live blocker has become purely this
radius-phase connected-zero-set construction.

## Context
- The odd uniform strip theorem is already proved:
  `padeR_odd_downArrowUniformRadiusPhaseStrip_of_neg_errorConst`.
- That theorem gives:
  - uniform `Re > 0` on a genuine odd strip,
  - positive/negative `Im` signs on the two boundary arcs,
  - hence at least one zero of the imaginary part on every fixed-radius slice.
- Cycle 338 refactored the old same-component theorem into a wrapper over the
  new connected-zero-set helper, and verified the file still compiles.
- Three ready Aristotle bundles from earlier cycles were rejected, and the
  fresh cycle-338 completed outputs were also rejected because they rebuilt toy
  interfaces (`orderWeb := Set.univ`, stub support records, or custom helper
  axioms) instead of proving against the live file.

## What was tried
- Strict transplant audit of the ready Aristotle bundles
  `6dba509e...`, `14cc6695...`, and `b5dd84a3...`.
- Local refactor to isolate the exact topological seam as a connected
  radius-phase zero-set theorem.
- Fresh focused Aristotle batch on five exact odd-only surfaces, followed by
  the single allowed 30-minute wait and single refresh.
- Inspection of the completed cycle-338 outputs:
  - `c0ce4dc0...` replaced the live interface with `orderWeb := Set.univ`
  - `ffc04fff...` introduced a stub theorem
    `orderWeb_connected_component_sector`
  - `08c58b2a...` imported `Mathlib` and replaced the live support structure

## Possible solutions
- Prove a theorem-local rectangle crossing lemma:
  for a continuous real-valued function on a compact radius-phase rectangle,
  opposite signs on the two phase edges yield a compact connected subset of the
  zero set whose first-coordinate projection is the full radius interval.
- Or prove the equivalent statement directly for the connected component of the
  odd-strip zero set containing the `r = 0` point, using compactness and a
  separation argument to show its radius projection cannot stop early.
- Once such a connected set `Z` is obtained, the remaining Padé proof is
  straightforward: map `Z` into `ℂ`, use connectedness of the image, and the
  already-landed wrapper finishes the same-component continuation automatically.
