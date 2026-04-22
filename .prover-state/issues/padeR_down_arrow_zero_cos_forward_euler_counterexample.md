# Issue: Forward-Euler Refutes the Global Padé Down-Arrow Strict Bridge

## Blocker
The global theorem-local target behind the current Padé seam is false:

- `PadeRDownArrowZeroCosExclusion 1 0`
- therefore also `PadeRDownArrowSignBridge 1 0`

for the current live definitions in `OpenMath/PadeOrderStars.lean`.

## Context
The formal witness now lives in `OpenMath/PadeOrderStars.lean`:

- `padeR10_pi_div_four_zeroCos`
- `padeR10_pi_div_four_isDownArrowDir`
- `not_padeRDownArrowZeroCosExclusion_one_zero`
- `not_padeRDownArrowSignBridge_one_zero`

Concrete witness:

- `n = 1`
- `d = 0`
- `θ = Real.pi / 4`

At this angle,

- `padePhiErrorConst 1 0 * Real.cos ((↑(1 + 0) + 1) * (Real.pi / 4)) = 0`

but the exact ray still satisfies

- `IsDownArrowDir (padeR 1 0) (Real.pi / 4)`.

So a down-arrow direction does not force strict positivity of the Padé cosine sign.

## What was tried
- Triaged the ready Aristotle bridge/exclusion outputs first; none provided a valid live repair.
- Reduced the forward-Euler ray to the exact real weight
  `(1 + √2 t + t^2) * exp (-√2 t)`.
- Proved that weight is strictly decreasing on `(0, ∞)` using an explicit derivative, which yields the down-arrow witness.

## Possible solutions
- Keep the Padé seam honest by requiring explicit theorem-local zero-cos exclusion only at outer wrappers that genuinely need strictness.
- Prefer the already-live nonstrict sign lemmas plus theorem-local exclusion hypotheses over any global strict bridge claim.
- If a downstream theorem needs a uniform strict bridge, that theorem needs a narrower hypothesis set; the current all-Padé statement is not salvageable as written.
