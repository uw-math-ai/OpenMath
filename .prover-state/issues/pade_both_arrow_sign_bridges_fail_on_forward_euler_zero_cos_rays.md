# Issue: Both global Padé arrow-sign bridges fail on forward-Euler zero-cos rays

## Blocker
The current global strict bridge targets are false for the live
`IsDownArrowDir` / `IsUpArrowDir` definitions in `OpenMath/PadeOrderStars.lean`.

Concrete counterexamples now exist for both directions in the forward-Euler
case `padeR 1 0 = 1 + z`:

- `¬ PadeRDownArrowZeroCosExclusion 1 0`
- `¬ PadeRDownArrowSignBridge 1 0`
- `¬ PadeRUpArrowZeroCosExclusion 1 0`
- `¬ PadeRUpArrowSignBridge 1 0`

So theorem-local zero-cosine exclusion is the honest outer boundary; a global
Padé-wide strict arrow-to-sign bridge is not salvageable as stated.

## Context
The live witnesses in `OpenMath/PadeOrderStars.lean` are:

- Down-arrow zero-cos ray:
  - `padeR10_pi_div_four_zeroCos`
  - `padeR10_pi_div_four_isDownArrowDir`
  - `not_padeRDownArrowZeroCosExclusion_one_zero`
  - `not_padeRDownArrowSignBridge_one_zero`
- Up-arrow zero-cos ray:
  - `padeR10_three_pi_div_four_zeroCos`
  - `padeR10_three_pi_div_four_isUpArrowDir`
  - `not_padeRUpArrowZeroCosExclusion_one_zero`
  - `not_padeRUpArrowSignBridge_one_zero`

The exact rays are:

- `θ = Real.pi / 4`, where
  `padePhiErrorConst 1 0 * Real.cos (2 * (Real.pi / 4)) = 0`
  but `IsDownArrowDir (padeR 1 0) (Real.pi / 4)`.
- `θ = 3 * Real.pi / 4`, where
  `padePhiErrorConst 1 0 * Real.cos (2 * (3 * Real.pi / 4)) = 0`
  but `IsUpArrowDir (padeR 1 0) (3 * Real.pi / 4)`.

The proofs reduce the exact rays to explicit real weights:

- down-arrow: `(1 + √2 t + t^2) * exp (-√2 t) < 1`
- up-arrow: `(1 - √2 t + t^2) * exp (√2 t) > 1`

## What was tried
- Proved both exact zero-cos identities directly.
- Proved the down-arrow and up-arrow exact-ray witnesses by reducing to the
  corresponding real radial weights and computing explicit derivatives.
- Re-checked the downstream seam: the live outer wrappers now honestly consume
  theorem-local zero-cos exclusion hypotheses instead of a global strict bridge.

## Possible solutions
- Keep the current honest seam:
  require theorem-local `PadeRDownArrowZeroCosExclusion` /
  `PadeRUpArrowZeroCosExclusion` only at wrappers that genuinely need strict
  sign.
- If a downstream theorem still wants a strict global bridge, narrow its
  hypotheses until the forward-Euler zero-cos witnesses are excluded by
  assumption.
- Do not spend more cycles trying to prove the current global
  `PadeRDownArrowSignBridge` / `PadeRUpArrowSignBridge`; the live counterexamples
  show those statements are false.
