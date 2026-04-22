# Issue: Padé concrete endpoint still needs an arrow-to-sign bridge after the explicit-sign seam refactor

## Blocker
Cycle 314 repaired `OpenMath/PadeOrderStars.lean` so
`PadeRConcreteNoEscapeInput` stores the honest explicit-sign local feeders
instead of the false direction-only cone interface. But the downstream theorem
`concreteRationalApproxToExp_of_padeR` still has to feed the generic
`OrderStars.concreteRationalApproxToExp_of_realizedArrowInfinityBranch_contradictions`,
which ultimately needs local cone control for arbitrary
`IsDownArrowDir (padeR n d) θ` / `IsUpArrowDir (padeR n d) θ`.

After the refactor, the exact remaining theorem-local gap is now isolated as:

- `PadeRDownArrowSignBridge n d`
- `PadeRUpArrowSignBridge n d`

These are the hypotheses needed to turn a Padé arrow direction into the cosine
sign required by the live explicit-sign feeders.

## Context
- `PadeRConcreteNoEscapeInput.local_minus_near_of_sign` now asks for
  `0 < padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ)`.
- `PadeRConcreteNoEscapeInput.local_plus_near_of_sign` now asks for
  `padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ) < 0`.
- The local constructors
  `padeRConcreteNoEscapeInput_of_realizesInfinityBranchGerms_of_zeroSupportExclusion`,
  `padeRConcreteNoEscapeInput_of_realizesInfinityBranchGerms`, and
  `padeREhleBarrierInput_of_padeR`
  now fill those fields directly with:
  - `padeR_local_minus_near_of_errorConst_cos_pos`
  - `padeR_local_plus_near_of_errorConst_cos_neg`
- The remaining downstream wrapper theorems
  `PadeRConcreteNoEscapeInput.concrete`,
  `PadeREhleBarrierInput.concrete`,
  `PadeREhleBarrierInput.thm_355D`, and
  `PadeREhleBarrierInput.thm_355E'`
  therefore now ask only for the two sign bridges above.

## What was tried
- Kept the refactor local to `OpenMath/PadeOrderStars.lean`.
- Removed the stronger local cone hypotheses from the Padé-side constructors and
  rewired them to use the landed explicit-sign feeder theorems directly.
- Avoided reviving the false route
  `IsDownArrowDir` / `IsUpArrowDir` `→` symmetric cone control.
- Avoided redesigning `OrderStars` or the realized-branch structures.

## Possible solutions
- Prove a Padé-local theorem that a down-arrow direction implies the positive
  sign in `PadeRDownArrowSignBridge`, and likewise an up-arrow direction
  implies the negative sign in `PadeRUpArrowSignBridge`.
- If a full direction-to-sign theorem is still too ambitious, prove a theorem
  directly in the contradiction-ready shape needed by
  `concreteRationalApproxToExp_of_padeR`, but keep it theorem-local and do not
  put fake bridge fields back into `PadeRConcreteNoEscapeInput`.
- Do not revert to the old direction-only local feeder interface, and do not
  redesign `OrderStars` in the next cycle unless the planner explicitly changes
  scope.
