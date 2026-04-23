# Issue: fixed-radius slice derivative error bound is still missing

## Blocker
The remaining theorem

```lean
oddDownArrowRadiusPhaseFixedRadiusSlice_atMostOne_zero_of_neg_errorConst
```

is now blocked on a theorem-local derivative estimate for the fixed-radius slice

```lean
gρ(s) := oddDownArrowRadiusPhaseIm n d (ρ, s)
```

on `Set.Icc (-ρ) ρ`.

The concrete missing statement is an estimate of the form

```lean
|deriv gρ s - leadρ(s)| ≤ errρ
```

for `s ∈ Set.Ioo (-ρ) ρ` and sufficiently small `ρ`, where `leadρ(s)` is the
derivative of the explicit odd-angle leading term from the second-order local
expansion.

Without that bound, the cycle can set up the derivative path and the monotonicity
wrappers, but cannot justify the key sign step `deriv gρ s < 0`.

## Context
- The live file `OpenMath/PadeOrderStars.lean` now has only these two `sorry`s:
  - `oddDownArrowRadiusPhaseFixedRadiusSlice_atMostOne_zero_of_neg_errorConst`
  - `oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both`
- The following small helpers are now live near the seam:
  - `atMostOne_zero_of_strictAntiOn'`
  - `cos_ge_half_of_abs_le'`
  - `strictAntiOn_Icc_of_deriv_neg'`
  - `deriv_neg_of_leading_neg_with_small_error'`
  - `hasDerivAt_im_of_complex_ofReal'`
  - `oddDownArrowRadiusPhasePoint_hasDerivAt_snd`
- The second-order value infrastructure already available in the live file is:
  - `padeR_exp_neg_second_order_local_bound`
  - `padeRExpNegSecondCoeff_abs_lt_half_main`
  - `oddDownArrowRadiusPhaseEndpointSigns_on_trueSlice_of_neg_errorConst`

## What was tried
- Harvested the compatible helper lemmas from Aristotle bundle
  `62abbffe-aaaf-4c79-81b8-297ae6998ae2` and landed them in the live file.
- Rejected the stale or non-live bundles:
  - `3980824d-da8c-4575-b492-7edde5876f29` — changes the uniqueness surface
  - `3241ba9a-5c64-425e-8f48-34602d587987` — wrapper-only and adds helper `sorry`
  - `1198ce13-65b1-4595-aa48-f07e782da0ff` — reopens the old endpoint-sign seam
  - `12b957ac-de3c-4e64-aa75-20b5ee50320f` — stale artifact
- Proved the local derivative setup needed for the slice parameter:
  - complex-imaginary-part derivative transfer along `ℝ → ℂ`
  - derivative of `oddDownArrowRadiusPhasePoint n d (ρ, ·)`
- Submitted a fresh five-job Aristotle batch on the exact derivative-to-uniqueness seam:
  - `cdef2118-ab6d-4d94-82cb-476c20c8c960`
  - `7edd756f-0937-4f2a-a239-5e78c0c1cd90`
  - `8fe174e3-e849-4612-b018-5474ec3d5cab`
  - `7bc140f8-d504-443d-b583-fa648e106073`
  - `01fb0f0c-73c6-4c03-b94c-0dd7a48f5d5f`
- After the mandated 30-minute wait and the single allowed refresh, all five new
  jobs were still `IN_PROGRESS`, so there was nothing to transplant this cycle.

## Possible solutions
- Rebuild the proof of `padeR_exp_neg_second_order_local_bound` at the derivative
  level for the composed slice function `s ↦ padeR n d z(s) * exp (-z(s))`,
  rather than trying to differentiate the already-final norm bound.
- Introduce a theorem-local exact derivative decomposition for the explicit
  second-order split used in the value proof, then bound each derivative term
  separately on `Set.Icc (-ρ) ρ`.
- If the full derivative error bound is too expensive, prove a weaker but still
  sufficient sign theorem directly:

```lean
∀ s ∈ Set.Ioo (-ρ) ρ, deriv gρ s < 0
```

from an explicit main-term derivative plus a dominated remainder derivative,
and use that immediately with `strictAntiOn_Icc_of_deriv_neg'`.
