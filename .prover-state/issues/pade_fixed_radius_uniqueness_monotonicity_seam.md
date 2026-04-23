# Issue: fixed-radius uniqueness still needs a monotonicity seam

## Blocker
`OpenMath/PadeOrderStars.lean` is now down to two live `sorry`s:

- `oddDownArrowRadiusPhaseFixedRadiusSlice_atMostOne_zero_of_neg_errorConst`
- `oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both`

The endpoint-sign theorem is closed, so the smallest remaining theorem-local seam is:

```lean
∀ ρ ∈ Set.Ioo (0 : ℝ) δmono,
  ∀ s₁ s₂ ∈ Set.Icc (-ρ) ρ,
    oddDownArrowRadiusPhaseIm n d (ρ, s₁) = 0 →
    oddDownArrowRadiusPhaseIm n d (ρ, s₂) = 0 →
    s₁ = s₂
```

What is still missing is a usable monotonicity/derivative-sign argument for the
fixed-radius slice `s ↦ oddDownArrowRadiusPhaseIm n d (ρ, s)`.

## Context
Cycle 352 added a quantitative second-order local bound
`padeR_exp_neg_second_order_local_bound` and used it to close
`oddDownArrowRadiusPhaseEndpointSigns_on_trueSlice_of_neg_errorConst`.

The file compiles with only the two remaining `sorry`s:

- `OpenMath/PadeOrderStars.lean:3752`
- `OpenMath/PadeOrderStars.lean:3762`

The current infrastructure is enough to control the value of the slice
function, but not yet its variation in `s`.

## What was tried
- Rejected the ready Aristotle bundles `0e8898de`, `914fbab1`, `cc01c469`,
  `db58b777`, `feb2aaaf`, and mixed bundle `b8f45bec` because they either
  reopened older seams, introduced new helper `sorry`s, or targeted stale
  theorem surfaces.
- Added theorem-local quantitative bounds for:
  - second-order Padé defect remainder,
  - second-order truncated-exponential remainder,
  - linear Padé-denominator error and inverse error,
  - `exp (-z) / padeQ n d z` quadratic error,
  - the final `O(‖z‖^(n+d+3))` bound for
    `padeR n d z * exp (-z)` after subtracting both explicit terms.
- Closed
  `oddDownArrowRadiusPhaseEndpointSigns_on_trueSlice_of_neg_errorConst`
  with the new second-order route.
- Submitted a fresh five-job Aristotle batch on the reduced two-sorry surface:
  - `4c958aca-b5b3-4622-bd13-4873094c6198` — still `IN_PROGRESS` (22%)
  - `cedda63b-fd05-432d-892b-74c2c1df9339` — still `IN_PROGRESS` (35%)
  - `3980824d-da8c-4575-b492-7edde5876f29` — `COMPLETE_WITH_ERRORS`
  - `9e276bba-6325-4ceb-86dc-ce0cbda7351a` — still `IN_PROGRESS` (31%)
  - `f0f3bf0c-6367-4fa4-98cf-ea7bd031b881` — still `IN_PROGRESS` (35%)

## Why the attempted wrapper result was rejected
The completed Aristotle wrapper-only result `3980824d...` filled the clopen
wrapper only by changing the uniqueness theorem surface to

```lean
{ρ : ℝ} (hρ : 0 < ρ) → ...
```

and leaving the uniqueness proof itself as `sorry`. That does not transplant to
the live theorem chain.

## Possible solutions
- Prove a theorem-local `StrictMonoOn` result for
  `fun s : ℝ => oddDownArrowRadiusPhaseIm n d (ρ, s)` on `Set.Icc (-ρ) ρ`
  for small `ρ`, using a derivative-sign estimate from the second-order local
  expansion.
- If the monotonicity proof is naturally local in `ρ`, then after the
  uniqueness theorem closes, thread its `δmono` into the later projection
  choice of `δ` so the wrapper theorem only needs to be used at radii already
  known to be `< δmono`.
- Only if justified from the actual slice formula, prove uniqueness for all
  positive radii; the current cycle did not establish that.
