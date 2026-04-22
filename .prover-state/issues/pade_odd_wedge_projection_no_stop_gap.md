# Issue: odd wedge projection no-stop lemma still missing

## Blocker
Cycle 343 split the remaining odd down-arrow gap into the two exact live helper
seams in `OpenMath/PadeOrderStars.lean`:

1. `oddDownArrowRadiusPhaseEndpointSigns_on_trueSlice_of_neg_errorConst`
2. `oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both`

The first seam is blocked by the quantitative target now exposed directly in
code:

```lean
K * r < (-padePhiErrorConst n d) * Real.sin (((↑(n + d) + 1) : ℝ) * r) / 2
```

for the `K, δ₀` returned by `padeR_exp_neg_local_bound n d`.

The second seam is blocked because the current live inputs only prove
nonemptiness of each true-wedge radius slice; they do **not** prove that the
fixed-radius slice of the zero set is connected, singleton, or otherwise unable
to meet both sides of a clopen partition.

## Context
- `oddDownArrowRadiusPhaseSliceZero_of_neg_errorConst` no longer reuses the
  failed `η = r` strip instantiation. It is now closed modulo the new helper
  `oddDownArrowRadiusPhaseEndpointSigns_on_trueSlice_of_neg_errorConst`.
- `oddDownArrowRadiusPhaseProjectionNoStop_of_neg_errorConst` is now closed
  modulo the new helper
  `oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both`.
- `OpenMath/PadeOrderStars.lean` compiles with exactly these 2 helper `sorry`s
  after the cycle-343 refactor.
- Cycle-343 Aristotle batch:
  - `c3160f50-9736-432f-8a49-3c422c7603cc`
  - `ee966484-4a7c-4cec-bfd7-e0571355ca08`
  - `fb99a47e-1f05-4adb-9cb2-e44462435db7`
  - `ec9a08b7-4ed5-419d-afd5-9974589af9f1`
  - `6ad5578f-fa4a-42ec-96eb-4c85673cad17`
- After the mandated single 30-minute wait and single refresh, **all five**
  cycle-343 Aristotle jobs were still `QUEUED`.
- Lean search found off-the-shelf sine lower bounds such as
  `Real.mul_lt_sin` / `Real.mul_le_sin`. These only reduce the first seam to a
  constant comparison:

  ```lean
  K < (-padePhiErrorConst n d) * (((↑(n + d) + 1) : ℝ)) / Real.pi
  ```

  or a nearby equivalent, but the current live hypotheses still provide no
  theorem connecting the `K` from `padeR_exp_neg_local_bound` to that explicit
  coefficient.

## What was tried
- Read the cycle-342 handoff, the existing blocker issue, and the two live
  `sorry` bodies first as instructed.
- Added the true-wedge helper
  `oddDownArrowRadiusPhaseEndpointSigns_on_trueSlice_of_neg_errorConst` above
  `oddDownArrowRadiusPhaseSliceZero_of_neg_errorConst`.
- Moved the old inner seam into a named local target `hgapTarget` inside that
  helper so the blocked comparison is explicit in code.
- Rewrote `oddDownArrowRadiusPhaseSliceZero_of_neg_errorConst` to use the new
  helper and keep the existing IVT proof shape on `Set.Icc (-r) r`.
- Added the fixed-radius helper
  `oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both` above
  `oddDownArrowRadiusPhaseProjectionNoStop_of_neg_errorConst`.
- Rewrote the final projection theorem so its remaining contradiction is exactly
  delegated to that fixed-radius helper.
- Verified with
  `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeOrderStars.lean`
  that the file compiles with exactly the two new helper `sorry`s.
- Submitted the five focused cycle-343 Aristotle jobs listed above, slept once
  for 30 minutes, and refreshed once.

## Possible solutions
- Strengthen the local asymptotic input near the origin from the coarse
  `≤ K * ‖z‖ ^ (n + d + 2)` remainder bound to a theorem with explicit
  next-order coefficient control, or at least a little-o statement strong enough
  to dominate the true-slice main term.
- Alternatively, derive a concrete upper bound on the **specific** `K` returned
  by `padeR_exp_neg_local_bound n d` that is small enough to imply the target
  inequality above after a standard lower bound on `Real.sin`.
- For the final clopen contradiction, prove one additional slice theorem on the
  true wedge for fixed `ρ`:
  either uniqueness of the zero on `Set.Icc (-ρ) ρ`, connectedness of the fixed
  radius zero slice, or a monotonicity theorem for
  `s ↦ Complex.im (padeR n d (...) * exp (-(...)))`.
  Without one of those, the current same-radius witnesses in `C` and `Cᶜ` do
  not contradict the live topology alone.
