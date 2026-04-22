# Cycle 344 Results

## Worked on
- `OpenMath/PadeOrderStars.lean`
- Live helper seam:
  `oddDownArrowRadiusPhaseEndpointSigns_on_trueSlice_of_neg_errorConst`
- Live helper seam:
  `oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both`
- Blocker issue update:
  `.prover-state/issues/pade_odd_wedge_projection_no_stop_gap.md`

## Approach
- Read:
  - `.prover-state/strategy.md`
  - `.prover-state/task_results/cycle_343.md`
  - `.prover-state/issues/pade_odd_wedge_projection_no_stop_gap.md`
  - the two live helper proofs in `OpenMath/PadeOrderStars.lean`
- Re-verified the live file with:
  `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeOrderStars.lean`
- Submitted a focused 5-job Aristotle batch on the current live seams:
  - `b58e353a-8d3b-468c-87ac-610ac57dcc10`
  - `488f6dd6-71c6-4afc-907e-5207d2287a26`
  - `b93eb787-fc18-41ed-ab57-992c1206a54f`
  - `a3eacefb-ee5f-4e2a-ad48-ac56d4f9adb0`
  - `861b766b-4677-4960-bb86-0294185f6a77`
- Launched the required `sleep 1800` wait and then performed the cycle’s
  single Aristotle refresh.
- After Aristotle stayed queued, worked the true-slice seam manually on paper by
  tracing the coefficient algebra one order past the existing
  `padeR_exp_neg_leading_term` theorem.
- Reduced the endpoint obstruction to a candidate exact second-order
  coefficient:

  ```lean
  let m := n + d
  a₂(n,d) =
    padePhiErrorConst n d * ((n - d) * (m + 1)) / (m * (m + 2))
  ```

  for the `z^(m+2)` term of `padeR n d z * exp (-z)` when `m > 0`.
- Observed that this would replace the old blocked comparison
  `K * r < (-padePhiErrorConst n d) * sin (...) / 2`
  by a second-order factorization plus a strictly favorable coefficient
  comparison.
- Wrote the sharper blocker back into
  `.prover-state/issues/pade_odd_wedge_projection_no_stop_gap.md`.

## Result
- FAILED to close either live `sorry` in `OpenMath/PadeOrderStars.lean`.
- SUCCESS in sharpening the blocker:
  the true-slice seam is no longer “some better asymptotic bound” abstractly,
  but specifically the missing second-order factorization

  ```lean
  padeR n d z * exp (-z) -
    (1
      - (padePhiErrorConst n d : ℂ) * z ^ (m + 1)
      + (a₂(n,d) : ℂ) * z ^ (m + 2))
  = z ^ (m + 3) * h z
  ```

  or an equivalent theorem-local `O(‖z‖^(m+3))` bound.
- SUCCESS in sharpening the fixed-radius seam:
  the exact missing local theorem is a strict-monotonicity or at-most-one-zero
  statement for the fixed-radius slice map on `Set.Icc (-ρ) ρ`.
- PARTIAL verification:
  `OpenMath/PadeOrderStars.lean` still compiles with the same two live
  `sorry`s.
- PARTIAL Aristotle outcome:
  all five fresh cycle-344 jobs remained `QUEUED` on the single refresh, so
  there was nothing to incorporate.

## Dead ends
- Reusing the coarse witness from `padeR_exp_neg_local_bound` would only
  reproduce the cycle-343 failure mode: the `O(r^(m+2))` constant is at the
  same order as the true-slice main term and is too blunt to force endpoint
  sign.
- A first-order-only model is insufficient on the true slice because the degree
  `m + 2` term contributes at exactly the same `r^(m+2)` scale as
  `sin ((m + 1) * r)`.
- For the fixed-radius seam, existence of a zero on each radius slice is still
  not enough to contradict a clopen split without an additional uniqueness or
  monotonicity theorem on that slice.

## Discovery
- The candidate exact degree-`m + 2` coefficient appears to be

  ```lean
  a₂(n,d) =
    padePhiErrorConst n d * ((n - d) * (m + 1)) / (m * (m + 2))
  ```

  with `m = n + d > 0`.
- The corresponding ratio

  ```lean
  |a₂(n,d)| / ((-padePhiErrorConst n d) * (m + 1)) =
    |n - d| / (m * (m + 2))
  ```

  is strictly less than `1`, and in particular is small enough to sit below the
  standard lower slope coming from `Real.mul_lt_sin`.
- That means the endpoint helper likely is salvageable once the second-order
  factorization is formalized.
- The final seam is now best stated as a fixed-radius strict-monotonicity or
  at-most-one-zero theorem, not as a broad connected-component/topology gap.

## Suggested next approach
- Formalize the second-order asymptotic at the origin:
  either directly for `padeR n d z * exp (-z)`, or first for the numerator-side
  defect and then divide by `padeQ`.
- Use that to rebuild
  `oddDownArrowRadiusPhaseEndpointSigns_on_trueSlice_of_neg_errorConst`
  without the old `hgapTarget`.
- After the endpoint helper closes, attack the remaining seam with the exact
  fixed-radius theorem now written in the blocker issue:
  `StrictMonoOn` of the slice map on `Set.Icc (-ρ) ρ`, or an equivalent
  at-most-one-zero theorem.
