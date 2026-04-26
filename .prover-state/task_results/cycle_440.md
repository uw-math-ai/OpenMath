# Cycle 440 Results

## Worked on

AM4 vector quantitative convergence chain — new file
`OpenMath/LMMAM4VectorConvergence.lean`. Promoted three AB5 vector
sixth-order Taylor helpers from `private` to public in
`OpenMath/LMMAB5Convergence.lean`:
- `iteratedDeriv_six_bounded_on_Icc_vec`
- `derivY_fifth_order_taylor_remainder_vec`

(`y_sixth_order_taylor_remainder_vec` was already public from cycle 423.)

## Approach

Literal port of the scalar AM4 chain (`LMMAM4Convergence.lean`, cycle 436)
to the vector setting, using the AM3 vector chain (cycle 439) as the
structural model. All eight theorems written in a single batch:

- `IsAM4TrajectoryVec`, `am4VecResidual`, `am4Vec_localTruncationError_eq`
- `am4Vec_one_step_lipschitz` (with local `B251`/`B646`/`B264`/`B106`/`B19`
  abbreviations to dodge heartbeat-timeouts on triangle-inequality goals)
- `am4Vec_one_step_error_bound` and `am4Vec_one_step_error_pair_bound`
  (4-window implicit recurrence under `(251/720)·h·L ≤ 1/2`, slackened to
  growth `4L` and residual coefficient `2`)
- `am4Vec_pointwise_residual_bound` (sixth-order Taylor identity, exact
  triangle coefficient `250389/21600 ≈ 11.59`, slackened to `12`)
- `am4Vec_local_residual_bound` (`‖τ_n‖ ≤ C·h⁶`)
- `am4Vec_global_error_bound` (`‖y_N − y(t₀+Nh)‖ ≤ exp(4L·T)·ε₀ + K·h⁵`
  for `(N+3)·h ≤ T`), assembled via `lmm_error_bound_from_local_truncation`
  at `p = 5` with effective Lipschitz constant `4L`.

After promoting the AB5 helpers, ran
`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build
OpenMath.LMMAB5Convergence` to expose the new public symbols (per the
cycle-438 lesson), then `lake env lean OpenMath/LMMAM4VectorConvergence.lean`
for the new file. Both passed on the first try.

## Result

SUCCESS — `OpenMath/LMMAM4VectorConvergence.lean` compiles cleanly
(zero warnings/errors) on the first attempt. The file is ~610 lines, well
under the size cap. `lake build OpenMath.LMMAM4VectorConvergence` also
passes cleanly. The full pipeline (Aristotle helpers were skipped — see
"Aristotle skipped" below) closed manually in a single edit.

`OpenMath/LMMAB5Convergence.lean` continues to compile after the `private`
promotions.

## Aristotle skipped

The strategy explicitly directed to skip the cycle-440 Aristotle queue:
all six "ready for incorporation" bundles either targeted the closed AM3
vector seam (`f33885a0`, `36794c4c`, `4887ae5b`) or stale AM5/AB6/Truncation
files (`2003d297`, `04cc8648`, `5d47be46`). No new Aristotle batch was
submitted this cycle since the manual port closed in one shot, mirroring
the cycle-439 pattern.

## Dead ends

None. The literal port from the AM4 scalar template combined with the AM3
vector smul/`module` idioms went through cleanly. Notably:

- `module` closes the residual algebraic identity directly after
  `simp only [smul_sub, smul_add, smul_smul]`, exactly as in AM3 vector.
- `conv_lhs => rw [hstep]` correctly avoids rewriting inside `f tn yn`
  (the cycle-438 hazard).
- Triangle inequality decomposition with explicit `B251`/`B646`/`B264`
  /`B106`/`B19` abbreviations (cycle 439 pattern) avoids any heartbeat
  pressure in the Lipschitz step.
- `nlinarith [hsmall]` closes the implicit `1 - (251/720)hL > 0` and
  `1 ≤ (1 - (251/720)hL) * 2` goals, and `nlinarith [hx_nn, hx_small,
  hsmall]` closes the divided-coefficient comparison
  `1 + (23/16)·hL ≤ (1 - (251/720)hL)·(1 + h·(4L))` — `4L` (not `3L`)
  per the cycle-436 lesson.

## Discovery

The vector AM4 chain follows the same coefficient algebra as the scalar
chain: the explicit-history weights still sum to `23/16 = 1035/720`, the
`nlinarith` divided-coefficient comparison still wants `4L` not `3L`, and
the Taylor triangle bound still gives `250389/21600` slackened to `12`.
The only structural changes from the scalar port are
`abs → norm`/`* → •`/`abs_sub_le → norm_sub_le`, and the use of `module`
for the polynomial smul identity in place of `ring`.

## Suggested next approach

Continue along the AM frontier: **AM5 vector** quantitative convergence
chain in a new `OpenMath/LMMAM5VectorConvergence.lean`. This will need
to-be-promoted seventh-order vector Taylor helpers from
`OpenMath/LMMAB6VectorConvergence.lean`
(`iteratedDeriv_seven_bounded_on_Icc_vec`,
`y_seventh_order_taylor_remainder_vec`,
`derivY_sixth_order_taylor_remainder_vec`), mirroring the scalar AM5 chain
in `OpenMath/LMMAM5Convergence.lean` (cycle 437) at coefficient
`23325037/725760 ≈ 32.14` slackened to `33` and growth `5L`.
