# Cycle 517 Results

## Worked on
Butcher §38 / §383-§387 `G1` characterization wrappers in
`OpenMath/ButcherGroup.lean`.

## Approach
Followed the unblocked option from cycle 516: stayed away from
`IsG1Equiv.product_congr`, `G1.mul`, and the §384 convolution gap, and
added small sorry-first declarations on the existing quotient/identity
surface. The stubs were checked with
`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean
OpenMath/ButcherGroup.lean`, then closed one by one.

Submitted the requested Aristotle scaffold batch under
`.prover-state/aristotle_scaffolds/cycle_517/`:

- `G1_bSeriesHomAt_mk_apply.lean`
- `G1_bSeriesHomAt_one_apply.lean`
- `G1_hasTreeOrder_one_iff.lean`
- `G1_eq_one_iff.lean`
- `G1_one_extra.lean`

All five submissions returned HTTP 429 ("too many requests in progress"),
so there were no project IDs to poll or results to incorporate.

## Result
SUCCESS. Landed six sorry-free declarations:

- `QuotEquiv.bSeriesHom_mk`
- `IsG1Equiv.bSeriesHom_eq`
- `G1.bSeriesHomAt_mk_apply`
- `G1.hasTreeOrder_one_iff`
- `G1.hasTreeOrder_zero_one`
- `G1.eq_one_iff`

`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean
OpenMath/ButcherGroup.lean` succeeds. `rg -n "sorry|admit"
OpenMath/ButcherGroup.lean` reports no matches.

Lean LSP `lean_verify` scans on the six new declarations reported no source
warnings.

## Dead ends
No proof dead ends. The only tool dead end was the expected Aristotle HTTP
429 response on every scaffold submission.

## Discovery
`G1.bSeriesHomAt_one` already had the per-tree shape requested by the
planner, so the tracked code did not add a duplicate
`G1.bSeriesHomAt_one_apply`. The new `G1.eq_one_iff` is the cleaner
downstream-facing replacement for identity extensionality goals.

The source tree condition reduces the zero-stage identity to
`0 = 1 / (τ.density : ℝ)`; therefore `G1.hasTreeOrder_zero_one` is closed
purely by `BTree.order_pos`.

## Suggested next approach
For cycle 518, the planner should either pivot to the §384 convolution
(option 1 from cycle 516) if ready, or continue with similarly small
`G1`-side characterization wrappers. The §38 multiplication path remains
blocked by `.prover-state/issues/butcher_g1_mul_section384_blocker.md` and
`.prover-state/issues/butcher_section384_convolution.md`.
