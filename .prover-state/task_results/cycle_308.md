# Cycle 308 Results

## Worked on
- Repaired the false global continuity seam for the Padé/order-web no-escape package in:
  - `OpenMath/OrderStars.lean`
  - `OpenMath/PadeOrderStars.lean`
- Added:
  - `padeQ_ne_zero_of_mem_orderWeb`
  - `padeR_norm_exp_neg_continuousOn_orderWeb`
- Added the optional wrapper:
  - `padeR_local_plus_near_even_angle_of_neg_errorConst`
- Triaged Aristotle result `d3493ba8-e9e6-497c-a75f-14d6629fbb8a`.

## Approach
- Read `.prover-state/strategy.md` and the blocker issue
  `.prover-state/issues/pade_no_escape_global_continuity_false_at_poles.md`.
- Inspected the ready Aristotle summary and the live theorem
  `OpenMath/PadeAsymptotics.lean:305`.
- Refactored the generic `OrderStars` contradiction seam so theorem-local
  continuity hypotheses are now
  `ContinuousOn (fun z => ‖R z * exp (-z)‖) (orderWeb R)`.
- In the branch-level intermediate-value lemma, restricted continuity from the
  order web to branch support using `branch.support_subset_orderWeb` and
  `ContinuousOn.mono`.
- Proved Padé denominator nonvanishing on the order web by unpacking the
  `orderWeb` witness and contradicting positivity if `padeQ n d z = 0`.
- Proved Padé continuity on the order web using:
  - continuity of `padeP` by `unfold padeP; fun_prop`
  - `padeQ_continuous`
  - `ContinuousOn.div`
  - multiplication by `exp (-z)`
  - `ContinuousOn.norm`
- Propagated the repaired continuity boundary through:
  - `concreteRationalApproxToExp_of_padeR`
  - `PadeRConcreteNoEscapeInput`
  - `PadeRConcreteNoEscapeInput.concrete`
  - `padeRConcreteNoEscapeInput_of_realizesInfinityBranchGerms_of_zeroSupportExclusion`
  - `padeRConcreteNoEscapeInput_of_realizesInfinityBranchGerms`
  - `padeREhleBarrierInput_of_padeR`
- After the seam repair compiled, added the recommended exact-angle wrapper
  `padeR_local_plus_near_even_angle_of_neg_errorConst`.

## Result
- SUCCESS.
- The false field
  `cont : Continuous (fun z => ‖padeR n d z * exp (-z)‖)` was removed from the
  Padé-local seam and replaced by the honest theorem-local field
  `cont_orderWeb : ContinuousOn ... (orderWeb (padeR n d))`.
- Both required files verified with the requested commands:
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/OrderStars.lean`
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeOrderStars.lean`
- Additional targeted rebuilds succeeded:
  - `lake build OpenMath.OrderStars`
  - `lake build OpenMath.PadeOrderStars`

## Dead ends
- The ready Aristotle result `d3493ba8-e9e6-497c-a75f-14d6629fbb8a` was stale.
  Its summary proves `PadeAsymptotics.alternating_vandermonde_choose`, which is
  already live at `OpenMath/PadeAsymptotics.lean:305`. I did not transplant it,
  because the cycle target had moved and there was no clear theorem-local delta.
- During verification, an initial `lake env lean OpenMath/PadeOrderStars.lean`
  still saw the old `OrderStars` interface through stale imported `.olean`
  artifacts. This was resolved by targeted `lake build` of the edited modules,
  then rerunning the exact `lake env lean` commands.

## Discovery
- The generic no-escape contradiction seam only needs continuity on
  `orderWeb R`; branch support restriction is cleanly handled with
  `ContinuousOn.mono`.
- For Padé approximants, order-web membership is enough to rule out denominator
  zeros without any meromorphic machinery: the positive real witness in
  `orderWeb (padeR n d)` is already incompatible with `padeQ n d z = 0`.
- New Aristotle submissions for the two Padé seam lemmas were launched, but
  they remained queued when checked this cycle, so nothing was incorporated:
  - `2187c386-b574-467d-94ed-a0700415a9cb` — `QUEUED`
  - `bc7b6f57-feae-4e1f-bf6f-15a74cc8121a` — `QUEUED`
  - `d6efaec8-64ce-4af0-b5a5-8fcd30329962` — `QUEUED`
  - `087a64ec-772c-4985-ad78-f0c544bb5f7f` — `QUEUED`
  - `3f8e3682-d2cf-4d09-b9b4-b9d48b3752db` — `QUEUED`

## Suggested next approach
- Use the repaired `cont_orderWeb` seam to continue the live 355C/355D/355E
  feeder work, not to revisit global continuity.
- Next productive targets remain theorem-local:
  - concrete zero-support exclusion feeders
  - concrete nonzero coincidence/unit-level exclusion feeders
  - far-field sign-control feeders
- The new wrapper `padeR_local_plus_near_even_angle_of_neg_errorConst` now gives
  the exact-angle up-arrow cone input parallel to the existing down-arrow one.
