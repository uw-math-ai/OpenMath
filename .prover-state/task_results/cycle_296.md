# Cycle 296 Results

## Worked on
- Re-triaged the planner-listed ready Aristotle outputs:
  - `f7242662-955d-4c1d-afb1-a2826b3cf0e0`
  - `29606db3-173f-47da-b9d3-c9ee9c93d5f3`
  - `5b2a90a3-277e-4453-ac7b-e2eda038f40a`
  - `5d037a95-6650-467a-bb22-14646750a2c3`
  - `40429ac6-365f-4c83-9ad0-340f9e8514a1`
  - `e15239fd-0c49-4e38-8dc0-6b8897919681`
  - `f03e9d7f-1fd1-491d-9bbf-fdd98f20476f`
  - `ecc9183a-2c68-450c-9d30-9ce9fc3b7409`
  - `6b148aa7-d736-4565-9130-ca53f8b96168`
- Built the Padé denominator-control infrastructure in live `OpenMath/Pade.lean`.
- Submitted a new asymptotic-first Aristotle batch under `.prover-state/aristotle/cycle_296/`.
- Investigated the generic leading coefficient/sign pattern for `padeR n d z * exp (-z)`.

## Approach
- Read the live direction API in `OpenMath/OrderStars.lean` and the current packaging seam in
  `OpenMath/PadeOrderStars.lean`.
- Applied the reject-by-default filter to the ready Aristotle bundles. Rejected every bundle
  that recreated `OpenMath/PadeOrderStars.lean`, redefined arrow/branch interfaces, or stayed
  in the already-closed support/witness layer.
- Wrote five scratch files matching the planner’s suggested decomposition:
  - `01_pade_defect_leading_coeff.lean`
  - `02_pade_expTaylor_to_exp_local_bound.lean`
  - `03_padeQ_nonzero_near_zero.lean`
  - `04_padeR_exists_downArrowDir.lean`
  - `05_padeR_down_branch_from_direction.lean`
- Verified the scratch files compile with `sorry`, submitted all five to Aristotle, waited
  30 minutes exactly once, and refreshed all five exactly once.
- Mined only the honest part of Aristotle `03`: continuity/open-neighborhood reasoning for
  the Padé denominator near `0`. Transplanted that reasoning into live code instead of using
  Aristotle’s rebuilt module.
- Used symbolic series checks to pin down the coefficient formula that the next proof should
  target.

## Result
FAILED — the cycle did not close the generic Padé local-direction theorem
`∃ θ, IsDownArrowDir (padeR n d) θ`.

Useful live progress was still made:
- added `padeQ_continuous`
- added `padeQ_nonzero_near_zero`
- added `padeQ_inv_norm_le_two_near_zero`

These are the denominator-control lemmas required before dividing by `padeQ` in the local
Padé asymptotic argument.

Cycle-296 Aristotle refresh results:
- `dc182a12...` (`01`) -> `COMPLETE_WITH_ERRORS`, rejected
- `e9c89bfa...` (`02`) -> `IN_PROGRESS` after the single allowed refresh
- `c14a5101...` (`03`) -> `COMPLETE`, rejected as a bundle but mined for the local proof idea
- `6ebe0669...` (`04`) -> `IN_PROGRESS` after the single allowed refresh
- `00735cff...` (`05`) -> `IN_PROGRESS` after the single allowed refresh

## Dead ends
- Every pre-existing ready Aristotle bundle was a dead end for this cycle’s target. The common
  failure mode was interface replacement:
  - rebuilding `OpenMath/PadeOrderStars.lean`
  - redefining `OrderArrowTerminationData`, `IsDownArrowDir`, `GlobalDownArrowBranch`, or
    `RealizedDownArrowInfinityBranch`
  - trying to solve branch/witness packaging instead of the Padé-local asymptotic seam
- Cycle-296 Aristotle `01` was also a dead end. It did not compute the coefficient at all; it
  simply defined the remainder to make the target identity tautological.

## Discovery
- Small-case symbolic expansion strongly suggests the exact generic leading term

```text
padeR n d z * exp (-z)
  = 1 - C_{n,d} z^(n+d+1) + O(z^(n+d+2))
```

with

```text
C_{n,d} = ((-1)^d) * n! d! / ((n+d)! (n+d+1)!)
```

- The sign appears to depend only on the parity of `d`.
  - `d` even -> `C_{n,d} > 0`, so `arrow_down_of_pos_errorConst` should apply at an even angle.
  - `d` odd -> `C_{n,d} < 0`, so `arrow_down_of_neg_errorConst_odd` should apply at an odd angle.
- No counterexample was found for `0 ≤ n,d ≤ 5`.
- The live proof obstruction has narrowed: local denominator control is now available, so the
  remaining missing mathematics is the genuine leading-coefficient proof plus the resulting
  `O(‖z‖^(n+d+2))` estimate.

## Suggested next approach
- Start from the new live denominator-control lemmas in `OpenMath/Pade.lean`.
- Prove the exact coefficient theorem for `padeR n d z * exp (-z) - 1`, not just divisibility.
- If proving it through `padeP - padeQ * expTaylor (n+d)` is cleaner, strengthen
  `pade_approximation_order` to retain the leading coefficient explicitly.
- After that, derive the local norm bound in the precise shape required by:
  - `arrow_down_of_pos_errorConst`
  - `arrow_down_of_neg_errorConst_odd`
- Only once `padeR_exists_downArrowDir` is live should the branch packaging lemma
  `padeR_exists_globalDownArrowBranch_of_downArrowsAtInfinity_pos_of_exists_downArrowDir`
  be reused.
