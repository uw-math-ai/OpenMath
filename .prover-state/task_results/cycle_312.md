# Cycle 312 Results

## Worked on
- Triaged the ready Aristotle bundles:
  - `.prover-state/aristotle_results/b778f09e-bfab-4acd-b80e-8373f64754b1`
  - `.prover-state/aristotle_results/d02eb7f9-be50-4521-b509-ee051d3f9888`
- Added honest explicit-sign local cone infrastructure on the live seam.
- Landed the Padé minus wrapper under the explicit cosine-sign hypothesis.

## Approach
- Rejected both pre-existing Aristotle bundles as direct patches:
  - `b778f09e...` reopened the non-live sign-extraction / wrapper seam.
  - `d02eb7f9...` rebuilt side-project Padé infrastructure and still carried a `sorry`.
- Added sorry-first skeletons for:
  - `OrderStars.local_minus_near_of_errorConst_cos_pos`
  - `OrderStars.local_plus_near_of_errorConst_cos_neg`
  - `PadeOrderStars.padeR_local_minus_near_of_errorConst_cos_pos`
  - `PadeOrderStars.padeR_local_plus_near_of_errorConst_cos_neg`
- Compiled the sorry-first state with:
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/OrderStars.lean`
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeOrderStars.lean`
- Submitted the mandated Aristotle batch:
  - `1c721556-f3bd-4c2c-b2d3-0326c9ed053e` generic minus lemma
  - `f263e639-f9f4-44bc-aba9-3b887cd953de` generic plus lemma
  - `6a55a267-c191-4568-9693-6209ede901f7` Padé minus wrapper
  - `e235e25f-8143-482e-bdbf-02f53a529719` Padé plus wrapper
  - `8418c228-9454-4df1-ad83-a77ab02d64a7` cone-margin helper
- Waited once for 30 minutes, refreshed once, and incorporated only live-compatible output.
- Proved the generic minus theorem manually by:
  - normalizing the Padé/error direction with `C / |C|`
  - choosing a cone aperture from continuity of `w ↦ w^(p+1)`
  - extracting a pointwise helper to keep the proof under the heartbeat ceiling
  - applying `main_minus_bound_of_re_pos`
- Removed the unfinished plus-side additions rather than leaving a live `sorry`.

## Result
SUCCESS for the minus-side explicit-sign seam:
- landed `OrderStars.local_minus_near_of_errorConst_cos_pos`
- landed `PadeOrderStars.padeR_local_minus_near_of_errorConst_cos_pos`

PARTIAL for the full cycle target:
- the plus-side explicit-sign companion was not landed this cycle
- a blocker issue was written to record the exact gap and next repair direction

## Dead ends
- The pre-existing Aristotle bundle `b778f09e...` depended on non-live sign-extraction lemmas and would have reopened the false wrapper seam.
- The pre-existing Aristotle bundle `d02eb7f9...` rebuilt Padé infrastructure in a side project and still had a `sorry`.
- Keeping the full minus proof in one public theorem hit the heartbeat ceiling; it only compiled after splitting out a private pointwise helper.
- The plus-side generic theorem was started but intentionally removed from the live files once it was clear it would not land cleanly this cycle without leaving a `sorry`.

## Discovery
- The explicit-sign minus cone theorem is viable on the live seam without any use of
  `IsDownArrowDir` / `IsUpArrowDir`.
- The `lake env lean` check on `PadeOrderStars.lean` only sees the new `OrderStars`
  declarations after rebuilding `OpenMath.OrderStars`; `lake build OpenMath.OrderStars`
  was needed before the wrapper file rechecked cleanly.
- The Aristotle wrapper jobs were useful:
  - `6a55a267-c191-4568-9693-6209ede901f7` matched the live minus wrapper proof shape
  - `e235e25f-8143-482e-bdbf-02f53a529719` matched the live plus wrapper proof shape, but the plus generic theorem itself was not landed
- The single refresh left the three `OrderStars` Aristotle jobs still in progress, so they were not incorporated.

## Suggested next approach
- Start from the landed minus-side helper and build the plus-side analogue with
  `main_plus_bound_of_re_neg`.
- After both explicit-sign feeders exist, weaken the downstream no-escape input seam to
  explicit sign-margin or one-sided wedge hypotheses instead of arrow-direction feeders.
- If the plus-side theorem again threatens the heartbeat budget, split it immediately into a public parameter-selection theorem and a private pointwise helper, mirroring the minus-side pattern.
