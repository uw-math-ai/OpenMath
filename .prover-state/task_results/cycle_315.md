# Cycle 315 Results

## Worked on
- Required Aristotle triage for ready artifact:
  - `.prover-state/aristotle_results/1c721556-f3bd-4c2c-b2d3-0326c9ed053e`
- Live Padé bridge seam in `OpenMath/PadeOrderStars.lean`:
  - `PadeRDownArrowSignBridge`
  - `PadeRUpArrowSignBridge`
  - new narrowed support lemmas:
    - `padeR_nonneg_sign_of_downArrowDir`
    - `padeR_nonpos_sign_of_upArrowDir`
    - `PadeRDownArrowZeroCosExclusion`
    - `PadeRUpArrowZeroCosExclusion`
    - `padeR_downArrowSignBridge_of_zeroCosExclusion`
    - `padeR_upArrowSignBridge_of_zeroCosExclusion`
- Focused blocker write-up:
  - `.prover-state/issues/pade_strict_arrow_sign_bridge_reduces_to_zero_cos_exclusion.md`

## Approach
- Read `.prover-state/strategy.md`, then inspected the ready Aristotle artifact
  before touching the live seam.
- Confirmed the artifact was stale: standalone `OrderStars.lean`, swapped the
  project import for `import Mathlib`, reproved already-live material, and
  introduced unrelated `sorry`s.
- Read the live bridge seam and the surrounding Padé direction/local-sign
  theorems in `OpenMath/PadeOrderStars.lean` and the underlying norm-only arrow
  definitions in `OpenMath/OrderStars.lean`.
- Re-checked the existing zero-cosine blocker history instead of assuming the
  strict sign bridge was merely missing.
- Set up a sorry-first Aristotle batch on five focused scratch lemmas under
  `.prover-state/aristotle_inputs/cycle_315/`, compiled those scratch files,
  submitted them, waited once, then refreshed once.
- Proved the honest weakened live bridge by contradiction from the already-live
  explicit-sign cone feeders:
  - negative sign contradicts `IsDownArrowDir`
  - positive sign contradicts `IsUpArrowDir`
- Reduced the old strict bridge to explicit zero-cosine exclusion wrappers
  rather than faking a proof of strict sign.

## Result
- SUCCESS: rejected Aristotle result `1c721556-f3bd-4c2c-b2d3-0326c9ed053e`.
  It is not incorporable because it rebuilds a standalone `OrderStars.lean`
  with `import Mathlib`, reproves already-live
  `local_minus_near_of_errorConst_cos_pos`, and contains new unrelated
  `sorry`s.
- SUCCESS: `OpenMath/PadeOrderStars.lean` now contains honest weakened bridge
  lemmas:
  - `padeR_nonneg_sign_of_downArrowDir`
  - `padeR_nonpos_sign_of_upArrowDir`
- SUCCESS: the strict bridges are now factored through explicit remaining
  hypotheses:
  - `PadeRDownArrowZeroCosExclusion`
  - `PadeRUpArrowZeroCosExclusion`
  together with:
  - `padeR_downArrowSignBridge_of_zeroCosExclusion`
  - `padeR_upArrowSignBridge_of_zeroCosExclusion`
- BLOCKED: `PadeRDownArrowSignBridge` and `PadeRUpArrowSignBridge` themselves
  were **not** closed.
- The exact minimal missing helper is now explicit:
  - prove zero-cosine exact-ray exclusion for Padé down arrows
  - prove zero-cosine exact-ray exclusion for Padé up arrows
  Equivalently, show that the product
  `padePhiErrorConst n d * Real.cos ((↑(n + d) + 1) * θ)` cannot vanish at an
  exact-ray `IsDownArrowDir` / `IsUpArrowDir`.
- Existing forward-Euler / `padeR 1 0` history suggests that this zero-cosine
  exclusion target may itself be false, so the downstream strict bridge
  interface may need to be weakened rather than proved.

## Dead ends
- Did not transplant any code from Aristotle result `1c721556...`; it was a
  sandbox rebuild with interface drift and new `sorry`s.
- Did not attempt the already-rejected inverse discrete-angle classification
  route `IsDownArrowDir` / `IsUpArrowDir` `→ exp (I * (p + 1) * θ) = ±1`.
- Did not try to fake strict sign from the weakened nonstrict bridge.
- The new Aristotle job `fab0de81-e592-49ee-972b-3654782c3ac2` completed, but
  its artifact redefined `rayConeNearOrigin` with a different angle-interval
  representation, so it was not incorporable.
- The new Aristotle jobs
  - `49336306-753e-4b23-8fb5-92c498428c1a`
  - `e759ed15-f94d-46fe-a94d-bdbff9f74fb2`
  returned wrapper proofs in local opaque rebuilds of `OpenMath.PadeOrderStars`;
  the proof ideas were trivial and already implemented manually in the live
  file, so nothing was transplanted.
- The new Aristotle jobs
  - `668a42b6-6e2d-4a6b-b04c-4e28a867ec23`
  - `782300a6-e562-4e0a-b381-a09bcfc618a2`
  were still `IN_PROGRESS` at the single refresh and were not needed to finish
  the cycle’s live narrowing work.

## Discovery
- The live strict bridge no longer hides behind a vague “classification” gap.
  After the cycle-315 refactor, it is exactly the zero-sign boundary case.
- The honest theorem shape currently available from the live explicit-sign
  feeders is nonstrict:
  - down arrow implies nonnegative leading sign
  - up arrow implies nonpositive leading sign
- This confirms that the remaining seam is not “recover the 355B families”
  but “exclude zero-cosine exact-ray arrows”, which is a materially sharper
  target for the planner.

## Suggested next approach
- Decide explicitly whether the downstream strict bridge interface is still the
  right target.
- If yes, attack only the zero-cosine exact-ray exclusion theorem-local input:
  - `PadeRDownArrowZeroCosExclusion`
  - `PadeRUpArrowZeroCosExclusion`
- Before spending another cycle on that, test the forward-Euler / `padeR 1 0`
  zero-cosine case formally; if it really is an exact-ray down-arrow at
  `θ = π / 4`, then the strict bridge is false and the seam must be weakened.
- Verification run this cycle:
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeOrderStars.lean`
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.PadeOrderStars`
