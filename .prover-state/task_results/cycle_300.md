# Cycle 300 Results

## Worked on
- `OpenMath/PadeOrderStars.lean`
- The cycle-300 zero-support audit below `PadeRConcreteNoEscapeInput`
- The first two feeder fields:
  - `zero_not_mem_down_support`
  - `zero_not_mem_up_support`

## Approach
- Re-read the live branch interface in `OpenMath/OrderStars.lean`:
  - `GlobalOrderArrowBranch`
  - `GlobalDownArrowBranch`
  - `GlobalUpArrowBranch`
  - `BranchTracksRayNearOrigin`
  - `RealizedDownArrowInfinityBranch`
  - `RealizedUpArrowInfinityBranch`
  - `mem_orderWeb_zero`
- Re-read the Padé seam in `OpenMath/PadeOrderStars.lean`:
  - `concreteRationalApproxToExp_of_padeR`
  - `PadeRConcreteNoEscapeInput`
  - `padeRConcreteNoEscapeInput_of_realizesInfinityBranchGerms`
- Audited the planner’s proposed countermodel:
  - start with a realized Padé branch
  - enlarge its support to `support ∪ {0}`
  - check connectedness, order-web support, local ray tracking, and escape to
    infinity one field at a time
- Formalized the audit directly in Lean by adding:
  - a Padé-side `0 ∈ orderWeb (padeR n d)` helper
  - realized down/up branch constructors with support enlarged by `{0}`
  - existence theorems showing a realized Padé branch with `0` in support can
    always be built from any realized Padé branch
- Added a small Padé-local seam split:
  - new structure `PadeRZeroSupportExclusionInput`
  - projection `PadeRConcreteNoEscapeInput.zeroSupportExclusion`
  - constructor
    `padeRConcreteNoEscapeInput_of_realizesInfinityBranchGerms_of_zeroSupportExclusion`

## Result
SUCCESS.

The truth audit succeeded: the current realized-branch interface does permit
adjoining `{0}` to the support of a realized Padé infinity branch while
preserving all recorded branch fields.

Concrete code changes:
- Added the audit theorems
  - `padeR_exists_realizedDownArrowInfinityBranch_with_zero_mem_support`
  - `padeR_exists_realizedUpArrowInfinityBranch_with_zero_mem_support`
- Added the Padé-local blocker bundle
  - `PadeRZeroSupportExclusionInput`
- Refined the seam by factoring a constructor through that bundle
  - `padeRConcreteNoEscapeInput_of_realizesInfinityBranchGerms_of_zeroSupportExclusion`

This isolates the blocker cleanly without changing `OpenMath/OrderStars.lean`.

## Dead ends
- I did not continue proof search for
  `zero_not_mem_down_support` / `zero_not_mem_up_support` after the audit.
  That would have been pushing a theorem target that the current interface does
  not support.
- I did not reopen the Ehle seam, local cone lemmas, or far-field sign lemmas,
  per the cycle strategy.

## Discovery
- The zero-support exclusion fields are not consequences of the current
  realized-branch interface.
- The obstruction is not merely informal; it now has explicit Padé-side Lean
  witnesses via the `support ∪ {0}` construction.
- The blocker is interface-level for the present branch notion, though it may
  still be recoverable from extra Padé-specific analytic hypotheses.

## Suggested next approach
- Treat zero-support exclusion as a separate Padé-local hypothesis surface,
  not as something derivable from `RealizesInfinityBranchGerms`.
- If future work wants to recover these fields honestly, it must add extra
  Padé-specific input beyond the current realized-branch records.
- After this audit, the next feeder work should target a genuinely new
  Padé-specific hypothesis rather than retrying the false interface-only route.

## Aristotle
- No new Aristotle batch was submitted this cycle.
- Reason:
  - cycle-300 required the truth audit first
  - the audit succeeded and showed the current zero-support target is blocked at
    the interface level
  - there was no honest surviving theorem target on the live shape to batch
    submit without fabricating a false premise

## Verification
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/PadeOrderStars.lean`
