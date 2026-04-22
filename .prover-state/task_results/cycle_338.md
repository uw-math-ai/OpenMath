# Cycle 338 Results

## Worked on
- Ready Aristotle bundles, in the required order:
  - `6dba509e-6abd-4e5c-9437-2888331c8dc8`
  - `14cc6695-5dab-45fc-85a7-0b6f47b01afa`
  - `b5dd84a3-89d9-485f-b392-6b6728970055`
- `OpenMath/PadeOrderStars.lean`
- New helper theorem:
  `padeR_odd_downArrowConnectedRadiusPhaseZeroSet_of_neg_errorConst`
- Refactored wrapper theorem:
  `padeR_odd_downArrowSameComponentRadiusPhaseBound_of_neg_errorConst`
- Fresh cycle-338 Aristotle batch:
  - `0df8b271-bf18-489a-b2ac-49e6f2c6f80b`
  - `c0ce4dc0-d071-4125-abea-6406ab9122ae`
  - `ffc04fff-8b40-4c8f-8a7c-ad24a13babef`
  - `08c58b2a-6c7c-4071-8b47-8693ddcf2c29`
  - `187b14fd-01fc-42c2-950f-b7e1cc0a85bb`

## Approach
- Read `.prover-state/strategy.md` and stayed inside the odd-only local block.
- Inspected the three ready Aristotle bundles before editing and applied the
  strict transplant filter.
- Rejected all three ready bundles:
  - `6dba509e...` assumes the false shortcut that the odd central ray itself is
    in the order web for small radius and rebuilds around its own local proof
    surface.
  - `14cc6695...` proves a stale fixed-strip / positive-real-axis zero-set on a
    rebuilt sidecar interface, not the live helper.
  - `b5dd84a3...` solves a toy support wrapper by redefining the support
    structure instead of proving against the live file.
- Refactored the live theorem by introducing one new theorem-local helper:
  `padeR_odd_downArrowConnectedRadiusPhaseZeroSet_of_neg_errorConst`.
  This isolates the remaining content as:
  - a connected subset `Z ⊆ ℝ × ℝ`,
  - satisfying the actual odd radius-phase geometry `s ∈ [-r, r]`,
  - lying in the zero set of the odd-strip imaginary part with `Re > 0`,
  - and projecting onto all radii in `Icc (0 : ℝ) δ`.
- Proved the old live theorem from that helper by:
  - mapping `Z` into `ℂ`,
  - using connectedness of the image,
  - taking the base point to be `0`,
  - and showing the image lies in `connectedComponentIn (orderWeb (padeR n d)) 0`.
- Verified the refactor with
  `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeOrderStars.lean`.
- Created five focused Aristotle inputs under
  `.prover-state/aristotle_inputs/cycle_338/`, submitted them, waited once for
  30 minutes via `sleep 1800`, and did the single allowed refresh.
- Inspected the three completed cycle-338 Aristotle outputs after the refresh.

## Result
- SUCCESS (reduction): `OpenMath/PadeOrderStars.lean` still compiles, and the
  single remaining `sorry` is now the more explicit helper
  `padeR_odd_downArrowConnectedRadiusPhaseZeroSet_of_neg_errorConst`.
- SUCCESS (proof movement): the former live theorem
  `padeR_odd_downArrowSameComponentRadiusPhaseBound_of_neg_errorConst`
  is now proved from the new helper.
- Aristotle refresh outcome after the single wait:
  - `0df8b271...` (`01_oddDownArrowConnectedRadiusPhaseZeroSet.lean`):
    `IN_PROGRESS` at 14%
  - `187b14fd...` (`05_oddDownArrowConnectedRadiusPhaseSupport.lean`):
    `IN_PROGRESS` at 15%
  - `c0ce4dc0...` (`02_oddDownArrowSameComponentRadiusPhaseBound.lean`):
    `COMPLETE_WITH_ERRORS`, rejected
  - `ffc04fff...` (`03_oddDownArrowSameComponentRadiusPhaseBound_atZero.lean`):
    `COMPLETE_WITH_ERRORS`, rejected
  - `08c58b2a...` (`04_oddDownArrowConnectedRayConeSupport.lean`):
    `COMPLETE_WITH_ERRORS`, rejected
- Reasons the completed cycle-338 results were rejected:
  - `c0ce4dc0...` creates its own `OpenMath/PadeOrderStars.lean` with
    `orderWeb := Set.univ` and `padePhiErrorConst := -1`.
  - `ffc04fff...` creates a stub theorem
    `orderWeb_connected_component_sector` in a rebuilt support module instead of
    proving the live helper.
  - `08c58b2a...` imports `Mathlib`, replaces the live support structure with a
    placeholder sector record, and ignores the real Padé/order-web geometry.

## Dead ends
- No ready Aristotle bundle contained a live-safe fragment that could be
  transplanted into the current file.
- The three completed cycle-338 Aristotle jobs again solved the goals only by
  recreating toy interfaces or introducing new stub infrastructure, so nothing
  was incorporable.
- The two still-running jobs were not usable this cycle because the strategy
  allows only one post-wait refresh.

## Discovery
- The proof now reduces cleanly to one exact topological statement:
  build a connected radius-phase zero set whose first-coordinate projection is
  the whole interval `Icc (0 : ℝ) δ`.
- Once that helper exists, the rest of the odd continuation is already wired:
  the image of that connected zero set in `ℂ` gives a connected subset of the
  live order web containing `0`, and therefore all resulting witnesses lie in
  one fixed connected component.
- So the remaining blocker is not any additional endpoint-sign estimate. It is
  exactly the rectangle-crossing / connected-zero-set step for the odd-strip
  imaginary-part function.

## Suggested next approach
- Work directly on
  `padeR_odd_downArrowConnectedRadiusPhaseZeroSet_of_neg_errorConst`.
- Formalize a theorem-local rectangle zero-set crossing lemma for the continuous
  odd-strip imaginary-part function on
  `Icc (0 : ℝ) δ ×ˢ Icc (-r) r`-style data, or an equivalent connected-component
  argument that yields a connected zero subset with full radius projection.
- At the start of the next cycle, check whether the still-running cycle-338
  Aristotle jobs `0df8b271...` or `187b14fd...` finished with anything
  transplantable, but keep the same strict reject filter.
