# Cycle 289 Results

## Worked on
The 355G / Ehle-barrier seam in `OpenMath/OrderStars.lean`, with the specific
goal of separating the Ehle-barrier correction terms from the explicit 355E
endpoint counts.

## Approach
Read `.prover-state/strategy.md` and re-audited the required declarations and
use-sites:
- `thm_355E`
- `degrees_eq_zero_of_exact_endpoint_counts_and_aStablePadeApprox`
- `degrees_eq_zero_of_thm_355E_and_aStablePadeApprox`
- `IsAStablePadeApprox`
- `ehle_barrier`
- `ehle_barrier_nat`
- `thm_355E'_of_padeR`

Confirmed again that all live consumers are local to
`OpenMath/OrderStars.lean` / `OpenMath/PadeOrderStars.lean`, so there was no
real downstream compatibility constraint.

Implemented the interface repair by:
- marking `IsAStablePadeApprox` as a legacy / quarantined boundary
- introducing `EhleBarrierInput` with separate zero-side and pole-side
  correction terms encoded existentially
- migrating `ehle_barrier` and `ehle_barrier_nat` to `EhleBarrierInput`
- leaving the mismatch theorems in place to record why the legacy interface
  still cannot be bridged honestly from `thm_355E`

Aristotle status this cycle:
- No submissions and no harvest. The planner explicitly said not to submit a
  new batch because the blocker was interface surgery, not a local proof-search
  gap.

## Result
SUCCESS: the live Ehle-barrier boundary is now statement-correct.

- `thm_355E` still exposes exact endpoint counts in
  `OrderArrowTerminationData`.
- `ehle_barrier` and `ehle_barrier_nat` now depend on separate correction-term
  hypotheses via `EhleBarrierInput`.
- `IsAStablePadeApprox` remains only as the legacy mismatched boundary, and the
  existing theorems showing its incompatibility with 355E remain available.

Verification:
- `lake env lean OpenMath/OrderStars.lean`
- `lake env lean OpenMath/PadeOrderStars.lean`

## Dead ends
- A first pass with a `Type`-valued replacement structure made the
  `ehle_barrier_nat` existential awkward because the theorem needs a
  proposition-valued hypothesis.
- A second pass with a `Prop`-valued structure and raw `ℕ` fields failed
  because Lean does not generate projections of non-proof fields from a
  `Prop`-valued structure.
- Encoding the correction terms existentially inside `EhleBarrierInput`
  resolved the Lean representation issue without reusing the 355E endpoint
  counts.

## Discovery
- The honest downstream boundary is now explicit in code:
  - 355E gives exact endpoint counts.
  - 355G / Ehle needs separate correction terms whose vanishing comes from
    A-stability/topology.
  - No current theorem constructs those correction terms for `padeR`.
- Because there are no downstream consumers outside the local order-star files,
  the repaired boundary could replace the live `ehle_barrier` interface
  directly.

## Suggested next approach
Prove concrete Padé/A-stability/topology lemmas that furnish the two
`EhleBarrierInput` correction-term hypotheses, then connect those repaired
inputs to `ehle_barrier_nat`. Do not add any wrapper claiming that
`thm_355E'_of_padeR` alone feeds the Ehle barrier.
