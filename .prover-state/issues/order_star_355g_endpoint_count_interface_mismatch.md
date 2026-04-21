# Issue: 355G interface reuses 355E endpoint counts as vanishing correction terms

## Blocker
The direct 355E-to-355G bridge is still missing, but the live Ehle-barrier
boundary has now been repaired.

- `thm_355E` / `thm_355E'` conclude
  `downArrowsAtZeros = numeratorDegree` and
  `upArrowsAtPoles = denominatorDegree`.
- The old `IsAStablePadeApprox.arrows_zero` and `.arrows_poles` fields instead
  require those same endpoint-count coordinates to be `0`, so that structure
  remains only as a legacy mismatch witness.
- `ehle_barrier` / `ehle_barrier_nat` now use `EhleBarrierInput`, whose
  zero-side and pole-side correction terms are separate existential natural
  numbers, not `data.downArrowsAtZeros` or `data.upArrowsAtPoles`.

What is still missing is a concrete theorem that produces those repaired
correction-term inputs from Padé/A-stability/topology data. An honest bridge
from `thm_355E'_of_padeR` into the legacy interface would still force
`numeratorDegree = 0` and `denominatorDegree = 0`, so the old packaging must
remain quarantined.

## Context
- Live seam audited this cycle:
  - `OpenMath/OrderStars.lean`
    - `thm_355E`
    - `thm_355E'`
    - `thm_355E'_of_concreteRationalApprox`
    - `IsAStablePadeApprox` (legacy quarantine)
    - `degrees_eq_zero_of_exact_endpoint_counts_and_aStablePadeApprox`
    - `degrees_eq_zero_of_thm_355E_and_aStablePadeApprox`
    - `EhleBarrierInput`
    - `ehle_barrier`
    - `ehle_barrier_nat`
  - `OpenMath/PadeOrderStars.lean`
    - `thm_355E'_of_padeR`
- Use-site audit still shows no downstream consumers outside
  `OrderStars.lean` / `PadeOrderStars.lean`, so the repaired boundary did not
  need a compatibility wrapper.
- `thm_355E'_of_padeR` continues to provide endpoint counts only; it does not
  yet supply the separate correction-term vanishing hypotheses needed by
  `EhleBarrierInput`.

## What was tried
- Re-audited the exact 355E endpoint theorem chain and the local 355G
  use-sites before editing.
- Kept `IsAStablePadeApprox` in place only as the legacy mismatched interface
  used by the existing collapse-to-degree-zero theorems.
- Introduced `EhleBarrierInput` so the live Ehle-barrier boundary now carries
  separate zero-side and pole-side correction terms.
- Migrated `ehle_barrier` and `ehle_barrier_nat` to the repaired boundary.
- Recompiled `OpenMath/OrderStars.lean` and `OpenMath/PadeOrderStars.lean`.

## Possible solutions
- Prove a concrete A-stability/topology lemma that supplies the zero-side
  `EhleBarrierInput` correction term for `padeR`.
- Prove the analogous pole-side correction-term lemma.
- Once both repaired inputs are available, derive a statement-correct bridge
  from concrete Padé data to `ehle_barrier_nat`.
- Keep the legacy mismatch theorems in place until that bridge exists, so the
  old endpoint-count interface cannot silently re-enter the live theorem path.
