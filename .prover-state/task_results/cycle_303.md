# Cycle 303 Results

## Worked on
- The live Padé/order-star seam in `OpenMath/PadeOrderStars.lean`
- The dependency chain through:
  - `padeR_no_nonzero_eq_exp_on_orderWeb`
  - `thm_355D_of_padeR`
  - `thm_355E'_of_padeR`
  - `PadeRConcreteNoEscapeInput`
  - `PadeREhleBarrierInput`

## Approach
- Read the three planner-specified blocker notes first.
- Audited the live code in `OpenMath/PadeOrderStars.lean` and
  `OpenMath/OrderStars.lean` before editing.
- Verified that the false fully uniform coincidence-exclusion theorem is no
  longer the live boundary; the remaining mismatch was that `PadeOrderStars`
  still threaded the stronger derived statement `no_nonzero_eq_exp` as an input.
- Repaired the interface by replacing that primitive Padé-local input with the
  smaller primitive `no_nonzero_unit_points_on_orderWeb`, matching the existing
  `OrderStars` contradiction seam.
- Kept exact-coincidence exclusion only as a derived helper theorem:
  `PadeRConcreteNoEscapeInput.no_nonzero_eq_exp`.
- Verified:
  - `lake env lean OpenMath/PadeOrderStars.lean`
  - `lake env lean OpenMath/OrderStars.lean`
- Set up five sorry-first Aristotle scratch files for the next feeder theorems:
  - `.prover-state/aristotle/cycle_303/padeR_no_nonzero_unit_points_on_orderWeb.lean`
  - `.prover-state/aristotle/cycle_303/padeR_local_minus_near_down.lean`
  - `.prover-state/aristotle/cycle_303/padeR_local_plus_near_up.lean`
  - `.prover-state/aristotle/cycle_303/padeR_far_plus_on_orderWeb.lean`
  - `.prover-state/aristotle/cycle_303/padeR_far_minus_on_orderWeb.lean`
- Verified each Aristotle scratch file compiles with only the expected
  `declaration uses sorry` warning.
- Submitted all five scratch files to Aristotle in batch:
  - `a43ef8ad-0287-465f-8571-8d96f644745d`
  - `c91e5315-67f7-4c21-a19a-2c0f7d4c952c`
  - `0bb82e67-8c95-4d67-a17e-4d9a4a669414`
  - `f5fce893-2d9c-4ea5-b1eb-fd61f4b47d8d`
  - `a7da198e-c81f-4722-8819-aa113ae19781`
- Initiated the mandated `sleep 1800` wait and then performed one status
  refresh; all five Aristotle jobs were still `QUEUED`, so there was nothing to
  incorporate back into live code this cycle.

## Result
SUCCESS — the live Padé/order-star seam is now narrower and more honest.

`OpenMath/PadeOrderStars.lean` now carries the primitive unit-level exclusion on
`orderWeb (padeR n d)` instead of treating the stronger exact-coincidence claim
as a primitive input. The exact-coincidence statement survives only as a
derived helper theorem.

No further live theorem below that seam was proved this cycle. The first status
check after the Aristotle submissions still showed every project queued.

## Dead ends
- Did not try to resurrect the false fully uniform theorem
  `∀ n d z, z ≠ 0 → z ∈ orderWeb (padeR n d) → padeR n d z = exp z → False`.
- Did not target zero-support exclusion as a live theorem:
  the cycle-300 branch-adjoining lemmas show it is not forced by the current
  realized-branch interface.
- Looked for a generic continuity-only proof of the local cone-sign fields in
  `OpenMath/OrderStars.lean`; the live cone lemmas instead require a stronger
  leading-term error estimate, so there was no quick further narrowing there.

## Discovery
- The actual live theorem boundary after cycle 303 is:
  `no_nonzero_unit_points_on_orderWeb` + local/far sign-control fields.
  The old exact-coincidence theorem is now downstream of that boundary.
- `thm_355D_of_padeR` and `thm_355E'_of_padeR` were already correctly phrased in
  terms of `ConcreteRationalApproxToExp`; the misleading part was only the
  Padé-local feeder bundle.
- The next plausible route is not a generic arbitrary-`R` argument. It is a
  Padé-specific leading-term analysis that can feed the existing
  `OrderStars.local_*_of_*_errorConst` lemmas.

## Suggested next approach
- Derive a Padé-specific leading-term remainder theorem for
  `padeR n d z * exp (-z)` using the existing `OpenMath/Pade.lean` approximation
  machinery and `padePhiErrorConst`.
- Use that remainder theorem to instantiate the existing local cone lemmas in
  `OpenMath/OrderStars.lean`.
- Keep the unit-level exclusion statement local and restricted until there is an
  actual proof for a concrete Padé subfamily; do not promote the exploratory
  `n + d > 0` Aristotle candidate into live code without evidence.
