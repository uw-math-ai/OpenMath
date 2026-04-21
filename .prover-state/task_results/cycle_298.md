# Cycle 298 Results

## Worked on
- `OpenMath/PadeOrderStars.lean`
- The live 355G/Ehle correction-term seam below `ehle_barrier_nat_of_padeR`
- Concrete theorems attacked:
  - `padeR_zero_side_correction_of_aStable`
  - `padeR_pole_side_correction_of_aStable`
  - `ehleBarrierInput_of_padeR_aStable`
  - `padeREhleBarrierNatInput_of_padeR_aStable`
  - `ehle_barrier_nat_of_padeR`

## Approach
- Re-read `.prover-state/strategy.md` and the live seam in
  `OpenMath/OrderStars.lean` / `OpenMath/PadeOrderStars.lean`.
- Verified the baseline target file with
  `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/PadeOrderStars.lean`.
- Followed sorry-first via a focused Aristotle batch in
  `.prover-state/aristotle/cycle_298/`:
  - `01_padeR_zero_side_correction_of_aStable.lean`
  - `02_padeR_pole_side_correction_of_aStable.lean`
  - `03_ehleBarrierInput_of_padeR_aStable.lean`
  - `04_padeREhleBarrierNatInput_of_padeR_aStable.lean`
  - `05_ehle_barrier_nat_of_padeR.lean`
- Compiled each Aristotle scaffold locally with `lake env lean`.
- Submitted all five jobs, waited once for 30 minutes via `sleep 1800`, then did
  a single refresh.
- Proved the live seam manually in `OpenMath/PadeOrderStars.lean` by using the
  already-existing `IsAStablePadeApprox` fields:
  - `sector_bound_n` + `arrows_zero` for the zero-side correction witness
  - `sector_bound_d` + `arrows_poles` for the pole-side correction witness
- Packaged those two witnesses into `EhleBarrierInput data`, then into
  `PadeREhleBarrierNatInput n d data`, and rewired the public Padé-side wedge
  theorem through the minimal seam.

Aristotle submissions:
- `b7db0077-f5d3-409e-9ddd-5e6dba014a9b`
- `2f3e45cf-57ea-4a50-9073-e7a2f470d8fc`
- `2688da21-bad8-4e4c-830b-34de93f6a025`
- `122fc9c4-2d21-42f2-bc76-909426c2f4fe`
- `ff676ad2-ae0d-4344-9987-68951f5dc7c4`

## Result
SUCCESS.

- The zero-side field moved: `padeR_zero_side_correction_of_aStable` is live and
  sorry-free.
- The pole-side field moved: `padeR_pole_side_correction_of_aStable` is live and
  sorry-free.
- The combined constructor is live:
  `ehleBarrierInput_of_padeR_aStable`.
- The direct minimal-seam constructor is live:
  `padeREhleBarrierNatInput_of_padeR_aStable`.
- `ehle_barrier_nat_of_padeR` now runs through the small seam instead of the
  heavier full-input bundle.
- The old full-input route was preserved explicitly as
  `ehle_barrier_nat_of_padeR_of_input`.

Verification runs:
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/PadeOrderStars.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake build OpenMath.PadeOrderStars`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean .prover-state/aristotle/cycle_298/01_padeR_zero_side_correction_of_aStable.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean .prover-state/aristotle/cycle_298/02_padeR_pole_side_correction_of_aStable.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean .prover-state/aristotle/cycle_298/03_ehleBarrierInput_of_padeR_aStable.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean .prover-state/aristotle/cycle_298/04_padeREhleBarrierNatInput_of_padeR_aStable.lean`
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean .prover-state/aristotle/cycle_298/05_ehle_barrier_nat_of_padeR.lean`

Aristotle result statuses after the one allowed refresh:
- `b7db0077-f5d3-409e-9ddd-5e6dba014a9b`: `COMPLETE`
- `2f3e45cf-57ea-4a50-9073-e7a2f470d8fc`: `COMPLETE`
- `2688da21-bad8-4e4c-830b-34de93f6a025`: `COMPLETE_WITH_ERRORS`
- `122fc9c4-2d21-42f2-bc76-909426c2f4fe`: `COMPLETE_WITH_ERRORS`
- `ff676ad2-ae0d-4344-9987-68951f5dc7c4`: `COMPLETE_WITH_ERRORS`

## Dead ends
- Aristotle did not yield any live-compatible proof to incorporate.
- The two `COMPLETE` jobs fabricated non-existent `IsAStablePadeApprox` fields
  such as `degree_le`, `num_le_den`, or `den_le_num_add_two`.
- The three `COMPLETE_WITH_ERRORS` jobs rebuilt parallel fake `OpenMath`
  modules and changed the meaning of the seam interfaces, so their outputs were
  rejected.
- Because the live proofs were already short compositions of existing fields,
  there was no reason to replace the manual proofs with fabricated Aristotle
  code.

## Discovery
- The correction-term seam was not blocked on new topology or no-infinity
  infrastructure.
- The existing legacy interface `IsAStablePadeApprox data` already contained
  exactly the two ingredients needed to build the repaired seam honestly:
  sector-count inequalities and vanishing correction terms.
- That was enough to lower the live theorem-local input for
  `ehle_barrier_nat_of_padeR` to the minimal `PadeREhleBarrierNatInput` path
  without touching `OpenMath/OrderStars.lean`.

## Suggested next approach
- Audit downstream call sites, if any, and switch them to the new lighter
  `ehle_barrier_nat_of_padeR` theorem or the explicit
  `padeREhleBarrierNatInput_of_padeR_aStable` constructor.
- If the project still wants a direct bridge from the heavier
  `PadeREhleBarrierInput`, keep using `ehle_barrier_nat_of_padeR_of_input`; the
  Ehle wedge theorem itself no longer needs the no-infinity payload.
