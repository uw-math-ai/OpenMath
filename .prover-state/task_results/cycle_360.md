# Cycle 360 Results

## Worked on
- Mandatory Aristotle triage for bundle `7edd756f-0937-4f2a-a239-5e78c0c1cd90`.
- Live audit of the repaired 355C/355D/355E and 355G order-star / Padé chain.
- Reconciliation of `plan.md` to the actual live theorem state.

## Approach
- Read `.prover-state/strategy.md` and the stale 355C/355D/355E section of `plan.md`.
- Re-read the live theorem blocks in:
  - `OpenMath/OrderStars.lean` around `noArrowsEscapeToInfinity_of_concreteRationalApprox`, `thm_355D_of_concreteRationalApprox`, and `thm_355E'_of_concreteRationalApprox`
  - `OpenMath/PadeOrderStars.lean` around `ehleBarrierInput_of_padeR_aStable`, `padeREhleBarrierNatInput_of_padeR_aStable`, and `ehle_barrier_nat_of_padeR`
- Triaged the Aristotle bundle by reading:
  - `PadeOrderStars_aristotle/ARISTOTLE_SUMMARY.md`
  - `PadeOrderStars_aristotle/PadeOrderStars.lean`
  - tarball contents including the bundled stub `PadeOrderStars_aristotle/OpenMath/OrderStars.lean`
- Verified the live files compile:
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/OrderStars.lean`
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeOrderStars.lean`
- Verified the corresponding module builds:
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.OrderStars`
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.PadeOrderStars`
- Checked the exact next theorem target against `../butcher_exp_1/OpenMath/extraction/formalization_data/entities/thm_358A.json` because this checkout does not contain the extraction tree.

## Result
- SUCCESS: rejected Aristotle bundle `7edd756f-0937-4f2a-a239-5e78c0c1cd90` with no harvested helper.
  - Its summary targets `oddDownArrowRadiusPhaseFixedRadiusSlice_atMostOne_zero_of_neg_errorConst`, which is already closed in the live repo.
  - It packages a much smaller standalone `PadeOrderStars.lean` plus fake local dependency files `OpenMath/Pade.lean`, `OpenMath/PadeAsymptotics.lean`, and `OpenMath/OrderStars.lean`.
  - The bundled stub `OpenMath/OrderStars.lean` contains new `sorry`s, so the run is not admissible as a live patch.
- SUCCESS: the stale 355C/355D/355E plan item was already closed in the live source.
  - `OpenMath/OrderStars.lean` already contains `noArrowsEscapeToInfinity_of_concreteRationalApprox`, `thm_355D_of_concreteRationalApprox`, and `thm_355E'_of_concreteRationalApprox`.
  - `OpenMath/PadeOrderStars.lean` already contains `ehleBarrierInput_of_padeR_aStable`, `padeREhleBarrierNatInput_of_padeR_aStable`, and `ehle_barrier_nat_of_padeR`.
- SUCCESS: updated `plan.md` to:
  - mark the 355C/355D/355E package complete
  - add the repaired 355G / Ehle-barrier result explicitly
  - remove the stale `NoArrowsEscapeToInfinity` next target
  - set the exact next theorem to `thm:358A`
- SUCCESS: no fresh blocker was found, so no new issue file was needed this cycle.

## Dead ends
- The current checkout does not include `extraction/formalization_data/entities/thm_358A.json`, so the exact 358A statement could not be re-read in-tree.
- I did not use the neighboring extraction copy as proof infrastructure; it was used only to name the next theorem accurately in `plan.md`.

## Discovery
- The live no-escape seam is no longer an abstract topology placeholder: `noArrowsEscapeToInfinity_of_concreteRationalApprox` already closes the needed boundary for the 355D/355E wrappers.
- The repaired Padé-side 355G/Ehle seam is also live: `ehle_barrier_nat_of_padeR` depends only on the theorem-local `PadeREhleBarrierNatInput` built from `ehleBarrierInput_of_padeR_aStable`.
- The next honest frontier after reconciliation is `thm:358A`, whose extracted statement is the algebraic-stability characterization of collocation methods via zeros of `P_s^* - θ P_{s-1}^*` with `θ ≥ 0`.

## Suggested next approach
- Start `thm:358A` directly from the collocation/algebraic-stability statement, not from the already-landed BN-stability corollaries.
- Reuse the existing shifted-Legendre and collocation infrastructure when choosing the theorem-local seam.
- Keep the next cycle focused on 358A unless a new live mismatch appears in the current source.
