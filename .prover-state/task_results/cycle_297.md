# Cycle 297 Results

## Worked on
- Required Aristotle triage for the three ready result directories:
  - `.prover-state/aristotle_results/c14a5101-5b84-4ef5-8c34-43099a1d9cbc`
  - `.prover-state/aristotle_results/dc182a12-31a3-434d-8cc0-cfec70a0e6c1`
  - `.prover-state/aristotle_results/80975eb2-ede1-434c-b0e0-dd10ae7c3bc5`
- Live seam audit in:
  - `OpenMath/OrderStars.lean`
  - `OpenMath/PadeOrderStars.lean`
  - `plan.md`
- Local theorem/interface refinement in `OpenMath/PadeOrderStars.lean`
  around the concrete Ehle barrier seam.
- Blocker issue:
  `.prover-state/issues/pade_ehle_barrier_needs_concrete_ehle_input.md`

## Approach
- Re-read the live seam before editing, focusing on:
  - `RealizesInfinityBranchGerms`
  - `ConcreteRationalApproxToExp`
  - `concreteRationalApproxToExp_of_padeR`
  - `PadeREhleBarrierInput`
  - `ehle_barrier_nat_of_padeR`
- Audited the current downstream use rather than trusting older issue text.
- Confirmed that `thm_355D_of_padeR` and `thm_355E'_of_padeR` really use the
  full Padé-side bundle, but `ehle_barrier_nat_of_padeR` does not.
- Landed the smallest honest local refinement:
  - `PadeREhleBarrierNatInput`
  - `PadeREhleBarrierInput.toNatInput`
  - `PadeREhleBarrierNatInput.ehle_barrier_nat`
  - `ehle_barrier_nat_of_padeR_of_natInput`
- Rewired `PadeREhleBarrierInput.ehle_barrier_nat` and
  `ehle_barrier_nat_of_padeR` through the smaller theorem-local seam.

Aristotle triage:
- `c14a5101...`: inspected and rejected as already incorporated. Its
  `03_padeQ_nonzero_near_zero.lean` only reproduces the local denominator
  control already live in `OpenMath/Pade.lean`
  (`padeQ_continuous`, `padeQ_nonzero_near_zero`,
  `padeQ_inv_norm_le_two_near_zero`).
- `dc182a12...`: rejected. The returned “leading coefficient” file defines the
  remainder term tautologically by division, so it does not advance the live
  theorem.
- `80975eb2...`: rejected immediately. It rebuilds a parallel
  `OpenMath/PadeOrderStars.lean` and routes through a fake local
  `exists_isDownArrowDir_padeR` theorem instead of proving anything against the
  live seam.

## Result
SUCCESS — the cycle landed a real local interface refinement that isolates the
live theorem-local blocker below the order-star seam without reintroducing any
false statement.

Concrete Lean change:
- `OpenMath/PadeOrderStars.lean` now separates the actual Ehle-barrier
  dependency from the heavier 355D/355E' Padé wrapper:
  - `PadeREhleBarrierNatInput`
  - `PadeREhleBarrierInput.toNatInput`
  - `PadeREhleBarrierNatInput.ehle_barrier_nat`
  - `ehle_barrier_nat_of_padeR_of_natInput`

What this establishes:
- The concrete hypothesis still blocking a real `padeR` Ehle application is
  exactly `EhleBarrierInput data` together with the degree equalities.
- `RealizesInfinityBranchGerms (padeR n d) data` and
  `ConcreteRationalApproxToExp (padeR n d) data` are not the missing input for
  `ehle_barrier_nat_of_padeR` itself; they belong only to the sibling
  `thm_355D_of_padeR` / `thm_355E'_of_padeR` path.

Verification:
- `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/PadeOrderStars.lean`

Aristotle:
- No new cycle-297 Aristotle batch was submitted.
- After the theorem-shape audit, the live target closed by direct composition
  and interface refactoring; there was no honest unresolved local proof target
  left to batch-submit without manufacturing artificial Aristotle work.

## Dead ends
- Treating `PadeREhleBarrierInput` as the honest blocker for
  `ehle_barrier_nat_of_padeR` was too coarse: the theorem only uses the degree
  equalities and `EhleBarrierInput data`.
- Reusing the ready Aristotle bundles was not viable:
  - one was already mined into the live `Pade.lean` denominator-control lemmas,
  - one made the target tautological by redefining the remainder,
  - one rebuilt a fake local Padé order-star world.

## Discovery
- The first honest concrete theorem below the seam is not blocked on the Padé
  no-infinity package. It is blocked on the 355G-side correction-term package
  `EhleBarrierInput data`.
- The live dependency split is now explicit:
  - `PadeREhleBarrierNatInput` for the Ehle barrier wedge theorem,
  - `PadeREhleBarrierInput` for the sibling 355D/355E' wrappers.

## Suggested next approach
- Prove the concrete zero-side correction-term theorem needed for
  `EhleBarrierInput data`.
- Prove the pole-side analogue.
- Once both are available, add a direct Padé-side constructor for
  `PadeREhleBarrierNatInput n d data` rather than routing the Ehle barrier
  theorem through the heavier no-infinity bundle.
