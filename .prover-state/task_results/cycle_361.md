# Cycle 361 Results

## Worked on
- Theorem 358A only, in a new live file:
  - `OpenMath/CollocationAlgStability.lean`
- Exact theorem-local scaffold for the collocation/algebraic-stability
  characterization via zeros of `P_s^* - θ P_{s-1}^*`.

## Approach
- Read `.prover-state/strategy.md` and the live infrastructure in:
  - `OpenMath/StiffEquations.lean`
  - `OpenMath/Legendre.lean`
  - `OpenMath/Collocation.lean`
- Re-read the extracted theorem metadata from:
  - `../butcher_exp_1/OpenMath/extraction/formalization_data/entities/thm_358A.json`
- Created `OpenMath/CollocationAlgStability.lean` with a polynomial-first,
  sorry-first scaffold:
  - `shiftedLegendrePoly`
  - `algStabilityBoundaryPoly`
  - `IsCollocation`
  - `HasAlgStabilityBoundaryNodes`
  - `nodePoly_polyMoment_orthogonal_of_algStable`
  - `nodePoly_interval_orthogonal_of_algStable`
  - `orthogonal_degree_eq_boundaryPoly`
  - `boundary_theta_nonneg_of_algStable`
  - `thm_358A_only_if`
  - `thm_358A_if`
  - `thm_358A`
- Verified the new module compiles:
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/CollocationAlgStability.lean`
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.CollocationAlgStability`
- Submitted one focused 5-job Aristotle batch on the live file.
- Slept for 30 minutes, then did one status check on all 5 projects.

## Result
- SUCCESS: landed the live 358A scaffold in `OpenMath/CollocationAlgStability.lean`.
- SUCCESS: the scaffold compiles with the required `lake env lean` and
  `lake build` commands.
- BLOCKED: no Aristotle result was ready to harvest after the mandated wait.
  The post-wait statuses were:
  - `314a6a62-23a9-4572-a6b4-be80da8c324c`: `IN_PROGRESS` (orthogonality bridge)
  - `fabcddf1-d2e4-46d2-b0b9-90ed47ed1cc8`: `IN_PROGRESS` (Legendre characterization)
  - `ffe56f65-fcc6-4d9f-9040-b47ac4158f52`: `IN_PROGRESS` (θ-sign lemma)
  - `995901fc-98bc-4885-a95e-c5dc63a0cabb`: `IN_PROGRESS` (converse direction)
  - `1fceebe5-19ab-472e-8616-8c14bddcf6ac`: `IN_PROGRESS` (final wrapper)
- Wrote a focused blocker issue:
  - `.prover-state/issues/cycle_361_358A_matrix_to_polynomial_bridge.md`

## Dead ends
- There was nothing safe to incorporate from Aristotle this cycle because all
  five jobs were still running at the single allowed post-wait check.
- The current repo still lacks the transformed-matrix bridge that turns
  `IsAlgStable` plus collocation assumptions into vanishing moments for
  `nodePoly t`.

## Discovery
- The cleanest live seam is indeed theorem-local and polynomial-first.
  Reusing `nodePoly`, `polyMomentN`, and the interval-integral uniqueness
  pattern from `gaussLegendreNodes_of_B_double` gives a coherent 358A scaffold
  without inventing a large new API.
- The exact first blocker is now explicit in the codebase:
  `ButcherTableau.nodePoly_polyMoment_orthogonal_of_algStable`.

## Suggested next approach
- Resume from `OpenMath/CollocationAlgStability.lean`, not from
  `OpenMath/CollocationBN.lean`.
- Attack `nodePoly_polyMoment_orthogonal_of_algStable` first; that is the real
  missing bridge from algebraic stability to the polynomial argument.
- Once that bridge is closed, the next steps are:
  - `orthogonal_degree_eq_boundaryPoly`
  - `boundary_theta_nonneg_of_algStable`
  - `thm_358A_only_if`
- Harvest the five already-submitted Aristotle projects later, but do not
  re-poll repeatedly inside one cycle.
