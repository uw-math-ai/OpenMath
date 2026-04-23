# Issue: 358A matrix-to-polynomial bridge for `nodePoly_polyMoment_orthogonal_of_algStable`

## Blocker
The first real blocker for Theorem 358A is the missing bridge from algebraic
stability of a collocation tableau to orthogonality of its node polynomial.

The intended missing helper is now stated in the live file as:

```lean
lemma ButcherTableau.nodePoly_polyMoment_orthogonal_of_algStable
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable) :
    ∀ q : ℝ[X], q.natDegree < s - 1 → polyMomentN (2 * s) (nodePoly t * q) = 0
```

Without this bridge, the extracted proof for 358A cannot reach the Legendre
characterization step.

## Context
- Live file: `OpenMath/CollocationAlgStability.lean`
- Existing usable infrastructure:
  - `OpenMath/StiffEquations.lean`: `algStabMatrix`, `HasNonNegWeights`, `IsAlgStable`
  - `OpenMath/Legendre.lean`: `nodePoly`, `polyMomentN`, interval-integral bridge,
    and the uniqueness pattern used in `gaussLegendreNodes_of_B_double`
  - `OpenMath/Collocation.lean`: `SatisfiesB`, `SatisfiesC`, `SatisfiesD`, `SatisfiesE`
- What is still absent is a theorem converting `hAlg.posdef_M` plus collocation
  data into vanishing moments for `nodePoly t`.

## What was tried
- Created the new theorem-local file `OpenMath/CollocationAlgStability.lean`
  with the full sorry-first scaffold for Theorem 358A:
  - `algStabilityBoundaryPoly`
  - `nodePoly_polyMoment_orthogonal_of_algStable`
  - `nodePoly_interval_orthogonal_of_algStable`
  - `orthogonal_degree_eq_boundaryPoly`
  - `boundary_theta_nonneg_of_algStable`
  - `thm_358A_only_if`
  - `thm_358A_if`
  - `thm_358A`
- Verified the scaffold compiles with:
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/CollocationAlgStability.lean`
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.CollocationAlgStability`
- Submitted the required 5-job Aristotle batch on the live file:
  - `314a6a62-23a9-4572-a6b4-be80da8c324c` for `nodePoly_polyMoment_orthogonal_of_algStable`
  - `fabcddf1-d2e4-46d2-b0b9-90ed47ed1cc8` for `orthogonal_degree_eq_boundaryPoly`
  - `ffe56f65-fcc6-4d9f-9040-b47ac4158f52` for `boundary_theta_nonneg_of_algStable`
  - `995901fc-98bc-4885-a95e-c5dc63a0cabb` for `thm_358A_if`
  - `1fceebe5-19ab-472e-8616-8c14bddcf6ac` for `thm_358A`
- Waited the mandated 30 minutes and did one check only.
- At that check, all 5 projects were still `IN_PROGRESS`, so there was no
  result to harvest this cycle.

## Possible solutions
- Formalize the transformed-matrix computation behind the textbook’s equation
  (358c): show that algebraic stability forces the collocation defect against
  every polynomial of degree `< s - 1` to vanish.
- If the matrix route is awkward directly, derive the needed orthogonality first
  as an interval-integral statement and only then rewrite back to `polyMomentN`
  using the existing bridge in `OpenMath/Legendre.lean`.
- Search for a small theorem-local family of test vectors `v : Fin s → ℝ`
  built from polynomial evaluations at the nodes, so `hAlg.posdef_M v` collapses
  to the required vanishing moment formula.
