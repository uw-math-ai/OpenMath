# Strategy

## SKIP: Dahlquist's second barrier (order_ge_three_not_aStable_core)

The 2 remaining sorrys (`hasDerivAt_Gtilde_one` and `continuousOn_Gtilde_closedBall`) require
removable singularity theory and L'Hôpital-type arguments for complex polynomial quotients
that are beyond current Mathlib tooling. **Do NOT work on these.** They have consumed 14+ cycles
with zero progress. An issue file has been written.

## Dahlquist equivalence theorem (Cycles 35-36)

The Dahlquist equivalence theorem is formalized in `OpenMath/DahlquistEquivalence.lean`.
`stableRecurrence_of_zeroStable` has been decomposed into structured sub-lemmas using
Mathlib's `LinearRecurrence` infrastructure.

**1 sorry remains**: `uniformly_bounded_tupleSucc_iterates` — the spectral bound on the
companion operator `tupleSucc`. This requires: under the root condition (zero-stability),
‖tupleSucc^n(v)‖ ≤ M·‖v‖ for all n, v.

**Proved in Cycle 36**:
- `toLinearRecurrence`: LMM → `LinearRecurrence ℂ`
- `satisfiesRecurrence_iff_isSolution`: equivalence of solution predicates
- `tupleSucc_iterate_eq_mkSol`: state vector at time n = tupleSucc^n(init)
- `stableRecurrence_of_zeroStable`: fully proved modulo spectral bound

## Current target: Close `uniformly_bounded_tupleSucc_iterates` OR advance to new material

### Option A: Close the spectral bound
The sorry needs: spectral radius ≤ 1 with semisimple unit eigenvalues → bounded operator powers.
Possible approaches:
1. **Cayley-Hamilton**: `aeval_self_charpoly` expresses tupleSucc^n mod charpoly as
   polynomial of degree < s in tupleSucc. Bound the coefficients under the root condition.
2. **Generalized eigenspace decomposition**: Mathlib has `Module.End.genEigenspace`.
   Decompose tupleSucc and bound each component.
3. **Direct companion matrix**: Define the s×s matrix, relate charpoly to ρ, bound powers.

### Option B: Move to new material
- **Chapter 4: Stiff equations** — L-stability, algebraic stability, stiff decay.
- **Collocation methods** (Section 2.3) — define collocation RK, prove order conditions.
- **Higher-order Gauss-Legendre** — 3-stage GL method, order 6.

### If blocked:
Write an issue file and move to Option B.

## Rules reminder
- Sorry-first: write full proof structure with sorry, verify compilation, then close sorrys.
- Do NOT return to the Dahlquist barrier sorrys.
- Each cycle MUST produce either a commit or an issue file.
