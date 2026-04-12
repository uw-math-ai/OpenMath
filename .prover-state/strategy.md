# Strategy

## SKIP: Dahlquist's second barrier (order_ge_three_not_aStable_core)

The 2 remaining sorrys (`hasDerivAt_Gtilde_one` and `continuousOn_Gtilde_closedBall`) require
removable singularity theory and L'Hôpital-type arguments for complex polynomial quotients
that are beyond current Mathlib tooling. **Do NOT work on these.** They have consumed 14+ cycles
with zero progress. An issue file has been written.

## Dahlquist equivalence theorem (Cycles 35-36)

The Dahlquist equivalence theorem is formalized in `OpenMath/DahlquistEquivalence.lean`.
**1 sorry remains**: `uniformly_bounded_tupleSucc_iterates` — the spectral bound.
See `.prover-state/issues/spectral_bound_tupleSucc.md` for detailed analysis.
This requires 3-5 cycles of eigenspace infrastructure work. Defer until Mathlib gaps shrink.

## Chapter 4: Stiff Equations (Cycle 38 — DONE)

`OpenMath/StiffEquations.lean` now contains:
- L-stability definitions and proofs (backward Euler L-stable, midpoint/GL2 NOT L-stable)
- Algebraic stability definitions and proofs (backward Euler, midpoint, GL2, Radau IIA)
- **Radau IIA 2-stage**: definition, consistency, order 3 (not 4), stability function,
  A-stability, stiff decay, L-stability — all sorry-free

## Current target: Continue Chapter 4 OR advance to new material

### Option A: More stiff equations
- **SDIRK methods** (Section 4.3) — singly-diagonally-implicit RK, L-stability proof
- **BDF methods** (Section 4.5) — backward differentiation formulae, A(α)-stability
- **Stiff order conditions** — B-series for stiff problems

### Option B: Collocation methods (Section 2.3)
- Define collocation RK methods
- Prove collocation → RK equivalence
- Show Gauss/Radau/Lobatto nodes give specific methods

### Option C: Higher-order methods
- 3-stage Gauss-Legendre (order 6)
- Radau IIA 3-stage (order 5)

## Rules reminder
- Sorry-first: write full proof structure with sorry, verify compilation, then close sorrys.
- Do NOT return to the Dahlquist barrier sorrys.
- Each cycle MUST produce either a commit or an issue file.
