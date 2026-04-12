# Strategy

## SKIP: Dahlquist's second barrier (order_ge_three_not_aStable_core)

The 2 remaining sorrys (`hasDerivAt_Gtilde_one` and `continuousOn_Gtilde_closedBall`) require
removable singularity theory and L'Hôpital-type arguments for complex polynomial quotients
that are beyond current Mathlib tooling. **Do NOT work on these.** They have consumed 14+ cycles
with zero progress. An issue file has been written.

## Completed: Dahlquist equivalence theorem (Cycle 35)

The Dahlquist equivalence theorem is formalized in `OpenMath/DahlquistEquivalence.lean`.
**1 sorry remains**: `stableRecurrence_of_zeroStable` (zero-stable → stable recurrence).

## Current target: Close `stableRecurrence_of_zeroStable` OR advance to new material

### Option A: Close the remaining sorry
The sorry `stableRecurrence_of_zeroStable` requires proving that the root condition on ρ
implies all solutions of the characteristic recurrence are bounded. This needs:
1. Define the **companion matrix** of ρ (s×s matrix).
2. Show solutions y_n correspond to A^n · y₀.
3. Prove ‖A^n‖ is uniformly bounded under the root condition (spectral radius ≤ 1 with
   semisimple unit eigenvalues).

Alternative: use **polynomial factorization** / induction on the degree of ρ to decompose
solutions into generalized eigensolutions ξ^n, n·ξ^n, etc.

### Option B: Move to new material
- **Chapter 4: Stiff equations** — L-stability, algebraic stability, stiff decay.
- **Collocation methods** (Section 2.3) — define collocation RK, prove order conditions.
- **Higher-order Gauss-Legendre** — 3-stage GL method, order 6.

### If blocked:
Write an issue file documenting the blocker and move to Option B.

## Rules reminder
- Sorry-first: write full proof structure with sorry, verify compilation, then close sorrys.
- Do NOT return to the Dahlquist barrier sorrys.
- Each cycle MUST produce either a commit or an issue file.
