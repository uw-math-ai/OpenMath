# Cycle 071 Results

## Worked on
Order barriers for explicit Runge-Kutta methods (new file `OpenMath/OrderBarriers.lean`).

## Approach
Formalized the structural theorem that explicit consistent RK methods have bounded order:
for s ≤ 4 stages, the maximum achievable order is p ≤ s. The key insight is that for any
explicit consistent method, c₀ = 0 (first abscissa is zero), which forces the "tall tree"
order condition to vanish identically. Specifically:
- 1-stage: order2 = ∑ bᵢcᵢ = 0 ≠ 1/2
- 2-stage: order3b = ∑ bᵢaᵢⱼcⱼ = 0 ≠ 1/6 (all chains hit c₀ = 0)
- 3-stage: order4d = ∑ bᵢaᵢⱼaⱼₖcₖ = 0 ≠ 1/24 (all chains hit c₀ = 0)
- 4-stage: order5i = ∑ bᵢaᵢⱼaⱼₖ(∑ aₖₗcₗ) = 0 ≠ 1/120 (inner sum = 0 via c₀ = 0)

Also proved that no explicit consistent method with distinct nodes can satisfy C(2).

## Result
**SUCCESS** — 8 theorems, all sorry-free:

1. `explicit_first_row_zero`: explicit → A[0][j] = 0 for all j
2. `explicit_c_zero`: explicit + row-sum consistent → c₀ = 0
3. `explicit_A_zero`: explicit → A[i][j] = 0 for j ≥ i (wrapper)
4. `explicit_order_barrier_1`: 1-stage explicit consistent → ¬HasOrderGe2
5. `explicit_order_barrier_2`: 2-stage explicit consistent → ¬HasOrderGe3
6. `explicit_order_barrier_3`: 3-stage explicit consistent → ¬HasOrderGe4
7. `explicit_order_barrier_4`: 4-stage explicit consistent → ¬HasOrderGe5
8. `explicit_not_C2_distinct`: explicit + C(2) + distinct nodes → False

All proofs verified via `lean_run_code` with zero diagnostics.

## Dead ends
None — the approach worked cleanly on the first attempt.

## Discovery
- The "tall tree" order condition (deepest chain: order4d for 3-stage, order5i for 4-stage)
  is the natural one to target for barriers because it requires the longest chain
  i > j > k > ... which must ultimately pass through stage 0 where c₀ = 0.
- The proof technique is uniform: case-split on whether each chain link has i ≤ j
  (killed by explicit condition) or i > j (propagated down), with the base case always
  being k = 0 where c₀ = 0 kills the term.
- These are the first GENERAL results about explicit methods in the codebase — previous
  barriers (in ExplicitRK.lean) were for specific methods only.

## Suggested next approach
- Extend to s = 5 barrier (order ≤ 4, the first case where Butcher's barrier is strictly
  below s). This requires showing that ALL 9 fifth-order conditions cannot be satisfied
  simultaneously, not just the tall tree one.
- Formalize Nørsett's theorem: symmetric methods have even order (uses adjoint/symmetry).
- Continue with Chapter 5 topics: embedded RK pairs, error estimation.
