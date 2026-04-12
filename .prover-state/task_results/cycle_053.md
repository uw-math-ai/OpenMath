# Cycle 053 Results

## Worked on
Order 5 conditions infrastructure and upgrading GL3 and RadauIIA3 to order ≥ 5.

## Approach
Extended the collocation framework (Option B from strategy) by:
1. Defining all 9 fifth-order RK conditions (rooted trees of order 5)
2. Proving the simplifying assumption theorem B(5)∧C(3)∧D(1) → order ≥ 5
3. Proving complete simplifying assumptions for GL3 and RadauIIA3
4. Concluding order ≥ 5 for both methods

## Result
SUCCESS — all sorry-free, full build passes.

### New definitions (RungeKutta.lean):
- `order5a` through `order5i`: 9 fifth-order RK conditions
- `HasOrderGe5`: order ≥ 5 combining all conditions through order 5

### New theorems (Collocation.lean):
- `HasOrderGe5_of_B5_C3_D1`: B(5) ∧ C(3) ∧ D(1) implies order ≥ 5
  - Conditions 1-4,6: C(2)/C(3) collapses inner sums → B(5)
  - Condition 5: D(1) swaps sums → B(4)−B(5)
  - Conditions 7-9: C collapses → multiples of condition 5

### New theorems (GaussLegendre3.lean):
- `rkGaussLegendre3_B6`: GL3 satisfies B(6) (maximal: B(2s) for s=3)
- `rkGaussLegendre3_D3`: GL3 satisfies D(3) (maximal for s=3)
- `rkGaussLegendre3_order5`: GL3 has order ≥ 5

### New theorems (RadauIIA3.lean):
- `rkRadauIIA3_B5`: Radau IIA 3-stage satisfies B(5) (B(2s−1))
- `rkRadauIIA3_C3`: satisfies C(3)
- `rkRadauIIA3_D1`: satisfies D(1)
- `rkRadauIIA3_order5`: Radau IIA 3-stage has order ≥ 5 (= 2s−1)
- Replaced 8 direct order-4 proofs with cleaner simplifying-assumption approach

## Dead ends
None — all proofs went through on first attempt.

## Discovery
- The B+C+D framework scales cleanly to order 5: only D(1) is needed beyond B(5)+C(3).
  Conditions 5,7,8,9 (which need C(4)) all reduce to ∑bᵢ(∑aᵢⱼcⱼ³) via C(2)/C(3),
  and this single "hard" sum is handled by D(1) sum-swapping.
- GL3 has complete simplifying assumptions B(6), C(3), D(3), ready for order 6
  (needs 20 sixth-order condition definitions + B(6)+C(3)+D(2) → order 6 theorem).
- RadauIIA3 order proof becomes much cleaner via simplifying assumptions vs. direct
  verification of 8 individual conditions.

## Suggested next approach
- **Order 6**: Define the 20 sixth-order conditions and prove B(6)+C(3)+D(2) → order 6.
  Then GL3 gets order ≥ 6 immediately (all prerequisites already proven).
- **SDIRK3**: Still available as a target (3-stage, order 3, L-stable).
- **Other methods**: LobattoIIIA3 and LobattoIIIC3 could get order ≥ 4 via
  simplifying assumptions (cleaner than direct verification if not done already).
