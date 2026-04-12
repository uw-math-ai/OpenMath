# Cycle 050 Results

## Worked on
- New file: `OpenMath/RadauIA2.lean` — Radau IA 2-stage method (complete formalization)
- Updated `OpenMath/Collocation.lean` — GL2 order 4 via simplifying assumptions

## Approach

### Radau IA 2-stage method
Following the established pattern from Radau IIA 2-stage and Lobatto methods, formalized:
1. Butcher tableau definition (nodes c₁=0, c₂=2/3; weights b₁=1/4, b₂=3/4)
2. Basic properties: consistency, non-negative weights, not explicit, not stiffly accurate
3. Order conditions: order exactly 3 (satisfies order 1-3, fails order 4a: ∑bᵢcᵢ³ = 2/9 ≠ 1/4)
4. Simplifying assumptions: B(3), C(1), D(2) — note D(2) is unusual for a method with only C(1)
5. Stability function = same as Radau IIA 2-stage: R(z) = (1+z/3)/(1-2z/3+z²/6)
6. A-stability, stiff decay, L-stability — all derived from shared stability function
7. Algebraic stability: M = (1/16)·[[1,-1],[-1,1]], quadratic form (v₀-v₁)²/16 ≥ 0

Key insight: Radau IA and Radau IIA 2-stage share identical stability functions (both give the (1,2)-Padé approximant to eᶻ), so A-stability, stiff decay, and L-stability transfer directly.

### Collocation framework extension
Added to Collocation.lean:
- `rkGaussLegendre2_D1`: GL2 satisfies D(1)
- `rkGaussLegendre2_order4'`: GL2 has order ≥ 4 via B(4) ∧ C(2) ∧ D(1)

This resolves the comment in the previous code that said "B(4) ∧ C(3) would require C(3) which needs s ≥ 3" — D(1) serves as the missing ingredient.

### Radau IIA simplifying assumptions (in RadauIA2.lean)
- `rkRadauIIA2_B3`: Radau IIA 2-stage satisfies B(3)
- `rkRadauIIA2_C2`: Radau IIA 2-stage satisfies C(2)
- `rkRadauIIA2_order3'`: Order ≥ 3 via B(3) ∧ C(2) (alternative derivation)

## Result
SUCCESS — 23 new theorems, all sorry-free:
- RadauIA2.lean: 20 theorems (17 for Radau IA, 3 for Radau IIA simplifying assumptions)
- Collocation.lean: 3 new theorems (GL2 D(1), GL2 order 4 from simplifying assumptions)

## Dead ends
None — all proofs followed established patterns.

## Discovery
- Radau IA and Radau IIA 2-stage have identical stability functions (1,2)-Padé
- Radau IA 2-stage satisfies D(2) despite only having C(1) — an asymmetric simplifying assumption profile compared to Radau IIA which has C(2)
- GL2's D(1) property was not previously verified in the codebase, enabling the order 4 derivation from B(4) ∧ C(2) ∧ D(1)

## Suggested next approach
1. **Radau IA 3-stage**: Like Radau IIA 3-stage but with left-endpoint node. Has irrational coefficients (√6) — same as Radau IIA 3-stage, so patterns transfer.
2. **W-transformation / adjointness**: Lobatto IIIA + IIIB satisfy b_i·a^A_{ij} + b_j·a^B_{ji} = b_i·b_j. This structural theorem connects the two families.
3. **A(α)-stability**: Define the concept and show BDF3/BDF4 are A(α)-stable for specific angles.
4. **3-stage Gauss-Legendre** (order 6): Flagship method, involves √15 coefficients.
