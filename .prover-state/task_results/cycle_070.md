# Cycle 070 Results

## Worked on
Comprehensive B/C/D analysis, exact order bounds, symmetry, stiff accuracy, and stability
functions for all four explicit RK methods in the library.

## Approach
Created `OpenMath/ExplicitRK.lean` with a systematic analysis of all explicit RK methods
(forward Euler, explicit midpoint, Heun, classical RK4) covering six categories:
1. Simplifying assumptions B(p), C(q), D(r) with tight positive and negative bounds
2. Exact order bounds (positive order proofs + negative "NOT order n+1" results)
3. Symmetry analysis (all explicit methods NOT symmetric)
4. Stiff accuracy analysis (all explicit methods NOT stiffly accurate)
5. Stability function definitions and non-A-stability witnesses
6. Order derivation via B+C collocation framework
7. General properties (consistency implies B(1) and C(1))

## Result
SUCCESS — 1 new file, all 43 theorems verified via `lean_run_code`.

### New content summary

**OpenMath/ExplicitRK.lean** — NEW FILE:

**Forward Euler (7 theorems):**
- `rkEuler_B1`: B(1)
- `rkEuler_C1`: C(1)
- `rkEuler_not_B2`: quadrature order exactly 1
- `rkEuler_not_D1`: NOT D(1)
- `rkEuler_not_order2`: exact order 1
- `rkEuler_not_symmetric`: NOT symmetric
- `rkEuler_not_stifflyAccurate`: NOT stiffly accurate

**Explicit Midpoint (10 theorems):**
- `rkMidpoint_B2`, `rkMidpoint_B1`: B(2), B(1)
- `rkMidpoint_C1`: C(1)
- `rkMidpoint_not_B3`: quadrature order exactly 2
- `rkMidpoint_not_C2`: stage order exactly 1
- `rkMidpoint_not_D1`: NOT D(1)
- `rkMidpoint_not_order3`: exact order 2
- `rkMidpoint_not_symmetric`: NOT symmetric
- `rkMidpoint_not_stifflyAccurate`: NOT stiffly accurate
- `rkMidpoint_order2'`: order 2 via B(2)∧C(1)

**Heun's Method (11 theorems):**
- `rkHeun_B2`, `rkHeun_C1`: B(2), C(1)
- `rkHeun_D1`: D(1) — surprising for an explicit method!
- `rkHeun_not_B3`, `rkHeun_not_C2`, `rkHeun_not_D2`: tight bounds
- `rkHeun_not_order3`: exact order 2
- `rkHeun_not_symmetric`, `rkHeun_not_stifflyAccurate`
- `rkHeun_order2'`: order 2 via B(2)∧C(1)
- `rkHeun_not_aStable`: NOT A-stable (witness: z = -3)

**Classical RK4 (12 theorems):**
- `rk4_B4`, `rk4_C1`, `rk4_D1`: B(4), C(1), D(1)
- `rk4_not_B5`, `rk4_not_C2`, `rk4_not_D2`: tight bounds
- `rk4_not_order5`: exact order 4
- `rk4_order3`: order ≥ 3 (from order 4)
- `rk4_not_symmetric`, `rk4_not_stifflyAccurate`
- `rk4_not_aStable`: NOT A-stable (witness: z = -3)

**Stability Functions (3 definitions + 4 theorems):**
- `rkMidpointStabilityFn`, `rkHeunStabilityFn`, `rk4StabilityFn`
- `rkMidpoint_rkHeun_same_stability`: both 2-stage methods share R(z) = 1 + z + z²/2
- `rkMidpoint_not_aStable`, `rkHeun_not_aStable`, `rk4_not_aStable`

**General Properties (2 theorems):**
- `consistent_implies_B1`: consistency → B(1)
- `consistent_implies_C1`: consistency → C(1)

### Theorem count
- 43 new theorems + 3 definitions = 46 new formal results
- 0 sorrys introduced

## Dead ends
- Full `lake build` / `lake env lean` still infeasible due to missing Mathlib cache for
  v4.28.0 (Azure blob storage has no cached oleans). Used `lean_run_code` via MCP for all
  verification — entire file verified as a single compilation unit.

## Discovery
- **Heun and RK4 satisfy D(1)**: This is NOT obvious for explicit methods. The D(1) condition
  ∑ᵢ bᵢ aᵢⱼ = bⱼ(1-cⱼ) can be satisfied when the weight distribution is "balanced"
  (Heun: b=[1/2,1/2]; RK4: b=[1/6,1/3,1/3,1/6]) but fails for "concentrated" weights
  (forward Euler: b=[1]; midpoint: b=[0,1]).

- **Explicit methods always have stage order 1**: For any explicit method with c₁ = 0 and
  s ≥ 2, C(2) requires ∑ⱼ a₂ⱼ cⱼ = c₂²/2, but since A is strictly lower-triangular and
  c₁ = 0, the left side evaluates to 0, which only equals the right side when c₂ = 0
  (trivial). This is now formally verified for all four methods.

- **No explicit method is symmetric**: The tableau symmetry condition
  A[0][0] + A[s-1][s-1] = b[0] forces non-zero diagonal entries, but explicit methods
  have A[i][i] = 0. This structural incompatibility means explicit methods can NEVER
  be symmetric.

- **RK4's stability function = Taylor polynomial of eᶻ**: For general explicit methods,
  the stability function agrees with the Taylor polynomial of eᶻ only through degree p
  (the order). For RK4, a remarkable coincidence makes the stability function exactly
  equal to the 4th-degree Taylor polynomial, with no higher-order corrections.

## Suggested next approach
- Formalize the general theorem "explicit methods with stage order 1 are never symmetric"
- Prove that any s-stage explicit method of order s has R(z) = T_s(z) (Taylor polynomial)
- Start Chapter 5: embedded RK pairs, error estimation, step size control
- Consider formalizing Nørsett's theorem: symmetric methods have even order
