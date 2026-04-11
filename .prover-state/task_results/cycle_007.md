# Cycle 007 Results

## Worked on
Chapter 2: Runge–Kutta methods. Created `OpenMath/RungeKutta.lean` with the full Butcher tableau framework, four standard RK methods, and all proofs completed (0 sorry).

## Approach
1. Followed plan.md which directed next work to Chapter 2 (Runge–Kutta methods).
2. Wrote the full file structure: Butcher tableau definition, consistency/explicit properties, order conditions up to order 4, four standard methods, and all proofs.
3. All proofs are computational (`simp + norm_num + fin_cases`) — no sorry's needed.
4. Verified compilation with `lake env lean` and verified key theorems with `lean_verify`.

## Result
SUCCESS — 0 sorry. All definitions and theorems fully proved and verified.

### New definitions
- `ButcherTableau s` — s-stage Butcher tableau (A matrix, b weights, c nodes)
- `ButcherTableau.IsRowSumConsistent` — row-sum condition c_i = ∑_j a_{ij}
- `ButcherTableau.IsConsistent` — consistency (∑ b_i = 1 and row-sum)
- `ButcherTableau.IsExplicit` — A is strictly lower triangular
- `ButcherTableau.order1` through `order4d` — individual order conditions
- `ButcherTableau.HasOrderGe1` through `HasOrderGe4` — composite order predicates

### New methods
- `rkEuler` — Forward Euler as 1-stage RK
- `rkMidpoint` — Explicit midpoint (modified Euler) as 2-stage RK
- `rkHeun` — Heun's method (improved Euler) as 2-stage RK
- `rk4` — Classical RK4 as 4-stage RK

### New theorems (all fully proved, verified with standard axioms)
- `rkEuler_consistent`, `rkEuler_explicit`, `rkEuler_order1`
- `rkMidpoint_consistent`, `rkMidpoint_explicit`, `rkMidpoint_order2`
- `rkHeun_consistent`, `rkHeun_explicit`, `rkHeun_order2`
- `rk4_consistent`, `rk4_explicit`, `rk4_order4`

## Dead ends
- `Fin.sum_univ_one` is not needed as a simp argument — Lean's simp already handles 1-element sums.
- When using `fin_cases i <;> simp [...] <;> norm_num`, some branches may not need `norm_num`, producing "tactic does nothing" warnings. Fixed with `try norm_num`.

## Discovery
- `Fin.sum_univ_four` exists in Mathlib and works for 4-stage RK methods.
- `fin_cases i <;> fin_cases j <;> simp_all [method]` is the pattern for proving explicit (strictly lower triangular) property.
- For order conditions with rational coefficients, `simp [..., Fin.sum_univ_four]; norm_num` closes the goal reliably.
- The `ButcherTableau` structure with plain functions (not matrices) keeps things simple and avoids Matrix API complexity.

## Suggested next approach
- **Implicit RK methods**: Define implicit RK (A not necessarily lower triangular), add implicit Euler and Gauss–Legendre methods, prove A-stability.
- **Convergence**: Define convergence for one-step methods, prove the convergence theorem (consistency + Lipschitz ⟹ convergence).
- **Dahlquist equivalence**: Requires ODE solution infrastructure; may be worth building shared helpers.
