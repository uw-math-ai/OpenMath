# Cycle 016 Results

## Worked on
Gauss–Legendre 2-stage (GL2) implicit Runge–Kutta method — full formalization including Butcher tableau, consistency, A-stability, and order 4 conditions.

## Approach
Per plan.md's suggestion to "Add Gauss–Legendre 2-stage method (order 4, A-stable)". Used sorry-first workflow: wrote full proof structure with sorry placeholders, verified compilation, then closed all sorrys.

### Key theorems added to `OpenMath/RungeKutta.lean`:
1. `rkGaussLegendre2` — Butcher tableau definition with √3 nodes
2. `rkGaussLegendre2_consistent` — consistency (∑bᵢ = 1, row-sum condition)
3. `rkGaussLegendre2_not_explicit` — not explicit (diagonal entry a₁₁ = 1/4 ≠ 0)
4. `gl2Num`, `gl2Denom`, `gl2StabilityFn` — stability function R(z) = N(z)/D(z)
5. `gl2Denom_eq_num_sub` — algebraic identity D(z) = N(z) - z
6. `gl2_normSq_denom_ge_num` — |N(z)|² ≤ |D(z)|² for Re(z) ≤ 0
7. `gl2_denom_ne_zero` — D(z) ≠ 0 for Re(z) ≤ 0
8. `gl2_aStable` — |R(z)| ≤ 1 for Re(z) ≤ 0
9. `rkGaussLegendre2_order4` — all 8 order conditions through order 4

## Result
SUCCESS — All 9 theorems compile with 0 sorry. File compiles cleanly via `lake env lean OpenMath/RungeKutta.lean`.

## Dead ends
- **normSq expansion**: Initial approach using `Complex.mk_re`/`Complex.mk_im` simp lemmas failed (these don't exist in current Mathlib). The fix: first simp to partially expand, then rewrite `(2 : ℂ)` and `(12 : ℂ)` as `↑(2 : ℝ)` and `↑(12 : ℝ)` via `show ... from by norm_num`, then use `Complex.div_ofReal` to fully expand real/imaginary parts.
- **pow_lt_pow_left**: This identifier doesn't exist in current Mathlib; replaced with `nlinarith` + `mul_pos` hint for the A-stability proof.

## Discovery
- Complex division by natural number literals (e.g., `z / 2` where `2 : ℂ`) is NOT recognized as division by ofReal. Must explicitly rewrite `(n : ℂ) = ↑(n : ℝ)` before `Complex.div_ofReal` applies. This is a recurring pattern for any proof involving `Complex.normSq` of expressions with literal denominators.
- `nlinarith [sqrt3_sq]` with `sqrt3_sq : Real.sqrt 3 ^ 2 = 3` handles all GL2 order conditions cleanly — the √3 terms either cancel (orders 1–2) or reduce to rationals via this hint.

## Suggested next approach
- Formalize convergence definition and Dahlquist equivalence theorem (consistency + stability ⟺ convergence) — this is the main open theorem in Chapter 1.
- Or continue the Dahlquist barrier sorry (`order_ge_three_not_aStable_core`) which requires the minimum principle for harmonic functions.
