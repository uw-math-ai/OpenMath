# Cycle 006 Results

## Worked on
A-stability (Chapter 3), BDF2 method, and Dahlquist's second barrier statement. Extended `OpenMath/MultistepMethods.lean` with stability polynomial infrastructure, A-stability proofs for concrete methods, a new numerical method (BDF2), and a key theorem statement.

## Approach
1. Defined `LMM.sigmaC` — second characteristic polynomial over ℂ.
2. Defined `LMM.stabilityPoly` — stability polynomial π(ξ, z) = ρ(ξ) - z·σ(ξ).
3. Defined `LMM.InStabilityRegion` — roots of π(·, z) in closed unit disk.
4. Defined `LMM.IsAStable` — stability region contains left half-plane.
5. Proved backward Euler and trapezoidal rule are A-stable via complex norm analysis.
6. Proved forward Euler is NOT A-stable (counterexample z = -3, ξ = -2, ‖ξ‖ = 2 > 1).
7. Added BDF2 method with full properties: consistency, order 2, implicit, zero-stable.
8. Stated Dahlquist's second barrier (A-stable → order ≤ 2) with sorry.
9. Used sorry-first workflow throughout.

## Result
SUCCESS — 9 new sorrys created and closed. 1 sorry remains (Dahlquist barrier — deep analytic result, intentionally sorry'd).

### New definitions
- `LMM.sigmaC` — second characteristic polynomial over ℂ
- `LMM.stabilityPoly` — stability polynomial π(ξ, z) = ρ(ξ) - z·σ(ξ)
- `LMM.InStabilityRegion` — z in stability region
- `LMM.IsAStable` — A-stability
- `bdf2` — BDF2 (Backward Differentiation Formula, 2-step) method

### New theorems (fully proved)
- `backwardEuler_aStable` — Backward Euler is A-stable
- `trapezoidalRule_aStable` — Trapezoidal rule is A-stable
- `forwardEuler_not_aStable` — Forward Euler is NOT A-stable
- `bdf2_consistent` — BDF2 is consistent
- `bdf2_order_two` — BDF2 has order 2
- `bdf2_implicit` — BDF2 is implicit
- `bdf2_zeroStable` — BDF2 is zero-stable

### New theorem statements (sorry)
- `LMM.dahlquist_second_barrier` — A-stable LMM has order ≤ 2

## Dead ends
- `Complex.abs_re_le_abs` doesn't exist; correct name is `Complex.abs_re_le_norm`.
- `Complex.norm_eq_abs` and `Complex.abs_apply` don't exist in current Mathlib.
- Working with `z * 2⁻¹` over ℂ expands `2⁻¹` using the complex inverse formula (`re/(re²+im²)`), creating very messy expressions. Solution: multiply through by 2 and work with `(2 + z)/(2 - z)` instead.
- `simp only [Complex.ofReal_re, Complex.ofReal_im]` doesn't simplify `Complex.re 2` or `Complex.im 2`; use `norm_num` instead.

## Discovery
- For A-stability proofs of 1-step methods: extract the linear equation `a * ξ = b` from the stability polynomial, take `‖·‖`, then compare `‖b‖ ≤ ‖a‖` using `Complex.normSq` (via `Complex.sq_norm`) and `nlinarith`.
- The `norm_num` tactic is essential for simplifying concrete complex number components like `Complex.re 2 = 2`.
- `linear_combination` continues to be the key tool for factoring complex polynomials.
- For the `‖a‖ ≤ ‖b‖` step: rewrite via `Complex.sq_norm` to normSq, expand with `Complex.normSq_apply + Complex.add_re/sub_re/add_im/sub_im`, then close with `norm_num; nlinarith`.
- The `sq_nonneg (‖b‖ - ‖a‖)` hint is useful for `nlinarith` to derive `‖a‖ ≤ ‖b‖` from `‖a‖^2 ≤ ‖b‖^2`.

## Suggested next approach
- **Runge–Kutta methods**: Define Butcher tableaux, explicit RK methods, classical RK4. This is Chapter 2 of Iserles.
- **Dahlquist equivalence theorem**: Define convergence for LMMs and state the equivalence (consistency + zero-stability ⟺ convergence). Requires ODE solution infrastructure.
- **BDF methods**: Add BDF3, BDF4 and prove their properties. BDF3+ are NOT A-stable (only A(α)-stable).
