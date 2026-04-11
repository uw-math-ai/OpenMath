# Cycle 008 Results

## Worked on
Implicit Runge–Kutta methods (Chapter 2, Section 2.2) and A-stability for RK methods (Chapter 3). Extended `OpenMath/RungeKutta.lean` with implicit method definitions, stability function infrastructure, and A-stability proofs.

## Approach
1. Sorry-first workflow: wrote full skeleton with 8 sorrys for definitions and theorems, verified compilation.
2. Closed all 8 sorrys using Lean LSP tools (`lean_multi_attempt`, `lean_goal`, `lean_loogle`).
3. Defined `rkImplicitEuler` and `rkImplicitMidpoint` as 1-stage Butcher tableaux.
4. Proved consistency, non-explicitness, and order properties for both.
5. Defined `ButcherTableau.stabilityFn1` — the stability function R(z) for 1-stage RK methods.
6. Defined `ButcherTableau.IsAStable1` — A-stability for 1-stage RK methods.
7. Proved implicit Euler and implicit midpoint are A-stable via complex norm analysis.
8. Proved forward Euler (RK) is NOT A-stable via counterexample z = -3.
9. Verified all theorems use only standard axioms (propext, Classical.choice, Quot.sound).

## Result
SUCCESS — 8 sorrys created and all 8 closed. Zero sorrys in committed code for RungeKutta.lean.

### New definitions
- `rkImplicitEuler` — implicit Euler as 1-stage RK (A=[[1]], b=[1], c=[1])
- `rkImplicitMidpoint` — implicit midpoint as 1-stage RK (A=[[1/2]], b=[1], c=[1/2])
- `ButcherTableau.stabilityFn1` — stability function R(z) for 1-stage RK methods
- `ButcherTableau.IsAStable1` — A-stability for 1-stage RK methods

### New theorems (fully proved)
- `rkImplicitEuler_consistent` — implicit Euler is consistent
- `rkImplicitEuler_not_explicit` — implicit Euler is NOT explicit
- `rkImplicitMidpoint_consistent` — implicit midpoint is consistent
- `rkImplicitMidpoint_not_explicit` — implicit midpoint is NOT explicit
- `rkImplicitMidpoint_order2` — implicit midpoint has order ≥ 2
- `rkImplicitEuler_aStable` — implicit Euler is A-stable
- `rkImplicitMidpoint_aStable` — implicit midpoint is A-stable
- `rkEuler_not_aStable` — forward Euler (RK) is NOT A-stable

## Dead ends
- `lean_multi_attempt` fails on lines inside `where` blocks for structure constructors due to parser conflicts. Solution: write proofs directly using patterns from existing code.
- `inv_le_one` doesn't exist in Mathlib; correct name is `inv_le_one_of_one_le₀` (for `GroupWithZero`).
- `simp` with `Complex.ofReal_re`/`Complex.ofReal_im` is unused for `(1/2 : ℂ)` — need `norm_num` to simplify `(1/2 : ℂ).re` and `(1/2 : ℂ).im`.
- After `norm_num`, the division norm `‖a/b‖` may already be split to `‖a‖/‖b‖`, so `rw [norm_div]` fails.

## Discovery
- For 1-stage implicit RK A-stability: the stability function R(z) = (1+z(b-a))/(1-za) reduces to simple fractions that match the corresponding LMM A-stability proofs.
- `inv_le_one_of_one_le₀` is the correct lemma for `1 ≤ a → a⁻¹ ≤ 1` in `ℝ` (which is a `GroupWithZero`).
- For implicit Euler: `R(z) = 1/(1-z)`, A-stability via `‖1-z‖ ≥ 1` when Re(z) ≤ 0, closed with `inv_le_one_of_one_le₀`.
- For implicit midpoint: `R(z) = (1+z/2)/(1-z/2)`, A-stability via `‖numerator‖² ≤ ‖denominator‖²` using `Complex.sq_norm`, `Complex.normSq_apply`, then `norm_num; nlinarith`.
- `norm_num` is essential after `simp` with `Complex.normSq_apply` to resolve `(1/2 : ℂ).re = 1/2` etc.

## Suggested next approach
- **Gauss–Legendre 2-stage**: Requires defining a stability function for 2-stage methods (involves 2×2 matrix inverse). More complex but achievable.
- **Dahlquist equivalence theorem**: Define convergence for LMMs and state consistency + zero-stability ⟺ convergence.
- **Stiffness**: Define stiffness ratio and L-stability.
