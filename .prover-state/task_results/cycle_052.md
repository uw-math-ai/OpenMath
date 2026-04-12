# Cycle 052 Results

## Worked on
New file `OpenMath/GaussLegendre3.lean`: complete formalization of the Gauss-Legendre 3-stage (GL3) implicit Runge-Kutta method.

## Approach
Following Strategy Option C (higher-order methods), formalized GL3 — the 3-stage Gauss-Legendre method achieving order 2s=6 (the maximum for any s-stage RK method).

Key design choice: used integer-coefficient stability function P(z) = 120 + 60z + 12z² + z³, Q(z) = 120 - 60z + 12z² - z³ (scaled by 120) to avoid complex division issues that plagued earlier attempts with fractional coefficients.

## Result
SUCCESS — Full file compiles cleanly with zero warnings and zero sorrys.

### Theorems proven:
1. **Butcher tableau** (`rkGaussLegendre3`): nodes c₁ = 1/2 - √15/10, c₂ = 1/2, c₃ = 1/2 + √15/10
2. **Consistency** (`rkGaussLegendre3_consistent`): ∑bᵢ = 1 and cᵢ = ∑ⱼ aᵢⱼ
3. **Non-negative weights** (`rkGaussLegendre3_nonNegWeights`)
4. **Not explicit** (`rkGaussLegendre3_not_explicit`)
5. **Simplifying assumptions**: B(4), C(3), D(1)
6. **Order ≥ 4** via B(4) ∧ C(3) (`rkGaussLegendre3_order4`)
7. **Stability function** properties:
   - Q(z) = P(-z) (diagonal Padé hallmark)
   - P(z) - Q(z) = 2z(60 + z²)
   - |P(z)|² ≤ |Q(z)|² for Re(z) ≤ 0 (factored form: |Q|²-|P|² = -48x(600+70x²+30y²+(x²+y²)²))
   - Q(z) ≠ 0 for Re(z) ≤ 0
8. **A-stability** (`gl3_aStable`): |R(z)| ≤ 1 for Re(z) ≤ 0
9. **NOT L-stable** (`gl3_not_stiffDecay`): R(z) → -1 as z → -∞, proved via showing |R(x)| ≥ 1/2 for all x ≤ -120
10. **Algebraically stable** (`rkGaussLegendre3_algStable`): M matrix is positive semidefinite

## Dead ends
- `Complex.ofNat_re` / `Complex.ofNat_im` don't exist in Mathlib — resolved by using `show (120 : ℂ).re = (120 : ℝ) from by norm_num` pattern
- Original factored form -240x(600 + 70r² + r⁴) was wrong — correct form is -48x(600 + 70x² + 30y² + (x²+y²)²)
- `le_div_iff` renamed to `le_div_iff₀` in current Mathlib
- `↑(real_expr)` cast syntax causes HAdd type class failures — fixed with explicit `(... : ℝ) : ℂ` ascription or `set` + `push_cast`
- `linarith` doesn't work on ℂ — used `h.symm` and explicit `rw` chains instead
- `by ring; rw [...]` in one tactic block causes "no goals" — split into separate steps

## Discovery
- The `show ... from by norm_num` pattern is essential for resolving `Complex.re (n : ℂ) = n` for numeric literals in normSq proofs
- For NOT-L-stable proofs using `Filter.eventually_atBot`, can't evaluate R at a fixed point (N might be more negative). Solution: show |R(x)| ≥ 1/2 for ALL x ≤ -120, then use `filter_upwards` / `eventually_atBot.mpr` to get the eventual bound

## Suggested next approach
- GL3 order 6 proof (currently only order ≥ 4 via B(4)∧C(3); full order 6 = 2s needs B(6)∧C(3) or direct verification of all order conditions through degree 6)
- SDIRK3 method formalization (Strategy Option A)
- Extend collocation framework with additional infrastructure (Strategy Option B)
