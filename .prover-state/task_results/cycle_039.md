# Cycle 039 Results

## Worked on
BDF3 and BDF4 backward differentiation formulae (Section 4.5 of Iserles) — definitions, consistency, order, zero-stability, and convergence.

## Approach
Following the strategy's "Option A: More stiff equations — BDF methods", I formalized BDF3 and BDF4 as `LMM` instances with full proofs of their basic properties. The sorry-first workflow was used: definitions first, then closing proofs one by one.

### BDF3 (fully sorry-free)
- **Definition**: `bdf3 : LMM 3` with exact rational coefficients α = [-2/11, 9/11, -18/11, 1], β = [0, 0, 0, 6/11].
- **Consistency**: Direct computation via `simp [..., Fin.sum_univ_four]; norm_num`.
- **Order 3**: Verified all order conditions V₀ = V₁ = V₂ = V₃ = 0 and V₄ ≠ 0.
- **Zero-stability**: Key proof technique — factor 11·ρ(ξ) = (ξ-1)(11ξ²-7ξ+2), then for the quadratic factor:
  - Triangle inequality: from 11ξ² = 7ξ-2, take norms: 11‖ξ‖² = ‖7ξ-2‖ ≤ 7‖ξ‖+2.
  - For ‖ξ‖ ≥ 1: 11‖ξ‖² - 7‖ξ‖ - 2 ≥ 11-7-2 = 2 > 0, contradiction with the bound.
  - Unit root simplicity: ρ'(1) = 6/11 ≠ 0; other roots have ‖ξ‖ < 1 (no unit circle check needed).
- **Convergence**: Immediate from Dahlquist equivalence (consistency + zero-stability).

### BDF4 (2 sorrys in zero-stability)
- **Definition**: `bdf4 : LMM 4` with exact rational coefficients.
- **Consistency**, **order 4**, **implicit**: All proved by computation.
- **Zero-stability**: Factor 25·ρ(ξ) = (ξ-1)(25ξ³-23ξ²+13ξ-3). The cubic factor's roots are hard to analyze formally:
  - The triangle inequality approach fails at ‖ξ‖ = 1 (25 < 23+13+3 = 39).
  - Proving no roots on the unit circle requires conjugate elimination (yields quadratic 32z²-67z+77=0 with |z|²=77/32≠1).
  - Proving all roots inside the disk requires monotonicity + Vieta's formulas or Schur-Cohn criterion.
  - Left as sorry with detailed documentation of proof approaches.

## Result
**SUCCESS (partial)** — BDF3 fully formalized (0 sorry), BDF4 partially formalized (2 sorrys in zero-stability).

New sorry-free theorems:
- `bdf3` (definition), `bdf3_consistent`, `bdf3_order_three`, `bdf3_implicit`, `bdf3_zeroStable`
- `bdf4` (definition), `bdf4_consistent`, `bdf4_order_four`, `bdf4_implicit`
- `bdf3_convergent` (modulo inherited spectral bound sorry)

New sorrys:
- `bdf4_zeroStable.roots_in_disk`: cubic 25ξ³-23ξ²+13ξ-3 has all roots in unit disk
- `bdf4_zeroStable.unit_roots_simple`: cubic has no roots on unit circle

## Dead ends
- **Triangle inequality for BDF4 cubic**: At ‖ξ‖ = 1, the bound 25‖ξ‖³ ≤ 23‖ξ‖²+13‖ξ‖+3 gives 25 ≤ 39, which is true (no contradiction). The triangle inequality only works for the quadratic (BDF3) where the leading coefficient dominates.
- **Direct normSq computation for cubic**: Extracting |ξ|² from a cubic equation requires either the conjugate elimination trick or Vieta's formulas, both of which involve substantial complex algebra in Lean.
- **`bdf4_cubic_no_unit_root` attempt**: Wrote a full proof using conjugate elimination but hit issues with `linarith` over ℂ (not linearly ordered) and `starRingEnd` simplification. The mathematical approach is correct but the Lean tactics need `linear_combination` throughout, which requires careful term matching.

## Discovery
- **Triangle inequality technique** for showing polynomial roots are inside the unit disk works well when the leading coefficient is strictly larger than the sum of other absolute coefficients (BDF3: 11 > 7+2 = 9). Fails when this condition doesn't hold (BDF4: 25 < 23+13+3 = 39).
- **Conjugate elimination** for "no unit circle roots": combining p(ξ)=0 with p̄(ξ̄)=0 and the reversed equation (from ξ·ξ̄=1) can eliminate highest-degree terms. For a cubic, this reduces to a quadratic whose roots' norms can be computed via the real/imaginary decomposition. Promising but requires careful complex algebra in Lean.
- **`norm_mul` and `norm_pow`**: The correct pattern for norm equalities in ℂ is `congr_arg norm h_eq` followed by `rwa [norm_mul, norm_pow, ...] at this`, NOT `rw [← norm_mul, ← norm_pow, h_eq]` (which fails to match the pattern).

## Suggested next approach
1. **Close BDF4 zero-stability**: The conjugate elimination approach for `unit_roots_simple` is correct mathematically. Use `linear_combination` instead of `linarith` for all complex algebra. For `roots_in_disk`, the monotonicity+Vieta approach should work: show the cubic's derivative has negative discriminant (p' > 0), locate real root in (3/25, 1), then use Vieta's for conjugate pair.
2. **BDF5, BDF6**: Follow the same pattern. BDF5 has denominators of 137, BDF6 of 147 — larger but still exact rationals.
3. **A(α)-stability**: Define the concept for LMMs (stability region contains a sector) and prove BDF1-2 are A-stable, BDF3-6 are A(α)-stable.
