# Cycle 022 Results

## Worked on
Closing sorry's in `order_ge_three_not_aStable_core` (Dahlquist's second barrier, Theorem 3.4).

## Approach

### 1. Added three new sorry-free helper lemmas

**`re_inv_sub_one_of_norm_one`**: Re(1/(ζ-1)) = -1/2 for any ζ on the unit circle (ζ ≠ 1). This generalizes `re_inv_exp_sub_one` from `e^{iθ}` to arbitrary unit-circle elements, using `Complex.norm_eq_one_iff` to find the angle.

**`re_half_plus_inv_sub_one_eq_zero`**: Re((ζ+1)/(2(ζ-1))) = 0 on the unit circle. Key algebraic identity: (ζ+1)/(2(ζ-1)) = 1/2 + 1/(ζ-1), and Re(1/(ζ-1)) = -1/2, so the real parts cancel.

**`IsAStable.E_nonneg_re_unit_circle`**: Re(σ(ζ)/ρ(ζ)) ≥ 0 for any ζ on the unit circle with ρ(ζ) ≠ 0 (handles σ = 0 case separately). Lifts `E_nonneg_re` from the e^{iθ} parameterization to arbitrary unit-circle elements.

### 2. Restructured the proof of `order_ge_three_not_aStable_core`

Decomposed the proof into a clean two-level `suffices` structure:

- **Outer suffices** (from cycle 020, unchanged): Given Gtilde with DiffContOnCl, boundary Re ≥ 0, and interior Re < 0, the minimum principle gives contradiction.

- **Inner suffices** (new): Given Gt with DiffContOnCl, Gt(1) = 0, boundary Re ≥ 0, and HasDerivAt Gt (1/12) 1, construct the three properties. The boundary condition is assumed (pushed into the construction sorry), and the **interior negative point is fully proved** from HasDerivAt.

### 3. Proved the interior negative point (sorry closed!)

From `HasDerivAt Gt (1/12) 1` and `Gt(1) = 0`, proved existence of w₀ ∈ ball(0,1) with Re(Gt(w₀)) < 0.

Proof strategy: Extract the ε-δ little-o condition from HasDerivAt using `hasDerivAt_iff_isLittleO`. With ε = 1/24 and w₀ = 1 - min(δ/2, 1/2):
- w₀ ∈ ball(0,1) since 0 < ε₀ ≤ 1/2 gives |w₀| = 1 - ε₀ < 1
- ‖Gt(w₀) - (-ε₀/12)‖ ≤ ε₀/24 (from the little-o estimate)
- |Re(Gt(w₀)) - (-ε₀/12)| ≤ ε₀/24 (Re part bounded by norm)
- Re(Gt(w₀)) ≤ -ε₀/12 + ε₀/24 = -ε₀/24 < 0

### 4. Proved boundary non-negativity (formula case)

For w on the unit circle with w ≠ 0, w ≠ 1, and ρ(w⁻¹) ≠ 0:
Re(σ(w⁻¹)/ρ(w⁻¹) - (w⁻¹+1)/(2(w⁻¹-1))) = Re(σ/ρ) - Re((ζ+1)/(2(ζ-1))) = Re(σ/ρ) - 0 ≥ 0

Uses `re_half_plus_inv_sub_one_eq_zero` and `E_nonneg_re_unit_circle`.

## Result
**PARTIAL SUCCESS** — Sorry count reduced from 2 to 1. Three new sorry-free lemmas proved. Interior negative point and boundary formula case fully closed.

### Sorry status
- **Remaining sorry (1)**: Construction of Gt satisfying DiffContOnCl, Gt(1) = 0, boundary Re ≥ 0, and HasDerivAt Gt (1/12) 1. This is the core complex analysis construction requiring:
  (a) Polynomial factoring of the modified numerator using order ≥ 3
  (b) Removable singularity argument at w = 1
  (c) DiffContOnCl from analyticity of rational functions
  (d) Boundary Re ≥ 0 at ρ = 0 boundary points (continuity argument)

## Dead ends
- Tried to prove boundary Re ≥ 0 at points where ρ(w⁻¹) = 0 by case analysis. This requires a density/continuity argument (ρ has finitely many roots, so "good" points are dense on the circle, and Gt is continuous from DiffContOnCl). Moved this into the construction sorry to keep the structure clean.

## Discovery
- `Complex.norm_eq_one_iff`: ‖z‖ = 1 ↔ ∃ θ, exp(θ*I) = z. Key for lifting results from e^{iθ} parameterization to abstract unit-circle elements.
- `hasDerivAt_iff_isLittleO`: Clean way to extract the little-o asymptotic from HasDerivAt for ε-δ arguments.
- The interior negative point proof is a pure consequence of HasDerivAt + Gt(1) = 0 + derivative ≠ 0. No complex analysis needed beyond the derivative hypothesis.

## Suggested next approach
The remaining sorry requires constructing Gt : ℂ → ℂ with four properties. The recommended strategy:

1. **Define reversed polynomials** ρ̃(w) = w^s·ρ(1/w) and σ̃(w) = w^s·σ(1/w).
2. **Prove ρ̃(w) ≠ 0 for |w| < 1** from A-stability (roots of ρ in unit disk map to |w| ≥ 1).
3. **Factor the modified numerator** Ñ(w) = 2σ̃(w)(1-w) - ρ̃(w)(1+w). Show Ñ has a triple root at w = 1 from order ≥ 3, giving Ñ = (1-w)³·P̃(w). Combined with ρ̃ = (1-w)·S̃(w) (simple root from zero-stability), get Gt(w) = (1-w)P̃(w)/(2S̃(w)) — a ratio of polynomials with no singularity at w = 1.
4. **DiffContOnCl** follows from rational function with nonvanishing denominator on closed ball.
5. **HasDerivAt**: Compute Gt'(1) = P̃(1)/(2S̃(1)) using order conditions to show = 1/12.
6. **Boundary Re ≥ 0**: Combine proved lemmas with continuity at ρ=0 boundary points.

The polynomial factoring step (step 3) is the main challenge — it requires showing that a polynomial vanishing at a point with its first k derivatives factors as (z-a)^{k+1}·Q(z). This could use Mathlib's `Polynomial.divByMonic` or manual Taylor expansion.
