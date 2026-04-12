# Cycle 030 Results

## Worked on
Dahlquist's second barrier theorem — refactoring the two remaining sorrys in `order_ge_three_not_aStable_core` into standalone helper lemmas.

## Approach
1. Analyzed the two remaining sorrys:
   - `ContinuousOn Gt (closure (Metric.ball 0 1))` — removable singularity continuity
   - `HasDerivAt Gt (1/12) 1` — derivative at the removable singularity

2. Identified the mathematical strategy for each:
   - **HasDerivAt**: The combined numerator P(w) = 2σ̃(w)(w-1) + ρ̃(w)(w+1) has a triple zero at w=1 (from C₀, C₁, C₂), with P'''(1) = -ρ'(1) (from C₃). The denominator D(w) = 2ρ̃(w)(w-1) has a double zero with D''(1) = -4ρ'(1). So the derivative is P'''(1)/(3·D''(1)) = 1/12.
   - **ContinuousOn**: Requires showing the removable singularity at w=1 is correctly handled, plus continuity at boundary points.

3. Extracted both claims into standalone theorems (`hasDerivAt_Gtilde_one` and `continuousOn_Gtilde_closedBall`) with detailed docstrings explaining the proof strategy.

4. Verified the refactored file compiles without errors.

## Result
SUCCESS — Structural improvement. The two sorrys are now in **focused, standalone lemmas** with clear mathematical descriptions, rather than buried deep inside the main proof. The main theorem `order_ge_three_not_aStable_core` now cleanly invokes these lemmas.

## Dead ends
- Direct polynomial division approach (defining R(w) = ρ̃(w)/(w-1) as an explicit sum) was considered but too verbose for one cycle.
- Using `HasDerivAt.div` directly doesn't work because the denominator is 0 at w=1.
- The ContinuousOn proof has a subtle issue: if ρ has other roots on the unit circle besides ζ=1, the function ρ̃ can vanish on the boundary of ball(0,1), creating poles. The resolution likely involves showing A-stability prevents σ/ρ from having genuine poles on the unit circle (the residue must be purely imaginary), or using a limiting argument with sub-balls.

## Discovery
- The algebraic computation P'''(1) = -σ(1) = -ρ'(1) was verified by expanding in terms of "reversed moments" and applying order conditions C₁, C₂, C₃. The coefficients of B₀, B₁, B₂ all cancel independently: coeff(B₀) = -1, coeff(B₁) = 0, coeff(B₂) = 0. So P'''(1) = -B₀ = -σ(1).
- The polynomial Q(ζ) = 2(1-ζ)σ(ζ) + (1+ζ)ρ(ζ) satisfies Q'''(1) = ρ'(1) under order ≥ 3 conditions, providing an alternative route via the identity P(w) = w^{s+1}·Q(1/w).
- For HasDerivAt, the approach using `Filter.EventuallyEq.hasDerivAt_iff` combined with a quotient of differentiable functions (after factoring) seems most promising.

## Suggested next approach
1. **HasDerivAt** (`hasDerivAt_Gtilde_one`): Use `hasDerivAt_iff_tendsto_slope` and prove the limit P(w)/[D(w)(w-1)] → 1/12 via explicit Taylor estimates. Key sub-tasks:
   - Prove P(1) = 0, P'(1) = 0, P''(1) = 0 using order conditions
   - Prove P'''(1) = -σ(1) using C₃
   - Prove D''(1) = -4ρ'(1) using ρ̃'(1) = -ρ'(1)
   - Use these to establish the limit via bounding the ratio

2. **ContinuousOn** (`continuousOn_Gtilde_closedBall`): Consider two approaches:
   - Prove ρ̃ has no zeros on sphere(0,1) except at w=1 (using A-stability boundary analysis)
   - OR use a limiting/sub-ball argument to avoid boundary root issues

3. Alternatively, submit one or both lemmas to Aristotle for automated proving.
