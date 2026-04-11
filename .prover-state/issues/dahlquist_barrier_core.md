# Issue: Dahlquist barrier core analytical step

## Blocker
The sorry `order_ge_three_not_aStable_core` in `OpenMath/MultistepMethods.lean` requires the minimum principle for harmonic functions.

## Status (updated cycle 015)
- **Bug found and fixed**: the theorem was FALSE without zero-stability. Now has correct hypothesis `hρ_simple : m.rhoCDeriv 1 ≠ 0`.
- Counterexample added (`dahlquistCounterexample`: order 3, A-stable, not zero-stable).
- Proof outline fully documented in the sorry comment.
- Aristotle submission (project 79385b8d) confirmed the bug.

## Context
The theorem states: for an A-stable, **zero-stable** LMM of order ≥ 3, derive False.

Hypotheses available:
- `hp : m.HasOrder p` with `hp3 : 3 ≤ p`
- `ha : m.IsAStable`
- `hρ_simple : m.rhoCDeriv 1 ≠ 0` (simple root at ζ = 1, from zero-stability)
- `hE_nonneg`: Re(σ/ρ) ≥ 0 on unit circle
- `hRe_inv`: Re(1/(e^{iθ}-1)) = -1/2

## Proof outline (documented in the sorry comment)

1. **Consistency**: ρ(1) = 0, σ(1) = ρ'(1) ≠ 0.
2. **Modified numerator**: N(ζ) = 2σ(ζ)(ζ-1) - ρ(ζ)(ζ+1).
   Order ≥ 2 gives N(1) = N'(1) = N''(1) = 0, so N = (ζ-1)³·Q(ζ).
3. **Third derivative**: N'''(1) = -σ(1), so Q(1) = -σ(1)/6 ≠ 0.
4. **G function**: With ρ = (ζ-1)R(ζ), G(ζ) = (ζ-1)Q(ζ)/(2R(ζ)).
   G(1) = 0, G'(1) = Q(1)/(2R(1)) = -σ(1)/(12ρ'(1)) = -1/12.
5. **Boundary data**: Re(G(e^{iθ})) = Re(σ/ρ) - Re(1/(ζ-1)+1/2) = Re(σ/ρ) ≥ 0.
6. **Conformal map**: w = 1/ζ gives G̃(w) = G(1/w) analytic in {|w| < 1} with Re(G̃) ≥ 0 on {|w| = 1} and G̃(1) = 0, G̃'(1) = 1/12.
7. **MINIMUM PRINCIPLE** (the sorry): Re(G̃) ≥ 0 in {|w| < 1}.
8. **Contradiction**: G̃(1-ε) ≈ -ε/12 + O(ε²) < 0 for small ε > 0, but 1-ε ∈ {|w| < 1}.

## What was tried
1. Fourier coefficient approach: FAILED — order conditions don't constrain Σ αⱼβⱼ.
2. Aristotle: found the bug (great!) but couldn't prove the corrected version.
3. Direct use of `Complex.AbsMax`: needs scaffolding for the conformal map setting.

## Minimal sorry needed
A clean lemma of the form:
> If f is analytic in {|w| < 1}, continuous on {|w| ≤ 1}, and Re(f(e^{iθ})) ≥ 0 for all θ, then Re(f(w)) ≥ 0 for all |w| < 1.

This is a standard consequence of the maximum modulus principle applied to e^{-f} (or the Poisson integral formula). Formalizing this in Mathlib requires connecting `Complex.AbsMax` to the disk setting.
