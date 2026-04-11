# Cycle 015 Results

## Worked on
Dahlquist's second barrier: discovered and fixed a critical bug (theorem was FALSE as stated), added counterexample, and proved new algebraic sub-lemmas.

## Approach
1. Checked Aristotle result from cycle 013 submission — it found the theorem is **FALSE without zero-stability**.
2. Verified the counterexample: ρ(ζ) = (ζ-1)², σ(ζ) = (ζ²-1)/2 gives an LMM with order 3, A-stable, but NOT zero-stable (double root at ζ = 1).
3. Fixed all three theorem statements (`order_ge_three_not_aStable_core`, `order_ge_three_not_aStable`, `dahlquist_second_barrier`) to require zero-stability.
4. Added counterexample method with three fully-proved theorems.
5. Added algebraic sub-lemmas connecting consistency to the complex derivatives.
6. Documented the full proof outline in the sorry comment.

## Result
**SUCCESS** — Fixed a critical soundness bug and added 6 new fully-proved theorems. 1 sorry remains (same as before, but now correctly stated).

### Bug fixed
The original `dahlquist_second_barrier` stated: A-stable ⟹ order ≤ 2. This is FALSE. The correct statement requires zero-stability (ρ has a simple root at ζ = 1). The counterexample `dahlquistCounterexample` has σ/ρ = (ζ+1)/(2(ζ-1)) (same as trapezoidal rule) but ρ = (ζ-1)² instead of ζ-1. The double root allows order 3 while maintaining A-stability, but the method diverges (parasitic solution y_n = c·n).

### New definitions
- `dahlquistCounterexample`: 2-step LMM with ρ = (ζ-1)², σ = (ζ²-1)/2

### New theorems (fully proved, sorry-free)
- `dahlquistCounterexample_order_three`: counterexample has order 3
- `dahlquistCounterexample_aStable`: counterexample is A-stable
- `dahlquistCounterexample_not_zeroStable`: counterexample is NOT zero-stable
- `IsConsistent.sigmaC_one_eq_rhoCDeriv_one`: σ_ℂ(1) = ρ'_ℂ(1) for consistent methods
- `IsConsistent.sigmaC_one_ne_zero`: σ(1) ≠ 0 for zero-stable consistent methods
- `order_ge_three_not_aStable`: wrapper that extracts ρ'(1) ≠ 0 from zero-stability and calls core

### Modified theorems
- `order_ge_three_not_aStable_core`: added `hρ_simple : m.rhoCDeriv 1 ≠ 0` hypothesis
- `dahlquist_second_barrier`: added `hzs : m.IsZeroStable` hypothesis

### Remaining sorry
- `order_ge_three_not_aStable_core`: requires minimum principle for harmonic functions (Hopf boundary lemma)

## Dead ends
- None this cycle — the main finding was the bug, not a proof attempt.

## Discovery
- **The Dahlquist barrier requires zero-stability.** The textbook statement "A-stable ⟹ order ≤ 2" implicitly assumes the method is convergent (hence zero-stable by the Dahlquist equivalence theorem). Without this, multiplying both ρ and σ by (ζ-1) preserves the ratio σ/ρ but changes the order conditions, allowing arbitrary order.
- The key mathematical insight: order conditions V_q depend on σ and ρ individually, not just their ratio. So ρ = (ζ-1)² with σ = (ζ²-1)/2 has σ/ρ = (ζ+1)/(2(ζ-1)) (same as trapezoidal rule, order 2) but the doubled coefficients satisfy V₃ = 0 (order 3).
- The proof outline is now fully documented: via conformal map w = 1/ζ, the function G̃(w) = G(1/w) is analytic in {|w| < 1} with Re(G̃) ≥ 0 on the boundary and G̃(1) = 0, G̃'(1) = 1/12. The minimum principle gives Re(G̃) ≥ 0 inside, but G̃(1-ε) ≈ -ε/12 < 0 for small ε > 0.
- Aristotle confirmed this is a genuine bug, not just a proof difficulty.

## Suggested next approach
- **For the remaining sorry**: formalize a clean "minimum principle for Re(analytic function)" lemma using Mathlib's `Complex.AbsMax` module. The specific statement needed: if f is analytic in {|w| < 1}, continuous on {|w| ≤ 1}, and Re(f) ≥ 0 on {|w| = 1}, then Re(f) ≥ 0 in {|w| < 1}. This would close the sorry via the Taylor expansion argument.
- **Alternative**: move to Dahlquist equivalence theorem or Gauss-Legendre methods while the analysis step remains blocked.
