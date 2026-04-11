# Cycle 020 Results

## Worked on
Closing the sorry in `order_ge_three_not_aStable_core` (Dahlquist's second barrier, Theorem 3.4).

## Approach

### 1. Proved the minimum principle for Re of analytic functions
The key missing mathematical ingredient was the minimum principle for harmonic functions: if f is analytic on a bounded domain and Re(f) ≥ 0 on the frontier, then Re(f) ≥ 0 on the closure.

**Proved as `re_nonneg_of_frontier_re_nonneg`** using Mathlib's maximum modulus principle (`Complex.norm_le_of_forall_mem_frontier_norm_le`), via the exp(-f) trick:
- exp(-f) has |exp(-f)| = exp(-Re(f)) ≤ 1 on the frontier
- Maximum modulus principle gives |exp(-f)| ≤ 1 on the closure
- Therefore Re(f) ≥ 0 on the closure

This is a general-purpose lemma for any bounded domain in ℂ.

### 2. Restructured the main sorry
Decomposed the proof of `order_ge_three_not_aStable_core` into:
- A `suffices` block asking for the existence of a function G̃ : ℂ → ℂ with three properties:
  (a) DiffContOnCl ℂ G̃ (Metric.ball 0 1)
  (b) Re(G̃) ≥ 0 on sphere(0, 1)
  (c) Re(G̃(w₀)) < 0 for some w₀ in ball(0, 1)
- The minimum principle + this suffices immediately gives False (proved, no sorry)
- The sorry is now isolated to constructing G̃ and verifying (a), (b), (c)

### 3. Added algebraic infrastructure
- `rhoC_conj`: ρ_ℂ(conj z) = conj(ρ_ℂ(z)) — polynomials with real coefficients commute with conjugation
- `sigmaC_conj`: σ_ℂ(conj z) = conj(σ_ℂ(z))
- `E_re_inv_eq`: Re(σ(ζ⁻¹)/ρ(ζ⁻¹)) = Re(σ(ζ)/ρ(ζ)) on the unit circle — key for relating G̃'s boundary behavior to the E-function hypothesis

### 4. Submitted to Aristotle
Submitted the file to Aristotle (project 94a2438c) for automated proof of the remaining sorry.

## Result
PARTIAL SUCCESS — The sorry count remains at 1, but:
- The minimum principle for harmonic functions is now **fully proved** (was the main missing ingredient)
- The sorry is reduced from "entire proof of the Dahlquist barrier" to "construction and verification of the modified E-function G̃"
- Added 4 new proved lemmas

## Dead ends
- Direct algebraic approach (using only boundary derivatives of Re(G) at θ=0) is insufficient — the second derivative condition is satisfied, not contradicted. The minimum principle is genuinely needed.
- Trying to define G̃ as a piecewise function (formula on interior, limits on boundary) doesn't directly give DiffContOnCl.
- The removable singularity at w = 1 requires careful handling of polynomial factoring in Lean.

## Discovery
- `Complex.norm_le_of_forall_mem_frontier_norm_le` from Mathlib.Analysis.Complex.AbsMax is the key tool for the maximum modulus principle. Combined with exp(-f), it gives the minimum principle for Re(f).
- On the unit circle, (1+w)/(2(1-w)) is purely imaginary (= i·cot(θ/2)/2), so Re(G̃) = Re(σ̃/ρ̃) on the boundary. This simplifies property (b).
- The conjugation lemmas (rhoC_conj, E_re_inv_eq) show that the E-function has the same real part at ζ and ζ⁻¹, which directly connects the boundary behavior of G̃ to the hypothesis hE_nonneg.

## Suggested next approach
The remaining sorry requires constructing G̃ with three properties:

**(a) DiffContOnCl**: Define reversed polynomials ρ̃(w) = w^s·ρ(1/w), σ̃(w) = w^s·σ(1/w). Then G̃(w) = σ̃(w)/ρ̃(w) - (1+w)/(2(1-w)). Show:
- ρ̃(w) ≠ 0 for |w| < 1 (from A-stability: roots of ρ in |ζ| ≤ 1 map to |w| ≥ 1)
- (1-w) ≠ 0 for |w| < 1
- Therefore G̃ is a ratio of polynomials with nonvanishing denominator on ball(0,1): differentiable
- For ContinuousOn on closure: resolve removable singularity at w = 1 using order ≥ 3. The factored form G̃(w) = -(w-1)Q̃(w)/(2S̃(w)) where ρ̃ = (w-1)S̃ and N̄ = (w-1)³Q̃ shows the singularity is removable.
- **This is the hardest part.** Consider using Mathlib's `AnalyticAt.eventually_ne_of_ne` or polynomial division.

**(b) Re ≥ 0 on boundary**: Use `E_re_inv_eq` and `hE_nonneg`. On sphere(0,1), Re(G̃(w)) = Re(σ(1/w)/ρ(1/w)) = Re(σ(w̄)/ρ(w̄)) = Re(σ(w)/ρ(w)) ≥ 0.

**(c) Interior negative**: From order ≥ 3, compute G̃(1) = 0 and G̃'(1) = 1/12 (algebraically from the order conditions). Then G̃(1-ε) ≈ -ε/12 for small ε > 0, giving Re(G̃(1-ε)) < 0. Requires HasDerivAt for G̃ at w = 1 and a continuity/IVT argument.

Check Aristotle project 94a2438c for automated progress.
