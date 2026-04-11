# Cycle 010 Results

## Worked on
Closing sorry's in Dahlquist's second barrier proof (`OpenMath/MultistepMethods.lean`):
- `LMM.IsAStable.E_nonneg_re` (line 560) — **PROVED**
- `LMM.order_ge_three_not_aStable` (line 637) — still sorry

## Approach

### E_nonneg_re (boundary locus lemma)
**Theorem**: For an A-stable LMM, Re(σ(e^{iθ})/ρ(e^{iθ})) ≥ 0 on the unit circle (away from roots of ρ).

**Proof strategy** (by contradiction + continuity):
1. Assume Re(σ/ρ) < 0 at ζ = e^{iθ}.
2. Show Re(ρ/σ) < 0 (reciprocal preserves sign of real part, via `Complex.inv_re`).
3. For any r > 1 with σ(r·ζ) ≠ 0: A-stability forces Re(ρ(r·ζ)/σ(r·ζ)) > 0 because r·ζ is a root of the stability polynomial with |r·ζ| = r > 1.
4. The function r ↦ Re(ρ(r·ζ)/σ(r·ζ)) is continuous at r = 1 (ρ and σ are polynomial, σ(ζ) ≠ 0). Since it's negative at r = 1, by continuity it's negative for some r > 1 — contradicting step 3.

Key Lean techniques used:
- `Complex.inv_re` + `div_neg_of_neg_of_pos` for the sign equivalence
- `continuous_finset_sum` + `Complex.continuous_ofReal` for continuity of rhoC and sigmaC
- `ContinuousAt.div` for quotient continuity
- `Filter.Tendsto.eventually` + `Iio_mem_nhds` for the ε-δ argument
- `Metric.mem_nhds_iff` to extract r > 1 from the neighborhood

### order_ge_three_not_aStable
This theorem requires harmonic analysis on the unit circle (minimum principle for harmonic functions or Fourier analysis argument). The standard proof uses:
1. Re(1/(e^{iθ}-1) + 1/2) = 0 (purely imaginary on the unit circle)
2. For order ≥ 3, G(ζ) = E(ζ) - 1/(ζ-1) - 1/2 is analytic at ζ = 1 with G(1) = 0
3. Re(G(e^{iθ})) ≥ 0 (from E_nonneg_re + step 1)
4. An integral/mean-value argument shows Re(G) ≡ 0, leading to contradiction

This remains a sorry — the harmonic analysis tools needed are not readily available in the current Mathlib setup.

## Result
**PARTIAL SUCCESS**: Proved 1 of 2 sorry's in Dahlquist's second barrier decomposition.
- `E_nonneg_re`: ✅ PROVED (boundary locus lemma — the key analytical step)
- `order_ge_three_not_aStable`: ❌ still sorry (requires harmonic analysis)

## Dead ends
None — the proof for E_nonneg_re worked on the first approach.

## Discovery
- The continuity-perturbation proof for E_nonneg_re is clean: for any |ξ| > 1 with σ(ξ) ≠ 0, A-stability directly gives Re(ρ(ξ)/σ(ξ)) > 0. Then continuity extends this to |ξ| = 1.
- Lean's `Complex.inv_re` lemma is key: Re(z⁻¹) = Re(z)/normSq(z), giving sign equivalence for reciprocals.
- The division-by-zero convention in Lean (a/0 = 0) is actually helpful: it means Re(ρ/σ) < 0 automatically implies σ ≠ 0.
- For `order_ge_three_not_aStable`, a useful sub-lemma is Re((e^{iθ}-1)⁻¹ + 1/2) = 0, which reduces to normSq(ζ) = 1 after clearing denominators.

## Suggested next approach
1. **Close `order_ge_three_not_aStable`**: Prove the helper lemma `re_inv_exp_sub_one_add_half` (direct computation using normSq(e^{iθ}) = 1). Then formalize the Fourier/integral argument showing Re(G) ≡ 0.
2. **Alternative**: Start formalizing Gauss-Legendre 2-stage RK method (order 4, A-stable) or the Dahlquist equivalence theorem while `order_ge_three_not_aStable` remains blocked on analysis tools.
