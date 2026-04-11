# Cycle 013 Results

## Worked on
Dahlquist's second barrier: decomposing and partially proving `order_ge_three_not_aStable` (the last sorry in `OpenMath/MultistepMethods.lean`).

## Approach
1. Analyzed the proof structure needed for the Dahlquist barrier: A-stable LMM ⟹ order ≤ 2.
2. Decomposed the single sorry into proved sub-lemmas + one isolated analytical core.
3. Sorry-first workflow: wrote proof structure with sorry, verified compilation, closed what I could.
4. Submitted the hard analytical core to Aristotle (project `79385b8d-b08d-4916-bd50-908a63c1e76f`).

## Result
PARTIAL SUCCESS — 6 new lemmas proved, 1 sorry remains (isolated as `order_ge_three_not_aStable_core`).

### New theorems (fully proved)
- `re_inv_exp_sub_one`: On the unit circle, Re(1/(e^{iθ}-1)) = -1/2. Key computational lemma for the Dahlquist barrier. Uses normSq on unit circle + field_simp.
- `rhoC_one_cast`: ρ_ℂ(1) equals the real-valued ρ(1) cast to ℂ.
- `IsConsistent.rhoC_one`: For consistent methods, ρ_ℂ(1) = 0.
- `modifiedNumeratorC_one`: For order ≥ 1, the modified numerator N(1) = 2σ(1)(1-1) - ρ(1)(1+1) = 0.
- `cross_energy_nonneg`: Re(σ(e^{iθ})·conj(ρ(e^{iθ}))) ≥ 0 for A-stable methods (from Re(σ/ρ) ≥ 0 times |ρ|² ≥ 0).
- `order_ge_three_not_aStable`: Now proved by combining the core with `E_nonneg_re` and `re_inv_exp_sub_one` (reduces to `order_ge_three_not_aStable_core`).

### New definitions
- `modifiedNumeratorC`: N(ζ) = 2σ(ζ)(ζ-1) - ρ(ζ)(ζ+1), the numerator of G(ζ) = σ/ρ - 1/(ζ-1) - 1/2.

### Remaining sorry
- `order_ge_three_not_aStable_core`: The hard analytical step requiring the minimum principle for harmonic functions or equivalent.

## Dead ends
- `Complex.normSq_eq_abs` doesn't exist in current Mathlib; use `Complex.normSq_eq_norm_sq`.
- `Complex.mul_conj'` gives `↑‖z‖^2` (norm-based) which doesn't simp with `ofReal_re/im`; use `Complex.mul_conj` which gives `↑(normSq z)`.
- `ext` for ℂ doesn't work; use `Complex.ext` directly.
- `field_simp; linarith` fails when denominator sign isn't known; use `div_eq_iff hd_ne; linarith` instead.
- The "Fourier coefficient" approach (showing Σ α_j β_j < 0 for order ≥ 3) does NOT work — the order conditions don't directly constrain the inner product Σ α_j β_j.

## Discovery
- The proof of Re(1/(e^{iθ}-1)) = -1/2 uses: normSq(ζ-1) = 2-2·Re(ζ) when |ζ|=1, then Re(1/(ζ-1)) = Re(ζ-1)/normSq(ζ-1) = (Re(ζ)-1)/(2-2·Re(ζ)) = -1/2.
- `Complex.normSq_eq_norm_sq` is the correct lemma: normSq z = ‖z‖².
- The key difficulty in the Dahlquist barrier is the minimum principle for harmonic functions, which Mathlib has partially (`Complex.AbsMax` module) but applying it to the specific setting of rational functions on the unit circle requires significant scaffolding.
- An alternative approach using Fourier coefficients would need: (1) express cross-energy as a trig polynomial, (2) use non-negativity + integral = 0 ⟹ identically 0, (3) derive contradiction. This avoids the maximum principle but needs integration machinery.

## Suggested next approach
- Check Aristotle result for `order_ge_three_not_aStable_core` (project `79385b8d`).
- If Aristotle fails: try the integration approach — show ∫₀²π Re(G(e^{iθ})) dθ = 2π·Re(G(0)) using Poisson integral, then combine with G(1)=0 and Re(G)≥0 using the strong maximum principle from `Complex.AbsMax`.
- Alternative: axiomatize the minimum principle as a separate sorry lemma and prove everything else around it.
- Consider moving to a different target (Dahlquist equivalence theorem or Gauss-Legendre methods) if this sorry remains intractable.
