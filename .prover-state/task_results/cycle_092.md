# Cycle 92 Results

## Worked on
- BDF5 convergence theorem (DahlquistEquivalence.lean)
- BDF6 zero-stability: `bdf6_zeroStable` (MultistepMethods.lean)
- BDF6 convergence theorem (DahlquistEquivalence.lean)

## Approach

### BDF5 convergence
One-liner: `(dahlquist_equivalence bdf5).mpr ⟨bdf5_consistent, bdf5_zeroStable⟩`

### BDF6 zero-stability — `roots_in_disk`
Adapted Aristotle result (project 15827988). Key changes:
- Replaced `grind` with `field_simp` + `linear_combination -h1` for the w = 1/ξ substitution
- Replaced `norm_num +zetaDelta` with `push_neg` for handling `¬‖ξ‖ ≤ 1`
- Structure: factor 147·ρ(ξ) = (ξ-1)·Q₅(ξ), case split, then for Q₅(ξ)=0:
  - By contradiction assume ‖ξ‖ > 1
  - Set w = ξ⁻¹, show ‖w‖ < 1
  - Derive quintic in w via field_simp + linear_combination
  - Decompose w = a + bi with a² + b² < 1
  - Case b=0: nlinarith with polynomial witnesses
  - Case b≠0: extract imaginary equation, nlinarith with sq_nonneg witnesses

### BDF6 zero-stability — `unit_roots_simple`
Used conjugate elimination + Bézout identity approach:
- Factor same as roots_in_disk, ξ=1 case: check rhoCDeriv(1) ≠ 0 by norm_num
- Q₅(ξ)=0 with ‖ξ‖=1: use ξ·conj(ξ)=1, so conj(ξ)=ξ⁻¹
- Since coefficients are real integers, p(conj ξ) = congr_arg Star.star h1
- Substitute conj(ξ)=ξ⁻¹, multiply by ξ⁵ to get reciprocal polynomial
- Subtract: (ξ-1)·(palindromic quartic) = 0, but ξ≠1 (would make Q₅(1)≠0)
- Bézout identity: A(ξ)·Q₅(ξ) + B(ξ)·quartic(ξ) = 70761600
- linear_combination derives 70761600 = 0, norm_num closes

### BDF6 convergence
One-liner: `(dahlquist_equivalence bdf6).mpr ⟨bdf6_consistent, bdf6_zeroStable⟩`

## Result
SUCCESS — All three theorems proved. Both files compile sorry-free:
- `lake env lean OpenMath/MultistepMethods.lean` — OK (warnings only)
- `lake env lean OpenMath/DahlquistEquivalence.lean` — OK (warnings only)

## Dead ends
- `lake exe cache get` initially failed due to GLIBC_2.29 incompatibility with lean toolchain's
  clang. Fixed by setting `LEAN_CC=/usr/bin/gcc` and `LIBRARY_PATH`.
- The mathlib packages directory was incorrectly symlinked to an Aristotle workspace. Fixed by
  removing the symlink and re-running cache get.

## Discovery
- For BDF polynomial root proofs, the real/imaginary decomposition approach works for BOTH
  roots_in_disk (with a²+b²<1) and unit_roots_simple (with a²+b²=1). The conjugate elimination
  cascade is unnecessary.
- The `field_simp` + `linear_combination` pattern reliably replaces `grind` for algebraic
  manipulations involving inverses.
- `LEAN_CC=/usr/bin/gcc` with `LIBRARY_PATH="/tmp/lean4-toolchain/lib:/tmp/lean4-toolchain/lib/lean"`
  works around the GLIBC_2.29 issue with the lean toolchain's bundled clang.

## Suggested next approach
BDF family is now complete (BDF1-6: definitions, consistency, order, zero-stability, convergence).
Next targets from plan.md:
1. Definition of stiffness (Chapter 3)
2. Convergence theorem for one-step methods (Section 1.3)
3. Chapter 4 convergence theory
