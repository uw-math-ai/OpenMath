# Cycle 040 Results

## Worked on
Closed both remaining sorrys in `bdf4_zeroStable` (BDF4 zero-stability) in `OpenMath/MultistepMethods.lean`.

## Approach

### `roots_in_disk` sorry (cubic roots have ‖ξ‖ ≤ 1)
Decomposed ξ = ⟨a, b⟩ into real/imaginary parts and proved by cases:

**Real case (b = 0):** The polynomial p(a) = 25a³-23a²+13a-3 satisfies:
- p(a) = (a-1)(25a²+2a+15) + 12 ≥ 12 for a ≥ 1
- p(a) = (a+1)(25a²-48a+61) - 64 ≤ -64 for a ≤ -1
Both quadratic factors have negative discriminant (always positive), so any real root has |a| < 1.

**Complex case (b ≠ 0):** From Im(p(ξ)) = 0:
- b·(75a²-25b²-46a+13) = 0, so b² = (75a²-46a+13)/25
- Substituting into Re(p(ξ)) = 0 yields: 1250a³-1150a²+427a-56 = 0
- Polynomial division: (100a²-46a-12)(50a-23) = 500-1250a
- From the cubic, a < 2/5 (since f(2/5) > 0 and f is strictly increasing: f' has Δ < 0)
- For a < 2/5: denominator (50a-23) < 0 and numerator (500-1250a) > 0
- So 100a²-46a-12 < 0, hence a²+b² = (100a²-46a+13)/25 < 1

### `unit_roots_simple` sorry (cubic has no unit circle roots)
Used conjugate elimination:
1. From ‖ξ‖ = 1: conj(ξ) = ξ⁻¹ (via normSq = 1 and mul_conj)
2. Conjugated p(ξ) = 0, substituted conj(ξ) = ξ⁻¹, multiplied by ξ³ (field_simp) → reversed equation
3. Linear combination of original and reversed eliminates ξ³: 32ξ²-67ξ+77 = 0
4. Same conjugation trick on quadratic → reversed quadratic: 77ξ²-67ξ+32 = 0
5. Subtraction: -45ξ²+45 = 0 → ξ² = 1
6. Substitute ξ² = 1 into original: 38ξ-26 = 0 → ξ = 13/19
7. But (13/19)² ≠ 1, contradiction.

## Result
**SUCCESS** — Both sorrys closed. `bdf4_zeroStable` is now fully sorry-free.

Verified with `lean_verify`: only standard axioms (propext, Classical.choice, Quot.sound).

## Dead ends
None for this cycle — both approaches worked on first attempt.

## Discovery
- **Real/imaginary decomposition** for polynomial root bounds: extract Im = 0 to get constraint on b², substitute into Re = 0 to get univariate equation in a, then use polynomial division to relate a²+b² to the constraint.
- **Conjugate elimination** for "no unit circle roots": conjugate + multiply by ξⁿ gives reversed polynomial. Linear combinations eliminate highest-degree terms, reducing degree. Iterate to get ξ² = 1, then check ξ = ±1.
- **`Complex.ext_iff`** is cleaner than `congr_arg Complex.im` for extracting real/imaginary parts.
- **`field_simp`** on hypotheses with ξ⁻¹ clears denominators nicely; follow with `linear_combination`.
- **`eq_inv_of_mul_eq_one_right`** directly gives conj(ξ) = ξ⁻¹ from ξ·conj(ξ) = 1.

## Suggested next approach
1. **BDF4 convergence**: Now that zero-stability is proved, `bdf4_convergent` can be added (consistency + zero-stability → convergence via Dahlquist equivalence, modulo the spectral bound sorry).
2. **SDIRK methods** (Section 4.3): Define singly-diagonally-implicit RK, prove L-stability.
3. **BDF5/BDF6**: Same pattern as BDF3/BDF4. The polynomial root analysis technique from this cycle generalizes — use real/imaginary decomposition for `roots_in_disk` and conjugate elimination for `unit_roots_simple`.
