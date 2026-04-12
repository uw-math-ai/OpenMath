# Cycle 048 Results

## Worked on
- Lobatto IIIC 3-stage method formalization (new file `OpenMath/LobattoIIIC3.lean`)
- New order theorem `HasOrderGe4_of_B4_C2_D1` in `OpenMath/Collocation.lean`

## Approach

### New order theorem (Collocation.lean)
The existing `HasOrderGe4_of_B4_C3` requires C(3), which Lobatto IIIC does not satisfy.
Formalized `HasOrderGe4_of_B4_C2_D1`: B(4) ∧ C(2) ∧ D(1) → order ≥ 4.

Key proof ideas:
- order4c: swap sums, apply D(1) to get ∑ bⱼcⱼ²(1-cⱼ) = 1/3 - 1/4 = 1/12
- order4d: use C(2) to collapse inner sum, then reduce to order4c

This theorem is based on Hairer-Norsett-Wanner Theorem IV.5.1.

### Lobatto IIIC 3-stage (LobattoIIIC3.lean)
Complete sorry-free formalization of the Lobatto IIIC 3-stage method with:

1. **Butcher tableau definition** with rational coefficients
2. **Basic properties**: consistency, non-negative weights, stiffly accurate, not explicit, constant first column
3. **Simplifying assumptions**: B(4), C(2), NOT C(3), D(1), D(2)
4. **Order 4** via the new `HasOrderGe4_of_B4_C2_D1` theorem
5. **NOT B(5)** (Simpson's rule limitation)
6. **Stability function**: R(z) = (24+6z)/(24-18z+6z²-z³)
7. **Denominator nonzero** for Re(z) ≤ 0 (two-case proof: real axis positivity + complex conjugate substitution)
8. **A-stability**: |R(z)| ≤ 1 for Re(z) ≤ 0 (via normSq inequality with nlinarith)
9. **Stiff decay**: R(x) → 0 as x → -∞ (degree argument)
10. **L-stability**: A-stable + stiff decay
11. **Algebraic stability**: quadratic form (v₀-2v₁+v₂)²/36 ≥ 0

## Result
SUCCESS — Both files compile sorry-free. 23 theorems in the new file.

## Dead ends
- Component-wise complex computation with `simp [Complex.pow_succ, Complex.pow_zero]` fails.
  Needed helper lemmas `complex_sq` and `complex_cube` for ⟨x,y⟩² and ⟨x,y⟩³.
- Manual factorization of |D|²-|N|² attempted but abandoned; `nlinarith` with suitable
  hint terms closed the A-stability goal directly.

## Discovery
- `nlinarith` can close degree-6 polynomial positivity for A-stability of 3-stage methods
  given enough hint terms (sq_nonneg of various monomials + mul_nonneg with (-x) ≥ 0).
- The `HasOrderGe4_of_B4_C2_D1` theorem is reusable for any method satisfying B(4), C(2), D(1).
  This applies to Lobatto IIIC and potentially other methods.
- `-48/ε` and `-(48/ε)` are syntactically different in Lean 4; linarith needs help via
  `neg_div_neg_eq` or explicit intermediate steps.

## Suggested next approach
- **Lobatto IIIB 3-stage**: rational tableau, all zeros in third column. Completes the family.
- **3-stage Gauss-Legendre** (order 6): involves √15, more challenging.
- **SDIRK3** (3-stage, order 3, L-stable): involves irrational λ from cubic equation.
