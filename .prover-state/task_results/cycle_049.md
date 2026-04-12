# Cycle 049 Results

## Worked on
- Lobatto IIIB 3-stage method formalization (new file `OpenMath/LobattoIIIB3.lean`)
- New order theorem `HasOrderGe4_of_B4_C1_D2` in `OpenMath/Collocation.lean`

## Approach

### New order theorem (Collocation.lean)
Added `HasOrderGe4_of_B4_C1_D2`: B(4) ∧ C(1) ∧ D(2) → order ≥ 4.

This is needed because Lobatto IIIB satisfies C(1) and D(2) but NOT C(2) or C(3),
so neither `HasOrderGe4_of_B4_C3` nor `HasOrderGe4_of_B4_C2_D1` apply.

Key proof technique: pointwise ring equalities + `simp_rw` + Finset structural lemmas:
```lean
have pw : ∀ j, LHS j = simplified j := by intro j; ring
simp_rw [pw, Finset.sum_sub_distrib, ← Finset.mul_sum, hB2, hB4]; ring
```

Also added `SatisfiesD.mono` for monotonicity of the D simplifying assumption.

### Lobatto IIIB 3-stage (LobattoIIIB3.lean)
Complete sorry-free formalization with 17 theorems:

1. **Butcher tableau definition** with rational coefficients (last column zero)
2. **Basic properties**: consistency, non-negative weights, not stiffly accurate, not explicit, zero last column
3. **Simplifying assumptions**: B(4), C(1), NOT C(2), D(1), D(2), D(3), NOT D(4)
4. **Order 4** via the new `HasOrderGe4_of_B4_C1_D2` theorem
5. **NOT B(5)** (Simpson's rule limitation)
6. **Stability**: A-stable via GL2 Padé (2,2) identity, NOT L-stable (R(z) → 1)
7. **NOT algebraically stable** (M₃₃ = −1/36 < 0)

## Result
SUCCESS — Both files compile sorry-free. 17 theorems in LobattoIIIB3.lean, 2 new declarations in Collocation.lean.

## Dead ends
- Previous cycle left broken uncommitted changes to Collocation.lean. Had to revert and rewrite.
- Direct `rw [Finset.mul_sum, ← Finset.sum_sub_distrib]` chains fail because the goal shape
  doesn't match (e.g., `1/2 * (∑ - ∑)` is not a bare sum). The pointwise ring + simp_rw pattern
  is much more robust.
- `simp [rkLobattoIIIB3] at this` for the stiffly accurate negation reduced to `2/3 = 5/6`
  but didn't close it; needed explicit `norm_num at this`.

## Discovery
- The `HasOrderGe4_of_B4_C1_D2` theorem completes the trio of order-4 theorems:
  - `HasOrderGe4_of_B4_C3` (Gauss/Lobatto IIIA)
  - `HasOrderGe4_of_B4_C2_D1` (Lobatto IIIC)
  - `HasOrderGe4_of_B4_C1_D2` (Lobatto IIIB)
  These cover all combinations of C(q) ∧ D(r) with q+r ≥ 3 needed for order 4.
- The Lobatto III 3-stage family is now complete: IIIA, IIIB, IIIC all formalized.

## Suggested next approach
- **3-stage Gauss-Legendre** (order 6): involves √15, significantly more challenging.
  Would need irrational collocation points and a new order theorem for order 6.
- **SDIRK3** (3-stage, order 3, L-stable): involves irrational λ from cubic equation.
- **Radau IA methods**: another important family not yet formalized.
- **Adjointness theorem**: IIIA + IIIB = 𝟙·bᵀ could be formalized as a relationship theorem.
