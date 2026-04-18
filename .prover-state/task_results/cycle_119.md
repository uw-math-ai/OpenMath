# Cycle 119 Results

## Worked on
- Theorem 355F: A-stability criterion via order stars
- Theorem 355B: Arrow tangency directions (general statement)
- Metadata updates in lean_status.json

## Approach
### Theorem 355F
Three forms proved in OrderStars.lean:
1. `aStable_imagAxis_not_orderStarPlus` — core result: A-stable ⟹ iy ∉ 𝒜⁺(R)
2. `aStable_imagAxis_mem_minus_or_bdry` — positive form: iy ∈ 𝒜⁻ ∪ 𝒜⁰
3. `not_aStable_of_imagAxis_orderStarPlus` — contrapositive

All proofs use `orderStarPlus_imaginaryAxis` (|exp(-iy)|=1 reduces to |R(iy)| bound).

### Theorem 355B (general)
Four lemmas proved in OrderStars.lean:
1. `norm_ofReal_mul_exp_I` — ‖t·e^{iθ}‖ = t for t ≥ 0
2. `pow_ray_even_angle` — (t·e^{i·2kπ/(p+1)})^{p+1} = t^{p+1} (uses `Complex.exp_nat_mul_two_pi_mul_I`)
3. `arrow_up_of_neg_errorConst` — C < 0 ⟹ θ=2kπ/(p+1) is up-arrow direction
4. `arrow_down_of_pos_errorConst` — C > 0 ⟹ θ=2kπ/(p+1) is down-arrow direction

The general statement uses an explicit error-bound hypothesis:
`∀ z, ‖z‖ < δ₀ → ‖R(z)·e^{-z} - (1 - C·z^{p+1})‖ ≤ K·‖z‖^{p+2}`

Proofs use triangle inequality + choosing ε = min(δ₀, |C|/(2K)).

### Metadata
Updated lean_status.json for: thm:355F, thm:355B, def:356A, def:357A, def:357B.

## Result
SUCCESS — 7 new theorems, all fully proved (0 sorry), file compiles clean.

## Dead ends
None — the proofs were straightforward once the right Mathlib lemmas were identified.
Key Mathlib lemma: `Complex.exp_nat_mul_two_pi_mul_I` for the periodicity of exp.

## Discovery
- The explicit error-bound hypothesis for 355B avoids any need for `Asymptotics.IsBigO`.
  Future theorems can instantiate this with concrete Padé error bounds.
- The odd-angle cases (θ = (2k+1)π/(p+1)) are NOT yet formalized — they would
  need similar proofs but with cos((p+1)θ) = -1 instead of 1.
- `lt_div_iff₀` is the key lemma for division-based ε arguments in Lean.

## Suggested next approach
1. **Theorem 355B odd angles**: prove arrow directions at (2k+1)π/(p+1) — mirror of even-angle proofs
2. **Connect 355B to concrete methods**: instantiate the general statement for
   Forward/Backward Euler and Trapezoidal by providing the explicit error bound
3. **Theorem 357D** (BN-stable + irreducible ⟹ AN-stable): requires embedding
   complex scalar ODE into real dissipative system — textbook proof is missing,
   substantial formalization effort needed
4. **Theorem 355D** (counting inequality): requires arrow termination (355C), which
   needs path topology — still blocked
