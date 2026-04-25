# Cycle 384 Results

## Worked on
Adams–Bashforth 5-step (AB5) — full pipeline:
- Definition `adamsBashforth5 : LMM 5` in `OpenMath/MultistepMethods.lean`
- `adamsBashforth5_consistent`
- `adamsBashforth5_explicit`
- `adamsBashforth5_order_five`
- `adamsBashforth5_zeroStable`
- `adamsBashforth5_convergent` in `OpenMath/DahlquistEquivalence.lean`
- Marked AB5 `[x]` in `plan.md` Section 1.2 and updated Current Target to AM5.

## Approach
Mechanical transplant of the AB4 pipeline (cycle 382), adapted to s = 5:
- Coefficients per planner: α = ![0, 0, 0, 0, -1, 1],
  β = ![251, -1274, 2616, -2774, 1901, 0] / 720.
- Sum unrolling: switched to `Fin.sum_univ_succ` (s + 1 = 6) instead of
  `Fin.sum_univ_five` used by AB4 (s + 1 = 5), matching the BDF5 precedent.
- Zero-stability factorization: ξ⁵ - ξ⁴ = ξ⁴(ξ - 1); used
  `pow_eq_zero_iff (n := 4)` instead of AB4's `(n := 3)`.
- Convergence corollary: one-line `dahlquist_equivalence` wrapper, identical
  to AB4 template.

## Result
SUCCESS. All three required compiles pass clean:
- `lake env lean OpenMath/MultistepMethods.lean` — no errors.
- `lake build OpenMath.MultistepMethods` — `Build completed successfully (8027 jobs).`
- `lake env lean OpenMath/DahlquistEquivalence.lean` — no errors.

## Sign-check outcome (per cycle 383 protocol)
Planner-supplied β signs were **correct**. No flip needed.
- ρ′(1) = 4·(-1) + 5·1 = 1.
- σ(1) = (251 - 1274 + 2616 - 2774 + 1901 + 0) / 720 = 720 / 720 = 1.
- ρ′(1) = σ(1) ✓; consistency closed by `simp + norm_num`, no manual flip.

## Leading error constant at q = 6
Unnormalized order condition value:
- ∑ jⁿ αⱼ = (-1)·4⁶ + 1·5⁶ = -4096 + 15625 = 11529.
- ∑ jⁿ⁻¹ βⱼ = (-1274 + 32·2616 + 243·(-2774) + 1024·1901) / 720
            = (-1274 + 83712 - 674082 + 1946624) / 720
            = 1354980 / 720.
- V₆ = 11529 - 6 · 1354980/720 = (11529·720 - 8129880)/720
     = (8300880 - 8129880)/720 = 171000/720 = 237.5.

Nonzero ⇒ AB5 has classical order exactly 5, as expected.
The classical leading error constant is C₆ = V₆ / 6! = 237.5 / 720 = 95/288.

## Zero-stability transplant
The AB4 zero-stability proof transplanted directly with **only two index
adjustments**:
1. `Fin.sum_univ_five` → `Fin.sum_univ_succ`.
2. `pow_eq_zero_iff (n := 3)` → `pow_eq_zero_iff (n := 4)`.

The structural skeleton (`linear_combination hξ`, `mul_eq_zero.mp`, branch on
ξ = 0 vs. ξ = 1, `norm_num` for ρ′(1) = 1) is otherwise identical.

## Aristotle usage
None this cycle. As anticipated by the strategy, no obligation blocked
manually — every component closed first try (modulo one trivial `; norm_num`
removal where `simp` already closed `m.rho 1 = 0`).

## Dead ends
One micro-issue: initial `simp [...]; norm_num` on the `rho 1 = 0` half of
`adamsBashforth5_consistent` triggered "no goals to be solved" — the all-zero
α prefix means `simp` alone closes the sum. Removed the trailing `norm_num`
on that half. Same pattern as the existing AB4 (which also has bare `simp`
on the `rho 1 = 0` half).

## Discovery
For s ≥ 5, `Fin.sum_univ_succ` is the right unrolling lemma (no
`Fin.sum_univ_six` exists in Mathlib at this version). BDF5 already uses this
pattern. Future AM5 / AB6 / BDF6 work should follow.

## Suggested next approach
**AM5** is the obvious next mechanical extension (planner already flagged):
- α = ![0, 0, 0, 0, -1, 1] (same as AB5).
- β = ![27/1440, -173/1440, 482/1440, -798/1440, 1427/1440, 475/1440]
  (textbook AM5 coefficients; verify signs against `adamsMoulton4` ordering
  and consistency identity before committing — repeat the cycle 383/384
  protocol).
- Implicit order-6 method.
- Zero-stability transplants verbatim from AB5 (same α).

After AM5, the natural Chapter 1.2 frontier becomes BDF-extensions or higher
Adams families; both are mechanical given the established templates.
