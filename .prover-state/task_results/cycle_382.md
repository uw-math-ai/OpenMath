# Cycle 382 Results

## Worked on
Adams–Bashforth 4-step (AB4): definition, consistency, explicit, order 4,
zero-stability, and convergence (via Dahlquist equivalence). Mechanical
addition mirroring AB3 from cycle 380.

## Approach
Followed the planner's strategy verbatim:

1. Added `adamsBashforth4 : LMM 4` to `OpenMath/MultistepMethods.lean` with
   coefficients
   - α = ![0, 0, 0, -1, 1]
   - β = ![-9/24, 37/24, -59/24, 55/24, 0]
2. Proved `adamsBashforth4_consistent` with `Fin.sum_univ_five` + `norm_num`.
3. Proved `adamsBashforth4_explicit` (β at last index is 0).
4. Proved `adamsBashforth4_order_four` by `interval_cases q` on the first
   five order conditions and a closing `norm_num` for `q = 5`.
5. Proved `adamsBashforth4_zeroStable` by literal copy of the AB3 proof,
   factoring `ρ(ξ) = ξ⁴ - ξ³ = ξ³(ξ - 1)` and using
   `pow_eq_zero_iff (n := 3)` for the triple zero root.
6. Added `adamsBashforth4_convergent` to
   `OpenMath/DahlquistEquivalence.lean` via `dahlquist_equivalence`.

Aristotle was not used: the AB3/AM3 templates closed manually on the first
attempt, exactly as the strategy anticipated.

## Result
SUCCESS.
- `lake env lean OpenMath/MultistepMethods.lean` compiles cleanly.
- `lake env lean OpenMath/DahlquistEquivalence.lean` compiles cleanly.
- `plan.md` §1.2 has the AB4 bullet marked `[x]`.

## Dead ends
None. The mechanical template ported with no modifications other than the
expected index/range bumps (`Fin.sum_univ_four → Fin.sum_univ_five`,
`pow_eq_zero_iff (n := 2) → (n := 3)`, one extra `interval_cases` branch).

## Discovery
The order-4 verification for AB4 ran inside default `maxHeartbeats` with the
standard `interval_cases q <;> simp [...] <;> norm_num` pattern, identical to
AB3 and BDF4. No special handling was needed.

## Suggested next approach
Exactly as the cycle 382 planner foresaw: AM4 by the same template
(β last index nonzero ⇒ implicit, order 5, ρ factorization same as AM3).
After that, the deeper stalled issues (Theorem 358A reverse direction,
odd up-arrow connected support, Radau IA family, "Theorem 359D" textbook
lookup) are still the medium-term blockers and need dedicated cycles each.
