# Cycle 380 Results

## Worked on
Added the Adams–Bashforth 3-step (AB3) linear multistep method to the
formalization, per the cycle 380 strategy.

## Approach
Followed the AB2/AM2 templates to land the AB3 deliverables in one pass:

1. `noncomputable def adamsBashforth3 : LMM 3` in
   `OpenMath/MultistepMethods.lean`, with α = ![0, 0, -1, 1] and
   β = ![5/12, -16/12, 23/12, 0]. Placed next to `adamsMoulton2`.
2. `adamsBashforth3_consistent` — `simp [LMM.rho/sigma, ..., Fin.sum_univ_four]`
   plus `norm_num`, mirroring `adamsBashforth2_consistent`.
3. `adamsBashforth3_explicit` — `simp [LMM.IsExplicit, adamsBashforth3,
   Fin.last]`.
4. `adamsBashforth3_order_three` — same shape as `adamsBashforth2_order_two`
   with `Fin.sum_univ_four` and `interval_cases q` running over 0,1,2,3.
   `orderCondVal 4 = 9/4 ≠ 0` is the nonzero witness.
5. `adamsBashforth3_zeroStable` — characteristic polynomial
   `ρ(ξ) = ξ³ - ξ² = ξ²(ξ - 1)`. After `simp [LMM.rhoC, ..., Fin.sum_univ_four]`,
   `linear_combination` recovers the factored form. The `ξ² = 0` branch is
   handled with `pow_eq_zero_iff` (giving ξ = 0, interior to disk so the
   simple-root condition is vacuous since `‖0‖ = 0 ≠ 1`). The `ξ = 1` branch
   matches AB2 line-for-line.
6. `adamsBashforth3_convergent` in `OpenMath/DahlquistEquivalence.lean` — direct
   one-liner via `dahlquist_equivalence`.
7. `plan.md` updated under §1.2 with the new bullet right after the AM2 entry.

## Result
SUCCESS. All five new declarations compile; `lake env lean
OpenMath/MultistepMethods.lean` and `lake env lean
OpenMath/DahlquistEquivalence.lean` both pass with no errors or sorry's.
`lake build OpenMath.MultistepMethods` completed in 8027 jobs.

## Aristotle batch
Skipped. Per CLAUDE.md the Aristotle batch is for closing sorry's; the
sorry-first scaffold collapsed under direct AB2-mirroring proofs on the first
attempt, so there were no sorry's left to delegate. Saving the free compute
for a cycle that genuinely needs it.

## Dead ends
None — proofs landed first try by following the AB2 pattern. The only minor
tweak: the AB2 root-disk argument uses `mul_eq_zero` on `ξ * (ξ - 1) = 0`,
but AB3's polynomial factors as `ξ² * (ξ - 1) = 0`, so the `ξ² = 0` branch
needs `pow_eq_zero_iff` to extract `ξ = 0`. Otherwise structurally identical.

## Discovery
The AB-family pattern is mechanical for any `LMM s` with
`α = (0,...,0,-1,1)`: the characteristic polynomial is
`ξ^s - ξ^{s-1} = ξ^{s-1}(ξ - 1)`, with simple root at 1 and an
(s-1)-fold root at 0. The zero-stability proof scales by replacing
`Fin.sum_univ_three` with `Fin.sum_univ_(s+1)` and using `pow_eq_zero_iff`
for the multiplicity-(s-1) zero root branch. AB4 / AB5 should follow the
same template.

## Suggested next approach
Two natural next targets (all from §1.3):
- **Adams–Moulton 3-step (AM3)**: `LMM 3`, β = (1/24, -5/24, 19/24, 9/24),
  α same as AB3 (so same ρ). Order 4, implicit. The zero-stability proof is
  literally `adamsBashforth3_zeroStable` since ρ is identical.
- **Adams–Bashforth 4-step (AB4)**: `LMM 4`, β = (-9/24, 37/24, -59/24, 55/24, 0),
  α = (0, 0, 0, -1, 1). Order 4, explicit. Zero stability follows the same
  ξ³(ξ-1) = 0 template with `Fin.sum_univ_five`.

Either is a one-cycle drop-in. After landing one or two more Adams methods,
the planner should consider lifting the pattern into a general lemma:
"any LMM with α = (0, ..., 0, -1, 1) is zero-stable", which would close all
future Adams-family zero-stability obligations in one go.
