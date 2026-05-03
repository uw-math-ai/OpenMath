# Cycle 694 Results

## Worked on
§521 Step C.13a — `toGLM_stabilityMatrixPY_zero_charpoly_eq`, the
closed form for `(toGLM_stabilityMatrixPY m 0).charpoly` (the PY block
charpoly specialised at `z = 0`). Active file
`OpenMath/LMMAsGLM/StabilityCharpoly.lean`.

## Approach
Followed the strategy recipe verbatim. Inserted the public theorem
between `charpoly_residual_degree_lt` and `end LMM`. The proof:

1. `hz : (1 : ℂ) - 0 * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0` discharged by `simp`.
2. `rw [toGLM_stabilityMatrixPY_charpoly m 0 hz]` to reduce to the
   `1 / (1 - 0 * β_last)`-scaled sum.
3. `congr 1; refine Finset.sum_congr rfl (fun l _ => ?_); congr 2`
   peels `X^s -`, the sum, and `Polynomial.C (·) * X^l` down to a
   scalar identity inside `Polynomial.C`.
4. `field_simp` (with `ring`) closed it.

## Result
SUCCESS — `toGLM_stabilityMatrixPY_zero_charpoly_eq` lands sorry-free.
Both `lake env lean OpenMath/LMMAsGLM/StabilityCharpoly.lean` and
`lake env lean OpenMath/LMMAsGLM.lean` compile cleanly with zero
errors and zero warnings.

## Dead ends
The strategy's bare `field_simp` did not close on its own — it left
the residual `↑(-m.α l.castSucc) = ↑(-m.α l.castSucc) * (1 - 0 * ↑(m.β (Fin.last s)))`
because `field_simp` cleared the divisor but did not simplify
`0 * _` to `0`. Appending `ring` closes it. (The strategy also listed
`simp` followed by `ring` as an alternative ending; `field_simp; ring`
is essentially that.)

## Discovery
`field_simp` on a `Polynomial.C` argument leaves a multiplicative
residual that `ring` finishes. The denominator `1 - 0 * β_last` is
fine for `field_simp` once `hz` is in scope, but `field_simp` is not
a normalizer — pair it with `ring` for these specialisations.

## Suggested next approach
The helper is ready to power cycle 695's
`activeStabilityPolyPoly_eq_stabilityPolyPoly_add_correction` bridge.
Concretely, since `activeStabilityPolyPoly` is pinned to
`D • PY(0).charpoly` (cycle 692), and `PY(0).charpoly` now has a
known closed form, the bridge identity
`activeStabilityPolyPoly = stabilityPolyPoly + (correction)`
reduces to comparing the new closed form against
`stabilityPolyPoly`'s definition coefficient by coefficient via a
`Fin.sum_univ_castSucc` split, as planned in the cycle 693 strategy
Step 1.
