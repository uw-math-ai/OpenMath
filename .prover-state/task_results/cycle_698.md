# Cycle 698 Results

## Worked on
§521 Step C.14 — `D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_plus_residual`
in `OpenMath/LMMAsGLM/StabilityCharpoly.lean`.

## Approach
Followed the strategy verbatim. Added the new theorem immediately after
`activeStabilityPolyPoly_eq_stabilityPolyPoly_add_correction`
(end of the prior block at line 1531). Proof is the planner-prescribed
two rewrites + `ring`:

```lean
rw [D_mul_toGLM_charpoly_eq_X_pow_mul_active_plus_residual m hz hs,
    activeStabilityPolyPoly_eq_stabilityPolyPoly_add_correction m z]
ring
```

## Result
SUCCESS. The new theorem
```
theorem D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_plus_residual
    (m : LMM s) {z : ℂ}
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) (hs : 0 < s) :
    Polynomial.C (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ)) *
        (m.toGLM.stabilityMatrix z).charpoly =
      (Polynomial.X : Polynomial ℂ) ^ s * m.stabilityPolyPoly z
        + (Polynomial.X : Polynomial ℂ) ^ s *
            ( Polynomial.C z *
                ∑ l : Fin s,
                  Polynomial.C
                      (((m.β l.castSucc : ℝ) : ℂ) -
                        ((m.β (Fin.last s) : ℝ) : ℂ) *
                          ((m.α l.castSucc : ℝ) : ℂ)) *
                    Polynomial.X ^ (l : ℕ) )
        - ( rowYQuot m * (Polynomial.X : Polynomial ℂ) ^ s *
              Polynomial.C (z * ((m.β (Fin.last s) : ℝ) : ℂ))
          + ( rowFAlphaPoly m +
                (toGLM_stabilityMatrixPY m 0).charpoly *
                  rowFBetaPoly m ) *
              Polynomial.C z ) := by
  rw [D_mul_toGLM_charpoly_eq_X_pow_mul_active_plus_residual m hz hs,
      activeStabilityPolyPoly_eq_stabilityPolyPoly_add_correction m z]
  ring
```
is sorry-free.

Verification:
- `lake env lean OpenMath/LMMAsGLM/StabilityCharpoly.lean`: zero
  output (success, no warnings).
- `lake env lean OpenMath/LMMAsGLM.lean`: zero output.

The file now sits at 1571 lines (previously 1533), still well under
the 3000-line cap mentioned in the strategy.

## Dead ends
None this cycle. The two-rewrite + `ring` recipe closed on the first
attempt exactly as the planner predicted.

## Discovery
The cycle 696 bridge composes cleanly with the cycle 690 active-form
headline under a single `ring`. No need for `mul_add` distribution or
`linear_combination` fallback — the polynomial-algebra outermost layer
(both sides are sums/products of `Polynomial.C (…)`-coefficient terms
times `X^k`, with no `Polynomial.C` interior to be cracked) is exactly
the regime where `ring` works on `Polynomial ℂ`.

## Suggested next approach
Step C.15: the residual-cancellation / spurious-root-killing argument
over the unit disk. With Step C.14 in hand, the textbook
`stabilityPolyPoly` is now exposed as the leading factor of
`X^s * stabilityPolyPoly`, and the remaining work for
`LMM.toGLM_isAStable_iff` is to show that

  - the `correction` summand `X^s * C(z) * ∑ C(β_l - β_last·α_l) X^l`
    contributes only roots of magnitude `≤ 1` for `Re z ≤ 0`
    (or, more usefully, that it is dominated by the residual on the
    unit circle and so does not change the root count there); and
  - the residual
    `rowYQuot * X^s * C(z β_last) + (rowFAlphaPoly + PY(0).charpoly *
       rowFBetaPoly) * C z` accounts for the difference between the
    GLM charpoly's `2s − 1` non-trivial roots and the `s` LMM roots.

The optional stretch goal — a degree bound for the correction sum —
would be a natural cycle 699 sub-deliverable: the per-summand bound
`Polynomial.C (…) * X^l` has degree `≤ l < s`, summed via
`Polynomial.degree_sum_le`. I did not attempt it this cycle to keep
the deliverable tight, per the strategy's "stretch (only if … with
time left)" framing.
