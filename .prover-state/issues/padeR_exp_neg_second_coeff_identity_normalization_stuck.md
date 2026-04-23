# Issue: `padeR_exp_neg_second_coeff_identity` normalization stuck

## Blocker
The local helper
`OpenMath/PadeOrderStars.lean` theorem
`padeR_exp_neg_second_coeff_identity`
still resists the final rational-normalization step needed to remove its `sorry`.

## Context
The theorem is:

```lean
private theorem padeR_exp_neg_second_coeff_identity
    (n d : ℕ) (hm : 0 < n + d) :
    expTaylorExpNegSecondCoeff (n + d) +
        padeDefectSecondCoeff n d -
        (((1 / (((n + d + 1).factorial : ℂ))) - (padePhiErrorConst n d : ℂ)) *
          ((n : ℂ) / (n + d : ℂ))) =
      (padeRExpNegSecondCoeff n d : ℂ) := by
  sorry
```

This is now the only remaining analytic helper on the second-order seam. The
surrounding theorems
`padeDefect_sub_second_factorization`,
`expTaylor_exp_neg_second_order_factorization`, and
`padeR_exp_neg_second_order_factorization`
are already in place and compile.

## What was tried
- Proved the identity in a standalone `lean_run_code` snippet by introducing a
  local `m := n + d`, rewriting `1 / (m + 1)!` as `(m + 2) / (m + 2)!`, then
  using `field_simp` and `ring`.
- Ported that proof structure into `OpenMath/PadeOrderStars.lean` directly.
- Rephrased the proof with local aliases for the defect and truncated-exponential
  coefficients.
- Rewrote `m : ℂ = (n : ℂ) + d` before the final `field_simp`.
- Tried both unfolding and not unfolding `padeRExpNegSecondCoeff` locally.

## Possible solutions
- Reintroduce the standalone proof as a separate tiny lemma with the coefficient
  expressions written literally, then `simpa` back to the named definitions.
- Split the identity into two lemmas:
  1. cancellation of the factorial terms,
  2. simplification of the remaining `padePhiErrorConst` term to
     `padeRExpNegSecondCoeff`.
- Avoid rewriting through the named private defs inside the main theorem body;
  prove a literal coefficient equality first, then only use the defs in the
  final `simpa`.
