# Issue: `padeR_exp_neg_second_order_factorization` elaboration/heartbeat blow-up

## Blocker
The next live theorem
`OpenMath/PadeOrderStars.lean:2354`
(`padeR_exp_neg_second_order_factorization`)
appears mathematically assembled, but the in-file proof repeatedly hits elaboration heartbeat limits when the defect factorization, truncated-exponential factorization, and denominator-side Padé factorization are combined into one theorem body.

## Context
The current target is:

```lean
private theorem padeR_exp_neg_second_order_factorization
    (n d : ℕ) (hm : 0 < n + d) :
    ∃ h : ℂ → ℂ, ∀ z : ℂ,
      padeR n d z * exp (-z) -
          (1
            - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1)
            + (padeRExpNegSecondCoeff n d : ℂ) * z ^ (n + d + 2)) =
        z ^ (n + d + 3) * h z := by
  sorry
```

The intended ingredients are already present:
- `PadeAsymptotics.padeDefect_poly_coeff_succ`
- `PadeAsymptotics.padeDefect_poly_coeff_succ_succ`
- `expTaylor_exp_neg_leading_term`
- `exp_neg_sub_linear_factorization`
- `exp_neg_div_padeQ_linear_factorization`

## What was tried
- Built a theorem-local proof that factors the Padé defect through degree `n + d + 2`, factors `expTaylor (n + d) z * exp (-z)` through degree `n + d + 2`, and then combines both with the existing denominator-side linear factorization.
- Moved the same proof into a separate helper file `OpenMath/PadeSecondOrder.lean` to reduce local context pressure.
- Simplified the final degree-`n + d + 2` coefficient to `padeRExpNegSecondCoeff n d` with explicit factorial rewrites and `field_simp`.

## Possible solutions
- Split the theorem into small private lemmas inside `PadeOrderStars.lean`:
  1. a defect-side second-order factorization lemma,
  2. a truncated-exponential second-order factorization lemma,
  3. a coefficient identity lemma for the `z^(n+d+2)` term.
- Keep each lemma stated with explicit local definitions instead of large `let`-bound expressions inside one theorem body.
- Delay the final `ring`/`field_simp` normalization until after the existential factorization lemmas are already established, so the elaborator does not normalize the full product expansion at once.
