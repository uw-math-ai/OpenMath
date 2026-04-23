# Issue: true-slice second-order remainder bound still missing

## Blocker
`oddDownArrowRadiusPhaseEndpointSigns_on_trueSlice_of_neg_errorConst` is no
longer blocked by the coefficient identity. It is now blocked by the missing
theorem-local bound needed after subtracting both explicit terms in
`padeR_exp_neg_second_order_factorization`.

The live proof needs a statement of the form:

```lean
∃ K₂ δ₂ > 0, ∀ z : ℂ, ‖z‖ < δ₂ →
  ‖padeR n d z * exp (-z) -
      (1
        - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1)
        + (padeRExpNegSecondCoeff n d : ℂ) * z ^ (n + d + 2))‖ ≤
    K₂ * ‖z‖ ^ (n + d + 3)
```

or an equivalent theorem-local bound specialized to the true slice
`z = r * exp ((oddDownArrowRadiusPhaseCenter n d ± r) * I)`.

## Context
Cycle 351 closed the analytic identity
`padeR_exp_neg_second_coeff_identity`, so the exact degree-`n + d + 2`
coefficient is now available in `OpenMath/PadeOrderStars.lean`.

The remaining endpoint-sign theorem still contains the old local target:

```lean
K * r < (-padePhiErrorConst n d) * Real.sin (((↑(n + d) + 1) : ℝ) * r) / 2
```

That target comes from `padeR_exp_neg_local_bound`, which only controls the
remainder after subtracting the degree-`n + d + 1` term.

## What was tried
- Closed `padeR_exp_neg_second_coeff_identity` with the planned literal
  normalization proof.
- Re-checked the ready Aristotle bundles first; none supplied a usable live
  patch for the coefficient identity or the remaining endpoint/fixed-radius
  seams.
- Attempted to reuse `padeR_exp_neg_second_order_factorization` directly inside
  the endpoint proof.

## Why the attempted route failed
`padeR_exp_neg_second_order_factorization` only gives an existential remainder

```lean
∃ h, ∀ z, lhs z = z ^ (n + d + 3) * h z
```

which is enough for algebraic recombination, but not enough by itself for sign
control. The theorem does **not** provide boundedness or continuity of the
witness near `0`, so it cannot replace the old `K * r^(n+d+2)` estimate on its
own.

The old `hgapTarget` route is therefore still wrong: when `η = r`, both sides
are linear in `r`, so it reduces to a hidden constant comparison involving the
arbitrary `K` from `padeR_exp_neg_local_bound`.

## Possible solutions
- Prove a small second-order local norm bound adjacent to the endpoint theorem,
  either general in `z` or specialized to the true slice, by replaying the
  factorization ingredients with quantitative bounds:
  - second-order defect bound from polynomial divisibility,
  - second-order truncated-exponential bound,
  - quadratic bound for `exp (-z) / padeQ n d z - (1 - n/(n+d) z)`,
  - boundedness of `padeQ` and `(padeQ)⁻¹` near `0`.
- Alternatively, refactor the second-order factorization seam to expose an
  explicit bounded remainder witness rather than a bare existential witness.
