# Issue: Padé recurrence factorial sums in `OpenMath/Pade.lean`

## Blocker
The remaining sorrys are the two coefficient recurrences
`padeQ_succ_left` and `padeP_succ_right`.

Both theorems are true with the coefficient
`q / ((p + q) (p + q + 1))` for `Q` and
`p / ((p + q) (p + q + 1))` for `P`.
The original cycle strategy stated the simpler factor `1 / (p + q + 1)`,
but that formula is false for the existing explicit Padé pairs.

## Context
Current statements in `OpenMath/Pade.lean`:

```lean
theorem padeQ_succ_left (p q : ℕ) (hq : 0 < q) (z : ℂ) :
    padeQ (p + 1) q z =
      padeQ p q z + (q : ℂ) * z / (((p + q : ℕ) : ℂ) * (p + q + 1 : ℂ)) * padeQ p (q - 1) z := by
  sorry

theorem padeP_succ_right (p q : ℕ) (hp : 0 < p) (z : ℂ) :
    padeP p (q + 1) z =
      padeP p q z - (p : ℂ) * z / (((p + q : ℕ) : ℂ) * (p + q + 1 : ℂ)) * padeP (p - 1) q z := by
  sorry
```

Sanity checks against explicit formulas:
- `Q_21 = Q_11 + z/6 * Q_10`
- `P_12 = P_11 - z/6 * P_01`

## What was tried
- Added general `padeP` and `padeQ` definitions and verified the corrected recurrence constants from the explicit `(1,1)`, `(2,1)`, `(1,2)`, `(2,2)` pairs.
- Tried direct `simp`/`norm_num`/`field_simp` on the unfolded sum identities.
- Submitted Aristotle jobs `ff9ee1b4` and `d61b6f0f` specifically for the two recurrence theorems.
- Aristotle completed the easier related jobs, but these two recurrence jobs remained `IN_PROGRESS` after the required 30-minute wait.

## Possible solutions
- Prove the identities coefficientwise after rewriting the shifted `z * padeQ p (q - 1)` and `z * padeP (p - 1) q` sums with `Finset.sum_range_succ`.
- Introduce an auxiliary coefficient lemma on factorial ratios, e.g.
  `a_{p+1,q,j} = a_{p,q,j} - p/((p+q)(p+q+1)) * a_{p-1,q,j-1}` and its `Q` analogue.
- Re-express the coefficients with binomial coefficients before clearing denominators; the recurrence constants become more transparent in that form.
