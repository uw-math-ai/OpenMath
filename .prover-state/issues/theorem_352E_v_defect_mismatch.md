# Issue: Theorem 352E V-defect statement mismatches current Padé normalization

## Blocker
The planner's written target for Theorem 352E uses

`V_{l,m}(z) = N_{l,m}(z) * D_{l,m}(-z) - N_{l,m}(-z) * D_{l,m}(z)`,

described as the defect measuring self-adjointness of `R_{l,m}(z) = N_{l,m}(z) / D_{l,m}(z)`.
But for self-adjointness we need

`R(z) * R(-z) = 1  <->  N(z) * N(-z) = D(z) * D(-z)`.

So the actual defect of self-adjointness is

`N_{l,m}(z) * N_{l,m}(-z) - D_{l,m}(z) * D_{l,m}(-z)`.

The planner's cross-term expression does not vanish on diagonal Padé approximants, so it
cannot be the intended quantity.

## Context
Concrete counterexamples with the current `padeP` / `padeQ` normalization:

1. Planner's cross-term defect on the diagonal:
   - `(l,m) = (1,1)`: `P_{1,1}(z) * Q_{1,1}(-z) - P_{1,1}(-z) * Q_{1,1}(z) = 2 z`
   - `(l,m) = (2,2)`: the same expression is `z * (z^2 + 12) / 6`
   - Therefore the cross-term defect is not zero on the diagonal.

2. Correct self-adjointness defect:
   - `(l,m) = (1,1)`: `P_{1,1}(z) * P_{1,1}(-z) - Q_{1,1}(z) * Q_{1,1}(-z) = 0`
   - This matches `Q_{s,s}(z) = P_{s,s}(-z)` and the expected symmetry of diagonal Padé approximants.

3. The planner's recurrence also fails for the corrected defect if copied unchanged:
   - For `(l,m) = (0,2)`, the corrected defect is `-z^4 / 4`
   - The planner RHS becomes `(1 - z / 2) * V_{1,1}(z) + (1/4) * z^2 * V_{0,0}(z) = 0`
   - So the printed recurrence is not compatible with the current normalization either.

## What was tried
- Added the mathematically correct self-adjointness defect
  `padeV l m z = padeP l m z * padeP l m (-z) - padeQ l m z * padeQ l m (-z)`
  to `OpenMath/Pade.lean`.
- Proved the consistent edge lemmas:
  - `padeV_eval_zero`
  - `padeV_zero_right`
  - `padeV_zero_left`
  - `padeV_diagonal_zero`
  - `padeQ_one_right`
  - `padeP_one_right`
  - `padeV_one_right`
- Checked the planner's recurrence shape symbolically on small indices; it fails immediately.

## Possible solutions
1. Re-check Iserles Theorem 352E against the textbook page and recover the exact definition of `V_{l,m}` used there.
2. Verify whether the textbook uses a different normalization or indexing convention for `N_{l,m}` and `D_{l,m}` than the current `padeP` / `padeQ`.
3. Once the correct theorem statement is identified, derive the recurrence from the existing `padeP_succ_right` / `padeQ_succ_left` infrastructure or add the missing pair recurrence in the textbook's indexing.
