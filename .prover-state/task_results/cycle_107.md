# Cycle 107 Results

## Worked on
- `OpenMath/Pade.lean`
- Theorem 352E setup: introduced the Padé self-adjointness defect `padeV`
- Right-edge and left-edge Padé formulas needed to probe the intended `V` recurrence
- Aristotle batch jobs for five Padé edge lemmas

## Approach
- Checked the queued cycle-106 Aristotle result directories first. They only contained approximation-order work that is already reflected in the current sorry-free `Pade.lean`; nothing new was mergeable for cycle 107.
- Added the self-adjointness defect
  `padeV l m z = padeP l m z * padeP l m (-z) - padeQ l m z * padeQ l m (-z)`,
  which matches the actual condition `R(z) * R(-z) = 1`.
- Proved the consistent edge lemmas:
  - `padeP_zero_left`
  - `padeV_eval_zero`
  - `padeV_zero_right`
  - `padeV_zero_left`
  - `padeQ_one_right`
  - `padeP_one_right`
  - `padeV_one_right`
  - `padeV_diagonal_zero`
- Wrote a structured blocker report after checking the planner's printed `V` formula and recurrence against small Padé instances.
- Submitted five Aristotle jobs:
  - `ac6d73fd-4362-47c0-b9e6-f19c79572872` (`01_padeP_zero_left.lean`)
  - `ef558ef3-2196-4141-a885-ab0e4a20b976` (`02_padeV_zero_left.lean`)
  - `2ecad18f-ff83-486a-8872-ffcf00179772` (`03_padeQ_one_right.lean`)
  - `5ebaa6b1-f1e2-4787-92df-02785858e9d5` (`04_padeP_one_right.lean`)
  - `f647dbeb-5551-4fa6-9a7a-c1f2c669e43a` (`05_padeV_one_right.lean`)
- Per the required single harvest pass, refreshed those jobs once. At harvest time none had finished:
  - `IN_PROGRESS`: `ac6d73fd`, `ef558ef3`, `5ebaa6b1`
  - `QUEUED`: `2ecad18f`, `f647dbeb`

## Result
PARTIAL

Cycle 107 made concrete progress in `Pade.lean` and kept the project sorry-free, but the target recurrence from the planner was not formalized because its printed statement is inconsistent with the current Padé normalization. The self-adjointness defect and its edge lemmas are now in place, and the mismatch is documented in a dedicated issue file.

## Dead ends
- The planner's written defect
  `N(z) * D(-z) - N(-z) * D(z)`
  does not vanish on diagonal Padé approximants:
  - `(1,1)` gives `2 z`
  - `(2,2)` gives `z * (z^2 + 12) / 6`
- Reusing the planner's recurrence shape with the corrected self-adjointness defect also fails immediately:
  - for `(l,m) = (0,2)`, the corrected defect is `-z^4 / 4`
  - the printed RHS becomes `0`

## Discovery
- The mathematically correct defect for self-adjointness in this codebase is
  `P(z) * P(-z) - Q(z) * Q(-z)`, not the planner's cross-term expression.
- `padeQ_diagonal_eq_padeP_neg` gives the diagonal vanishing theorem for the corrected defect directly.
- The right edge `m = 1` is now explicit in closed form, which should be useful once the textbook statement of Theorem 352E is corrected.

## Suggested next approach
- Re-check Iserles p.259 and recover the exact theorem statement for Theorem 352E, including the book's normalization/indexing for `V_{l,m}`.
- Once that statement is corrected, derive the recurrence against the existing `padeP_succ_right` / `padeQ_succ_left` lemmas or add the missing recurrence in the textbook's indexing first.
- If Aristotle later completes the five queued edge-lemma jobs, harvest them and compare against the now-merged local proofs for any shorter proof terms.
