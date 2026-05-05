# Cycle 138 Aristotle Submissions

Both jobs target Butcher §550 Theorem 550A (`thm:550A`).

## Job A — general-n
- **File**: `A_general_n_factorization.lean`
- **Project ID**: `7062c2a2-4a8b-4fae-b694-9355e06427a9`
- **Submitted at**: 2026-05-05 19:10:37 UTC
- **Target**: `doublyCompanionMatrix_det_factorization` for general `n`.
- **Approach hint**: eigenvalue density (Butcher's textbook path) or
  cofactor expansion / induction.

## Job B — n=2 specialization
- **File**: `B_n_two_factorization.lean`
- **Project ID**: `70f26d67-b37e-4eda-b946-64c9f4616612`
- **Submitted at**: 2026-05-05 19:10:38 UTC
- **Target**: `doublyCompanionMatrix_det_factorization_n_two`.
- **Approach hint**: direct `Matrix.det_fin_two` calculation with
  pointwise residue `-(α 0·β 1 + α 1·β 0)z³ - α 1·β 1·z⁴ = z³ · g(z)`.

## Polling

Per project policy: do NOT poll repeatedly. Check after 30 minutes.
If both fail, fall back on cycle 139 to manually close n=2 (~80 LOC of
direct calculation), and write a follow-up issue for general n.
