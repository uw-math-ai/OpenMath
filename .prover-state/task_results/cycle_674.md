# Cycle 674 Results

## Worked on
§521 Step 1 — `toGLM_stabilityMatrixPHF_zero_charmatrix_adjugate_last_col`:
closed-form evaluation of column ⟨s-1, _⟩ of the adjugate of
`(toGLM_stabilityMatrixPHF m 0).charmatrix` as the geometric power vector
`(1, X, X², …, X^{s-1})`. This is the structural foundation needed to
extract an `X^s` factor from the general (non-BDF) `RowF` in the §521
LMM-as-GLM stability charpoly machinery.

## Approach
Implemented in `OpenMath/LMMAsGLM/StabilityCharpoly.lean` (Step C.6 section).

Architecture: rather than trying to expand the cofactor sum directly, define
an explicit candidate matrix and prove it satisfies the right-inverse-of-det
identity, then conclude by cancellation in the integral domain
`Polynomial ℂ`.

1. `toGLM_stabilityMatrixPHF_zero_apply` — rewrite of the PHF entries when
   the second-argument scalar is 0 (collapses to the strict upper-shift
   pattern `[(l : ℕ) = (j : ℕ) + 1]`).

2. `toGLM_stabilityMatrixPHF_zero_charmatrix_apply` — corresponding entries
   of the charmatrix: `X` on the diagonal, `-1` on the strict upper shift,
   `0` elsewhere.

3. `phfZeroCharmatrixAdjExplicit` — explicit candidate adjugate:
   `if (i : ℕ) ≤ (j : ℕ) then X^(s-1-(j-i)) else 0`. Upper-triangular
   with column `s-1` equal to `X^i`.

4. `phfZeroCharmatrixAdjExplicit_last_col` — closed form for the last
   column.

5. `adjugate_eq_of_mul_eq_det_smul` — abstract helper: if `A * B = det A • 1`
   and `det A ≠ 0` in an integral domain, then `A.adjugate = B`. Proved by
   left-multiplying by `adjugate A` and cancelling `det A`.

6. `phfZeroCharmatrix_mul_adjExplicit` — the main mul identity. Each entry
   reduces to a sum with at most two non-zero terms (`k = i` and
   `k = ⟨(i : ℕ) + 1, _⟩`), eliminated via `Finset.sum_eq_single` (last row)
   or `Finset.sum_eq_add` (general). Diagonal collapses to `X * X^(s-1) =
   X^s`; the two off-diagonal contributions telescope using
   `s - 1 - (j - i') = (s - 1 - (j - i)) + 1` and `pow_succ'`.

7. `toGLM_stabilityMatrixPHF_zero_charmatrix_adjugate_eq` — apply the
   abstract helper using `toGLM_stabilityMatrixPHF_zero_charpoly` for the
   determinant.

8. `toGLM_stabilityMatrixPHF_zero_charmatrix_adjugate_last_col` — the
   headline target, immediate from steps 4 + 7.

## Result
SUCCESS. File compiles cleanly under `lake env lean
OpenMath/LMMAsGLM/StabilityCharpoly.lean` (875 lines total, +266 from
cycle 672).

## Dead ends
- Initial attempt at a direct `simp_rw` based formulation of
  `toGLM_stabilityMatrixPHF_zero_eq` ran into `fun j l ↦ if l = j + 1 …`
  being parsed as `ℕ → ℕ → ℂ`, not a `Matrix (Fin s) (Fin s) ℂ`. Replaced by
  the pointwise `_apply` lemma.
- `ext i j` on a matrix equality over `Polynomial ℂ` started destructuring
  polynomial coefficients (introducing `n✝`); had to use
  `refine Matrix.ext (fun i j => ?_)` to stop at the matrix-entry level.
- Used `pow_succ'` (with arg order `a * a^n = a^(n+1)`) so the
  `X * X^(s-1)` factor on the diagonal of `phfZeroCharmatrix_mul_adjExplicit`
  collapses without an awkward `1 + (s-1)` rewrite.
- Got the direction of `s - 1 - (j - i')` vs `(s - 1 - (j - i)) + 1`
  backwards on the first try; correct relation is the latter, since
  `i' = i + 1` makes `(j - i')` *smaller*, hence `s - 1 - (j - i')` larger.

## Discovery
The integral-domain cancellation pattern (define candidate B, prove
`A * B = det A • 1`, cancel `det A`) is a clean and reusable substitute for
expanding cofactors entry-by-entry whenever an explicit candidate is
available. The helper `adjugate_eq_of_mul_eq_det_smul` is general (lives at
the top of the new section) and could be promoted to
`OpenMath/Helpers/BlockAdjugate.lean` if reused.

## Suggested next approach
Step 2 of the §521 program: lift the new closed form into the general
(non-BDF) `RowF` and extract the `X^s` factor in the headline charpoly
identity. Concretely, take the `RowF` row-vector against
`(toGLM_stabilityMatrixPHF m 0).charmatrix.adjugate`, peel off the last
column with `toGLM_stabilityMatrixPHF_zero_charmatrix_adjugate_last_col`,
and collect the geometric `Σ a_i X^i` factor. The result should mirror the
BDF specialisation already proved in §521 Step C.5.
