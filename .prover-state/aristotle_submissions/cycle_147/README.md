# Cycle 147 Aristotle submission

## Project ID
`9643742d-aac9-4e57-9f7a-2ba69a5f25ee` (submitted 2026-05-06T00:49:04 UTC)

## Goal

Close `doublyCompanionMatrix_det_factorization_n_five` — the n=5
specialization of Butcher Theorem 550A — as the fifth concrete-n
axiom-clean stepping stone.

## Files

- `n_five_factorization.lean` — self-contained snippet defining
  `doublyCompanionMatrix`, `alphaPoly`, `betaPoly`, the verbatim
  cycle 145 n=4 closed proof template, and the n=5 sorry'd target.

## Recipe (cycle 145 n=4 template extended)

1. **Step 1 — `h_diff`** Pointwise rewrite the residue as
   `z^6 * inner_polynomial`. Three sub-steps:
   - (i) Reduce `doublyCompanionMatrix α β` to an explicit `!![...]` 5×5 matrix
     via `ext i j; fin_cases i <;> fin_cases j <;> simp [doublyCompanionMatrix]`.
   - (ii) Reduce `1 - z • X` to an explicit 5×5 `!![...]` via the same
     `ext + fin_cases + simp` cascade with `first | (simp; ring) | simp`.
   - (iii) Expand the 5×5 determinant via `Matrix.det_succ_row_zero`
     to obtain five 4×4 sub-determinants, then expand each 4×4 via
     `Matrix.det_succ_row_zero` again, then use `Matrix.det_fin_three`
     for the 3×3 minors. Close with
     `simp [Fin.sum_univ_five, Fin.sum_univ_four,
            Matrix.det_succ_row_zero (n := 3), Matrix.det_fin_three,
            alphaPoly, betaPoly, ...]; ring`.

2. **Step 2 — `IsBigO.of_bound`** Apply with the constant
   `‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖`, where the convolution coefficients
   are
   - `a := -(α 0·β 4) - α 1·β 3 - α 2·β 2 - α 3·β 1 - α 4·β 0`
   - `b := -(α 1·β 4) - α 2·β 3 - α 3·β 2 - α 4·β 1`
   - `c := -(α 2·β 4) - α 3·β 3 - α 4·β 2`
   - `d := -(α 3·β 4) - α 4·β 3`
   - `e := -(α 4·β 4)`
   then `Metric.eventually_nhds_iff` with radius `1`, then bound
   `‖a + y·b + y²·c + y³·d + y⁴·e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖`
   by a four-step `norm_add_le` cascade and four
   `mul_le_of_le_one_left` sub-bounds.

## Notes

Aristotle has been brittle on this ladder (n=2 took ≥30 min, general-n
stalled at 6%). The manual closure is being attempted in parallel
during the 30-minute sleep window. Whichever lands first wins,
preferring the manual proof on tie for provenance.
