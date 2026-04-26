# Cycle 429 Results

## Worked on
AB3 vector bridge refactor in `OpenMath/LMMAB3Convergence.lean`.

Rewired `LMM.ab3Vec_global_error_bound` through
`LMM.ab_global_error_bound_generic_vec` using `s = 3` and the AB3
coefficient tuple `(5/12, -16/12, 23/12)`.

## Approach
First triaged the ready Aristotle bundles from earlier cycles:

- `7ee03a6c...` targeted `LMMAB6VectorConvergence.lean`.
- `8268fb5e...` targeted `LMMABGenericConvergence.lean`.

Both live target files have zero sorries (`grep -c sorry` returned `0` for
each), so both bundles were rejected as stale. Their extracted files are also
not transplant-safe: they use standalone `import Mathlib` rewrites, and the
AB6 result still contains sorries.

Then followed the cycle-428 AB2 vector pilot:

1. Added `import OpenMath.LMMABGenericConvergence`.
2. Added `ab3GenericCoeff : Fin 3 -> R` with simp lemmas for entries
   `5/12`, `-16/12`, and `23/12`.
3. Added and proved the bridge lemmas:
   - `abLip_ab3GenericCoeff`
   - `ab3IterVec_eq_abIterVec`
   - `ab3VecResidual_eq_abResidualVec`
4. Replaced the inline proof body of `ab3Vec_global_error_bound` with a thin
   specialization of `ab_global_error_bound_generic_vec`.

The public theorem statement of `ab3Vec_global_error_bound` was not changed.
`OpenMath/LMMABGenericConvergence.lean` was untouched.

## Result
SUCCESS.

`abLip 3 ab3GenericCoeff L = (11 / 3) * L` was confirmed and proved in Lean,
so the generic constant matches the existing headline
`Real.exp ((11 / 3) * L * T)` exactly.

Manual proofs closed all bridge obligations:

- `abLip_ab3GenericCoeff`: expanded `Fin.sum_univ_three`, folded absolute
  values, and closed by `ring`.
- `ab3IterVec_eq_abIterVec`: strong induction on `n`; base cases unfold
  `abIterVec`, and the `k + 3` case uses `abIterVec_step`,
  `Fin.sum_univ_three`, IH at `k`, `k+1`, `k+2`, cast rewrites, `neg_smul`,
  and `abel`.
- `ab3VecResidual_eq_abResidualVec`: unfolded both residuals, expanded the
  `Fin 3` sum, aligned time coordinates, rewrote the negative coefficient
  with `neg_smul`, and reordered the module expression with `abel`.
- `hstart`: used `Finset.sup'_le`, `fin_cases j`, direct evaluation of
  `abIterVec` at indices `0`, `1`, `2`, and the three initial error bounds.

Aristotle batch for this cycle:

- `88b422b0...` (`abLip_ab3GenericCoeff`): COMPLETE. Produced a small
  `simp/norm_num` proof; local proof was already closed, so no transplant was
  needed.
- `9453fd80...` (`ab3IterVec_eq_abIterVec`): IN_PROGRESS at the single
  post-sleep refresh, 46%.
- `175dffa6...` (`ab3VecResidual_eq_abResidualVec`): COMPLETE_WITH_ERRORS.
  Extracted result used stub `OpenMath` files and was not live-compatible; no
  transplant.
- `23def74f...` (`hstart`): IN_PROGRESS at the single post-sleep refresh, 36%.
- `4fe3b5df...` (spare all-bridge pass): IN_PROGRESS at the single
  post-sleep refresh, 33%.

Verification:

- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/LMMAB3Convergence.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.LMMAB3Convergence`
- `grep -c sorry OpenMath/LMMAB3Convergence.lean` returned `0`.
- `lean_verify` on `LMM.ab3Vec_global_error_bound` reported only standard
  axioms (`propext`, `Classical.choice`, `Quot.sound`) and no source-scan
  warnings.

## Dead ends
The completed Aristotle residual job was not usable because it introduced
minimal stub `OpenMath` files in its extracted project. This repeats the
previous lesson that Aristotle bundles with stub infrastructure should not be
transplanted into the live tree.

Lean warns that `Fin.val_zero`, `Fin.val_one`, and `Fin.val_two` are unused
in three residual time-coordinate `simp` calls. They were kept deliberately,
matching the cycle-428 note that these Fin simp hints can be load-bearing
when the bridge shape is edited.

## Discovery
The cycle-427 generic vector scaffold is sufficient for AB3 without modifying
`OpenMath/LMMABGenericConvergence.lean`.

The AB3 effective Lipschitz constant is exactly
`(5 + 16 + 23) / 12 * L = (11 / 3) * L`, matching the existing
`ab3Vec_one_step_lipschitz` and headline global-error constant.

## Suggested next approach
Repeat the same bridge pattern for AB4 vector convergence in a separate
cycle. Keep the scope to one `s`-step chain, define the AB4 generic
coefficient tuple, prove the `abLip` equality first, then bridge iteration,
residual, and window-start bounds before replacing the headline proof body.
