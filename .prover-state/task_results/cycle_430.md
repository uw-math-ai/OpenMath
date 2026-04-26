# Cycle 430 Results

## Worked on
AB4 vector bridge refactor in `OpenMath/LMMAB4Convergence.lean`.

Rewired `LMM.ab4Vec_global_error_bound` through
`LMM.ab_global_error_bound_generic_vec` using `s = 4` and the AB4
coefficient tuple `(-9/24, 37/24, -59/24, 55/24)`.

## Approach
First triaged the three completed Aristotle bundles from cycle 429:

- `88b422b0…` (COMPLETE) targeted `abLip_ab3GenericCoeff`, already closed
  in `LMMAB3Convergence.lean`. Rejected as stale.
- `23def74f…` (COMPLETE_WITH_ERRORS) and `175dffa6…` (COMPLETE_WITH_ERRORS)
  both rewrote five live files including `LMMABGenericConvergence.lean`,
  `LMMTruncationOp.lean`, `AdamsMethods.lean`, and a partial bundle
  `MultistepMethods.lean`. Verified `grep -c sorry` returned `0` for the
  first three and `3` for `MultistepMethods.lean`. Per the standing rule,
  any rewrite of a sorry-free live file is a stub replacement; rejected.
  The `MultistepMethods.lean` portion was an existing-state file with three
  pre-existing sorries unrelated to AB3, so the bundle was not transplant
  material. Rejected.

Then followed the cycle-429 AB3 vector pilot template:

1. Added `import OpenMath.LMMABGenericConvergence`.
2. Added `ab4GenericCoeff : Fin 4 → ℝ` with simp lemmas for entries
   `-9/24`, `37/24`, `-59/24`, `55/24`.
3. Added and proved the bridge lemmas:
   - `abLip_ab4GenericCoeff`
   - `ab4IterVec_eq_abIterVec`
   - `ab4VecResidual_eq_abResidualVec`
4. Replaced the inline proof body of `ab4Vec_global_error_bound` with a
   thin specialization of `ab_global_error_bound_generic_vec` at `s = 4`,
   `p = 4`.

The public theorem statement of `ab4Vec_global_error_bound` was not changed.
`OpenMath/LMMABGenericConvergence.lean` was untouched.

## Result
SUCCESS.

`abLip 4 ab4GenericCoeff L = (20 / 3) * L` was confirmed and proved in
Lean, so the generic constant matches the existing headline
`Real.exp ((20 / 3) * L * T)` exactly.

Manual proofs closed all bridge obligations:

- `abLip_ab4GenericCoeff`: expanded `Fin.sum_univ_four`, folded absolute
  values, and closed by `ring`.
- `ab4IterVec_eq_abIterVec`: strong induction on `n`; base cases
  `0, 1, 2, 3` unfold both definitions, and the `k + 4` case uses
  `ab4IterVec_succ_succ_succ_succ`, `abIterVec_step`, `Fin.sum_univ_four`,
  four IH applications at `k`, `k+1`, `k+2`, `k+3`, cast rewrites,
  `neg_smul` for the two negative coefficients (-9/24 and -59/24), and
  `abel`. Note that `Fin.val_three` does not exist in Mathlib at the head
  of this branch, so a local `have hval3 : ((3 : Fin 4) : ℕ) = 3 := rfl`
  was used in place of the missing simp lemma.
- `ab4VecResidual_eq_abResidualVec`: unfolded both residuals, expanded the
  `Fin 4` sum, aligned time coordinates, rewrote the two negative
  coefficients with `neg_smul`, and reordered the module expression with
  `abel`.
- `hstart`: used `Finset.sup'_le`, `fin_cases j`, direct evaluation of
  `abIterVec` at indices `0, 1, 2, 3`, and the four initial error bounds.

Aristotle batch (defensive) for this cycle:

- `9c25564e-9424-4433-9a59-a1fd3d19469b` (`AB4Bridge.lean` covering all
  three bridge lemmas, plus the `abLip` identity): IN_PROGRESS at 1% at the
  single post-submission check. The local manual proofs already closed,
  so this run is purely backup; no transplant attempted.

Verification:

- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/LMMAB4Convergence.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.LMMAB4Convergence`
- `grep -c sorry OpenMath/LMMAB4Convergence.lean` returned `0`.
- `lean_verify` on `LMM.ab4Vec_global_error_bound` reported only standard
  axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Dead ends
`Fin.val_three` is not a real Mathlib lemma at the live toolchain;
attempted as a simp argument it failed with `Unknown constant`. Replaced
with a local `rfl` `have` in the inductive step and a local `rfl`-and-
`push_cast` chain in the residual time-coordinate alignment.

A small leftover linter complaint: the `simp [Fin.val_zero]`,
`simp [Fin.val_one]`, `simp [Fin.val_two]` calls inside
`ab4VecResidual_eq_abResidualVec` are flagged as unused simp arguments.
The cycle-428/429 task results both noted these `Fin.val_*` hints can be
load-bearing under small edits to the bridge shape, so they were kept on
purpose; they generate warnings but no errors.

## Discovery
The cycle-427 generic vector scaffold continues to be sufficient at `s = 4`
without modifying `OpenMath/LMMABGenericConvergence.lean`.

The AB4 effective Lipschitz constant is exactly
`(9 + 37 + 59 + 55) / 24 * L = 160/24 * L = 20/3 * L`, matching the
existing `ab4Vec_one_step_lipschitz` and headline global-error constant.

Coefficient ordering convention (read off `ab4IterVec`'s recurrence, not
the textbook formula):
`α 0 = -9/24` (oldest sample, coefficient of f_n),
`α 1 =  37/24` (coefficient of f_{n+1}),
`α 2 = -59/24` (coefficient of f_{n+2}),
`α 3 =  55/24` (newest sample, coefficient of f_{n+3}).
This matches the AB3 convention `(α 0, α 1, α 2) = (5/12, -16/12, 23/12)`.

## Suggested next approach
Repeat the same bridge pattern for AB5 vector convergence in cycle 431:

- Define `ab5GenericCoeff : Fin 5 → ℝ` with entries
  `(251/720, -1274/720, 2616/720, -2774/720, 1901/720)` (oldest → newest).
- Prove `abLip_ab5GenericCoeff L = (8821/720) * L` (sum of absolute
  values).
- Mirror the cycle-428/429/430 induction template using
  `Fin.sum_univ_five` and IH applications at `k`, `k+1`, `k+2`, `k+3`,
  `k+4`.
- Specialize `ab_global_error_bound_generic_vec` at `s = 5`, `p = 5`.

If any `Fin.val_n` constant is missing in Mathlib (similar to
`Fin.val_three` here), substitute with a local `rfl` `have`.
