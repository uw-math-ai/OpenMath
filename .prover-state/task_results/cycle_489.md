# Cycle 489 Results

## Worked on
BDF4 forced Lyapunov recurrence infrastructure in `OpenMath/BDFQuadraticLyapunov.lean`.

## Approach
First triaged the ready Aristotle directories from previous cycles. The live no-sorry check on `OpenMath/BDFQuadraticLyapunov.lean`, `OpenMath/LMMAB13Convergence.lean`, and `OpenMath/LMMAB13VectorConvergence.lean` had no matches. The BDF4 certificate bundles (`1d4383ca`, `8cfc273b`, `d680a869`, `b968aa9f`) were already reflected in the live BDF4 Lyapunov file; `e762fff3` was the known `import Mathlib`/stub-context variant; `f8bed1c4` was stale AB13-family work; `39de9f8e` was off-topic from another project.

Added the sorry-first BDF4 forced Lyapunov theorem surface, verified it compiled, then submitted five Aristotle scaffolds under `.prover-state/aristotle_scaffolds/cycle_489/`:

- `34db5bbf` (`bdf4_bilinear_algebra.lean`): COMPLETE. Used the returned `ring` proof for `bdf4CubicBil_self` and the `nlinarith` sum-of-squares proof for `bdf4CubicBil_step_ones_sq_le`.
- `f8378fc5` (`bdf4_forced_energy.lean`): IN_PROGRESS at the single post-sleep check. Proved the forced-energy bound manually.
- `23e02b40` (`bdf4_value_bound.lean`): COMPLETE_WITH_ERRORS but produced usable proofs for the exact `e(n+4)` decomposition, the stable-linear energy bound, and `bdf4_eIdx4_le_W_add_defect`.
- `81e7c4e8` (`bdf4_W_recurrence.lean`): COMPLETE. Used its proof pattern for `bdf4LyapW_succ_le_of_defect`.
- `63013abe` (`bdf4_one_step_abstract.lean`): COMPLETE_WITH_ERRORS but produced usable scalar algebra for solving the implicit defect inequality and the abstract one-step recurrence.

## Result
SUCCESS. Closed:

- `LMM.bdf4StableEnergy`, `LMM.bdf4LyapW`, and nonnegativity lemmas.
- `LMM.bdf4CubicBil`, `LMM.bdf4CubicBil_self`, and the fixed `(1,1,1)` Cauchy helper.
- `LMM.bdf4StableEnergy_forced_step_bound`.
- `LMM.bdf4LyapW_succ_le_of_defect`.
- `LMM.bdf4_eIdx4_le_W_add_defect`.
- `LMM.bdf4LyapW_one_step_error_bound`.

Verified:

```bash
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/BDFQuadraticLyapunov.lean
rg -n '^\s*sorry\b|:= by\s*sorry|by\s+sorry' OpenMath/BDFQuadraticLyapunov.lean
```

The Lean check passed and the no-sorry check returned no matches.

## Dead ends
The focused Aristotle forced-energy job did not finish by the required single check after the 30-minute sleep. I did not poll repeatedly. The manual proof closed by extracting the scalar square estimate into two private helpers:

- `bdf4CubicBil_step_ones_abs_le`
- `bdf4CubicQuad_forced_step_le`

These avoid increasing `maxHeartbeats` and keep the sqrt step modular.

## Discovery
The loose constant works cleanly because
`((25/12)^2) * (6583/960) ≤ 36`. Combining the fixed-direction bilinear Cauchy estimate with the homogeneous step identity gives the forced stable-energy inequality without a general matrix framework.

The trajectory theorem bridges directly to `bdf4_one_step_lipschitz` after unfolding `bdf4RecDefect` and normalizing the `Nat.cast_add` time indices.

## Suggested next approach
Use `bdf4LyapW_one_step_error_bound` as the next prerequisite for the full BDF4 global theorem. The next useful lemmas are the planned initial-window bound `bdf4LyapW_initial_bound` and the readout bound `bdf4_eIdx3_le_W`, then a Gronwall assembly using the existing BDF4 local residual bound.
