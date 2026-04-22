# Cycle 317 Results

## Worked on
- Triaged the ready Aristotle artifact for `padeR_nonneg_sign_of_downArrowDir`.
- Formalized the forward-Euler up-arrow truth test at `n = 1`, `d = 0`,
  `θ = 3 * Real.pi / 4`.
- Refuted the global Padé up-arrow zero-cos / strict-sign bridge.
- Audited the live `PadeRUpArrowSignBridge` seam after the counterexample landed.

## Approach
- Compared the ready Aristotle file
  `.prover-state/aristotle_results/668a42b6-6e2d-4a6b-b04c-4e28a867ec23/padeR_nonneg_sign_of_downArrowDir_aristotle/padeR_nonneg_sign_of_downArrowDir.lean`
  against the live theorem in `OpenMath/PadeOrderStars.lean`.
- Added the new `3π/4` forward-Euler skeleton in `OpenMath/PadeOrderStars.lean`
  with temporary `sorry`s, verified the file compiled, and split the new work
  into five Aristotle targets under `.prover-state/aristotle/cycle_317/`.
- Submitted the five Aristotle jobs:
  - `eb91a7e4-88a7-4034-bd92-713bdfc44d97`
  - `2456b5cd-c7fc-4b6e-8325-bb718db01b0f`
  - `b7232c18-e60f-4c38-bcac-47e790917925`
  - `0fe90928-29d1-419c-8c10-b68228fbbc8b`
  - `8400a088-090d-4146-aa1b-1fb094da08b3`
- Proved the live theorems manually by mirroring the cycle-316 `π/4`
  down-arrow argument:
  - exact zero-cos identity at `3π/4`,
  - exact norm-square formula
    `‖(1 + z) * exp (-z)‖^2 = (1 - √2 t + t^2) * exp (√2 t)`,
  - derivative formula
    `((1 - √2 t + t^2) * exp (√2 t))' = √2 * t^2 * exp (√2 t)`,
  - strict monotonicity on `(0, ∞)`,
  - `IsUpArrowDir (padeR 1 0) (3 * Real.pi / 4)`,
  - the two refutations
    `¬ PadeRUpArrowZeroCosExclusion 1 0` and
    `¬ PadeRUpArrowSignBridge 1 0`.

## Result
- SUCCESS: `OpenMath/PadeOrderStars.lean` now contains:
  - `padeR10_three_pi_div_four_zeroCos`
  - `padeR10_three_pi_div_four_isUpArrowDir`
  - `not_padeRUpArrowZeroCosExclusion_one_zero`
  - `not_padeRUpArrowSignBridge_one_zero`
- SUCCESS: the symmetric up-arrow truth test falsifies the global strict
  up-arrow bridge exactly as the cycle strategy predicted.
- SUCCESS: the seam audit shows `PadeRUpArrowSignBridge` is now only used as:
  its definition, the new `¬ ... 1 0` counterexample, and the honest
  zero-cos-exclusion recovery theorem `padeR_upArrowSignBridge_of_zeroCosExclusion`.
- SUCCESS: verified with
  `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeOrderStars.lean`
  and
  `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.PadeOrderStars`.
- SUCCESS: added
  `.prover-state/issues/pade_both_arrow_sign_bridges_fail_on_forward_euler_zero_cos_rays.md`
  recording that both global strict Padé arrow-sign bridges already fail on
  forward-Euler zero-cos exact rays.

## Dead ends
- The ready Aristotle artifact was rejected. It is not a strict improvement:
  the live theorem `padeR_nonneg_sign_of_downArrowDir` is already present with
  the current interface, and the artifact only replays the same contraposition
  argument inside a stale `Cycle315Aristotle` namespace.
- The fresh cycle-317 Aristotle batch did not produce anything mergeable during
  this cycle. At the single status check, all five jobs were still `IN_PROGRESS`.

## Discovery
- The cycle-316 falsification of the strict down-arrow bridge is not an
  isolated asymmetry. The symmetric forward-Euler ray at `3π/4` also gives a
  zero-cos exact ray that is nevertheless a genuine up-arrow direction.
- Therefore both global strict Padé arrow-sign bridges already fail in the
  smallest Padé case `padeR 1 0`.
- The honest outer boundary for the 355D / 355E seam is theorem-local
  zero-cosine exclusion, not a global Padé-wide sign bridge.

## Suggested next approach
- Do not try to revive a global `PadeRUpArrowSignBridge` or
  `PadeRDownArrowSignBridge`.
- Keep downstream wrappers on the current honest interface:
  theorem-local zero-cos exclusion hypotheses where strict sign is genuinely
  needed.
- After the Aristotle jobs finish, harvest them only if one of them offers a
  genuinely smaller drop-in proof for the new `3π/4` helper lemmas; otherwise
  discard them and continue the theorem-local outer-wrapper audit.
