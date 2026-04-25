# Cycle 397 Results

## Worked on

Split the local truncation-operator section out of
`OpenMath/MultistepMethods.lean` into the new module
`OpenMath/LMMTruncationOp.lean`, then extended that module with
translation-invariance and shifted-polynomial vanishing.

## Approach

- Moved the complete `## Local Truncation Operator (Iserles Section 1.2 / eqn (2.6))`
  block, originally lines 2706--2979 of `OpenMath/MultistepMethods.lean`, into
  `OpenMath/LMMTruncationOp.lean`.
- Added `import OpenMath.MultistepMethods` to the split file and
  `import OpenMath.LMMTruncationOp` to `OpenMath.lean` so the default library
  target includes the new module.
- Scanned `OpenMath/*.lean` for uses of the moved API. No downstream module
  besides the new split file referenced `truncationOp` names, so no imports
  were needed in `AdamsMethods.lean`, `DahlquistEquivalence.lean`, or `BDF.lean`.
- Used the sorry-first workflow for the two new theorems, verified the skeleton
  compiled, then closed both manually.
- Aristotle: no jobs submitted. This follows the cycle-specific Aristotle
  policy because the split was mechanical and both Task B proofs closed directly
  after the sorry-first skeleton check.

## Result

SUCCESS.

- `OpenMath/MultistepMethods.lean` now has 2704 lines after removing the
  trailing blank separator line left by the split.
- `OpenMath/LMMTruncationOp.lean` now has 305 lines after the moved block plus
  the two new theorems.
- Added `LMM.truncationOp_translation`.
- Added `LMM.truncationOp_polyShift_eq_zero_of_HasOrder`.
- Updated `plan.md` to reference the split file and mark the
  translation-invariance work as complete.
- Verification passed with `lake env lean OpenMath/LMMTruncationOp.lean`,
  `lake env lean OpenMath/MultistepMethods.lean`, full `lake build`, and
  `lean_verify` on both new theorem declarations.

## Dead ends

None. The direct translation proof closed with `unfold truncationOp; simp
[add_comm]`. The shifted-polynomial theorem closed by instantiating
`truncationOp_translation` with the shifted polynomial pair, rewriting the
target to evaluation at `0`, and simplifying `((u + t) - t)` by
`add_sub_cancel_right`.

## Discovery

The theorem skeleton in the cycle strategy instantiated
`truncationOp_translation` with the unshifted polynomial pair, but the clean
Lean proof instantiates it with the shifted pair
`u => sum k, a k * (u - t)^k`. Then the theorem's right-hand side is exactly
the target and its left-hand side simplifies to the existing origin theorem.

`rg` for `sorry` under `OpenMath/*.lean` only finds documentation/comment
mentions, not live Lean `sorry` terms.

## Suggested next approach

Continue from `OpenMath/LMMTruncationOp.lean` toward the smooth Taylor/local
truncation-error bridge for Iserles Section 1.2 eqn (2.6). Keep this in the
split file unless shared base LMM infrastructure is required.
