# Cycle 659 Results

## Worked on
Butcher §521 LMM-to-GLM A-stability bridge infrastructure in
`OpenMath/LMMAsGLM.lean`, targeting `toGLM_V_active_charpoly`.

## Approach
Followed the cycle plan sorry-first: added the block-form and charpoly
targets, checked the sorry skeleton, then closed the local proof holes with
Lean LSP guidance.

Aristotle was attempted after the sorry-first skeleton, but both a directory
submission and a smaller prompt submission timed out before returning a
project id, so there were no Aristotle results to poll or incorporate.

## Result
SUCCESS.

Added:

- `toGLM_stabilityMatrixPHFY_zero`
- `toGLM_V_active_lift_eq_fromBlocks_zero`
- `toGLM_V_active_charpoly`

The final block form differs slightly from the planner's provisional shape:
only the lower-left `PHFY` block vanishes at `z = 0`. The upper-right `PYHF`
block is generally nonzero because it contains the structural
`β (Fin.castSucc l)` entries from `Vℂ`. The characteristic polynomial still
factors by `Matrix.charpoly_fromBlocks_zero₂₁`.

Verification: `lake env lean OpenMath/LMMAsGLM.lean` passed after closing the
new Lean proofs; a final direct Lean check with the same Lake search path also
passed after the stretch theorem was removed.

## Dead ends
The planned stretch theorem `toGLM_V_active_charpoly_explicit` was attempted
but removed because the first direct proof made the targeted file check much
slower. It is not needed for the cycle headline deliverable.

## Discovery
The cycle-658 issue note saying both off-diagonal blocks vanish at `z = 0`
is too strong. The correct statement is:

```lean
Vℂ =
  reindex e e (fromBlocks (PY 0) (PYHF 0) 0 (PHF 0))
```

This is enough for the block-triangular charpoly factorization.

## Suggested next approach
For the next Step 3 follow-up, specialize
`toGLM_stabilityMatrixPY_charpoly` and `toGLM_stabilityMatrixPHF_charpoly`
at `z = 0` in a carefully staged lemma, avoiding broad `simp`, to derive an
explicit closed form for `toGLM_V_active_charpoly`.
