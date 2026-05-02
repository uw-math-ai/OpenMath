# Cycle 645 Results

## Worked on

`OpenMath/LMMAsGLM.lean`, §521 LMM-as-GLM BDF charpoly bridge:

- `toGLM_stabilityMatrixPYHF_eq_zero_of_bdf`
- `toGLM_stabilityMatrix_charpoly_of_bdf`

## Approach

Followed the cycle plan directly. First added a sorry scaffold for the
two target declarations and checked that the statements typechecked with
`lake env lean OpenMath/LMMAsGLM.lean`.

Then proved the upper-right block vanishing entrywise. After `ext j l`,
the matrix-zero RHS needed to be changed to scalar zero:

```lean
change toGLM_stabilityMatrixPYHF m z j l = (0 : ℂ)
```

In the last-row branch, `Fin.castSucc l ≠ Fin.last s` follows from
`(l : ℕ) < s`; the BDF hypothesis then rewrites
`m.β (Fin.castSucc l)` to zero and `ring_nf` closes the residual
complex expression.

The headline proof uses the existing block decomposition:

```lean
rw [toGLM_stabilityMatrix_eq_fromBlocks m z]
rw [Matrix.charpoly_reindex]
rw [toGLM_stabilityMatrixPYHF_eq_zero_of_bdf m z hbdf]
rw [Matrix.charpoly_fromBlocks_zero₁₂]
rw [toGLM_stabilityMatrixPHF_charpoly_of_bdf m z hbdf]
```

## Result

SUCCESS. Both target theorems landed sorry-free.

The exact Mathlib block-zero charpoly lemma used was:

```lean
Matrix.charpoly_fromBlocks_zero₁₂
```

This is the upper-right-zero shape:
`(fromBlocks M₁₁ 0 M₂₁ M₂₂).charpoly =
M₁₁.charpoly * M₂₂.charpoly`.

## Dead ends

No Lean proof dead end. The only adjustment was the expected
`Pi.zero_apply` mismatch in the prerequisite: after matrix extensionality,
the RHS initially appeared as `0 j l`; changing the goal to scalar zero
before unfolding resolved it cleanly.

Aristotle usage: I attempted to submit the project directory after the
sorry scaffold was added, asking Aristotle to fill the two new sorries.
The MCP call timed out after 120 seconds while packaging/submitting the
directory, so no Aristotle result was available to incorporate.

## Discovery

- `Matrix.charpoly_fromBlocks_zero₁₂` is available and works directly
  once the `PYHF` block is rewritten to zero.
- `Matrix.charpoly_reindex` resolves the
  `toGLM_stabilityBlockEquiv s : Fin s ⊕ Fin s ≃ Fin (2 * s)`
  transport without any additional helper lemmas.
- No helper lemma beyond the planned
  `toGLM_stabilityMatrixPYHF_eq_zero_of_bdf` was needed.
- The file remains below the line cap: `OpenMath/LMMAsGLM.lean` is
  2454 lines after this cycle.

## Suggested next approach

Continue from the new factorisation:

```lean
LMM.toGLM_stabilityMatrix_charpoly_of_bdf
```

Cycle 646 can start the separate bridge between
`(toGLM_stabilityMatrixPY m z).charpoly` and the appropriate
polynomial-valued BDF/LMM stability factor. Do not fold that bridge into
the block factorisation proof; cycles 642 and 643 showed that the
polynomial-valued auxiliary is a separate multi-cycle task.

## Sorry count

`grep -c sorry OpenMath/LMMAsGLM.lean` -> `0`.

`lake env lean OpenMath/LMMAsGLM.lean` exits 0.
