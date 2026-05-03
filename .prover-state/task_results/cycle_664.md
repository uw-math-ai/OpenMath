# Cycle 664 Results

## Worked on
Butcher §521 Step C.3 — the block-adjugate infrastructure behind the
past-`h*f` scalar adjugate-row entry in the LMM-as-GLM stability charpoly
bridge.

## Approach
The live cycle already had the Step C.3 scaffold plus the past-`y`
entry:

- `Matrix.vecMul_adjugate_apply`
- `LMM.toGLM_stabilityCharpolyRowY_eq_explicit`
- `LMM.toGLM_stabilityMatrix_charpoly_explicit`

I closed the remaining reusable helper
`Matrix.adjugate_fromBlocks_zero₂₁` in `OpenMath/Helpers/BlockAdjugate.lean`.
The proof avoids a monolithic cofactor expansion:

1. Prove the row-vector Cramer helper already present in the file.
2. Add small private row-update and `Pi.single` restriction lemmas for
   block matrices.
3. Prove block-diagonal adjugate formulas for
   `fromBlocks A 0 0 1` and `fromBlocks 1 0 0 D` by `adjugate_apply`.
4. Prove the unipotent formula
   `adjugate (fromBlocks 1 B 0 1) = fromBlocks 1 (-B) 0 1` using the
   explicit right inverse and determinant one.
5. Factor
   `fromBlocks A B 0 D =
    fromBlocks 1 0 0 D * fromBlocks A B 0 1`
   and finish with `Matrix.adjugate_mul_distrib`.

## Result
SUCCESS. `Matrix.adjugate_fromBlocks_zero₂₁` is now proved
without live proof placeholders. The downstream Step C.3 active file
still compiles.

Verification:

- `lean -R . OpenMath/Helpers/BlockAdjugate.lean` with
  `LEAN_PATH` prefixed by `/tmp/lean4-toolchain/lib/lean` — clean.
- `lean -R . OpenMath/LMMAsGLM/StabilityCharpoly.lean` with the same
  `LEAN_PATH` — clean.
- `lean -R . OpenMath/LMMAsGLM.lean` with the same `LEAN_PATH` — clean.

`lake env lean ...` still hangs in this environment because the Lake/Lean
launcher resolves its core library directory to the GPFS-hosted elan
toolchain. Direct `lean -R .` with `/tmp/lean4-toolchain/lib/lean` first
in `LEAN_PATH` avoids that hang and checks the same files.

## Dead ends
The first assembly proof used broad entrywise `simp` after
`fromBlocks_multiply`; that was slow and noisy. Replacing it with
factor-level simplification and small local lemmas kept elaboration under
control.

The diagonal block proofs also needed explicit `Pi.single` restriction
lemmas. Plain `simp [Matrix.updateRow]` did not normalize expressions like
`Pi.single (Sum.inr i) 1 (Sum.inr k)` reliably after row updates.

## Discovery
The block-adjugate identity is much easier to prove multiplicatively than
by expanding all four cofactors directly. The useful factorization is:

```
fromBlocks A B 0 D =
  fromBlocks 1 0 0 D * fromBlocks A B 0 1
```

and

```
fromBlocks A B 0 1 =
  fromBlocks 1 B 0 1 * fromBlocks A 0 0 1
```

This isolates the only off-diagonal sign in the unipotent block, where
the explicit inverse is `fromBlocks 1 (-B) 0 1`.

## Suggested next approach
Apply `Matrix.adjugate_fromBlocks_zero₂₁` to
`(toGLM_V_active_lift m).charmatrix` in
`OpenMath/LMMAsGLM/StabilityCharpoly.lean` and replace the placeholder
`LMM.toGLM_stabilityCharpolyRowF_eq_explicit` with the actual bottom-column
formula. The charmatrix off-diagonal block is
`-(toGLM_stabilityMatrixPYHF m 0).map Polynomial.C`, so the top-right
adjugate correction should simplify with a double negative before pairing
against the past-`y` rank-one row.
