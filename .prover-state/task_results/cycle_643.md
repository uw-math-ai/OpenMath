# Cycle 643 Results

## Worked on

`OpenMath/LMMAsGLM.lean`, specifically the BDF-only past-`h*f` block
charpoly lemma and the next BDF stability-matrix charpoly scaffold.

## Approach

Followed the cycle 643 strategy after reading the current strategy file and
the live cycle 638/641 LMM-as-GLM block lemmas. Added the requested
sorry-first statements, verified the file compiled, then closed the PHF
helper manually.

For the proved lemma, under `hβ : ∀ l : Fin s, m.β l.castSucc = 0`, the
past-`h*f` block entry formula reduces to the pure shift
`if (l : ℕ) = (j : ℕ) + 1 then 1 else 0`. This makes
`m.toGLM_stabilityMatrixPHF z` upper-triangular with zero diagonal, and
`Matrix.charpoly_of_upperTriangular` reduces the charpoly to `X^s`.

Aristotle was skipped as instructed by the strategy.

## Result

SUCCESS.

Landed sorry-free:

```lean
LMM.toGLM_stabilityMatrixPHF_charpoly_of_bdf
```

Also landed the planned one-sorry scaffold:

```lean
LMM.toGLM_stabilityMatrix_charpoly_of_bdf
```

Updated `.prover-state/issues/lmm_toGLM_general_charpoly_rank_one.md` to
record the cycle 642 revert reason: the PHF block is not nilpotent for
general LMMs, with the trapezoidal `s = 1` counterexample
`PHF[0,0] = z / (2 - z)`.

## Dead ends

None new. This cycle deliberately avoided the reverted general
polynomial-valued stability polynomial route and the false zero-block
charpoly route.

## Discovery

The BDF-only PHF proof does not need a custom determinant lemma. The existing
upper-triangular charpoly theorem is enough once the BDF entry computation is
available.

## Suggested next approach

Close `LMM.toGLM_stabilityMatrix_charpoly_of_bdf` by reducing the
`fromBlocks` charmatrix determinant to the already-landed BDF PHF charpoly
plus a row/column expansion along the rank-one right block.

Verification:

```bash
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/LMMAsGLM.lean
rg -n "^\\s*sorry\\b" OpenMath -g "*.lean"
```

The live Lean sorry count is exactly one, the planned scaffold in
`OpenMath/LMMAsGLM.lean`.
