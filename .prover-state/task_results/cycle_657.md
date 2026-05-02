# Cycle 657 Results

## Worked on
Butcher §521 RK-side GLM A-stability transports for the 3-stage Lobatto
IIIA and IIIC tableaux in `OpenMath/RKAsGLM.lean`.

## Approach
Followed the sorry-first structure after `rkLobattoIIIB2_toGLM_isAStable`.
Imported `OpenMath.LobattoIIIA3` and `OpenMath.LobattoIIIC3`, then used
the cycle 653 / 654 `Matrix.inv_def` plus
`Matrix.adjugate_fin_three_of` pattern for `1 - z • A`.

For IIIA3, reused `gl2_denom_ne_zero`; the determinant certificate is
`M.det = gl2Denom z` and the weighted adjugate sum is `1`.

For IIIC3, reused `lobIIIC3_denom_ne_zero`; the determinant certificate
is `M.det = lobIIIC3Denom z / 24` and the weighted adjugate sum is
`(z ^ 2 - 6 * z + 24) / 24`.

Submitted the sorry-first file to Aristotle; it returned `QUEUED`, so
manual closure proceeded with Lean LSP checks and local compilation.

## Result
SUCCESS. Landed:

- `rkLobattoIIIA3_stabilityFunction_eq`
- `rkLobattoIIIA3_toGLM_isAStable`
- `rkLobattoIIIC3_stabilityFunction_eq`
- `rkLobattoIIIC3_toGLM_isAStable`

`lake env lean OpenMath/RKAsGLM.lean` succeeds. The remaining output is
the pre-existing unused-simp warnings around SDIRK proofs, plus Lean
linter panic backtraces that were already present before closing the new
proofs.

## Dead ends
The first IIIA3 `hsumInv` proof tried `rw [← hsum]` against a right-hand
side simplified to `(gl2Denom z)⁻¹`; rewriting could not find the literal
`1`. Replaced it with a short `calc` that factors `(gl2Denom z)⁻¹` out
of the finite sum before rewriting by `hsum`.

## Discovery
The 3-stage Lobatto rational tableaux do not need the sqrt certificate
machinery from Radau IIA3 / GL3. Plain `ring` closes both determinant
and adjugate-sum identities once the matrix is made explicit.

## Suggested next approach
Proceed with the §521 LMM-side iff bridge
`LMM.toGLM_isAStable_iff`, starting from the BDF-specialized bridge and
the block determinant issue
`.prover-state/issues/lmm_toGLM_general_charpoly_rank_one.md`.
