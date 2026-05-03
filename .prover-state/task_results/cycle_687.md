# Cycle 687 Results (retroactive write-up — landed in cycle 688 commit)

## Worked on
§521 Step C.10 — degree bound for `rowFAlphaPoly`, plus three supporting
private helpers about the adjugate of a characteristic matrix.

## Approach
Closed the cascade bottom-up:

1. `charmatrix_adjugate_natDegree_le` — each entry of `(charmatrix A).adjugate`
   has `natDegree ≤ n` for an `(n+1) × (n+1)` matrix. Proof unfolds
   `adjugate_apply` and `det_apply`, bounds each permutation summand by
   `Polynomial.natDegree_smul_le` + `Polynomial.natDegree_prod_le`, then
   counts row contributions: row `j` (replaced by `Pi.single i 1`)
   contributes 0, the other `n` rows contribute ≤ 1 each via
   `Matrix.charmatrix_apply_natDegree_le`. The cardinality of
   `{k | σ k ≠ j} = univ.erase (σ.symm j)` is `n`.
2. `charmatrix_adjugate_degree_lt` — `degree` wrapper using
   `Polynomial.degree_le_natDegree` and `Nat.lt_succ_of_le`. Splits on
   `n` to handle the empty-`Fin` case via `i.elim0`.
3. `rowFAlphaResidual_matrix_entry_degree_lt` — each entry of
   `(-charmatrix.adjugate) * (-PYHF.map C)` has degree `< s`: combines
   `charmatrix_adjugate_degree_lt` (degree `< s`) with `Polynomial.degree_C_le`
   (degree ≤ 0) on each `Matrix.mul_apply` summand.
4. `rowFAlphaResidual_degree_lt` — degree `< s` for each residual: factors
   the `Matrix.vecMul` over `Polynomial.degree_sum_le` /
   `Polynomial.degree_mul_le`, where the C-vector contributes ≤ 0 and the
   matrix entry `< s`.
5. `rowFAlphaPoly_degree_lt` — degree `< 2*s - 1`: applies
   `rowFAlphaResidual_degree_lt` per `l ∈ Fin s` along with `degree_X_pow`
   to bound each `residual l * X^l` by `s + l < 2*s - 1`.

## Result
SUCCESS — 136 lines added at the bottom of
`OpenMath/LMMAsGLM/StabilityCharpoly.lean` (between
`rowFAlphaPoly_eq_residual_sum` and `end LMM`). All deliverables
sorry-free; file and umbrella compile clean. The cycle 687 commit was
omitted (the only failure of the cycle); deliverables landed in the
cycle 688 commit alongside Step C.11.

## Deliverables (verbatim from the diff)
- `private lemma charmatrix_adjugate_natDegree_le`
  — `(A.charmatrix.adjugate i j).natDegree ≤ n` for `(n+1) × (n+1)` matrices.
- `private lemma charmatrix_adjugate_degree_lt`
  — `(A.charmatrix.adjugate i j).degree < (n : WithBot ℕ)`.
- `private theorem rowFAlphaResidual_matrix_entry_degree_lt`
  — degree `< s` for entries of `(-charmatrix.adjugate) * (-PYHF.map C)`.
- `private theorem rowFAlphaResidual_degree_lt`
  — `(rowFAlphaResidual m l).degree < (s : WithBot ℕ)`.
- `theorem rowFAlphaPoly_degree_lt`
  — `(rowFAlphaPoly m).degree < ((2 * s - 1 : ℕ) : WithBot ℕ)`.

## Dead ends
None recorded for cycle 687 itself (the proofs landed cleanly).
The cycle's only failure was the missed commit-and-push step.

## Discovery
- The combination `Matrix.adjugate_apply` + `Matrix.det_apply` +
  `Polynomial.natDegree_smul_le` + `Polynomial.natDegree_prod_le` is a
  reusable recipe for adjugate-degree bounds; the only project-specific
  ingredient is `Matrix.charmatrix_apply_natDegree_le`.
- `Equiv.eq_symm_apply` is the cleanest way to identify
  `{k | σ k = j}` with `{σ.symm j}` for `Finset.card_erase_of_mem` to fire.

## Suggested next approach
Step C.11 — substitute the named PHF, RowY, and RowF identities into
`toGLM_stabilityMatrix_charpoly_explicit` to land the fully-named
consolidated form. (Done in cycle 688.)
