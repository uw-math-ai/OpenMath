# Cycle 722 Results

## Worked on

`OpenMath/LMMAsGLM/StabilityCharpoly.lean`, §521 Step D.15 + D.16a/b/c/d
— `rowFAlphaResidual` cofactor expansion.

Five new private theorems landed sorry-free:

- `rowFAlphaResidual_eq_double_sum` (D.15)
- `rowFAlphaResidual_eval_eq_double_sum` (D.16a)
- `rowFAlphaResidual_eval_zero_eq_double_sum` (D.16b)
- `rowFAlphaResidual_eval_one_eq_double_sum` (D.16c)
- `rowFAlphaResidual_eval_one_of_bdf_eq_zero` (D.16d)

## Approach

Followed the cycle 720 pattern (`rowYQuot_eq_adjugate_sum` + four
specialisations + BDF wrapper) and adapted to the rowF side, where
`rowFAlphaResidual` is a `Matrix.vecMul` against `(-adj * -PYHF.map C)`
rather than an `updateRow` determinant.

D.15 proof skeleton:
```
unfold rowFAlphaResidual
rw [Matrix.vecMul_eq_sum]
simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
refine Finset.sum_congr rfl (fun k _ => ?_)
rw [Matrix.mul_apply]
simp only [Matrix.neg_apply, Matrix.map_apply, neg_mul_neg, Finset.mul_sum]
refine Finset.sum_congr rfl (fun j _ => ?_)
rw [Polynomial.C_mul]; ring
```

D.16a is `Polynomial.eval_finset_sum` plus `Polynomial.eval_mul / eval_C`
under nested `Finset.sum_congr`. D.16b/c are direct specialisations
at `ξ ∈ {0, 1}`. D.16d uses `toGLM_stabilityMatrixPYHF_eq_zero_of_bdf`
(cycle 645) — the matrix-equality version is converted to entry-wise
zero via two `congrFun`s.

## Result

SUCCESS — all five theorems landed sorry-free.
`lake env lean OpenMath/LMMAsGLM/StabilityCharpoly.lean` exits 0
silently. File grew from 2145 to 2225 lines (well under the 3000 cap).

## Dead ends

- The cycle 722 strategy stated D.15 with a positive `m.α` factor:
  `Polynomial.C (((m.α (Fin.castSucc k) : ℝ) : ℂ) * PYHF j l) * adjugate`.
  This is **off by a sign** from the correct identity: the
  `rowFAlphaResidual` definition has THREE negations (the row vector
  `-α`, plus `-adj` and `-(PYHF.map C)`); only the inner two cancel
  via `neg_mul_neg`, leaving one outer `-α`. Confirmed by Lean
  diagnostic on the first attempt — `ring` failed with
  `C(-α) * adj * C(PYHF) ≠ C(α) * C(PYHF) * adj`. Adjusted all five
  statements to use `(-m.α (Fin.castSucc k) : ℝ)` instead of
  `(m.α (Fin.castSucc k) : ℝ)`. This matches the cycle 720
  `rowYQuot_eq_adjugate_sum` convention (which also keeps the leading
  `-α`), and does not affect D.16d (the BDF case still vanishes
  because `PYHF j l = 0`).

## Discovery

- `Matrix.vecMul_eq_sum` plus `simp only [Finset.sum_apply,
  Pi.smul_apply, smul_eq_mul]` cleanly reduces a `vecMul` to a
  pointwise sum, exactly the pattern already used in cycle 716's
  `rowFAlphaResidual_degree_lt`.
- `neg_mul_neg` is a one-shot cancellation for the inner pair of
  matrix negations once `Matrix.neg_apply` and `Matrix.map_apply`
  push the negations into entries.
- `toGLM_stabilityMatrixPYHF_eq_zero_of_bdf` returns matrix equality;
  `congrFun (congrFun this j) l` gives the entry-wise zero needed
  inside the `Finset.sum_eq_zero` skeleton.

## Suggested next approach

The D.16 layer is now ready for the iff bridge target
`LMM.toGLM_charpoly_eval_one_eq_zero_iff_of_bdf` (per the strategy):

1. Substitute D.16d into `D_mul_toGLM_charpoly_eval_one_substituted_of_bdf`
   (cycle 718) — the `∑ l, (rowFAlphaResidual m l).eval 1` summand
   collapses to zero, leaving a clean `(stabilityPolyPoly z).eval 1`
   plus the `rowYQuot.eval 1` term.
2. Then divide through by the `1 - z * β_last` factor (use the
   already-established `hz` non-zero hypothesis) to obtain the iff
   bridge for `(stabilityMatrix z).charpoly.eval 1 = 0`.
3. The eventual target `LMM.toGLM_isAStable_iff` will need analogous
   `eval ξ` evaluations on the unit circle `|ξ| = 1`; D.16a is
   already general enough (parametrised in `ξ`) to support that
   without a re-proof.

## File size status

`OpenMath/LMMAsGLM/StabilityCharpoly.lean`: 2145 → 2225 lines (+80).
Still well below the 3000 line cap. No split needed.
