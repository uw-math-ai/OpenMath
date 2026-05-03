# Cycle 726 Results

## Worked on
§521 Step F (F.1–F.4) — `rowYQuot` BDF-independent closed form and BDF
unit-circle scalar headline. All four targets landed sorry-free in
`OpenMath/LMMAsGLM/StabilityCharpoly.lean`, each in its own commit.

## Approach

### F.1 — `toGLM_stabilityMatrixPY_zero_charmatrix_adjugate_last`

Showed `(charmatrix(PY 0)).adjugate ⟨s-1,_⟩ ⟨s-1,_⟩ = X^(s-1)` via:

1. `Matrix.adjugate_apply` rewrites the entry as
   `det((charmatrix(PY 0)).updateRow ⟨s-1,_⟩ (Pi.single ⟨s-1,_⟩ 1))`.
2. The full updated matrix `N` is upper triangular
   (`N.BlockTriangular id`):
   - For `j = ⟨s-1,_⟩` (updated row): `N j l = Pi.single ⟨s-1,_⟩ 1 l = 0`
     for `l ≠ ⟨s-1,_⟩`, dispatched by `Pi.single_eq_of_ne`.
   - For `j ≠ ⟨s-1,_⟩` (charmatrix row): use `toGLM_stabilityMatrixPY_apply_shift`
     (cycle 643). For `l < j`, both `(diagonal X) j l = 0` (off-diagonal)
     and `PY 0 j l = δ_{l, j+1} = 0` (since `l < j ≤ j+1`).
3. `Matrix.det_of_upperTriangular htri` reduces to `∏ i, N i i`.
4. Diagonal: `N ⟨s-1,_⟩ ⟨s-1,_⟩ = 1` (via `Pi.single_eq_same`),
   `N i i = X` for `i ≠ ⟨s-1,_⟩` (charmatrix diagonal at non-last row
   = `X - C(0) = X`).
5. Product: `Finset.mul_prod_erase` peels off the last index,
   `Finset.prod_const + Finset.card_erase_of_mem + Finset.card_univ +
   Fintype.card_fin` give `X^(s-1)`.

### F.2 — `rowYQuot_eq_neg_alpha_sum`

Closed form `rowYQuot m = -∑ l, C(α(castSucc l)) * X^l`. Recipe:

1. Cycle 692 closed form for `(PY 0).charpoly` (at z=0 the resolvent
   denominator `1 - 0·β_last = 1` collapses via `div_one`).
2. `Matrix.mul_adjugate` gives `charmatrix * adjugate = charpoly • 1`;
   take `(s-1, s-1)` entry to get
   `∑ k, charm[s-1, k] · adj[k, s-1] = charpoly`.
3. Substitute `charm[s-1, k] = (diagonal X)[s-1, k] - C(PY 0[s-1, k])`
   and `PY 0[s-1, k] = (-α(castSucc k)) / 1 = -α(castSucc k)` (via
   `toGLM_stabilityMatrixPY_apply_last`, cycle 643 generalised).
4. Split sum: diagonal collapses by `Finset.sum_eq_single ⟨s-1,_⟩` at
   the unique nonzero `(diagonal X)` term; substitute
   `adj[s-1, s-1] = X^(s-1)` (F.1) so `X · X^(s-1) = X^s`.
5. Substitute `rowYQuot_eq_adjugate_sum` (cycle 720) into the residual
   sum.
6. Conclude `X^s - rowYQuot m = X^s - ∑ C(-α(castSucc l)) * X^l`,
   move `X^s` and convert sign with `Polynomial.C_neg + push_cast`,
   close by `linear_combination -hEntry + h_sum_eq`.

### F.3 — `rowYQuot_eval_one`, `rowYQuot_eval_zero`

Direct from F.2 by `Polynomial.eval_neg`, `Polynomial.eval_finset_sum`,
`Polynomial.eval_mul`, `Polynomial.eval_C`, `Polynomial.eval_pow`,
`Polynomial.eval_X`. For `eval 0`, `Finset.sum_eq_single ⟨0, hs⟩`
extracts the only surviving summand (via `pow_zero` for the target,
`zero_pow hlne` for the others).

### F.4 — `D_mul_toGLM_charpoly_eval_one_eq_stabilityPolyPoly_of_bdf`

Public BDF unit-circle scalar headline:
`(1 - z β_last) · charpoly.eval 1 = (stabilityPolyPoly z).eval 1`.
Substitute E.2 (`D_mul_toGLM_charpoly_eval_one_reduced_of_bdf`) and
F.3 (`rowYQuot_eval_one`); the abstract `(rowYQuot m).eval 1 = -∑ α`
makes `-(rowYQuot m).eval 1 · (z β_last) = z β_last · ∑ α` cancel the
`-z β_last · ∑ α` correction. `ring` closes.

## Result

**SUCCESS — score 3 (excellent).** F.1 + F.2 + F.3 (both eval lemmas)
+ F.4 all sorry-free, each individually committed:

- `9ec7ab5cc1` — Step F.1 PY(0) charmatrix adjugate diagonal entry
- `08327c336d` — Step F.2 rowYQuot BDF-independent closed form
- `544f11e3e3` — Step F.3 rowYQuot evaluations at 0 and 1
- `6fe864ae5b` — Step F.4 BDF unit-circle scalar headline

Full `lake build` succeeded; only pre-existing simp-arg warnings in
`Section386Aug/DepthThree.lean` (unrelated to this cycle).

## Dead ends

Two minor friction points:

- `subst hj` in F.1 BlockTriangular case failed because `j` appears
  inside the `⟨s - 1, by omega⟩` proof term anchor; switched to
  `rw [hj]` and the rewrite chain unfolded cleanly.
- Initial `have h1 : N ⟨s-1,_⟩ l = Pi.single ⟨s-1,_⟩ 1 l` had
  Pi.single's codomain metavariable refuse to resolve. Replaced with
  direct `rw [hN_def, Matrix.updateRow_self]; apply Pi.single_eq_of_ne`,
  letting the rewrite chain plumb the type through naturally.
- `congr 1` after `rw [← pow_succ']` for `X · X^(s-1) = X^s` left
  zero goals (apparently auto-discharging via internal arithmetic
  reduction). Replaced with explicit
  `rw [← pow_succ', show s - 1 + 1 = s from by omega]`.

No proof attempts failed; recipe in strategy.md was directly applicable.

## Discovery

The strategy's "use Matrix.det_of_upperTriangular" route for F.1 is
significantly cleaner than the alternative `Matrix.det_succ_row` /
cofactor-expansion path. Treating the adjugate-defining matrix as
upper triangular at the level of the WHOLE matrix (rather than
expanding along the updated row to a minor) avoids any
`Fin.castSucc`/`Fin.succ` reindexing entirely. The upper-triangular
proof obligation cleanly splits on `j = ⟨s-1,_⟩` vs `j ≠`, and the
diagonal product computes via `Finset.mul_prod_erase` — about 70 lines
total for F.1.

The cycle-720 cofactor-sum lemma (`rowYQuot_eq_adjugate_sum`) and the
cycle-692 `(PY 0).charpoly` closed form composed together cleanly,
exactly as the planner predicted.

## Suggested next approach

The §521 BDF unit-circle headline (F.4) is now public and self-contained.
Natural next seams:

1. **Step G — generic (non-BDF) unit-circle identity.** The current
   `D_mul_toGLM_charpoly_eval_one_substituted` (line 2031, no `_of_bdf`)
   already exposes `rowYQuot.eval 1` and `∑ rowFAlphaResidual.eval 1`
   as the only obstructions. F.3's `rowYQuot_eval_one` discharges one;
   the rowFAlphaResidual side needs a closed form analogous to F.2.
   Cycle 720's `rowFAlphaResidual_eq_double_sum` plus an analogue of
   F.1 for *off-diagonal* adjugate entries (`adj k j` for `k ≠ j` on
   the appropriate diagonal slot) would be the F-prime sub-ladder.

2. **Step H — connect F.4 to the §521 A-stability iff bridge.** With
   `(1 - z β_last) · charpoly.eval 1 = stabilityPolyPoly.eval 1` in
   hand for the BDF branch, the next layer is the iff direction
   showing `charpoly.eval 1 = 0 ↔ stabilityPolyPoly.eval 1 = 0`
   (modulo the resolvent denominator). The `hz` non-vanishing
   guarantees the prefactor is nonzero, so the iff is direct division.

3. **Stretch — extend F.4 to a *family* of unit-circle evaluations.**
   The same recipe at any `ξ` on the unit circle would give the full
   stability boundary correspondence; the obstruction is generalising
   F.3 from `ξ ∈ {0, 1}` to arbitrary `ξ` (which already exists in
   weaker form via `rowYQuot_eval_eq_sum`, line 2103, but not as a
   closed-form polynomial in `ξ`).
