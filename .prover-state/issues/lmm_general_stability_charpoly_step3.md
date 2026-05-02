# Issue: General LMM stability matrix charpoly factorisation (Step 3)

## Blocker

Cycle 658 closed the *block-level* charpoly identities for general LMMs:

```lean
toGLM_stabilityMatrixPHF_charpoly      -- general PHF block companion charpoly
toGLM_stabilityMatrixPY_charpoly       -- general PY block companion charpoly
toGLM_stabilityMatrixPY_apply_last     -- general (drops unused hbdf)
toGLM_stabilityMatrixPHF_eq_companion  -- private bridge
toGLM_stabilityMatrixPY_eq_companion   -- private bridge
```

What is still missing is the *full* charpoly factorisation of
`m.toGLM.stabilityMatrix z` for general LMMs. For BDF-type LMMs we already
have

```lean
toGLM_stabilityMatrix_charpoly_of_bdf :
  (m.toGLM.stabilityMatrix z).charpoly =
    (toGLM_stabilityMatrixPY m z).charpoly *
      (Polynomial.X : Polynomial ℂ) ^ s
```

via `Matrix.charpoly_fromBlocks_zero₁₂` once `toGLM_stabilityMatrixPYHF` is
shown to be zero under `hbdf`. For general LMMs both off-diagonal blocks
PYHF and PHFY are non-zero rank-one, so neither
`Matrix.charpoly_fromBlocks_zero₁₂` nor `_zero₂₁` apply.

## Context

The useful pieces sitting in `OpenMath/LMMAsGLM.lean` already are:

- `toGLM_stabilityMatrix_eq_fromBlocks` — block decomposition via the
  `toGLM_stabilityBlockEquiv` reindex.
- `toGLM_stabilityMatrix_eq_V_active_plus_rank_one` — exact identity
  ```lean
  m.toGLM.stabilityMatrix z =
    toGLM_V_active_lift m +
      (1 / (1 - z * β_last)) • toGLM_rankOneCorrection m z
  ```
  where `toGLM_rankOneCorrection = Matrix.vecMulVec col row`.
- `toGLM_stabilityMatrixPHF_charpoly` and `toGLM_stabilityMatrixPY_charpoly`
  (cycle 658) — give the companion-form charpolys of the diagonal blocks.

What is *not* in Mathlib (verified via `lean_loogle` / `lean_state_search`
during cycles 641–642 and re-checked in 658):

- A direct charpoly identity for `M + c • vecMulVec u v` with `M` block-2x2
  having two non-zero off-diagonal rank-one blocks.
- A general "shift companion plus rank-one" charpoly closed form.

## What was tried (cycles 641–658)

- **Cycle 641**: block decomposition + rank-one update form (landed).
- **Cycle 642**: tried `Matrix.charpoly_fromBlocks_zero₁₂` and `_zero₂₁`
  for the full general-LMM stability matrix. **Failed**: trapezoid has
  `PHF[0,0] = z/(2-z) ≠ 0` and `PYHF`, `PHFY` are non-zero rank-one.
  Recorded the trapezoid counterexample in `disproven.md` (PHF nilpotency
  claim).
- **Cycle 643**: hand-proved the *BDF* PHF charpoly via
  `Matrix.charpoly_of_upperTriangular`. Works only under `hbdf`.
- **Cycle 658 (this cycle)**: dropped `hbdf` from the *block* charpoly
  identities by routing through the existing
  `toGLM_stabilityMatrixPYCompanion_charpoly` hammer. The full assembly
  remains open.

## Possible solutions (Step 3 candidates)

The two routes the cycle 658 strategy named, ranked by which looks more
tractable:

### (a) Compute `charpoly(Vℂ)` directly, then matrix determinant lemma

`toGLM_V_active_lift m = m.toGLM.Vℂ` is *block-upper-triangular* at
`z = 0`: the PY block is the bottom-row companion with coefficients
`(-α_castSucc l : ℂ)` and a zero last row for `β`, and the PHF block is
the pure shift `X^s` (`β` last row is zero too at `z = 0`).

Wait — that is wrong; `Vℂ` does not depend on `z`, but the off-diagonal
blocks PYHF and PHFY in `Vℂ` need to be checked. From the four
`toGLM_stabilityMatrix_*Add_*Add_apply` lemmas, at `z = 0` the
off-diagonal blocks both vanish (the `z * 1/(1 - z·β_last) · …`
contributions all carry an explicit `z` factor). So `Vℂ` is genuinely
block-upper-triangular and its charpoly is

```lean
charpoly Vℂ =
  (X^s + ∑ l, C ((-α_castSucc l : ℂ)) * X^l) * X^s
```

Then `m.toGLM.stabilityMatrix z = Vℂ + c • vecMulVec col row` and Mathlib
has `Matrix.det_one_add_smul` (and friends), but what we actually need is

```lean
charpoly (Vℂ + c • vecMulVec u v) =
  charpoly Vℂ - c · (some polynomial built from u, v, and (X·1 - Vℂ).adj)
```

i.e. the **matrix determinant lemma for charpoly**, not for det. This
appears as `Matrix.charpoly_one_add_smul_vecMulVec` in some forks but I
did **not** find it in the local Mathlib via `lean_local_search` in
cycle 658. Step (a) as written needs either:

1. proving the charpoly form of the matrix determinant lemma as a helper
   in `OpenMath`; or
2. expressing it via `Polynomial.det` of `charmatrix (Vℂ + c • vecMulVec u v)`
   and applying `Matrix.det_one_add_smul`-type tools to the polynomial-
   valued matrix `(X•1 - Vℂ) - c • vecMulVec u v`, where the leading
   linear-in-X piece is invertible (over the polynomial ring).

### (b) Block determinant calculation exploiting rank-one off-diagonal

Both PYHF and PHFY are rank-one (only the last row is non-zero). For a
block-2x2 with rank-one off-diagonals, there is a direct determinant
identity using the Schur complement when one of the diagonal blocks is
invertible (over `ℂ(X)`). Concretely, in the polynomial-ring lift,
`(X•1 - PHF)` is invertible at all but finitely many `X`, and the Schur
complement identity gives

```lean
det (X•1 - M(z)) =
  det (X•1 - PHF) ·
    det ((X•1 - PY) - PYHF · (X•1 - PHF)^(-1) · PHFY)
```

The Schur complement here is a rank-one update of the bottom-row
companion `X•1 - PY`, which **is** within reach of
`Matrix.det_one_add_replicateCol_mul_replicateRow` (or a variant) once we
identify the rank-one piece.

## Recommended next two lemmas

If a future cycle attacks Step 3, my recommendation (route (a)):

1. `toGLM_V_active_charpoly`: prove `(toGLM_V_active_lift m).charpoly` is
   `(X^s + ∑ l, C ((-α_castSucc l : ℂ)) * X^l) * X^s`. Use
   `toGLM_stabilityMatrix_eq_fromBlocks` at `z = 0` plus
   `Matrix.charpoly_fromBlocks_zero₁₂` (now both off-diagonal blocks
   vanish because the `z`-factor kills them). Reuse the new
   `toGLM_stabilityMatrixPHF_charpoly` and
   `toGLM_stabilityMatrixPY_charpoly` at `z = 0`.

2. `Matrix.charpoly_add_smul_vecMulVec` (helper, may need to live in
   `OpenMath/Helpers/CharpolyRankOne.lean` or similar): prove the
   charpoly-form matrix determinant lemma as a one-shot lemma, taking
   `M : Matrix n n ℂ`, `u v : n → ℂ`, `c : ℂ`, and yielding
   `charpoly (M + c • vecMulVec u v) = charpoly M - c · ⟨v, adj(X•1 - M) · u⟩`.
   This is a standard identity but does not appear in the local Mathlib.

Together (1) + (2) reduce the LMM A-stability iff to evaluating
`adj(X•1 - Vℂ) · col` paired against `row^T`, which by inspection of the
rank-one column / row is a polynomial-valued inner product computable
from the explicit `Vℂ` charpoly.

## Cross-references

- `lmm_toGLM_general_charpoly_rank_one.md` (cycle 641's older write-up;
  this issue supersedes the analysis there for Step 3).
- `disproven.md` entry on the FALSE PHF-nilpotency claim from cycle 642
  (still load-bearing as a counterexample to naive route attempts).
