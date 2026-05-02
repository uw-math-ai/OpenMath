# Cycle 642 Results

## Worked on

§521 LMM-as-GLM A-stability frontier (Backlog #7). Strategy steps 1, 2, 3 from the
cycle-642 planner brief, all in `OpenMath/LMMAsGLM.lean`.

## Approach

Sorry-first: appended a new `namespace LMM` block at the end of
`OpenMath/LMMAsGLM.lean` with three new declarations (definition + two
theorems). Verified with `lake env lean OpenMath/LMMAsGLM.lean` after each
edit. Closed the first two declarations completely; left the headline as a
sorry-first scaffold.

## Result

**SUCCESS** at the planner's "Better" tier (steps 1 + 2 sorry-free, step 3
stated as sorry-first scaffold).

Landed sorry-free:

- `LMM.stabilityPolyPoly (m : LMM s) (z : ℂ) : Polynomial ℂ`
  — degree-`s` polynomial in `ℂ[X]` with coefficient `(α_j − z β_j)` at
  degree `j`.
- `LMM.stabilityPolyPoly_eval` — evaluation `(stabilityPolyPoly m z).eval ξ
  = m.stabilityPoly ξ z` (closed via `Finset.sum_sub_distrib` + `ring`).
- `LMM.toGLM_stabilityMatrixPHF_charpoly_of_explicit_past` — for BDF-shaped
  methods (`∀ l, m.β l.castSucc = 0`), the past-`h*f` block charpoly is
  `X^s`. Proof goes via `Matrix.det_of_upperTriangular` applied to the
  charmatrix: diagonal is identically zero, sub-diagonal is identically
  zero, so `det charmatrix = ∏ i, X = X^s`.

Sorry-first scaffold (intentional):

- `LMM.toGLM_stabilityMatrix_charpoly` — headline factorisation
  `(1 − z β_s) • charpoly = X^s * stabilityPolyPoly`. Sorry left for
  cycle 643 per the strategy's "Better" definition of done.

## Dead ends

- The strategy's step 2 claim that `toGLM_stabilityMatrixPHF` is nilpotent
  in **general** is **false**. Verified by hand on the trapezoidal rule
  (s = 1): PHF[0,0] = `z β_0 / (1 − z β_1) = z/(2−z) ≠ 0`, so the matrix
  is not nilpotent and its charpoly is `X − z/(2−z) ≠ X^1`. The PHF block
  is only nilpotent for BDF-shape methods (β = 0 on past slots). I
  therefore conditioned the helper on `∀ l, m.β l.castSucc = 0` and noted
  the general case in the issue file.
- The strategy's suggestion to split the headline via
  `Matrix.charpoly_fromBlocks_zero₁₂` / `_zero₂₁` does not work: cycle
  641's `toGLM_stabilityMatrixPYHF` and `toGLM_stabilityMatrixPHFY` are
  **not zero** off-diagonals in general — they are rank-≤1 blocks (only
  row `j = s−1` is nonzero). Documented in the updated issue file.
- The strategy's headline `charpoly = X^s * stabilityPolyPoly` (without the
  `(1 − z β_s)` scalar on the LHS) is not the natural denominator-cleared
  shape. Hand verification at BDF2 and trapezoidal both confirm the
  scalar-cleared shape `(1 − z β_s) • charpoly = X^s * stabilityPolyPoly`
  is the correct identity. Adjusted accordingly.

## Discovery

- The natural polynomial-valued LMM stability polynomial is just
  `∑_j (α_j − z β_j) X^j` — no denominator clearing in the polynomial
  itself. The denominator factor `(1 − z β_s)` lives on the `charpoly`
  side of the headline identity, where it absorbs the leading-coefficient
  normalisation of the active block.
- `Matrix.det_of_upperTriangular` (with `BlockTriangular id`) plus
  `Matrix.charmatrix_apply` is the cleanest path to charpoly of any
  upper-triangular matrix with all-zero diagonal: just check the
  upper-triangular structure of the charmatrix, then diagonal entries are
  `X − C(0) = X`.
- The cycle-641 fromBlocks decomposition (PY, PYHF, PHFY, PHF) has a
  consistent "row j = s−1 is special" structure across all four blocks.
  Both off-diagonal blocks are rank-≤1 in this sense.

## Suggested next approach (cycle 643)

The detailed cycle-643 plan is in
`.prover-state/issues/lmm_toGLM_general_charpoly_rank_one.md` (Cycle 642
update section). Headline:

1. Generalize the PHF charpoly to drop the BDF hypothesis. The general
   charpoly is a transposed-companion-matrix charpoly
   `X^s − (z β_{s-1}/(1−z β_s)) X^{s-1} − … − (z β_0/(1−z β_s))`. Search
   Mathlib for `companionMat` / `charpoly_companion`; if absent, do
   sparse-row determinant expansion locally for the PHF shape.
2. Close `LMM.toGLM_stabilityMatrix_charpoly` by exploiting the rank-≤1
   off-diagonal structure of the cycle-641 fromBlocks. Likely tools:
   `Matrix.det_one_add_smul`, `Matrix.det_one_add_replicateCol_mul_replicateRow`
   after denominator clearing.
3. Then `LMM.toGLM_isAStable_iff` follows by
   `(stabilityPolyPoly_eval).symm` plus the `IsAStable` /
   `InStabilityRegion` definitions on both sides.

## Aristotle

Not used this cycle. Strategy permits up to one batch of ≤3 jobs; given
the planner's strong "manual close" preference for the small algebraic
steps and the cycle-641 lesson about HTTP 429, manual was the right
call. Step 3 is the next candidate for an Aristotle batch when its
goal stabilises in cycle 643.

## Build status

`lake env lean OpenMath/LMMAsGLM.lean`: clean except for the one
intentional `sorry` warning at line 2458 (`toGLM_stabilityMatrix_charpoly`
scaffold). File grew from 2352 → 2464 lines, well below the 3000-line
soft cap.
