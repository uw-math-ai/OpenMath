# Cycle 632 Results

## Worked on

§521 LMM A-stability — third concrete LMM-side transport through the
§503 GLM embedding: `bdf2_toGLM_isAStable` in
`OpenMath/LMMAsGLM.lean`. This is the first `s = 2` (i.e. 4×4 GLM
stability matrix) entry in the cycle 630/631 series, which previously
covered only the `s = 1` cases backward Euler and trapezoidal rule.

## Approach

Followed the same direct recipe as cycles 630/631 — bypass the open
`LMM.toGLM_isAStable_iff` bridge and compute the charpoly of
`bdf2.toGLM.stabilityMatrix z` by hand. Aristotle was intentionally
skipped per the cycle strategy. No new tracked `OpenMath/*.lean` file
was added; the new theorem lands inline in `OpenMath/LMMAsGLM.lean`
just after `trapezoidalRule_toGLM_isAStable`.

For BDF2 (`α = ![1/3, -4/3, 1]`, `β = ![0, 0, 2/3]`) the §503 embedding
gives a 4×4 GLM stability matrix with a clean block structure:

```lean
!![0, 1, 0, 0;
   -(1 / (3 - 2 * z)), 4 / (3 - 2 * z), 0, 0;
   0, 0, 0, 1;
   -(z / (3 - 2 * z)), 4 * z / (3 - 2 * z), 0, 0]
```

The right two columns of the top two rows are zero — this is exactly
the block-lower-triangular shape `fromBlocks A 0 C D` after
relabelling via `finSumFinEquiv`. The bottom-right 2×2 block `D` is
nilpotent (`!![μ, -1; 0, μ]` shifted = `μI - !![0,1;0,0]`), giving
`det D = μ²` and accounting for the two extra zero eigenvalues from
the enlarged GLM state. The top-left block `A` is the genuine BDF2
companion-shape factor, with `det A = μ² - (4/(3-2z)) μ + 1/(3-2z)`
— exactly `bdf2.stabilityPoly μ z` divided by `3 - 2z` (up to a global
factor of `3` that lands as a `linear_combination` coefficient).

Concretely, the proof:

1. Computes `Aℂ = !![2/3]` (one-stage `s = 2` LMM has scalar `Aℂ`).
2. Inverts `1 - z • !![2/3]` via `Matrix.adjugate_fin_one`.
3. Verifies the explicit 4×4 form of `stabilityMatrix z` entrywise via
   `fin_cases k <;> fin_cases l` and `field_simp [hne, hne']; try ring`.
   Two hypotheses are needed because `simp` normalises `2 * z` to
   `z * 2` in some cases.
4. Rewrites `μI - M` as `(fromBlocks A 0 C D).submatrix
   finSumFinEquiv.symm finSumFinEquiv.symm` and chains
   `det_submatrix_equiv_self` + `det_fromBlocks_zero₁₂`, finishing
   with `Matrix.det_fin_two`.
5. Splits `μ² · Q(μ, z) = 0` into `μ = 0` (trivially `‖μ‖ ≤ 1`) and
   `Q(μ, z) = 0`, transports the latter to `bdf2.stabilityPoly μ z = 0`
   via `linear_combination` (clearing the `3 - 2z` denominator and
   matching the `1/3, -4/3, 1` LMM coefficients via a global factor 3),
   and finishes with the existing `bdf2_aStable`.

## Result

SUCCESS. `bdf2_toGLM_isAStable : bdf2.toGLM.IsAStable` lands sorry-free
in `OpenMath/LMMAsGLM.lean`. `lake env lean OpenMath/LMMAsGLM.lean`
passes cleanly with no warnings. `maxHeartbeats` was **not** increased
above 200000 — the block-decomposition route stays well inside the
default budget.

`plan.md` was updated to record cycle 632 in the §521 chapter section,
the Active Frontier, and Backlog item #7 (which now lists three landed
concrete LMM-side transports and prioritises the `Matrix.exp`
stability-order definition over further concrete transports).

## Dead ends

- **Brute-force `Matrix.det_succ_row_zero` + `Matrix.det_fin_three` +
  long `simp` set hit a deterministic timeout** at `maxHeartbeats =
  200000`. The strategy explicitly forbids raising the limit.
  Resolved by switching to the block decomposition above, which avoids
  the cubic-in-`s` cofactor expansion entirely.
- **`field_simp [hne]; ring`** initially produced "No goals to be
  solved" on two of the 16 `fin_cases` entries — `field_simp` had
  closed the goal alone. Resolved by changing the closer to
  `field_simp [hne, hne']; try ring`.
- **`field_simp` matching mismatch `(3 - z * 2)⁻¹` vs `hne : 3 - 2 * z
  ≠ 0`** — `simp` normalised `2 * z` to `z * 2` in some entries.
  Resolved by adding `hne' : (3 : ℂ) - z * 2 ≠ 0 := by rwa [...]` and
  passing both hypotheses to `field_simp`.
- **`rw [hquad]; ring` on the quadratic-to-stabilityPoly transport**
  failed because the goal had been over-simplified into the `z * 2`
  form, breaking pattern match. Resolved by switching to a single
  `linear_combination h1 - h_eq` step.

## Discovery

- For `s ≥ 2` LMM embeddings the §503 GLM stability matrix has a
  natural `Matrix.fromBlocks` shape: top-left block is the genuine
  `s × s` companion factor of `π(ξ, z)`, bottom-right block is
  nilpotent of dimension `s` (contributing `s` extra zero
  eigenvalues), and the bottom-left block is `z`-scaled. This is
  exactly the structural factorisation
  `charpoly(M(z)) = X^s · π̃(·, z)` that the open
  `LMM.toGLM_isAStable_iff` bridge needs in general — cycle 632 has
  now exhibited it concretely at `s = 2`.
- `Matrix.det_fromBlocks_zero₁₂` together with
  `Matrix.det_submatrix_equiv_self` and `finSumFinEquiv.symm` is a
  scalable substitute for the missing `Matrix.det_fin_four`.
- The denominator-clearing trick `linear_combination h1 - h_eq` is
  more robust than `rw + field_simp + ring` when `simp` may have
  normalised the polynomial form unexpectedly.

## Suggested next approach

§521 now has three concrete LMM-side A-stability transports
(backward Euler, trapezoidal, BDF2). The next §521 cycle should
**not** add a fourth concrete transport (e.g. `am2` / `ab2`).
Instead, pursue:

1. **`stabilityOrder` definition via `Matrix.exp`** on the GLM side
   (small, self-contained, can attempt next cycle). Pair `M(z)` with
   `Matrix.exp (z • C)` for some companion `C` and define
   `stabilityOrder` as the vanishing order of the matrix-valued
   `M(z) - Matrix.exp z`.
2. **`LMM.toGLM_isAStable_iff`**, using the general-`s` block
   decomposition pattern that cycle 632 just exhibited concretely:
   prove `charpoly(M(z)) = X^s · π̃(ξ, z)` for arbitrary `s` via
   `Matrix.fromBlocks` + `det_fromBlocks_zero₁₂`, then bridge
   `π̃(·, z)` to `LMM.stabilityPoly` up to a unit scaling. The cycle
   630/631/632 templates collectively show this is tractable.
