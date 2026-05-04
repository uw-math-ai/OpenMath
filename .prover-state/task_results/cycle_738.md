# Cycle 738 Results

## Worked on

Mechanical split of `OpenMath/LMMAsGLM/StabilityCharpoly.lean`
(3166 lines, over the 3000-line soft cap since cycle 736) into two
files. Carry-over from stalled cycle 737. No theorem work.

## Approach

Followed the planner's recipe verbatim:

1. Cut the original file between line 1532 and line 1533 — i.e. the
   doc-comment `/-- §521 Step C.14 — General \`s\`-step LMM
   headline …`  for
   `D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_plus_residual`
   (lines 1533–1542) goes into the move file with the theorem.
2. Truncated `StabilityCharpoly.lean` to lines 1–1532 + new closing
   `end LMM` → 1534 lines.
3. Created `OpenMath/LMMAsGLM/StabilityCharpolyEval.lean` with the
   planner-specified preamble (imports, doc-comment, `open Finset
   Real`, `namespace LMM`, `variable {s : ℕ}`) followed by lines
   1533–3165 of the original file verbatim plus a closing `end LMM`
   → 1662 lines.
4. Compiled both files. Promoted private helpers used across the
   cut.

## Result

SUCCESS.

- `lake env lean OpenMath/LMMAsGLM/StabilityCharpoly.lean` — clean,
  no errors / warnings / sorry.
- `lake env lean OpenMath/LMMAsGLM/StabilityCharpolyEval.lean` —
  clean, no errors / warnings / sorry.
- `lake build` — full build succeeds.
- `git status` shows exactly two changed files in `OpenMath/`:
  modified `StabilityCharpoly.lean` and new `StabilityCharpolyEval.lean`.
- File sizes: 1534 / 1662 lines — both well under the 3000-line cap,
  roughly even split, neither side over the planner's ~1700-line
  budget.

## Private-helper promotions

The planner listed eleven `private` symbols above the cut to watch
for cross-cut usage. After the split, the Lean compiler reported
exactly **two** that were used below the cut and needed promotion:

- `rowFAlphaResidual` (line 1060) — promoted from `private
  noncomputable def` to `noncomputable def`.
- `rowFAlphaPoly_eq_residual_sum` (line 1069) — promoted from
  `private theorem` to `theorem`.

The other nine watched `private` symbols (`fin_q_succ_eq_s_iff`,
`reindex_updateRow_eq`, `fromBlocks_zero₂₁_updateRow_castAdd`,
`adjugate_eq_of_mul_eq_det_smul`, `charmatrix_adjugate_natDegree_le`,
`charmatrix_adjugate_degree_lt`,
`rowFAlphaResidual_matrix_entry_degree_lt`,
`rowFAlphaResidual_degree_lt`, `rowYQuot_natDegree_le`) remain
`private` in the keep file. No promotions were required for any
symbol below the cut.

## Dead ends

None. The split followed the planner recipe exactly. The first
compile attempt of the move file reported a flurry of "unknown
identifier" errors for `rowFAlphaPoly`, `rowFBetaPoly`,
`D_mul_toGLM_charpoly_eq_X_pow_mul_active_plus_residual`, and
similar — all were artefacts of a stale `.olean` for
`StabilityCharpoly`. After `lake build OpenMath.LMMAsGLM.StabilityCharpoly`
rebuilt the dependency, the only remaining errors were the two
genuine `private` cross-cut uses listed above.

## Discovery

After modifying a file that's a dependency of the file you're
compiling with `lake env lean`, you must `lake build` the dependency
first to refresh its `.olean`. Otherwise you get spurious "unknown
identifier" errors for public symbols. (Worth remembering for any
future split / refactor cycle.)

The `/-! ###` doc block boundary mentioned in the strategy doesn't
actually exist at line 1525 of the original file — the doc-comment
above `D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_plus_residual`
is a regular `/--` doc-comment occupying lines 1533–1542. The cut
location was unambiguous (between the `ring` ending the previous
theorem at line 1531 and the next doc-comment at line 1533); the
planner's intent was preserved.

## Suggested next approach

Cycle 739: per the planner's handoff, promote
`LMM.toGLM_isAStable_iff` (Backlog item #7) to the **Current
Target**. Open `OpenMath/LMMAsGLM/StabilityIff.lean` with the iff
bridge as a sorry-first headline. The bridge consumes Step K.1
(`D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly`, now in
`StabilityCharpolyEval.lean`) plus a root-counting argument: roots
of `(m.toGLM.stabilityMatrix z).charpoly` lie in the closed unit disk
iff the same is true of `m.stabilityPolyPoly z`, modulo the spurious
`X^s` factor. The new module should `import
OpenMath.LMMAsGLM.StabilityCharpolyEval`.
