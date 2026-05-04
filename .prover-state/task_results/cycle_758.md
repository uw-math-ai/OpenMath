# Cycle 758 Results

## Worked on
§525 G-symplectic GLM predicate, RK-side bridge, and Gauss–Legendre
1/2/3 witnesses. Re-issue of the cycle 753/755/757 target after three
zero-output stalls.

## Approach
Followed the planner's pinned scaffold verbatim:

1. Confirmed `symplecticDefect`, `IsSymplectic`,
   `rkGaussLegendre{1,2,3}_isSymplectic`, and the `toGLM_*` simp
   lemmas (`toGLM_A`, `toGLM_U`, `toGLM_B`, `toGLM_V`) all exist with
   the expected shape via `Grep` on `OpenMath/SymplecticRK.lean` and
   `OpenMath/RKAsGLM.lean`.
2. Wrote `OpenMath/GSymplecticGLM.lean` with the index-form predicate
   `GeneralLinearMethod.IsGSymplectic` (using `Fin r → Fin r → ℝ` for
   the weight matrix `G`, mirroring `IsRankOneV` in
   `OpenMath/DIMSIM.lean`), the RK-side bridge
   `ButcherTableau.toGLM_isGSymplectic_of_isSymplectic`, and the
   three witnesses
   `rkGaussLegendre{1,2,3}_toGLM_isGSymplectic`.
3. The bridge proof used `G k₁ k₂ := 1`, `D := t.b`. The four
   subgoals collapse mechanically because `r = 1`:
   - symmetry of `G`: `rfl`.
   - stage symplecticity: `simp [toGLM_A, toGLM_B]` followed by
     `linarith` against `symplecticDefect i j = 0` (= the
     `b i * A i j + b j * A j i - b i * b j = 0` shape).
   - input/output compatibility: `simp [toGLM_U, toGLM_B, toGLM_V]`.
   - output preservation: `simp [toGLM_V]`.
4. Verified with `lake env lean OpenMath/GSymplecticGLM.lean`. First
   pass had three benign `unusedSimpArgs` linter warnings on
   `Fin.sum_univ_one`; removed those args (the `simp` lemmas
   `toGLM_*` already handle the `r = 1` collapse).
5. Updated `plan.md`:
   - `[ ] §525 G-symplectic methods` → `[x]` with cycle 758 reference.
   - Added cycle 758 entry to the Active Frontier history.
   - Replaced `## Current Target` with the §530/§531 GLM order pivot.

## Result
SUCCESS. `OpenMath/GSymplecticGLM.lean` compiles cleanly (no
warnings). Three concrete witnesses are proved one-liners off the
bridge. No `sorry`s introduced.

## Dead ends
None — the planner's pinned scaffold worked verbatim. The only
adjustment was dropping `Fin.sum_univ_one` from the `simp`
argument lists once the linter flagged them as unused (the existing
`toGLM_*` simp lemmas already trigger the `r = 1` collapse).

## Discovery
The §525 predicate at `r = 1` collapses cleanly in three of four
subgoals to single-term sums that `simp` handles directly via the
`toGLM_*` lemmas — `Fin.sum_univ_one` is not needed because
`simp` chases `m.B` and `m.V` to `t.b j` and `1` respectively, then
reduces the sum on its own. This is the same simplification pattern
as cycles 748/752/754/756 for §541/§542/§543.

The fourth subgoal (stage symplecticity) is the only one needing
`linarith` against the §37 defect identity. The compatibility and
output subgoals do **not** need the cycle 607 `bA_col_eq` column
identity, confirming the planner's "Do not wire through `bA_col_eq`"
note.

## Suggested next approach
Take the **§530 / §531 GLM order definition** pivot already written
into `## Current Target`. The shape is:

- Define `GeneralLinearMethod.HasOrder p` (or a §530-faithful name)
  via Taylor-expansion local truncation error in
  `OpenMath/GeneralLinearMethod.lean`. Scalar test problem suffices
  for the predicate.
- Bridge `ButcherTableau.toGLM_hasOrder_of_hasOrderGe` connecting to
  existing §31 RK order predicates (`HasOrderGe1`, `HasOrderGe2`)
  at small `p`. Trivial cases close by `simp` plus the RK
  consistency / row-sum lemmas.
- Concrete witness: `rkEuler` at order 1 or
  `rkImplicitMidpoint` at order 2.

Skip §55 IRKS — the predicate involves the minimal polynomial of
`M(z)`, which is closer to the LMM charpoly territory that stalled
in earlier cycles. Skip §544–§547 ARK examples — they need `r ≥ 2`
GLM charpoly factorisation (see `disproven.md`).

A plausible stretch goal for cycle 759 is a packaging corollary
combining `IsGSymplectic` with cycle 613 `IsConsistent` for the GL
RK embeddings, analogous to cycle 752's §541 × §542 packaging.
Trivial one-liner if pursued; skip otherwise.
