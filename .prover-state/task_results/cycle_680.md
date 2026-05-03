# Cycle 680 Results

## Worked on

Strategy deliverable: assemble the cycle-676 column projection
identities for `toGLM_stabilityCharpolyRowF` into a single closed form,
plus the trivial BDF re-export and the structural forward-look note.

## Approach

1. Read the existing `toGLM_stabilityCharpolyRowF_eq_explicit` (line 343)
   to confirm its RHS shape exactly matches the LHS shapes of the two
   cycle-676 summand lemmas (`_α_summand_col_eq` and `_β_summand_eq`).
2. Append the new theorem
   `toGLM_stabilityCharpolyRowF_eq_summand_split` immediately after
   `_α_summand_col_eq` (line 947 area), proving by the strategy's exact
   3-line `rw` chain.
3. Append the BDF re-export
   `toGLM_stabilityCharpolyRowF_eq_summand_split_of_bdf` whose proof is
   just `toGLM_stabilityCharpolyRowF_of_bdf m hs hbdf`.
4. Verify with `lake env lean OpenMath/LMMAsGLM/StabilityCharpoly.lean`.

## Result

SUCCESS. Both new theorems compile cleanly with no diagnostics. File
length 949 → 991 lines (well under cap). The 3-line `rw` chain fired
without needing `conv_lhs` / `show` scaffolding — the cycle-676 summand
lemmas were stated in exactly the matching shape.

Also updated `.prover-state/issues/lmm_stability_charpoly_step_c.md` to
reflect Step C.7 closure and the structural forward-look note (the
α-summand caps at `X^(s-1)`, so a general `X^s` extraction of `RowF` is
a dead end).

## Dead ends

None this cycle. The strategy's predicted 3-line proof was correct on
the first attempt.

## Discovery

The `_β_summand_eq` and `_α_summand_col_eq` lemmas from cycle 676 were
stated with `by omega` proofs of `s - 1 < s` rather than the
`by have := i.isLt; omega` shape used elsewhere — this matches the
explicit form's `by omega` precisely, so `rw` fires without bound-proof
mismatches. (Worth keeping in mind for future column-projection lemmas:
keep the bound proof shape uniform across the chain.)

## Suggested next approach

Per the strategy's structural forward-look: `LMM.toGLM_isAStable_iff`
should NOT proceed via `X^s` extraction from `RowF`. The α-summand
column closed form caps at `X^(s-1)` for non-BDF LMMs, so any
`rowFQuot_mul_X_pow_eq_RowF` shape is a dead end (it only holds when
`RowF = 0`, i.e. BDF).

Recommended next-cycle target: design `LMM.toGLM_isAStable_iff` as a
root-location argument over
`toGLM_stabilityCharpolyRowF_eq_summand_split` plus the existing
`toGLM_stabilityMatrix_charpoly_explicit`. The cleanest framing seems
to be: show that the rank-one correction's contribution to the full
charpoly has degree strictly less than `2s`, so the spurious roots
(the `s` zeros at `X = 0` introduced by the duplicated `Y`-block) do
not interact with the active stability roots from `PY` — i.e. the
charpoly factors as `X^? · (active stability poly) · (unit)` for a
shift exponent that depends on degree counting, not on extracting `X^s`
literally.

A focused next cycle would be: state the degree of
`toGLM_stabilityCharpolyRowF` (via the assembled split) and its
contribution to `toGLM_stabilityMatrix_charpoly_explicit`, then derive
the active-poly factorisation from there.
