# Cycle 714 Results

## Worked on

§521 Step D.9 (`D_mul_toGLM_charpoly_eval_one_concrete`) and Step D.9b
(`D_mul_toGLM_charpoly_eval_one_concrete_of_bdf`) in
`OpenMath/LMMAsGLM/StabilityCharpoly.lean`. Cycles 711 and 713 were
scheduled for this work and produced zero output; cycle 714 reissues
and lands it.

## Approach

Followed the strategy verbatim. Single `Edit` inserting two theorems
immediately before `end LMM` (replacing the trailing block of the
cycle 712 D.8 theorem + `end LMM` line as anchor). One `Bash`
verification run.

* D.9: bare 3-`rw` chain — `D_mul_toGLM_charpoly_eval_one_eq` then
  `toGLM_stabilityMatrixPY_zero_charpoly_eval_one` then
  `rowFBetaPoly_eval_one`. This is the literal `ξ = 1` analogue of
  the cycle 712 D.8 close, mirroring its 3-`rw` pattern at lines
  1900–1902.
* D.9b: `rw [D.9]`, then a `Finset.sum_eq_zero` proof of
  `∑ k, β(castSucc k) = 0` using the line-1765 `Fin.castSucc_lt_last
  k).ne` BDF discharge pattern, then `rw [hBetaSum]` then `ring`.

## Result

**SUCCESS.** Both theorems compiled on the first try; the bare
3-`rw` chain closed D.9 directly (no `rfl` / `ring` /
`linear_combination` fallback was needed), and the
`hBetaSum` + final `ring` chain closed D.9b directly. `lake env lean
OpenMath/LMMAsGLM/StabilityCharpoly.lean` returned with no output,
confirming a clean compile of the file at its new ~1969-line state.

## Dead ends

None. The strategy's predicted 3-`rw` close worked verbatim; no
fallback path was exercised.

## Discovery

The cycle 712 D.8 close pattern transfers verbatim to the `ξ = 1`
analogue with no subterm or coercion adjustments. This is consistent
with the design choice in cycle 710 D.3 of stating
`D_mul_toGLM_charpoly_eval_one_eq`'s RHS to leave the literal subterms
`((toGLM_stabilityMatrixPY m 0).charpoly).eval 1` and
`(rowFBetaPoly m).eval 1` exposed for direct `rw`. The
parenthesisation matches the closed-form RHSs of D.5 and D.7 exactly,
which is why no `ring` was needed at the end.

For D.9b, the `(1 + ∑ α(castSucc l)) * 0 = 0` collapse leaves the
`+ 0` adjustment that `ring` discharges trivially after the `hBetaSum`
rewrite. No `linear_combination` fallback was needed.

## File-state confirmation

* Only `OpenMath/LMMAsGLM/StabilityCharpoly.lean` was edited.
* No other lemma in that file was touched.
* No other file (in `OpenMath/`, `extraction/`, `ButcherGroup/`,
  etc.) was edited.
* No new tracked files were created. No `sorry` was introduced; the
  project remains at zero `sorry` count.
* The file is now ~1969 lines, well under the 3000-line cap.

## Suggested next approach (cycle 715)

The natural follow-up is **D.10**: closed-form evaluations of
`(rowFAlphaPoly m).eval 0` and `(rowFAlphaPoly m).eval 1`. This is
the only remaining abstract opacity in both ξ-evaluations of
`((m.toGLM.stabilityMatrix z).charpoly).eval ξ` for `ξ ∈ {0, 1}`
(the other residual is `(rowYQuot m).eval ξ`).

`rowFAlphaPoly` is harder than the `rowFBetaPoly` family because it
routes through `Matrix.vecMul` against an adjugate at `X` (not at a
scalar). The cycle 712 task result already flagged this. Recommended
scout sequence for cycle 715:

1. `Grep` `rowFAlphaPoly` across `OpenMath/LMMAsGLM/*.lean` to find
   its definition and any landed lemmas.
2. `Grep` `Matrix.adjugate_apply` and `Matrix.vecMul_adjugate_apply`
   across the file to locate any landed adjugate-eval helpers.
3. `Grep` `charmatrix_adjugate_natDegree_le` and
   `charmatrix_adjugate_degree_lt` to recover the cycle 686 / 687
   degree bounds.
4. Once located, plan whether `rowFAlphaPoly_eval_zero` and
   `_eval_one` are closeable via direct `Polynomial.eval ·` pushdown
   through `Matrix.vecMul` and the adjugate, or whether they need an
   intermediate `vecMul`-eval helper.

Beyond D.10 is **D.11** (degree-counting for spurious roots), still
several cycles away from `LMM.toGLM_isAStable_iff`.

## Strategy-compliance notes

* Did not touch §38 `ButcherGroup/*.lean` (paused).
* Did not redefine `activeStabilityPolyPoly` or any cycle-708 / 710
  / 712 lemma signature.
* Did not restate `toGLM_stabilityMatrixPY_zero_charpoly_eval_one`
  or `rowFBetaPoly_eval_one`.
* Did not attempt the disproven `activeStabilityPolyPoly_eq_…` or
  `D_mul_toGLM_charpoly_eq_X_pow_mul_active_of_bdf` identities (see
  `disproven.md` and the cycle 692 issue).
* Did not add `push_cast`/`linear_combination`/`simp` to the close —
  pure `rw` worked as predicted.
* Did not open `OpenMath/LMMAsGLM.lean` or `Stability.lean`.
* No tracked scratch files were added.
