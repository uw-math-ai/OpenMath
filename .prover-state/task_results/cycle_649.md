# Cycle 649 Results

## Worked on

Backlog Queue item #7: Butcher Section 521 LMM-as-GLM A-stability bridge
in `OpenMath/LMMAsGLM.lean`.

Added:

- `LMM.toGLM_stabilityMatrixPY_charpoly_isRoot_iff_stabilityPoly_of_bdf`
- `LMM.toGLM_stabilityMatrix_eigenvalue_iff_of_bdf`
- `LMM.toGLM_isAStable_of_bdf`

## Approach

Started sorry-first with the PY-block root bridge, the full GLM charpoly
root split, and the A-stability transport theorem. Verified the scaffold
with `lake env lean OpenMath/LMMAsGLM.lean`, then closed the sorries in
dependency order.

The PY-block helper evaluates cycle 648's
`toGLM_stabilityMatrixPY_charpoly_eq_stabilityPolyPoly_of_bdf` at `xi`,
uses `Polynomial.eval_smul` and the nonzero denominator hypothesis to
cancel the scalar, then applies `stabilityPolyPoly_eval`.

The full charpoly bridge uses cycle 645's
`toGLM_stabilityMatrix_charpoly_of_bdf`, `Polynomial.root_mul`, and the
PY-block helper. The statement has a `[NeZero s]` typeclass hypothesis:
without it, the planner's exact `xi = 0 \/ ...` conclusion is false for
`s = 0`, because the nilpotent factor is `X^0 = 1`.

The A-stability theorem handles `s = 0` separately. In that case the
full charpoly formula simplifies to the zero-dimensional PY block and
`simp` eliminates impossible roots. For `s != 0`, it instantiates
`NeZero s`, applies the eigenvalue split, closes the zero root by
`simp`, and closes the stability-polynomial root by the input
`m.IsAStable`.

## Result

SUCCESS for deliverables 1 and 2, sorry-free.

Verification:

```bash
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/LMMAsGLM.lean
```

exits 0 with no warnings. `rg -n "sorry|admit" OpenMath/LMMAsGLM.lean`
finds no matches. The file is now 2801 lines, still below the 3000-line
hard cap.

Stretch deliverable 3 was skipped. The live code has
`theorem bdf3_not_aStable : not bdf3.IsAStable` in `OpenMath/BDF.lean`;
there is no `bdf3_aStable` theorem to use, and a theorem
`(bdf3 : LMM 3).toGLM.IsAStable` would contradict the intended BDF3
stability facts.

## Dead ends

The planner's exact root-iff statement without a nonzero-step hypothesis
does not hold at `s = 0`. Counterexample shape: the `X^s` factor is `1`,
so `0` is not introduced as a spurious root, while the proposed RHS still
contains `xi = 0`. The landed theorem keeps the requested name but adds
`[NeZero s]`; `toGLM_isAStable_of_bdf` remains fully general by treating
`s = 0` directly.

No Mathlib spectrum/eigenvalue-membership lemma was needed because
`GeneralLinearMethod.IsAStable` is already defined directly in terms of
`charpoly.IsRoot`.

## Discovery

Useful Mathlib lemmas and tactics:

- `Polynomial.root_mul` splits roots of a product over `Complex`.
- `Polynomial.IsRoot.def` converts roots to evaluation equalities.
- `Polynomial.eval_smul` is enough to cancel the nonzero scalar from the
  cycle 648 PY-block proportionality.
- `pow_eq_zero_iff (NeZero.ne s)` converts roots of `X^s` to `xi = 0`
  when `s != 0`.

The `s = 0` edge case is not relevant to standard BDF methods, but it
matters for universally quantified `LMM s` infrastructure.

## Aristotle status

No Aristotle submission. The manual proof closed cleanly, and recent
cycles report immediate HTTP 429 for submissions. The cycle 649 strategy
explicitly said not to block on Aristotle and to submit at most an
optional scaffold after manual landing.

## Suggested next approach

Use `LMM.toGLM_isAStable_of_bdf` to replace or shorten concrete BDF1/BDF2
GLM A-stability proofs, or add concrete BDF denominator lemmas for methods
that are actually LMM A-stable. Do not target `bdf3_toGLM_isAStable` as
an A-stability theorem unless the goal is deliberately weakened to an
A(alpha)-stability sector statement.
