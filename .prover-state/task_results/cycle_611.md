# Cycle 611 Results

## Worked on

Butcher §503 — embedding an arbitrary `s`-step linear multistep method
as a one-stage general linear method with `r = 2 * s` past-state input
quantities.

## Approach

Created `OpenMath/LMMAsGLM.lean` following the §502 `RKAsGLM` template:

- `LMM.toGLM : GeneralLinearMethod 1 (2 * s)` with `A`, `U`, `B`, and
  `V` blocks for the past `y` / past `h · f` representation.
- Projection lemmas for `A 0 0`, the past-`y` half of `U`, and the
  past-`f` half of `U`.
- Scalar stage-map agreement theorem splitting the `Fin (2 * s)` input
  sum into the two `Fin s` halves.
- Explicitness equivalence between `m.IsExplicit` and
  `m.toGLM.IsExplicit`.

Aristotle was not used; the target closed manually with `simp`,
`Fin.sum_univ_add`, and `ring`.

## Result

SUCCESS — `OpenMath/LMMAsGLM.lean` compiles cleanly with zero `sorry`.
`lake build OpenMath.LMMAsGLM` also succeeds; it replays existing
warnings from `OpenMath/MultistepMethods.lean`, but introduces no new
warnings in `OpenMath/LMMAsGLM.lean`. The plan was updated to mark
§503 complete, add the cycle 611 frontier log entry, and promote §510
to backlog item #1.

## Dead ends

The first direct implementation hit a Lean indexing mismatch:
`Fin.castAdd s k` and `Fin.natAdd s k` live in `Fin (s + s)`, while
the required API uses `Fin (2 * s)`. These are propositionally equal
by `Nat.two_mul`, but not definitionally equal. The final file keeps
the requested `2 * s` surface and uses a file-local coercion through
`Fin.cast (Nat.two_mul s).symm` so the exact half-vector notation
elaborates without exporting helper lemmas.

## Discovery

For stage-map splitting over `Fin (2 * s)`, first transport the sum to
`Fin (s + s)` with `Fin.sum_congr'`, then apply `Fin.sum_univ_add`.
After that, `simp [Fin.addCases, Fin.natAdd]` plus
`simp [Fin.addNat, Nat.add_comm]` aligns the right-half indices.

## Suggested next approach

Proceed to backlog item #1, Butcher §510: replace the placeholder
`GeneralLinearMethod.IsConsistent` hook with the Chapter 5 consistency
and stability predicates. The §502 and §503 embeddings now provide
concrete examples to test those definitions against.
