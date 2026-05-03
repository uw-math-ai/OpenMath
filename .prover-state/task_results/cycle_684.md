# Cycle 684 Results

## Worked on
§521 Step C.9 — name the α-summand polynomial of
`toGLM_stabilityCharpolyRowF`, mirroring cycle 682's β-summand naming, and
restate the assembled split with both summand polynomials named.

Active file: `OpenMath/LMMAsGLM/StabilityCharpoly.lean` (1028 → 1071 lines).

## Approach
Followed the strategy verbatim. Three deliverables landed in order at the
end of `StabilityCharpoly.lean`, before `end LMM`:

1. `rowFAlphaPoly (m : LMM s) : Polynomial ℂ` — α-summand named, with
   the body matching the α-summand of
   `toGLM_stabilityCharpolyRowF_eq_summand_split` verbatim.
2. `toGLM_stabilityCharpolyRowF_eq_alphaPoly_plus_PY_betaPoly` —
   restatement of the split with both summand polynomials named, proved
   via `rw [toGLM_stabilityCharpolyRowF_eq_alpha_plus_PY_beta m hs]` then
   `rfl` (the cycle 682 pattern; `rfl` sufficed without an `unfold`).
3. (Stretch) `rowFAlphaResidual` private abbreviation + the trivial
   `rowFAlphaPoly_eq_residual_sum` factorization through it. Both
   private; closes by `unfold ...; rfl`.

## Result
SUCCESS — all three deliverables landed sorry-free.

`lake env lean OpenMath/LMMAsGLM/StabilityCharpoly.lean` compiles clean,
as do `OpenMath/LMMAsGLM/Stability.lean` and the umbrella
`OpenMath/LMMAsGLM.lean`.

## Dead ends
None — the strategy's predicted resolution (`rfl` after `rw`) worked on
the first attempt for deliverable 2, and `unfold ...; rfl` worked on
the first attempt for deliverable 3.

## Discovery
- The α-summand definitional shape matched the RHS of
  `toGLM_stabilityCharpolyRowF_eq_alpha_plus_PY_beta` directly, so the
  fallback paths suggested in the strategy (extra `unfold rowFAlphaPoly`
  before `rfl`, or rewriting via `_eq_summand_split` instead) were not
  needed.
- The α-summand and β-summand now have parallel surface forms:
  `rowFAlphaPoly m` and `rowFBetaPoly m`. The headline reads as a clean
  `α + PY.charpoly · β` polynomial identity.

## Suggested next approach
The next planning seam — already flagged by the cycle 684 strategy — is
the degree analysis of `rowFAlphaPoly`. This is **not** the trivial
`< s` mirror of `rowFBetaPoly_degree_lt`, because `rowFAlphaResidual l`
already has nontrivial degree (it routes through the
`PY.charmatrix.adjugate`, whose entries have degree ≤ s-1). The natural
next deliverables are:

1. A degree bound for each `rowFAlphaResidual m l` (likely `≤ s-1`,
   coming from `Polynomial.degree_adjugate_le` on the `PY` charmatrix).
2. From (1), a degree bound for `rowFAlphaPoly` — combining the
   per-`l` residual bound with the `X^l` factor and `degree_sum_le`,
   the expected bound is something like `≤ 2*s - 2` or `< 2*s - 1`.
   The exact constant is what the degree-counting argument of
   `lmm_stability_charpoly_step_c.md` needs.

The private `rowFAlphaResidual` abbreviation was added precisely so a
later cycle can state and prove (1) cleanly without re-expanding the
nested `Matrix.vecMul` at every step.

## File size status
`StabilityCharpoly.lean` 1028 → 1071 lines (added ~43 lines). Well
under the 3000-line cap. No file split needed.
