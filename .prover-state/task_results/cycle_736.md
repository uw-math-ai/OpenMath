# Cycle 736 Results

## Worked on
§521 Step K.1 — polynomial-level lift of J.4
(`D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly`).

## Approach
Followed the strategy recipe verbatim. Verified the candidate Mathlib
lemma `Polynomial.funext` via `lean_loogle` first:

```
Polynomial.funext : {R : Type u} [CommRing R] [IsDomain R] [Infinite R]
  {p q : Polynomial R} (∀ r, p.eval r = q.eval r) → p = q
```

Module: `Mathlib.Algebra.Polynomial.Roots`. ℂ is automatically a
`CommRing`, `IsDomain`, and `Infinite`, so the typeclass side conditions
resolve via `inferInstance` with no manual work.

Inserted K.1 immediately after J.4 (`D_mul_toGLM_charpoly_eval_general`,
line 3090) and before `end LMM`. Proof body is exactly the three-line
recipe:

```lean
apply Polynomial.funext
intro ξ
simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
  Polynomial.eval_C]
exact D_mul_toGLM_charpoly_eval_general m ξ hz hs
```

## Result
SUCCESS. `lake env lean OpenMath/LMMAsGLM/StabilityCharpoly.lean`
returns clean (no errors, no warnings, no `sorry`). File grew from 3149
to 3167 lines (+18). Still under the soft cap mention from the
strategy hand-off (split scheduled for a future cycle once the
K-ladder settles).

## Dead ends
None. The recipe landed exactly as the strategy predicted; no
deviations.

## Discovery
- `Polynomial.funext` is the direct, hypothesis-light name in current
  Mathlib (`Mathlib.Algebra.Polynomial.Roots`); no `Polynomial.ext_of_eval`
  detour needed.
- `simp only` with `eval_mul, eval_pow, eval_X, eval_C` reduces the
  polynomial-equality goal to the J.4 evaluation identity verbatim.
  The signature of J.4 (`(1 - z*β_last) * charpoly.eval ξ = ξ^s * poly.eval ξ`)
  matches exactly, so no further rewriting is required between `simp only`
  and `exact`.

## K.2 (optional stretch) — skipped
Per the strategy: the cycle 702 nonzero-ξ root iff lemma already exposes
the bridge. Did not detour into K.2 to keep the cycle tight and avoid
the recent two-cycle stall pattern (731, 735).

## Suggested next approach
Per the strategy hand-off: the next planner can promote
`LMM.toGLM_isAStable_iff` (item #7 of the Backlog Queue) to the
**Current Target** for cycle 737. The remaining work reduces to a
unit-disk root-counting argument over `stabilityPolyPoly` plus
zero-stability bookkeeping, now that K.1 is in place.

A file split for `OpenMath/LMMAsGLM/StabilityCharpoly.lean` (currently
3167 lines) is also one to two cycles away — the natural seam from the
cycle 734 hand-off note (H/I endpoint identities vs. K/J generic-ξ
identities) is unchanged.
