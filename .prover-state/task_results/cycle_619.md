# Cycle 619 Results

## Worked on

Butcher §503 / §512 preparation in `OpenMath/LMMAsGLM.lean`: structural
`LMM.toGLM.V` row projection simp lemmas for the LMM-as-GLM embedding.

## Approach

Followed the sorry-first workflow by inserting the five planned lemmas with
`sorry` bodies and checking `lake env lean OpenMath/LMMAsGLM.lean`. Submitted
that scaffold to Aristotle as one batch; the project was accepted and moved to
`IN_PROGRESS`, but the local proofs were short enough to close immediately from
the existing `toGLM_isConsistent` expansion templates.

Each proof unfolds `toGLM`, normalizes the outer row index with the explicit
round-trip
`Fin.cast (Nat.two_mul s) (Fin.cast (Nat.two_mul s).symm _) = _`, then selects
the appropriate `Fin.addCases_left` or `Fin.addCases_right` branch and resolves
the row test with `if_pos` / `if_neg`. The two last past-y row lemmas also
normalize the inner column cast before selecting the past-y or past-h*f column
branch.

## Result

SUCCESS. Landed:

* `toGLM_V_castAdd_shift_apply`
* `toGLM_V_castAdd_last_castAdd_apply`
* `toGLM_V_castAdd_last_natAdd_apply`
* `toGLM_V_natAdd_shift_apply`
* `toGLM_V_natAdd_last_apply`

Also updated `plan.md` with the cycle 619 note for §512.

Verified:

* `lake env lean OpenMath/LMMAsGLM.lean`
* `lake env lean OpenMath/RKAsGLM.lean`

## Dead ends

No proof dead ends. The only pitfall was the expected cast normalization seam:
Lean does not automatically collapse
`Fin.cast (Nat.two_mul s) (Fin.cast (Nat.two_mul s).symm (...))` in these
matrix-row positions, so each lemma carries an explicit `hrow` or `hcol`
proved by `ext; simp`.

## Discovery

The manual V-row expansions inside `toGLM_isConsistent` already contain the
right normal forms. The new lemmas package those normal forms without changing
the larger consistency proof. Refactoring that proof can be deferred until the
new simp lemmas are consumed by the stability lift.

## Suggested next approach

Cycle 620 should start Phase 2 of the LMM stability lift:
prove an h*f-slot vanishing lemma for iterates of `m.toGLM.V`, using
`toGLM_V_natAdd_shift_apply` and `toGLM_V_natAdd_last_apply` as the row-level
normal forms. Keep the proof structural and avoid introducing complex-side
coercion lemmas until Phase 3.
