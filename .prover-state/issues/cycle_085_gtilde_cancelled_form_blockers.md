# Issue: Cycle 85 Gtilde cancelled-form blockers

## Blocker
`hasDerivAt_Gtilde_one` is now decomposed along the intended polynomial-cancellation route, but
the remaining blockers are:
- transporting `Rpoly.eval 1 ≠ 0` from `hρ_simple : m.rhoCDeriv 1 ≠ 0`
- proving the triple root `3 ≤ Ppoly.rootMultiplicity 1`
- finishing the derivative of the cancelled form `GtCancelled`

## Context
Current local structure in `OpenMath/MultistepMethods.lean`:
- `ρrevPoly`, `σrevPoly` are local `Polynomial ℂ` models for `rhoCRev` / `sigmaCRev`
- `hρ_factor : ρrevPoly = (X - 1) * Rpoly` is proved
- `hP_factor : Ppoly = (X - 1)^3 * Qpoly` is proved from the yet-unfinished `hP_triple`
- `GtCancelled w := (w - 1) * Qpoly.eval w / (2 * Rpoly.eval w)` is defined

The file compiles, but `hasDerivAt_Gtilde_one` still contains focused sub-`sorry`s for:
- `hR_eval_one_ne`
- `hP_triple`
- `hGtCancelled`
- `hGt_eventually`

Aristotle job status after the mandated single 30-minute wait:
- COMPLETE: `0d4838c3...` (`hR_eval_one_ne`)
- COMPLETE: `a6839dc1...` (`hGt_eventually`)
- COMPLETE_WITH_ERRORS: `5f282388...` (`hP_factor`) — manually salvaged
- IN_PROGRESS at check time: `9d83a22b...` (`hP_triple`)
- IN_PROGRESS at check time: `dbf75fd2...` (`hGtCancelled`)

## What was tried
- Replaced the old direct-limit proof attempt with the polynomial cancelled-form skeleton from
  planner guidance.
- Verified the file compiles after the structural refactor.
- Submitted five Aristotle jobs, waited 30 minutes, and checked exactly once.
- Tried to inline the Aristotle proofs for `hR_eval_one_ne` and `hGt_eventually`, but the proof
  terms were not local-drop-in correct.

## Possible solutions
- Prove `hR_eval_one_ne` in two lemmas:
  1. `Rpoly.eval 1 = (Polynomial.derivative ρrevPoly).eval 1`
  2. `(Polynomial.derivative ρrevPoly).eval 1 = -m.rhoCDeriv 1`
- Prove `hP_triple` by showing
  `Ppoly.eval 1 = 0`, `(Polynomial.derivative Ppoly).eval 1 = 0`,
  and `(Polynomial.derivative^[2] Ppoly).eval 1 = 0`,
  then applying `Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative`.
- After `hR_eval_one_ne` is available, revisit the Aristotle `hGt_eventually` proof and adapt its
  neighborhood argument using a cleaner open set:
  `{w | Polynomial.eval w Rpoly ≠ 0}`.
- Finish `hGtCancelled` last; it should become a standard quotient-rule proof once
  `Qpoly.eval 1 / (2 * Rpoly.eval 1) = 1/12` is established.
