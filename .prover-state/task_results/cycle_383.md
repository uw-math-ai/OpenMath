# Cycle 383 Results

## Worked on
Adams-Moulton 4-step (AM4): definition, consistency, implicitness, order 5,
zero-stability, and convergence via Dahlquist equivalence.

## Approach
Followed the AM4 extension pattern from AM3/AB4:

1. Added `adamsMoulton4 : LMM 4` after `adamsBashforth4`.
2. Wrote the sorry-first scaffold for consistency, implicitness, order, and
   zero-stability, then checked `OpenMath/MultistepMethods.lean`.
3. Closed consistency with `Fin.sum_univ_five` and `norm_num`.
4. Closed implicitness by reducing the last beta coefficient to
   `(251 / 720 : Real) != 0`.
5. Closed `adamsMoulton4_order_five` by `interval_cases q`, using the live
   `HasOrder` definition's required `q = 6` nonzero condition.
6. Reused the AB4 zero-stability argument, since AM4 has the same
   `alpha = ![0, 0, 0, -1, 1]` and hence `rho(xi) = xi^3 * (xi - 1)`.
7. Added `adamsMoulton4_convergent` in `OpenMath/DahlquistEquivalence.lean`.
8. Marked AM4 complete in `plan.md`.

Aristotle job results: no Aristotle job was submitted. The cycle-specific
strategy explicitly said not to front-load a batch and to submit only if a
specific AM4 lemma blocked after a manual attempt; all AM4 proof obligations
closed manually.

## Result
SUCCESS.
- `lake env lean OpenMath/MultistepMethods.lean` compiles.
- `lake build OpenMath.MultistepMethods` refreshed the imported olean cache.
- `lake env lean OpenMath/DahlquistEquivalence.lean` compiles.
- `plan.md` section 1.2 now marks AM4 `[x]`.

## Dead ends
The scaffold initially used the planner-provided beta signs
`[19, -106, 264, -646, 251]/720`. Those signs do not satisfy the live
consistency equation for the existing LMM convention. I corrected AM4 to the
standard Adams-Moulton coefficients
`[-19, 106, -264, 646, 251]/720`, matching the AM3 ordering already in the
file.

## Discovery
`lake env lean OpenMath/DahlquistEquivalence.lean` reads the cached
`OpenMath.MultistepMethods` olean, so after adding exported declarations to
`MultistepMethods.lean`, `lake build OpenMath.MultistepMethods` is needed
before checking downstream files directly.

## Suggested next approach
The next mechanical addition is AM5, but per the cycle strategy it should be
left for the next planner cycle. The deeper blockers remain the deferred
Theorem 359D textbook lookup, `thm_358A_if`, Radau IA family bridge, and the
odd up-arrow connected-support chain.
