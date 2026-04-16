# Cycle 085 Results

## Worked on
`OpenMath/MultistepMethods.lean`, specifically `hasDerivAt_Gtilde_one` and the shared
polynomial-cancellation infrastructure it needs.

## Approach
Replaced the old single-`sorry` proof with a sorry-first cancelled-form skeleton:
- defined local reversed polynomials `ρrevPoly`, `σrevPoly`
- connected them to `m.rhoCRev` / `m.sigmaCRev`
- factored `ρrevPoly = (X - 1) * Rpoly`
- defined `Ppoly`, `Qpoly`, and the cancelled form `GtCancelled`
- reduced the proof to four explicit subgoals:
  `hR_eval_one_ne`, `hP_triple`, `hGtCancelled`, `hGt_eventually`

Also closed the easy divisibility/factorization step:
- `hP_factor : Ppoly = (X - 1)^3 * Qpoly`

Submitted five Aristotle jobs against the updated file:
1. `0d4838c3-ff8b-400e-8b19-d5211ee4f8d0` for `hR_eval_one_ne`
2. `9d83a22b-4eef-4ba0-b6bc-a734040807ca` for `hP_triple`
3. `5f282388-d13c-4a96-915b-335cc22eb524` for `hP_factor`
4. `dbf75fd2-30e7-412d-8d9e-f22369ff61af` for `hGtCancelled`
5. `a6839dc1-497b-44f9-874b-29bc01721232` for `hGt_eventually`

Then followed the mandated wait (`sleep 1800`) and performed one status check.

## Result
FAILED

The target theorem is still open, but the proof shape now matches the cycle-85 strategy and
the file compiles with the two original theorem declarations still as the only `sorry`-using
declarations.

Aristotle outcomes after the single post-wait check:
- `0d4838c3...` COMPLETE: produced a plausible `hR_eval_one_ne` proof, but the reindexing step
  did not drop into the local file cleanly.
- `5f282388...` COMPLETE_WITH_ERRORS: the useful part was salvaged manually into the file as the
  working proof of `hP_factor`.
- `a6839dc1...` COMPLETE: produced a plausible neighborhood-transfer proof for `hGt_eventually`,
  but it depends on the unfinished `hR_eval_one_ne` transport lemma and still needs polishing.
- `9d83a22b...` IN_PROGRESS at check time.
- `dbf75fd2...` IN_PROGRESS at check time.

Verified:
- `env PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/MultistepMethods.lean`
  compiles (with the expected two declaration-level `sorry` warnings).

## Dead ends
- Directly pasting Aristotle’s `hR_eval_one_ne` proof failed on the `Fin.rev` reindexing rewrite.
- Directly pasting Aristotle’s `hGt_eventually` proof failed because the neighborhood/preimage
  term was not type-correct in the local environment.
- `hP_triple` was not reachable quickly by brute-force simplification alone; the first derivative
  reduces to a manageable expression, but the second derivative and nonzero-polynomial side
  condition still need structured work.

## Discovery
- The polynomial-cancellation setup itself is viable in Lean and compiles.
- `hP_factor` can be proved cleanly from `hP_triple` using
  `Polynomial.pow_rootMultiplicity_dvd`, `Polynomial.modByMonic_eq_zero_iff_dvd`, and
  `Polynomial.modByMonic_add_div`.
- `simp` already reduces `Ppoly.eval 1` to the consistency fact. The triple-root proof is likely
  feasible by evaluating `Ppoly`, `Ppoly'`, and `Ppoly''` at `1` and feeding those into
  `Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative`.

## Suggested next approach
1. Finish `hR_eval_one_ne` cleanly using
   `Polynomial.divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative` plus a separate
   lemma identifying `(Polynomial.derivative ρrevPoly).eval 1 = -m.rhoCDeriv 1`.
2. Prove `hP_triple` via
   `Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative` with explicit derivative
   evaluations at `1`.
3. Use those two lemmas to repair `hGt_eventually`.
4. Only after that attack `hGtCancelled`, which is now the isolated final analytic/algebraic step.
