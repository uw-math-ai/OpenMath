# Cycle 627 Results

## Worked on
Butcher §521 GLM A-stability framework:
`GeneralLinearMethod.IsAStable`,
`ButcherTableau.toGLM_isAStable_iff`, and
`rkImplicitEuler_toGLM_isAStable`.

## Approach
Followed the sorry-first shape from the strategy. Added the GLM predicate
after the §520 stability matrix block, using roots of
`(m.stabilityMatrix z).charpoly` as the eigenvalue encoding. Added a
local 1x1 constant-matrix charpoly helper in `OpenMath/RKAsGLM.lean`,
then used it to collapse the RK GLM A-stability condition to the scalar
stability-function bound.

Aristotle was attempted before manual proof work. Both
`submit_directory` and `submit_file` timed out after 120 seconds without
returning a project id, so there was no Aristotle project to sleep on or
check.

## Result
SUCCESS.

Landed steps 1, 2, 3, and 4:
- `GeneralLinearMethod.IsAStable`
- `ButcherTableau.toGLM_isAStable_iff`
- `rkImplicitEuler_toGLM_isAStable`
- `plan.md` §521 and backlog updates

The concrete implicit Euler bridge uses the existing
`rkImplicitEuler_aStable` theorem after proving that, on the closed left
half-plane, the total inverse RKAsGLM stability function agrees with the
existing one-stage `stabilityFn1` expression.

## Dead ends
The expected `Matrix.charpoly_fin_one` name is not present in this
Mathlib snapshot. Directly unfolding `Matrix.charpoly` and simplifying
`Matrix.charmatrix` closed the 1x1 constant charpoly lemma. A discovered
`Matrix.det_fin_one` lemma was not needed by `simp`.

## Discovery
For 1x1 RK embeddings, the key reusable fact is:
`Matrix.charpoly (fun (_ : Fin 1) (_ : Fin 1) => a) = X - C a`.
In this codebase it is easiest to prove locally with
`rw [Matrix.charpoly]; simp [Matrix.charmatrix]`.

`Polynomial.IsRoot` plus `simp [sub_eq_zero]` then turns roots of that
charpoly into equality with the single matrix entry. If a future cycle
wants to pivot between spectrum and charpoly encodings, Mathlib has
`Matrix.mem_spectrum_iff_isRoot_charpoly`.

## Suggested next approach
Keep `charpoly.IsRoot` as the GLM-level encoding for now. It matched the
RK sanity check and should align well with LMM stability polynomials.
`Matrix.spec`/spectrum may be cleaner for abstract spectral-radius
statements later, but it would add an encoding bridge immediately; defer
that until a theorem actually needs it.

Next §521 milestone: prove `LMM.toGLM_isAStable_iff` using
`LMM.toGLM_stabilityMatrix_apply`, then transport concrete LMM
A-stability results such as backward Euler and trapezoidal rule.
