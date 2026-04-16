# Issue: tupleSucc power boundedness restriction gap

## Blocker
The remaining Dahlquist-equivalence sorry is blocked at the step turning the
spectral/root-condition information into a global bound on `tupleSucc ^ n`.

The first unresolved subproblem is:
- on `Module.End.maxGenEigenspace T μ` with `‖μ‖ = 1`, show
  `T v = μ • v` for every `v`.

The second unresolved subproblem is:
- combine per-generalized-eigenspace bounds into a single bound on all of
  `Fin s → ℂ`.

## Context
Current decomposition in `OpenMath/DahlquistEquivalence.lean`:
- `tupleSucc_minpoly_rootMultiplicity_eq_one_of_unit_eigenvalue` — proved
- `tupleSucc_eq_smul_on_unit_eigenspace` — sorry
- `tupleSucc_pow_bounded_on_disk_eigenspace` — sorry
- `uniformly_bounded_tupleSucc_iterates` — final sorry still open

The proved helper gives:
- for a unit-circle eigenvalue `μ` of `T = m.toLinearRecurrence.tupleSucc`,
  `(minpoly ℂ T).rootMultiplicity μ = 1`.

## What was tried
- Tried the planner’s `finrank_maxGenEigenspace_eq` shortcut. This stalls because
  it speaks about the actual `LinearMap.charpoly T`, while the existing root
  simplicity theorem is for the recurrence polynomial `E.charPoly`.
- Added a proved bridge to the ambient `minpoly` instead:
  simple unit-circle roots of `E.charPoly` force simple unit-circle roots of
  `minpoly ℂ T`.
- Set up the requested helper-lemma structure and verified the file builds.
- Submitted five Aristotle jobs focused on the unit-eigenspace lemma, the
  disk-eigenspace lemma, and the final combination.

## Possible solutions
- Restriction/minpoly route:
  show the minimal polynomial of `T` restricted to `maxGenEigenspace T μ`
  divides both `minpoly ℂ T` and `(X - C μ)^k`. Since the `μ`-multiplicity in
  `minpoly ℂ T` is `1`, conclude the restricted minimal polynomial divides
  `X - C μ`, hence `T = μ • id` on that subspace.
- If the restriction lemma is too awkward in Mathlib, isolate the final step as a
  separate theorem:
  “an endomorphism over `ℂ` with all eigenvalues in the closed unit disk and
  semisimple unit-circle generalized eigenspaces has uniformly bounded powers.”
- For the global combination, look for a direct sum / projection API around
  `iSup_maxGenEigenspace_eq_top` and `independent_maxGenEigenspace`; otherwise
  phrase the result in terms of a finite family of generalized eigenspaces first.
