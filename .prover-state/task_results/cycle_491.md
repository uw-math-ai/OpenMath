# Cycle 491 Results

## Worked on
Chapter 5 Hamiltonian infrastructure in `OpenMath/Hamiltonian.lean`:
phase-space split, separable Hamiltonians, Hamiltonian vector field, and
energy conservation along exact Hamiltonian trajectories.

## Approach
Followed the sorry-first workflow: scaffolded the new file with definitions
and helper lemmas, verified it with `lake env lean OpenMath/Hamiltonian.lean`,
then submitted five Aristotle jobs:

- `29898545-ca0e-4bdc-b44c-7b273d1e0786`: full `energy_conserved`.
- `951968a9-a47a-4d23-9658-03f2fdec798b`: `dH_along_trajectory_eq_zero`.
- `74b9e657-4716-434b-8157-312a1494d594`: algebraic `inner_canonicalJ_self_eq_zero`.
- `7f638017-6fcd-458e-a5a9-de61d7cfb611`: elementary split/projection simp lemmas.
- `06b9e852-94dc-4e97-a58a-2f1766d998fc`: backup full-file attempt.

After the required 30-minute wait, checked the jobs once, inspected the
outputs, and transplanted the clean proof route from the derivative-helper
job. Kept the original narrow imports and rejected the backup output that
switched to `import Mathlib`.

## Result
SUCCESS. `OpenMath/Hamiltonian.lean` now contains no sorries and proves
`Hamiltonian.energy_conserved`. Added `import OpenMath.Hamiltonian` to
`OpenMath.lean`.

Verification:

- `lake env lean OpenMath/Hamiltonian.lean`
- `lake build OpenMath.Hamiltonian`
- `lake env lean OpenMath.lean`
- `rg -n "sorry" OpenMath/Hamiltonian.lean`
- `lean_verify Hamiltonian.energy_conserved` reported only standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`) and no source warnings.

## Dead ends
Aristotle job 5 produced a compiling full-file proof but replaced the imports
with `import Mathlib`, so it was not transplanted. Job 1 also compiled, but
contained generated `exact?` tactic artifacts; the final proof uses the
cleaner job 2 structure instead.

## Discovery
The `Fin (2*d)` split is manageable by defining
`splitIndexEquiv d : Fin d ⊕ Fin d ≃ Fin (2*d)` from `finSumFinEquiv` and
`Nat.two_mul`. The algebraic core is short after rewriting the Euclidean
inner product, reindexing through that equivalence, and cancelling the
position/momentum sums.

## Suggested next approach
Proceed to `OpenMath/Symplectic.lean`. Reuse `Hamiltonian.splitIndexEquiv`,
`Hamiltonian.qIndex`, `Hamiltonian.pIndex`, and
`Hamiltonian.inner_canonicalJ_self_eq_zero` when defining the canonical
symplectic matrix/operator and the symplecticity predicate.
