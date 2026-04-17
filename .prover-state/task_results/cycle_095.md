# Cycle 95 Results

## Worked on
Picard-Lindelof existence and uniqueness theorem (Iserles §1.1, thm:110C) and Lipschitz condition definition (def:110A). New file `OpenMath/PicardLindelof.lean`.

## Approach
Sorry-first workflow: wrote full file structure with all definitions and theorem statements, compiled, then closed sorrys one by one using Mathlib wrappers.

- **Uniqueness**: Wrapped `ODE_solution_unique_of_mem_Icc_right` with `s := fun _ => univ`
- **Continuous dependence**: Wrapped `dist_le_of_trajectories_ODE_of_mem` with NNReal conversion
- **Perturbation bound**: Wrapped `dist_le_of_approx_trajectories_ODE_of_mem` with `εf := 0`
- **HasDerivWithinAt conversion**: Proved `hasDerivWithinAt_Icc_to_Ici` using `Icc_mem_nhdsGE` at left endpoint and `Icc_mem_nhds` at interior
- **Existence**: Submitted to Aristotle (project da85ce79-426b-46f8-b1a8-5fc85c94c090). Aristotle stuck at 3% after 30+ minutes. The proof requires interval subdivision for general `L*(b-a) >= 1` which is ~200 lines. Accepted sorry.

## Result
PARTIAL SUCCESS — 6 theorems proved, 1 sorry remaining (`exists_solution`).

Proved (sorry-free):
1. `IsLipschitzInSecondVar` — definition (def:110A)
2. `IsLipschitzInSecondVar.lipschitzWith` — conversion to Mathlib LipschitzWith
3. `IsLipschitzInSecondVar.lipschitzOnWith` — conversion to LipschitzOnWith
4. `PicardLindelof.unique` — uniqueness (thm:110C uniqueness part)
5. `PicardLindelof.continuous_dependence` — exponential bound on solution difference
6. `PicardLindelof.perturbation_bound` — gronwallBound for approximate solutions
7. `PicardLindelof.hasDerivWithinAt_Icc_to_Ici` — filter conversion helper
8. `PicardLindelof.exists_unique` — combined existence+uniqueness (depends on sorry)

Sorry remaining:
1. `PicardLindelof.exists_solution` — existence part. Needs `IsPicardLindelof` construction with interval subdivision.

## Dead ends
- Direct `IsPicardLindelof` construction fails for general `L*(b-a)` because Mathlib requires `M * (b-a) <= R` (ball radius constraint), which is only satisfiable when `L*(b-a) < 1`.
- `lean_multi_attempt` with `exact?`, `aesop`, `simp` could not close the existence sorry.
- Aristotle job submitted but still in progress at 3% after 30+ minutes.

## Discovery
- Mathlib's Gronwall module provides excellent wrappers for uniqueness and continuous dependence — just need `s := fun _ => univ` and NNReal coercion handling.
- `Icc_mem_nhdsGE` (not `Icc_mem_nhdsWithin_Ici`) is the correct name for the filter inclusion at left endpoints.
- `HasDerivWithinAt.mono_of_mem_nhdsWithin` (not `HasFDerivAtFilter.mono_of_mem`) is the correct filter monotonicity lemma.
- General Picard-Lindelof existence requires interval subdivision (~200 lines) because `IsPicardLindelof` only handles the case where the Picard iteration contracts on a single ball.

## Suggested next approach
- Close `exists_solution` in a dedicated cycle: subdivide `[a,b]` into `n` subintervals with `L*(b-a)/n < 1`, construct `IsPicardLindelof` on each, chain solutions using `unique`. This is ~200 lines of careful interval arithmetic.
- Alternatively, accept the sorry and move to Chapter 4 targets (convergence theory for multistep methods).
