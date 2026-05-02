# Cycle 608 Results

## Worked on

Butcher §341 — solvability of implicit Runge–Kutta stage equations
(Backlog Queue item #7). All five strategy deliverables landed sorry-free
in `OpenMath/RungeKutta.lean`:

1. `ButcherTableau.stageMap` plus the `@[simp]` projection
   `stageMap_apply`
2. `ButcherTableau.rowAbsSumMax` plus `rowAbsSumMax_nonneg` and the
   helper `row_absSum_le_rowAbsSumMax`
3. `stageMap_dist_le` (concrete distance bound) and
   `stageMap_lipschitzWith` (`LipschitzWith` packaging)
4. Headline: `stageEquations_unique_solution`
5. Concrete corollary: `rkImplicitEuler_stageEquations_unique_solution`

## Approach

Sorry-first scaffold, then proved each lemma in turn.

- `stageMap` and `stageMap_apply`: definitional `rfl`.
- `rowAbsSumMax`: dependent-`if` on `0 < s` to handle the vacuous case.
  `rowAbsSumMax_nonneg` from `Finset.le_sup'_of_le` plus
  `Finset.sum_nonneg` of `abs_nonneg`. `row_absSum_le_rowAbsSumMax`
  extracts `0 < s` from `Fin s`-element `i` then `Finset.le_sup'`.
- `stageMap_dist_le`: sup-metric reduction via `dist_pi_le_iff` (RHS
  nonneg by `positivity`). Coordinate-wise:
  - `f`-Lipschitz step using `LipschitzWith.dist_le_mul`.
  - Inner distance simplified via `Real.dist_eq`, `linear_combination`
    on the linearised stage difference, and `abs_of_nonneg hh`.
  - Triangle on `Finset` sums (`Finset.abs_sum_le_sum_abs`,
    `Finset.sum_le_sum`, `dist_le_pi_dist`) reduces
    `|∑ A i j (K j − K' j)| ≤ (∑ |A i j|) · dist K K'`.
  - Combined via three `mul_le_mul_of_nonneg_left` plus `ring`
    rearrangement.
- `stageMap_lipschitzWith`: wraps `stageMap_dist_le` through
  `LipschitzWith.of_dist_le_mul`, using `Real.toNNReal` for both `h`
  and `rowAbsSumMax`. The coercion identity uses `NNReal.coe_mul`
  and `Real.coe_toNNReal _ (· ≥ 0)` twice.
- `stageEquations_unique_solution`: assemble the contraction (Lipschitz
  + `Klip < 1` from `hsmall` via `exact_mod_cast`), instantiate
  `ContractingWith`, supply `Nonempty (Fin s → ℝ)` via the zero
  function, then `ContractingWith.exists_fixedPoint` from base point
  `(0 : Fin s → ℝ)` (`edist_ne_top` for the Pi metric is automatic) and
  `ContractingWith.fixedPoint_unique` for uniqueness.
- Backward Euler corollary: `rkImplicitEuler.rowAbsSumMax = 1` by
  unfolding the dependent-`if` at `0 < 1` and `simp [rkImplicitEuler]`.
  Specialise the headline.

## Result

SUCCESS. `lake env lean OpenMath/RungeKutta.lean` is silent;
`lake build` finishes with `Build completed successfully (8087 jobs).`
`grep -c sorry OpenMath/RungeKutta.lean` returns `0`.

## Dead ends

- `(⟨h, hh⟩ : ℝ≥0) * L` did not synthesise the `HMul` instance — the
  anonymous constructor was treated as `Subtype` rather than `NNReal`
  by typeclass resolution. Replaced with `Real.toNNReal h`, which
  threads cleanly through `NNReal.coe_mul` / `Real.coe_toNNReal`.
- `linarith [hsum]` could not handle the
  `(y₀ + h*A) − (y₀ + h*B) = h * (A − B)` rearrangement because
  `h * sum` is opaque to it. `linear_combination h * hsum` closed it
  in one line.
- Initial calc-block had inconsistent indentation that triggered a
  spurious "function expected" error on a previously-bound `step1`
  hypothesis. Replaced by a sequence of `mul_le_mul_of_nonneg_left`
  steps and one short calc; this also reads better.
- The `ℝ≥0` notation was undefined until I added `open scoped NNReal`
  next to the existing `open Finset Real`.

## Discovery

- `Real.toNNReal` is the friction-free way to lift a `ℝ` with a
  nonnegativity hypothesis into `ℝ≥0` for downstream `LipschitzWith` /
  `ContractingWith` usage. Avoid the anonymous-constructor form
  `⟨x, hx⟩` here unless the target type is fully forced by an outer
  signature.
- `dist_pi_le_iff` (Pi sup metric) plus `dist_le_pi_dist` is the
  right pairing for sup-metric Lipschitz proofs on `Fin s → ℝ`. The
  RHS-nonnegativity hypothesis can be discharged by `positivity` once
  every factor is known nonneg.
- `ContractingWith.fixedPoint_unique` returns `x = fixedPoint f hf`,
  so uniqueness across two fixed points is `h₁ ▸ h₂.symm` style;
  used `rw [h1, ← h2]` directly.
- `dist_le_pi_dist K K' j` is the hidden gem for the coordinate
  bound. (Not `Pi.dist_le_iff`, which packages the iff direction.)

## Suggested next approach

The pattern (define a stage self-map, package it as `LipschitzWith`,
hit it with `ContractingWith` for existence/uniqueness) is very
reusable. Two natural follow-ups, both within the same Butcher §34
neighbourhood:

1. **Vector lift of §341.** Generalise to `f : (Fin n → ℝ) → (Fin n → ℝ)`
   so the result applies to coupled ODE systems. The structure is
   identical: `stageMap` becomes `(Fin s → Fin n → ℝ)`-valued, and
   `dist_pi_le_iff` applied twice (once on the stage index, once on
   the component index) reduces back to the scalar case.

2. **Picard-iterate convergence rate.** `ContractingWith.exists_fixedPoint`
   already returns `Filter.Tendsto (fun n => f^[n] x) atTop (nhds y)`
   plus the geometric bound `edist (f^[n] x) y ≤ edist x (f x) * K^n / (1 − K)`
   — package this as a quantitative §341 corollary stating the
   convergence rate of stage Picard iteration. Pure Mathlib wrapping;
   no new analysis.

For the planner: §38 / §386 cut-aggregate work remains paused per
strategy. The pivot ladder (§250 / §372 / §341) is working — pick the
next concrete §3X / §4X / §5X target along the same lines.
