# Cycle 609 Results

## Worked on

Butcher §500 — general linear methods. Created
`OpenMath/GeneralLinearMethod.lean` with the four-block
`GeneralLinearMethod` structure `(A, U, B, V)`, scalar autonomous stage
and step equations, explicitness, and the §341-style contraction
solvability theorem for GLM stage equations.

## Approach

Followed the sorry-first workflow:

1. Added the full module with all requested definitions and six theorem
   skeletons using `sorry`.
2. Verified the skeleton with
   `lake env lean OpenMath/GeneralLinearMethod.lean`.
3. Submitted the sorry-first file to Aristotle as project
   `358847a8-be5c-4ebb-a1ca-416fcc464560`.
4. Closed the proofs locally by mirroring the cycle 608
   `ButcherTableau` contraction argument.

The stage-map proof differs from cycle 608 only in where the Lipschitz
bound is applied: for GLMs the map is
`h * ∑ j, A i j * f (Y j) + constant`, so the constant `U` term cancels
and each coordinate uses
`|f (Y j) - f (Y' j)| ≤ L * dist Y Y'` before summing.

## Result

SUCCESS. All deliverables landed sorry-free:

- `GeneralLinearMethod` with matrix blocks
  `A : Matrix (Fin s) (Fin s) ℝ`,
  `U : Matrix (Fin s) (Fin r) ℝ`,
  `B : Matrix (Fin r) (Fin s) ℝ`,
  `V : Matrix (Fin r) (Fin r) ℝ`.
- `step`, `stageResidual`, and their `@[simp]` projection lemmas.
- `IsExplicit` plus `IsExplicit.A_diag_zero`.
- `stageMap`, `rowAbsSumMax`, `rowAbsSumMax_nonneg`,
  `row_absSum_le_rowAbsSumMax`, `stageMap_dist_le`,
  `stageMap_lipschitzWith`, and
  `stageEquations_unique_solution`.
- Stretch hook: minimal `IsConsistent : Prop` placeholder for §510.

`plan.md` was updated to mark §500 `[x]`, remove §500 from the Backlog
Queue, renumber the remaining backlog items, and note that Chapter 5
has been opened in cycle 609.

Verification:

- `lake env lean OpenMath/GeneralLinearMethod.lean` succeeds.
- `grep -c sorry OpenMath/GeneralLinearMethod.lean` returns `0`.
- `lean_verify` on
  `GeneralLinearMethod.stageEquations_unique_solution` reports no source
  warnings.
- `lake build` succeeds (`Build completed successfully (8087 jobs)`),
  with pre-existing warnings in unrelated modules.

## Dead ends

- No Matrix-vs-function mismatch occurred. `Matrix` elaborated as a
  function type, so `m.A i j`, `m.U i k`, `m.B k j`, and `m.V k l`
  worked directly in finite sums.
- The contraction proof did not need an issue file. The only friction
  was changing the cycle 608 inner-distance calculation into a direct
  cancellation of the constant `U` offset and then applying the
  Lipschitz hypothesis under the finite sum.

## Discovery

- The cycle 608 `rowAbsSumMax` recipe transcribes unchanged to
  matrix-backed GLMs.
- For GLM stage maps, it is cleaner to prove the coordinate identity
  ```
  dist (stageMap Y i) (stageMap Y' i)
    = h * |∑ j, A i j * (f (Y j) - f (Y' j))|
  ```
  first, then use `Finset.abs_sum_le_sum_abs`,
  `LipschitzWith.dist_le_mul`, and `dist_le_pi_dist`.
- The headline theorem requested the fixed-point equation as
  `Y = stageMap Y`, whereas `ContractingWith.exists_fixedPoint` returns
  `stageMap Y = Y`. Taking `.symm` at the existence and uniqueness
  boundary is enough.

## Suggested next approach

Proceed to Backlog Queue item #1 after renumbering: §502, embedding
ordinary Runge-Kutta methods as GLMs with `r = 1`. The new
`GeneralLinearMethod` structure is already matrix-backed, so the main
task should be choosing the exact `U`, `V`, and `B` blocks from an
existing `ButcherTableau` and proving the scalar `step` agrees with the
RK update in the `r = 1` case.
