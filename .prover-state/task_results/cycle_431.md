# Cycle 431 Results

## Worked on
`OpenMath/LMMAB5Convergence.lean`: refactored `LMM.ab5Vec_global_error_bound`
through `LMM.ab_global_error_bound_generic_vec` at `s = 5`, `p = 5`.

## Approach
Rejected Aristotle project `9453fd80-217f-462d-a6a6-894e461547a8` after
confirming it was the documented non-incorporable AB3 stub run: it created
replacement dependency modules and left unrelated sorries.

Added `LMM.ab5GenericCoeff` with coefficient order matching `ab5IterVec`
from oldest to newest sample:
`251/720, -1274/720, 2616/720, -2774/720, 1901/720`.
Proved:
- `LMM.abLip_ab5GenericCoeff`
- `LMM.ab5IterVec_eq_abIterVec`
- `LMM.ab5VecResidual_eq_abResidualVec`

Then replaced the inline vector headline proof with a specialization of the
generic vector theorem and converted the generic window error back through
the iteration bridge.

## Result
SUCCESS. `LMM.ab5Vec_global_error_bound` now uses the generic vector AB
scaffold while preserving the public statement and the
`Real.exp ((551/45) * L * T)` constant.

Verification run:
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/LMMAB5Convergence.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.LMMAB5Convergence`
- `grep -c sorry OpenMath/LMMAB5Convergence.lean` returned `0`
- `lean_verify` on `LMM.ab5Vec_global_error_bound` reported only
  `propext`, `Classical.choice`, and `Quot.sound`

Submitted defensive Aristotle validation job
`b8459e9d-a296-4b84-8488-f983765ecfef` for the AB5 bridge lemmas after the
local proof closed; per strategy, did not wait for it before committing.

## Dead ends
None. The AB4 bridge pattern transferred directly. The residual bridge still
keeps the `Fin.val_zero`, `Fin.val_one`, and `Fin.val_two` simp arguments
despite linter warnings, following the cycle-431 strategy.

## Discovery
The AB5 generic coefficient order is the recurrence order, not the textbook
newest-to-oldest display order. The absolute-value sum is `551/45`, matching
the existing AB5 vector one-step constant.

## Suggested next approach
Cycle 432 should bridge AB5 scalar and AB6 scalar/vector headlines through
the existing generic scaffold. The AB5 vector proof now gives the five-entry
residual/iteration template needed for the AB6 vector bridge.
