# Cycle 625 Results

## Worked on
§512 LMM stability lift, Phase D step 4 in `OpenMath/LMMAsGLM.lean`.

Added the real-to-complex y-half companion bridge:

1. `LMM.toGLM_y_step_complex_eq`
2. `LMM.toGLM_y_step_iter_complex_eq`
3. `LMM.toGLM_y_half_iter_complex_norm_bound`

Also added the required `import OpenMath.DahlquistEquivalence`.

## Approach
Followed the planned Phase D step 4 seam.

First inserted the three deliverables with `sorry` and verified
`lake env lean OpenMath/LMMAsGLM.lean` compiled with only the expected
sorry warnings. Submitted the scaffold to Aristotle as project
`fd1e9b81-d440-4147-bdb2-6cab23f05435`; a single later status check
still showed `QUEUED`, so the proofs were closed manually without
blocking on it.

For `toGLM_y_step_complex_eq`, unfolded `toGLM_y_step`,
`LinearRecurrence.tupleSucc`, and `LMM.toLinearRecurrence`, then split on
`(k : ℕ) + 1 < s`. The shift branch is definitionally the same after
matching the `dif` branches. The last-row branch closes by pushing
`Complex.ofReal` through the finite sum and products.

For `toGLM_y_step_iter_complex_eq`, used induction on `j`,
`Function.iterate_succ_apply'`, and the pointwise bridge on the outer
step.

For `toGLM_y_half_iter_complex_norm_bound`, obtained the spectral witness
from `uniformly_bounded_tupleSucc_iterates m hzs`, rewrote the y-half of
`V^[n+j]` using `toGLM_y_half_iter_eq`, converted the real companion
iterate to `tupleSucc^[j]` via `toGLM_y_step_iter_complex_eq`, and applied
the spectral bound.

## Result
SUCCESS.

Verification:

- `lake env lean OpenMath/LMMAsGLM.lean` exits 0.
- `grep -c sorry OpenMath/LMMAsGLM.lean` prints `0`.
- `lake env lean OpenMath/DahlquistEquivalence.lean` exits 0, confirming
  the new import does not introduce a source cycle.

## Dead ends
None. The planned branch split for the pointwise bridge was sufficient.

## Discovery
`LinearRecurrence.tupleSucc` and `toGLM_y_step` have exactly matching
index conventions: shift when `(k : ℕ) + 1 < s`, otherwise the final
row is the `∑ l, -(m.α (Fin.castSucc l) : ℂ) * v l` coefficient
combination. No reindexing equivalence is needed.

The lifted y-half norm bound can be stated directly on the same
`V`-iterate expression used by `GeneralLinearMethod.IsStable`; the only
conversion needed is the existing cycle 624 theorem
`toGLM_y_half_iter_eq`.

## Suggested next approach
Phase E: prove `LMM.toGLM_isStable : m.IsZeroStable → m.toGLM.IsStable`.
Use `toGLM_y_half_iter_complex_norm_bound` for the `n ≥ s` y-half,
the existing `M_max` / `toGLM_V_iter_le` bound for the finite prefix
`n < s`, and `toGLM_V_iter_natAdd_eq_zero_of_le` for the h·f half after
`s` iterations. Then `LMM.toGLM_isConvergent` should be the planned
one-line combination with consistency.
