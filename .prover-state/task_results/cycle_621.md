# Cycle 621 Results

## Worked on

Butcher §510 / §512 LMM stability lift in `OpenMath/LMMAsGLM.lean`:
Phase B cleanup and Phase C's coarse structural row bound for the
LMM-as-GLM `V` block.

## Approach

Followed the planner sequence.

1. Added `LMM.toGLM_V_iter_natAdd_eq_zero_of_le`, the `n ≥ s`
   corollary of cycle 620's past-`h*f` vanishing theorem.
2. Introduced the private local proof artefact `M_max`, with
   `M_max_nonneg` and `one_le_M_max`.
3. Proved `toGLM_V_row_l1_le` by splitting rows according to the
   cycle 619 `V` row simp lemmas:
   * shift rows collapse with `Finset.sum_eq_single` to row sum `1`;
   * the last past-`y` row reindexes `Fin (2*s)` to `Fin (s+s)`,
     splits with `Fin.sum_univ_add`, and compares the alpha/beta
     absolute-value sums to `M_max`;
   * the last past-`h*f` row is identically zero.
4. Proved `toGLM_V_step_le` with `Finset.abs_sum_le_sum_abs`,
   pointwise `hq`, `Finset.sum_mul`, and `toGLM_V_row_l1_le`.
5. Closed the stretch headline `toGLM_V_iter_le` by induction on the
   iterate count, using `toGLM_V_step_le` for the successor.

## Result

SUCCESS. Full Phase C landed in `OpenMath/LMMAsGLM.lean`:

* `toGLM_V_iter_natAdd_eq_zero_of_le`
* private `M_max`, `M_max_nonneg`, `one_le_M_max`
* private `toGLM_V_row_l1_split`
* `toGLM_V_row_l1_le`
* `toGLM_V_step_le`
* `toGLM_V_iter_le`

Verified with:

* `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/LMMAsGLM.lean`

`plan.md` was updated in the §512 row to record cycle 621's landings.

## Dead ends

None. The only bookkeeping issue was avoiding a public row-bound
constant; keeping `M_max` private worked, and Lean displays it as the
local private artefact in theorem states.

## Discovery

For the dense last past-`y` row, the most robust route is the same
`Fin.sum_congr'` / `Fin.sum_univ_add` reindexing pattern already used
in the consistency proof. For shift rows, splitting the row is
unnecessary; `Finset.sum_eq_single` over the full `Fin (2*s)` row is
shorter.

`toGLM_V_step_le` derives `0 ≤ M` from the existing coordinate bound
`hq k`, which avoids adding an extra hypothesis and is valid because
the theorem already has a row index `k : Fin (2*s)`.

## Suggested next approach

Proceed to Phase D of
`.prover-state/issues/butcher_section512_lmm_stability_lift.md`:
use `toGLM_V_iter_natAdd_eq_zero_of_le` to drop the past-`h*f` half
after `n ≥ s`, then prove the y-slot reindexing bridge to the companion
operator / `tupleSucc` spectral bound. Do not reopen Phase C unless the
Phase D shape reveals that a renamed or specialised wrapper is needed.
