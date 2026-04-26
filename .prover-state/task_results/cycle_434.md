# Cycle 434 Results

## Worked on
Step 0 + Steps 1–4 of the planner strategy: AM2 quantitative convergence chain
in a new tracked file `OpenMath/LMMAM2Convergence.lean`, plus the required
visibility fix in `OpenMath/LMMAB3Convergence.lean`.

## Approach
- Step 0 (visibility fix): dropped `private` from
  `iteratedDeriv_four_bounded_on_Icc`,
  `iteratedDeriv_four_bounded_on_Icc_vec`,
  `y_fourth_order_taylor_remainder`, and
  `derivY_third_order_taylor_remainder` in `LMMAB3Convergence.lean` so the
  AM2 chain can reuse them rather than duplicating proofs. Verified the
  AB3 file still compiles.
- Step 1 (sorry-first scaffold): replayed the proven structure from the
  reverted cycle-433 attempt for `IsAM2Trajectory`,
  `am2_localTruncationError_eq`, `am2_one_step_lipschitz`, and
  `am2_one_step_error_bound`. Dropped the `am2Trajectory_exists` Banach
  fixed-point declaration entirely (it carried a `sorry` in cycle 433 and is
  not part of the cycle-434 error-analysis chain — existence remains a
  separate frontier theorem).
- Added `am2_one_step_error_pair_bound` to package the divided one-step
  bound as a max-norm rolling-pair recurrence, mirroring the AB2/AB3
  packaging used by `lmm_error_bound_from_local_truncation`.
- Step 4 (residual): wrote `am2_pointwise_residual_bound` from the 4-term
  algebraic identity
  `R = R_y(2) − R_y(1) − (5h/12)·R_y'(2) − (8h/12)·R_y'(1)`, bounded each
  Taylor remainder via the now-public AB3 helpers, and collected the natural
  coefficient `11/8` (slacked to `2`). Then `am2_local_residual_bound`
  packages the existential surface using the AB3-style compact-interval
  bound on `|y^(4)|`.
- Step 5 (headline): `am2_global_error_bound` applies
  `lmm_error_bound_from_local_truncation` at `p = 3` with effective
  Lipschitz constant `3L` and forcing `2C·h^4`, exactly mirroring AB2's
  base/inductive split.

## Result
SUCCESS.

- `OpenMath/LMMAB3Convergence.lean` still compiles (visibility-only change).
- `OpenMath/LMMAM2Convergence.lean` exists, compiles cleanly via
  `lake env lean OpenMath/LMMAM2Convergence.lean` and `lake build
  OpenMath.LMMAM2Convergence`, contains zero `sorry`, and exports
  `LMM.am2_global_error_bound`.

The AM2 file compiled with **zero sorries on the first attempt**, so no
Aristotle batch was submitted this cycle. The proven Lipschitz/LTE
infrastructure from cycle 433 transferred verbatim, and the new
residual/global-bound proofs ported directly from the AB2/AB3 templates
via the now-public AB3 fourth-order Taylor helpers.

## Dead ends
None this cycle.

## Discovery
- The cycle-433 reverted file already contained working proofs for
  `am2_localTruncationError_eq`, `am2_one_step_lipschitz`, and
  `am2_one_step_error_bound`. The blocker was strictly the missing
  visibility fix on the LMMAB3 helpers and the two open `sorry`s on
  `am2_local_residual_bound` and `am2_global_error_bound`. Once those were
  filled by direct ports of the AB3 / AB2 templates, the chain closed.
- The AM2 residual algebraic identity simplifies to a 4-term combination
  (`R_y'(0)` drops out because its Taylor remainder vanishes), giving the
  natural coefficient `11/8` rather than the strategy's `11/8` / `2L · 9/7`
  slack. Slacking `11/8 ≤ 2` keeps `nlinarith` ergonomic.

## Suggested next approach
- AM3 (Adams–Moulton 3-step, order 4) is the natural successor; the same
  template (Lipschitz one-step → divide implicit factor → fourth-order
  Taylor residual) ports up. The implicit coefficient is `9/24 = 3/8`,
  comfortably under `1` for typical step sizes.
- Alternatively, generalise the AM2 chain through a generic AM scaffold
  analogous to `LMMABGenericConvergence`, parameterised by the implicit
  coefficient and the AM weights.
- The `am2Trajectory_exists` Banach fixed-point construction remains an
  open frontier; would unblock fully self-contained AM convergence chains
  without supplying an external trajectory predicate.
