# Cycle 286 Results

## Worked on
- Triage of the five ready Aristotle result bundles from cycle 284:
  - `a937370e-0b94-43f2-bcc9-1ebeef9eace8`
  - `478be5a7-9b1b-4814-b3d5-784dc45ac547`
  - `0cdf5b9a-65a6-4c77-85e4-097595e4d057`
  - `2d4e2259-f858-44c6-a65e-d9dff606301e`
  - `40100c59-47ab-46a0-a41d-476a1d0626d4`
- Added the first concrete Padé-side order-star consumer in
  `OpenMath/PadeOrderStars.lean`.
- Stated the first concrete Padé-specific analytic theorem boundary
  `padeR_no_nonzero_eq_exp_on_orderWeb`.
- Submitted and refreshed one focused Aristotle batch for concrete `padeR`
  targets only.

## Approach
- Read:
  - `.prover-state/task_results/cycle_284.md`
  - `.prover-state/task_results/cycle_285.md`
  - `.prover-state/issues/order_star_concrete_pade_target_not_stated.md`
  - `.prover-state/issues/order_star_exact_coincidence_exclusion_requires_r_specific_input.md`
- Re-read the live `OrderStars` seam around:
  - `IsPadeApproxToExp`
  - `ConcreteRationalApproxToExp`
  - `thm_355D_of_concreteRationalApprox`
  - `thm_355E'_of_concreteRationalApprox`
- Re-read `OpenMath/Pade.lean` around `padeR`.
- Inspected the five ready Aristotle bundles before doing any new proof work.
- Added a new adjacent file `OpenMath/PadeOrderStars.lean` importing:
  - `OpenMath.Pade`
  - `OpenMath.OrderStars`
- In that file, added the concrete wrapper theorems:
  - `thm_355D_of_padeR`
  - `thm_355E'_of_padeR`
- Added the first concrete Padé theorem boundary:
  - `padeR_no_nonzero_eq_exp_on_orderWeb`
  in sorry-first form.
- Verified compilation with:
  - `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/OrderStars.lean`
  - `export PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH && lake env lean OpenMath/PadeOrderStars.lean`
- Created the focused Aristotle scratch batch under
  `.prover-state/aristotle/cycle_286/`:
  - `01_padeR_no_nonzero_eq_exp_on_orderWeb.lean`
  - `02_padeR_zero_not_mem_realizedDownArrowInfinityBranch_support.lean`
  - `03_padeR_zero_not_mem_realizedUpArrowInfinityBranch_support.lean`
  - `04_padeR_local_cone_sign_package.lean`
  - `05_padeR_far_field_sign_package.lean`
- Submitted the five files to Aristotle:
  - `de228e57-369e-471f-8c2c-9a564d634849`
  - `40f68f7a-7d40-40bc-9f0e-36f260ad786e`
  - `a7f483f7-08c4-4fdd-837a-ed9dd3db30c0`
  - `39c98115-5f6a-487d-9ccb-317b70483ebf`
  - `e26ad296-6137-4950-84fe-d4516c5812b4`
- Waited once for 30 minutes with `sleep 1800`, then refreshed each project once
  and inspected the extracted result bundles.

## Result
SUCCESS on the infrastructure target, BLOCKED on the first concrete analytic proof.

Concrete outcomes:
- `OpenMath/PadeOrderStars.lean` was created and compiles.
- Added theorem names in that file:
  - `thm_355D_of_padeR`
  - `thm_355E'_of_padeR`
  - `padeR_no_nonzero_eq_exp_on_orderWeb`
- The first concrete `padeR` theorem was only scaffolded, not proved:
  `padeR_no_nonzero_eq_exp_on_orderWeb` is still `sorry`.
- Wrote the focused blocker issue:
  `.prover-state/issues/order_star_padeR_nonzero_coincidence_exclusion_missing.md`

Cycle-284 Aristotle triage decisions:
- Rejected `2d4e2259...`.
  Its file proves an obsolete theorem name (`eq_exp_of_mem_orderWeb`) against a
  stale interface, and the target theorem already exists live as
  `eq_exp_of_mem_orderWeb_of_norm_eq_one`. No useful line-level simplification to copy.
- Rejected `40100c59...`.
  Its proof attacks the already-live theorem
  `eq_one_of_mem_orderWeb_of_norm_eq_one` with a brittle norm-expansion script.
  No useful line-level simplification to copy.
- Rejected `0cdf5b9a...`.
  The result redefines `orderWeb` as a unit-circle condition on `f z / exp z`
  rather than using the live positive-real order-web interface.
- Rejected `478be5a7...`.
  The result rebuilds realized branch structures with incompatible support
  invariants (`support_sub`, `mem_support_norm_gt`, etc.), making the target
  contradiction trivial for the wrong reason.
- Rejected `a937370e...`.
  The result rebuilds `ConcreteRationalApproxToExp` around a boundedness claim
  on a redefined `orderWeb`, not the live no-realized-branch interface.

Cycle-286 Aristotle batch after the single allowed refresh:
- `de228e57...` (`01_padeR_no_nonzero_eq_exp_on_orderWeb`):
  `COMPLETE_WITH_ERRORS`, rejected. It created replacement `OpenMath/Pade.lean`
  and `OpenMath/OrderStars.lean` files and changed `orderWeb` to an imaginary-part
  condition on `padeR z / exp z`.
- `40f68f7a...` (`02_padeR_zero_not_mem_realizedDownArrowInfinityBranch_support`):
  `COMPLETE_WITH_ERRORS`, rejected. It replaced the realized down-arrow interface
  with a strict `‖f z‖ < ‖exp z‖` support condition.
- `a7f483f7...` (`03_padeR_zero_not_mem_realizedUpArrowInfinityBranch_support`):
  `COMPLETE_WITH_ERRORS`, rejected. It replaced the realized up-arrow interface
  with a strict `‖f z‖ > ‖exp z‖` support condition.
- `39c98115...` (`04_padeR_local_cone_sign_package`):
  `COMPLETE_WITH_ERRORS`, rejected. It redefined `IsDownArrowDir` /
  `IsUpArrowDir` so the theorem became `exact ⟨fun θ h => h, fun θ h => h⟩`.
- `e26ad296...` (`05_padeR_far_field_sign_package`):
  `COMPLETE_WITH_ERRORS`, rejected. It redefined `orderWeb` as a bounded near-field
  critical-point set so the far-field package became vacuous.

## Dead ends
- None of the five ready cycle-284 Aristotle bundles was compatible with the live
  `OpenMath/OrderStars.lean` interface.
- None of the five cycle-286 Aristotle outputs produced a proof fragment that could
  be copied into live code without also importing a replacement `OpenMath/Pade.lean`
  or `OpenMath/OrderStars.lean`.
- Re-running the concrete targets through Aristotle did not produce the missing
  analytic ingredient; it mostly collapsed the statements by changing the meaning
  of `orderWeb`, realized branches, or arrow directions.

## Discovery
- The concrete `R := padeR n d` target now exists in live code, which was the
  main infrastructure gap from cycle 285.
- The exact first missing analytic statement is now explicit in live code:
  `padeR_no_nonzero_eq_exp_on_orderWeb`.
- `OpenMath/Pade.lean` still has no theorem controlling nonzero coincidence points
  of `padeR n d` with `exp` on the live order web.
- The next concrete branch-level inputs after that remain:
  - zero not in realized branch support
  - local cone sign control
  - far-field sign control
  but those are still behind the exact coincidence exclusion in the present file.

## Suggested next approach
- Keep `OpenMath/PadeOrderStars.lean` as the concrete Padé-side home for the
  order-star bridge.
- Treat
  `∀ z : ℂ, z ≠ 0 → z ∈ orderWeb (padeR n d) → padeR n d z = exp z → False`
  as the first missing analytic statement in line.
- Either prove that theorem for the intended concrete Padé family, or weaken it
  immediately to the first honest Padé-local theorem that the current development
  can actually support.
- Do not accept Aristotle outputs that solve the target by redefining `orderWeb`,
  rebuilding branch structures, or replacing the live `ConcreteRationalApproxToExp`
  interface.
