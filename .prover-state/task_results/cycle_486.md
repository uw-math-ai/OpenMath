# Cycle 486 Results

## Worked on

AB13 scalar quantitative convergence:

- `OpenMath/AdamsMethods.lean`: confirmed the AB13 method registration and structural lemmas.
- `OpenMath/LMMAB13Convergence.lean`: closed the remaining residual and global-error proofs.
- `plan.md`: marked the AB13 scalar chain closed and updated the active frontier.
- `.prover-state/issues/ab13_residual_algebra.md`: removed the stale blocker after the proof was completed.

## Approach

First triaged the five ready Aristotle result bundles in `.prover-state/aristotle_results/`. Each target file was already sorry-free:

- `LMMAM12VectorConvergence.lean`
- `LMMAM9Convergence.lean`
- `LMMAB10VectorConvergence.lean`
- `LMMAB12VectorConvergence.lean`
- `LMMAB12Convergence.lean`
- `LMMABGenericConvergence.lean`
- `LMMAM11VectorConvergence.lean`
- `LMMTruncationOp.lean`

No bundle was transplanted onto the live tree.

Then submitted five Aristotle jobs against the live AB13 file and waited once for 30 minutes, as requested:

- `2bc0d7b6-1973-47a7-8aa2-2490c2ce9eaf`: still `IN_PROGRESS` at 13%.
- `0a6a7d61-556d-4d03-b82c-43af3d6dab10`: still `IN_PROGRESS` at 23%.
- `2334c683-6d03-46dc-b603-3e1724ee476c`: still `IN_PROGRESS` at 15%.
- `b405fc67-051a-428f-b0c8-a533b5f1a730`: still `IN_PROGRESS` at 25%.
- `d4a7ca3a-af1f-42a1-9f1d-9bf3d8fc4316`: still `IN_PROGRESS` at 9%.

Because none had completed after the scheduled check, no Aristotle proof was incorporated this cycle.

The manual proof avoided a 14-witness packed-polynomial identity by routing the pointwise residual through the existing generic Taylor-polynomial infrastructure:

- `taylorPolyOf_eval_thirteen`
- `taylorPolyOf_derivative_eval_thirteen`
- `adamsBashforth13.truncationOp_smooth_eq_taylor_residual`
- `adamsBashforth13.truncationOp_taylorPoly_eq_zero_of_HasOrder`
- `adamsBashforth13_order_thirteen`

The residual sum is bounded termwise and collapsed with `ab13_taylor_residual_sum_alg`.

## Result

SUCCESS.

Closed:

- `LMM.ab13_pointwise_residual_bound`: `|τ_n| ≤ 529729 · M · h^14`.
- `LMM.ab13_local_residual_bound`: uniform local residual bound.
- `LMM.ab13_global_error_bound`: headline AB13 scalar global bound through `LMM.ab_global_error_bound_generic` at `s = p = 13`.

The effective Lipschitz growth constant is `(1439788039057 / 638512875) · L`.

The exact residual coefficient behind the integer slack is

```text
5616577262114645115720677 / 10602754543180800000 ≈ 529728.12
```

so `529729` is sufficient.

Verification:

- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/LMMAB13Convergence.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/AdamsMethods.lean`
- `rg -n "sorry" OpenMath/LMMAB13Convergence.lean OpenMath/AdamsMethods.lean` returned no matches.

## Dead ends

No proof dead end remained after switching to the generic Taylor-polynomial residual decomposition. The planned packed-polynomial approach was not needed for the final scalar proof.

## Discovery

The generic truncation-operator Taylor decomposition is strong enough to avoid spelling out the entire AB13 14-remainder algebra in the theorem statement. This keeps the AB13 scalar residual proof substantially smaller than the AB12-style packed witness path while staying within the 200K heartbeat budget.

The old issue file `.prover-state/issues/ab13_residual_algebra.md` is obsolete and was deleted.

## Suggested next approach

The next frontier can move to AB13 vector convergence or to the planner's next Adams/BDF target. For an AB13 vector mirror, reuse the public 14th-order vector Taylor helpers from `OpenMath/LMMAM12VectorConvergence.lean` and check whether the same generic Taylor-polynomial residual decomposition can replace the wider packed-vector residual identity.
