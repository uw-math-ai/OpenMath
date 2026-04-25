# Cycle 408 Results

## Worked on
Adams–Bashforth 2-step (AB2) scalar convergence chain in
`OpenMath/LMMTruncationOp.lean`, lifting the cycle-406 forward-Euler
scalar template to a 2-step explicit method with order-2 local
truncation and order-2 global convergence.

## Approach
Followed the strategy's sorry-first / Aristotle-first workflow.

1. Drafted the AB2 scaffold at the bottom of `LMMTruncationOp.lean`:
   `ab2Iter`, `ab2Iter_zero/one/succ_succ`, `ab2_localTruncationError_eq`,
   `ab2_one_step_lipschitz`, `ab2_one_step_error_bound`,
   `ab2_local_residual_bound`, and the headline `ab2_global_error_bound`,
   each with `sorry` for the four nontrivial proofs.
2. Verified the scaffold elaborated with exactly four sorries via
   `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean
   OpenMath/LMMTruncationOp.lean`.
3. Submitted four Aristotle jobs in one batch and slept 1800s.
4. Manually proved the four headline theorems by adapting the
   forward-Euler template at one higher Taylor order:
   - `ab2_one_step_lipschitz`/`ab2_one_step_error_bound` use
     `|f t a − f t b| ≤ L|a − b|` on both `f_{n+1}` and `f_n` to derive
     `max(eₙ₊₁,eₙ₊₂) ≤ (1 + h(3L/2 + L/2))·max(eₙ,eₙ₊₁) + |τ_n|
                  = (1 + 2hL)·max(eₙ,eₙ₊₁) + |τ_n|`.
   - `ab2_local_residual_bound` combines Lagrange Taylor remainders for
     `y` (at order 3) and for `deriv y` (at order 2) into the algebraic
     identity
     `LTE = (y(t+2h) − y(t) − 2h·y'(t) − 2h²·y''(t))
           − (y(t+h) − y(t) − h·y'(t) − h²/2·y''(t))
           − (3h/2)·(y'(t+h) − y'(t) − h·y''(t))`,
     bounded by `(4M/3 + M/6 + 3h/2 · M/2)·h³ = 9/4·M·h³`.
   - `ab2_global_error_bound` introduces the max-norm sequence
     `EN k := max(|y_k − y(t_k)|, |y_{k+1} − y(t_{k+1})|)` and applies
     `lmm_error_bound_from_local_truncation` at `p = 2` with effective
     Lipschitz constant `2L` to bound `EN N' ≤ exp(2LT)·EN 0 + T·exp(2LT)·C·h²`
     for `N = N' + 1`; the `N = 0` case is trivial via `1 ≤ exp(2LT)`.

## Result
SUCCESS. `OpenMath/LMMTruncationOp.lean` is sorry-free and builds with
the NVMe toolchain command. `plan.md` §1.2 now records the cycle-408
AB2 convergence chain.

New public API:

```lean
noncomputable def LMM.ab2Iter
@[simp] theorem LMM.ab2Iter_zero
@[simp] theorem LMM.ab2Iter_one
theorem LMM.ab2Iter_succ_succ
theorem LMM.ab2_localTruncationError_eq
theorem LMM.ab2_one_step_lipschitz
theorem LMM.ab2_one_step_error_bound
theorem LMM.ab2_local_residual_bound
theorem LMM.ab2_global_error_bound
```

Private helpers:

```lean
private theorem LMM.iteratedDeriv_three_bounded_on_Icc
private theorem LMM.y_third_order_taylor_remainder
private theorem LMM.derivY_second_order_taylor_remainder
private theorem LMM.ab2_pointwise_residual_bound
```

## Aristotle jobs
Four jobs were submitted in batch for the four nontrivial sorries
(one_step_lipschitz, one_step_error_bound, local_residual_bound,
global_error_bound). All bundles were instructive but rejected as direct
patches — the bundles tended to add stub modules and the live project
already exposes specific helper APIs (`adamsBashforth2.localTruncationError`,
`ab2Iter_succ_succ`) that the bundles did not target. The forward-Euler
proof shape ported cleanly with the obvious Taylor-order bumps.

## Dead ends
- Initial attempt at `simp [..., Nat.factorial]` left a goal of the form
  `True ∨ iteratedDeriv 2 y t = 0` because `simp` matched `mul_eq_zero`
  on the inner `smul` term. Replaced with `simp only [smul_eq_mul, ...,
  Nat.factorial]` followed by `ring` to keep control.
- `((2 + 1 : ℕ).factorial : ℝ) = 6` is not `decide`-able under
  `Real.decidableEq`; the proof closes with `simp [Nat.factorial]`.
- The `EN N' + 1` case in the global error bound originally inferred
  `n : ℝ` for the recurrence quantifier because `((n : ℝ) + 2) * h ≤ T`
  was elaborated first; fixed by annotating `∀ n : ℕ`.
- `Real.add_one_le_exp` chained through `le_of_eq rfl` with a trivial
  `Real.exp _ ≤ Real.exp _` was awkward; replaced with
  `Real.one_le_exp_iff.mpr (by positivity)`.

## Discovery
For the multistep generalization, the key abstraction is the max-norm
error sequence `EN k := max(eN k, eN(k+1))`. Once you have a one-step
Lipschitz bound of the form
`max(eₙ₊₁, eₙ₊₂) ≤ (1 + h·L_eff)·max(eₙ, eₙ₊₁) + |τ_n|`, the existing
`lmm_error_bound_from_local_truncation` Grönwall bridge applies directly
to `EN`. The trade-off: the effective Lipschitz constant is the sum of
`|β_{i,k}|·L` over the explicit-step coefficients, so AB2 carries
`L_eff = 2L`. Skip-window cases (here `N = 0`) need a separate `1 ≤ exp(L_eff T)`
argument.

## Suggested next approach
The natural next consumer is the AB3 (or general AB-s) scalar chain,
mirroring the AB2 structure but with three starting samples and a
`L_eff = (1 + 23/12 + 16/12 + 5/12)·L = ...`-style recurrence. The
private helper triple (`iteratedDeriv_(p+1)_bounded_on_Icc`, value
remainder at order `p+1`, deriv remainder at order `p`) is reusable.
Alternatively, lift AB2 to vector-valued state spaces, mirroring the
forward-Euler vector chain in cycle 407.
