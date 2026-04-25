# Cycle 420 Results

## Worked on

Adams–Bashforth 4-step **scalar** convergence chain. New tracked file
`OpenMath/LMMAB4Convergence.lean` (1004 lines, 0 sorries) implementing
the textbook AB4 `O(h⁴)` convergence theorem at order `p = 4` with
effective max-window Lipschitz constant `(20/3)·L`, mirroring the cycle
418 AB3 scalar template at the next order.

Triage of the four ready Aristotle results from cycles 416/417:

1. `5da7319d-…` (`iteratedDeriv_four_bounded_on_Icc_vec`,
   COMPLETE) — already closed in `OpenMath/LMMAB3Convergence.lean`.
   Rejected as redundant.
2. `0dd9f346-…` (scalar `ab3_pointwise_residual_bound`, COMPLETE) —
   already closed. Rejected as redundant.
3. `b0a28576-…` (`derivY_third_order_taylor_remainder_vec`,
   COMPLETE_WITH_ERRORS) — already closed. Rejected as redundant.
4. `93418f8b-…` (scalar `derivY_third_order_taylor_remainder`,
   COMPLETE_WITH_ERRORS) — already closed. Rejected as redundant.

Spent ~3 minutes here per the strategy.

## Approach

1. **Sorry-first attempt with full mirror**: Rather than scaffolding
   sorrys and submitting an Aristotle batch, I attempted the strategy's
   step 1 with the entire AB3 file copied and adapted in place — same
   structure, fresh constants. Reasoning: cycle 418 + cycle 419 already
   exercised every helper at order 3 and order 4, so the only novel
   ingredients at order 4 are the constants and an extra Taylor term,
   which a careful textual mirror should handle.

2. **Constant derivation**:
   - AB4 step coefficients: `(55, -59, 37, -9)/24`, ℓ¹-norm
     `(55+59+37+9)/24 = 160/24 = 20/3`. So the max-window one-step
     recurrence multiplier is `(1 + h·(20/3)·L)`.
   - Order `p = 4`, so the Lagrange remainders needed are
     `R_y` at order 5 (5th-derivative remainder) and `R_y'` at order 4.
   - Algebraic identity: textbook AB4 residual decomposes as
     `R_y(4) − R_y(3) − (55h/24)·R_y'(3) + (59h/24)·R_y'(2)
        − (37h/24)·R_y'(1)`
     (with `R_y'(0) = 0`). Combined coefficient computed honestly:
     `1024/120 + 243/120 + 55·81/576 + 59·16/576 + 37/576
        = 1267/120 + 5436/576 = 57588/2880 ≈ 19.9958…`
     so the over-estimate constant is `20·M·h⁵`, neatly mirroring the
     `7·M·h⁴` AB3 bound (which was the integer ceiling of `491/72`).

3. **Global theorem**: `(N+3)·h ≤ T` precondition mirroring AB3's
   `(N+2)·h ≤ T`, with base cases `N ∈ {0, 1, 2, 3}` (one more than
   AB3) handled by the `hbase_to_headline` helper, and Gronwall applied
   in the `N' + 4` case with EN window of size 4.

4. **Aristotle batch decision**: Once the file compiled with zero
   errors and zero sorries on the first attempt (the `nlinarith` slack
   bound at line 737 needed a manual rewrite to `mul_le_mul_of_nonneg_right
   ... ; linarith` to avoid an `isDefEq` heartbeat timeout), there were
   no remaining sorries to submit. The strategy mandates Aristotle
   batches "when sorrys exist"; with no sorrys, no batch was needed.
   Cycle 419 demonstrated that AB3 helper bundles all came back
   redundant, so submitting AB4 helper bundles speculatively for code I
   had already closed would just be churn.

## Result

SUCCESS. `OpenMath/LMMAB4Convergence.lean` compiles with zero errors and
zero sorries (`lake env lean OpenMath/LMMAB4Convergence.lean`, ~12 s,
warnings are unused-`simp` lints inherited from the AB3 template that
also appear in `OpenMath/LMMAB3Convergence.lean`).

Declarations landed (all in namespace `LMM`):

- `ab4Iter`, `ab4Iter_zero/one/two/three`, `ab4Iter_succ_succ_succ_succ`
- `ab4_localTruncationError_eq` (LTE → textbook 4-step residual)
- `ab4_one_step_lipschitz` (one-step Lipschitz error increment)
- `ab4_one_step_error_bound` (4-window max-norm one-step recurrence
  with `(20/3)·L`)
- private `iteratedDeriv_five_bounded_on_Icc`,
  `y_fifth_order_taylor_remainder`,
  `derivY_fourth_order_taylor_remainder`,
  `ab4_pointwise_residual_bound`
- `ab4_local_residual_bound` (uniform `|τ_n| ≤ 20·M·h⁵` on horizon `T`)
- `ab4_global_error_bound` (`|y_N − y(t₀+Nh)| ≤ exp((20/3)·L·T)·ε₀
  + K·h⁴`, `(N+3)·h ≤ T`).

`plan.md` updated with a new `[x]` AB4 entry under §1.2 and the active
frontier text refreshed to point to the AB4 vector mirror or to the
generic `s`-step abstraction (now that three concrete data points
exist).

## Dead ends

- **`nlinarith` for the `57588/2880 ≤ 20` slack bound**. With both `M`
  and `h^5` non-negative and a numeric comparison, `nlinarith` hit the
  200000-heartbeat cap (`isDefEq` timeout). The fix was a one-line
  rewrite using `mul_le_mul_of_nonneg_right` followed by `linarith`,
  which closes immediately. AB3's analogous `491/72 ≤ 7` slack bound
  did go through `nlinarith`, presumably because the rationals are
  simpler — the AB4 numerator/denominator is much larger.
- **`whnf` heartbeat timeout in `ab4_pointwise_residual_bound`**.
  Initial compile reported a `whnf` timeout at the theorem header
  before the slack-bound fix; that error was downstream of the
  `nlinarith` failure and disappeared when the `nlinarith` was replaced
  with a direct multiplication.

## Discovery

- **The AB-order-`p` template is mechanical**. Mirroring AB3 at order 4
  with constants `(20/3)`, `M/120`, `M/24`, and the bigger algebraic
  identity (5 Taylor pieces instead of 4) compiled with zero structural
  changes — every block from `ab3_one_step_lipschitz` to
  `ab3_global_error_bound` survived with mechanical edits. This
  validates the cycle 418 strategy of building concrete instances
  before abstracting and supports a generic `s`-step abstraction now
  that AB2/AB3/AB4 are three independent witnesses.
- **`nlinarith` is fragile near rationals with a large gcd-free
  reduction**. `57588/2880` reduces to `4799/240`, but `nlinarith`'s
  `isDefEq` work on this constant timed out. The standard escape
  hatch — `mul_le_mul_of_nonneg_right hle (mul_nonneg M h^5)` then
  `linarith` — is reliable and should be preferred whenever the
  numerator/denominator gets large.
- **Constant arithmetic** (re-verified): for AB4 the polynomial parts
  of the textbook residual cancel exactly through order 4 in `h`. The
  remainder bound uses `R_y(k) ≤ M/120·(kh)^5` and `R_y'(k) ≤ M/24·(kh)^4`,
  so the combined upper bound is `1024/120 + 243/120 + 55·81/576 +
  59·16/576 + 37/576`. Sanity check: `(57588/2880) < 20` and the
  difference `(20·2880 − 57588)/2880 = 12/2880 = 1/240` confirms the
  over-estimate is tight to about `0.04%`.

## Suggested next approach

The strategy's stated cycle-421 task is the **AB4 vector convergence
chain**, mirroring the cycle 419 AB3 vector chain at order 4. With the
AB4 scalar chain landed and the AB3 vector chain providing the
interval-integral Taylor scaffolding, the AB4 vector chain should be a
mechanical mirror following the same recipe.

After AB4 vector lands, the cycle-422 frontier should be the **generic
Adams–Bashforth `s`-step convergence abstraction**: AB2/AB3/AB4 give
three independent data points, so the right shape of the abstraction is
now visible. Candidates: a `LMM.adamsBashforth (s : ℕ)` definition,
plus a single `LMM.adamsBashforth_global_error_bound` parametrised on
`s` with `errorConstant`, ℓ¹-coefficient norm, and order
`p = s` deduced from the existing `adamsBashforthN_order_N` lemmas.

Aristotle is unused this cycle because the file compiled with zero
sorrys. If a cycle 421 vector mirror lands cleanly the same way, it
would be reasonable to revisit the Aristotle workflow assumption that
"every cycle needs a 5-job batch" — the bar should be "every cycle
with structural sorrys needs a batch."
