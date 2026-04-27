# Cycle 479 Results

## Worked on
AB12 scalar quantitative convergence chain in `OpenMath/LMMAB12Convergence.lean`, plus `adamsBashforth12` registration in `OpenMath/AdamsMethods.lean`.

## Approach
Added the AB12 method with exact Adams-Bashforth weights computed by integrating the Lagrange basis on nodes `0,...,11` over `[11,12]`.

Weights, ordered from `f_n` through `f_(n+11)`, over the smallest common denominator `958003200`:

`[-262747265, 3158642445, -17410248271, 58189107627, -131365867290, 211103573298, -247741639374, 214139355366, -135579356757, 61633227185, -19433810163, 4527766399] / 958003200`.

Sanity checks:

- Sum of weights: `1`.
- Signs alternate, and the leading coefficient is `4527766399 / 958003200`.
- Effective Lipschitz constant: `(443892 / 385) * L`.

I first created a sorry-first `OpenMath/LMMAB12Convergence.lean` surface and verified it with `lake env lean`. Aristotle submission was attempted before and after the mandatory 30-minute sleep, but the service returned `429` both times: `You have too many requests in progress`. No Aristotle project IDs were created.

## Result
SUCCESS.

Closed:

- Public scalar thirteenth-order Taylor helpers:
  `iteratedDeriv_thirteen_bounded_on_Icc`,
  `y_thirteenth_order_taylor_remainder`,
  `derivY_twelfth_order_taylor_remainder`.
- `LMM.ab12Iter`, `LMM.ab12_localTruncationError_eq`,
  `LMM.ab12_one_step_lipschitz`, and
  `LMM.ab12_one_step_error_bound`.
- AB12 residual algebra, triangle, and combine helpers.
- `LMM.ab12_pointwise_residual_bound` with exact coefficient
  `171625746494360048711 / 1059216238080000`, slackened to `162031`.
- `LMM.ab12_local_residual_bound`.
- Generic AB bridge:
  `LMM.ab12GenericCoeff`, `LMM.abLip_ab12GenericCoeff`,
  `LMM.ab12Iter_eq_abIter`, `LMM.ab12Residual_eq_abResidual`.
- Headline `LMM.ab12_global_error_bound`.

Also updated `plan.md` with the closed AB12 scalar entry.

## Dead ends
Aristotle was unavailable for this cycle because both submission attempts hit the in-progress request limit. I did not retry repeatedly after the required post-sleep retry.

## Discovery
The scalar AB12 residual algebra closes under the cycle-476 parameterized abstract-remainder pattern with `set` / `clear_value` in the consumer and a standalone `ring` proof in the abstract identity. The residual combine step still fits under the 200K heartbeat budget with a direct `linarith` over the thirteen bounded terms.

## Suggested next approach
Proceed to the next Adams frontier item: AB12 vector or AM11 scalar. The public thirteenth-order scalar Taylor helpers are now available for AM11 scalar reuse; vector thirteenth-order helpers were not added in this cycle.
