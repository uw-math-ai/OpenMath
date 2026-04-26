# Cycle 461 Results

## Worked on
BDF5 scalar truncation chain in `OpenMath/LMMBDF5Convergence.lean`.

## Approach
Created the BDF5 module sorry-first with the supplied trajectory predicate,
local truncation residual unfolding, Lipschitz defect bound, private scalar
residual algebra helper, pointwise residual bound, and finite-horizon local
residual bound. Verified the sorry-first surface, then submitted five
Aristotle jobs:

- `bdf5_localTruncationError_eq`: `8ea0d162-3ac7-4c10-acbb-5925c13258bb`
- `bdf5_one_step_lipschitz`: `2ebbd920-e328-48cb-b3fe-1fe8dcf01f3e`
- `bdf5_pointwise_residual_alg`: `b6fbdb0f-bd08-40b4-bef3-852be45d809f`
- `bdf5_pointwise_residual_bound`: `cd2e8988-3564-4b53-bb43-1ceebd1d4eac`
- `bdf5_local_residual_bound`: `ead2cd79-76e3-4af4-9ae2-d94bd8c8c408`

After the required 30-minute wait, all five jobs were still `QUEUED`, so I
closed the proofs manually.

## Result
SUCCESS. `OpenMath/LMMBDF5Convergence.lean` compiles with no sorries. The
pointwise residual proof uses the AB5 public sixth-order Taylor helpers and
an extracted private algebra lemma with `clear_value` on the six abstract
residuals. The exact residual coefficient is `59075/1233`, slackened to
`48`, giving `|τ_n| ≤ 48·M·h⁶` and the finite-horizon local residual bound.

Updated `plan.md` to mark the BDF5 scalar truncation chain closed and to set
BDF6 truncation as the next concrete BDF frontier. The BDF5 global Lyapunov
theorem remains deferred under the same obstruction as BDF4.

## Dead ends
Aristotle did not produce completed output within the mandated wait window.
No proof-shape output was available to incorporate.

## Discovery
The BDF5 Taylor cancellation closes cleanly with a single `ring` identity
once the residual is decomposed as
`R_y(5) − (300/137)R_y(4) + (300/137)R_y(3) − (200/137)R_y(2)
 + (75/137)R_y(1) − (60h/137)R_y'(5)`.
The scalar algebra constant is `59075/1233 ≈ 47.91`.

## Suggested next approach
Proceed to the BDF6 scalar truncation chain, using the same pattern:
sorry-first surface, Aristotle batch, extracted private residual algebra
helper, `clear_value` before applying the helper, and no Lyapunov/global
theorem in the truncation cycle.
