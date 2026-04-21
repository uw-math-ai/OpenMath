# Cycle 307 Results

## Worked on
- `OpenMath/PadeAsymptotics.lean`
- `OpenMath/PadeOrderStars.lean`
- Aristotle triage for:
  - `.prover-state/aristotle_results/6a782b6a-adaf-4550-b880-cb26a3136e58`
  - `.prover-state/aristotle_results/ad40a2b9-64b2-4c67-8f3b-7fe71b7cee6f`
  - `.prover-state/aristotle_results/e9c89bfa-d01b-478f-8972-e3131f4802cf`
- Pole audit for `PadeRConcreteNoEscapeInput.cont`

## Approach
- Read `.prover-state/strategy.md` first and followed the cycle-307 work order.
- Rejected the two cycle-306 Aristotle bundles quickly after reading their summaries:
  - `6a782b6a...` only targeted `padeDefect_poly_coeff_lt`, which cycle 306 had already closed.
  - `ad40a2b9...` was the same stale seam.
- Read the only plausibly relevant Aristotle artifact:
  - `.prover-state/aristotle_results/e9c89bfa-d01b-478f-8972-e3131f4802cf/02_pade_expTaylor_to_exp_local_bound_aristotle/02_pade_expTaylor_to_exp_local_bound.lean`
- Harvested only the low-cost helper ideas from that file:
  - neighborhood nonvanishing of `padeQ`
  - reciprocal bound for `padeQ`
  - factor-through-`Polynomial.X` strategy for `padeQ_sub_one_lipschitz`
- Rejected its derivative-based `pade_matching_vanishing_deriv` route exactly as instructed.
- Audited the global continuity field before trying any no-escape package:
  - for `(n,d) = (0,1)`, `padeQ 0 1 z = 1 - z` and `padeR 0 1 z = 1 / (1 - z)`, so
    `z ↦ ‖padeR 0 1 z * exp (-z)‖` is not continuous at `z = 1`
  - wrote `.prover-state/issues/pade_no_escape_global_continuity_false_at_poles.md`
- Used the required sorry-first workflow in `OpenMath/PadeAsymptotics.lean`, then submitted five focused Aristotle jobs for:
  - `padeQ_ne_zero_nhds`
  - `padeQ_inv_bound`
  - `padeQ_sub_one_lipschitz`
  - `numerator_local_bound`
  - `padeR_exp_neg_local_bound`
- Closed the proofs locally after the batch submission:
  - `padeQ_ne_zero_nhds` and `padeQ_inv_bound` are lightweight wrappers over the already-proved local continuity lemmas in `OpenMath/Pade.lean`
  - `padeQ_sub_one_lipschitz` factors `padeQ_poly n d - 1` through `Polynomial.X` and bounds the quotient polynomial on the closed unit disk by compactness
  - `numerator_local_bound` uses:
    - `PadeAsymptotics.padeDefect_poly_sub_leading_X_pow_dvd`
    - the evaluated defect factorization
    - `expTaylor_exp_neg_local_norm_bound`
    - `padeQ_sub_one_lipschitz`
    - `Complex.norm_exp_sub_one_le`
  - `padeR_exp_neg_local_bound` divides by `padeQ n d z` near `0` using `padeQ_inv_bound` and `padeQ_ne_zero_nhds`
- Since `OpenMath/PadeAsymptotics.lean` compiled cleanly, added one optional feeder theorem in `OpenMath/PadeOrderStars.lean`:
  - `padeR_local_minus_near_even_angle_of_pos_errorConst`

## Result
- SUCCESS
- Added and proved in `OpenMath/PadeAsymptotics.lean`:
  - `padeQ_ne_zero_nhds`
  - `padeQ_inv_bound`
  - `padeQ_sub_one_lipschitz`
  - `numerator_local_bound`
  - `padeR_exp_neg_local_bound`
- Added in `OpenMath/PadeOrderStars.lean`:
  - `padeR_local_minus_near_even_angle_of_pos_errorConst`
- Wrote the required blocker issue:
  - `.prover-state/issues/pade_no_escape_global_continuity_false_at_poles.md`
- Verification succeeded:
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeAsymptotics.lean`
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.PadeAsymptotics`
  - `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeOrderStars.lean`

## Dead ends
- Did not attempt to populate full `PadeRConcreteNoEscapeInput`; the continuity field is false globally once `padeR` has poles.
- Did not use Aristotle’s derivative/iterated-derivative approach from `e9c89bfa...`; it would have recreated the stalled analytic bottleneck the planner explicitly ruled out.
- `lake env lean OpenMath/PadeOrderStars.lean` initially saw a stale `PadeAsymptotics.olean`; I had to refresh it with `lake build OpenMath.PadeAsymptotics` before the optional feeder theorem became visible to imports.

## Discovery
- The live Padé feeder for 355C/355D/355E is now concrete and local, not abstract:
  `padeR_exp_neg_local_bound` is available with the explicit coefficient
  `padePhiErrorConst n d`.
- The numerator seam really is the right decomposition:
  - defect term from `padeDefect_poly_sub_leading_X_pow_dvd`
  - truncated-exponential remainder from `expTaylor_exp_neg_local_norm_bound`
  - residual degree-`n+d+1` mismatch absorbed by
    `exp(-z) - padeQ n d z = O(‖z‖)` using
    `padeQ_sub_one_lipschitz` and `Complex.norm_exp_sub_one_le`
- The no-escape package in `PadeOrderStars` is still overstated at poles; any future repair must localize or restrict the continuity hypothesis instead of trying to prove the current global field.
- Aristotle status at the single check during this cycle:
  - `0aad500d-372e-4477-980b-4b35de0222dd` (`padeQ_ne_zero_nhds`): `QUEUED`
  - `44678cd6-8b09-4774-9d3a-3baa24c80547` (`padeQ_inv_bound`): `QUEUED`
  - `61968d89-8a66-4850-af77-c84109335b0f` (`padeQ_sub_one_lipschitz`): `QUEUED`
  - `af144331-a434-42f9-b7df-76daec67f48a` (`numerator_local_bound`): `QUEUED`
  - `872ef15e-0c15-46cf-a1e6-90afda17a0f2` (`padeR_exp_neg_local_bound`): `QUEUED`
- No new Aristotle output was incorporable this cycle beyond the initial summary triage and helper-proof ideas harvested from `e9c89bfa...`.

## Suggested next approach
- Use `padeR_exp_neg_local_bound` plus the sign/parity of `padePhiErrorConst n d`
  to build more exact-angle Padé wrappers in `PadeOrderStars.lean`, one parity/sign
  case at a time.
- Repair the false global continuity seam in `PadeRConcreteNoEscapeInput` before
  anyone spends another cycle trying to populate that structure.
