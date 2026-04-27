# Cycle 481 Results

## Worked on
AM11 scalar quantitative convergence chain and AM11 method registration.

## Approach
Computed AM11 weights by exact Python `Fraction` Lagrange integration on nodes
`0,...,11` over `[10,11]`:
`(5675265, -68928781, 384709327, -1305971115, 3007739418,
-4963166514, 6043521486, -5519460582, 3828828885, -2092490673,
1374799219, 262747265) / 958003200`, summing to `1`.

Registered `adamsMoulton11` in `OpenMath/AdamsMethods.lean` with consistency,
implicitness, order 12, and zero-stability. Added
`OpenMath/LMMAM11Convergence.lean` by mirroring AM10 scalar and reusing the
public thirteenth-order scalar Taylor helpers from `LMMAB12Convergence`.

Built a sorry-first AM11 scaffold and verified it with
`lake env lean OpenMath/LMMAM11Convergence.lean`. Submitted five Aristotle
jobs targeting `am11_one_step_error_bound`, `am11_one_step_error_pair_bound`,
`am11_pointwise_residual_bound`, `am11_local_residual_bound`, and
`am11_global_error_bound`.

## Result
SUCCESS. `OpenMath/LMMAM11Convergence.lean` compiles with zero `sorry`, and
`lake build OpenMath.LMMAM11Convergence` succeeds.

The local residual bound is `|τ_n| ≤ 14003 * M * h^13`; the exact arithmetic
coefficient is
`345161607571042875013 / 24650850631680000 ≈ 14002.02`.

The divided implicit recurrence uses growth `61 * L`. The planner suggested
`ceil(Σ|β|/(1-|β_11|)) = 42`, but the existing AM-style smallness assumption
`β_11 * h * L ≤ 1/2` requires
`G ≥ ceil(2 * Σ|β|) = 61` for the inequality
`1 + explicitAbsSum*x ≤ (1 - β_11*x) * (1 + G*x)` over the full allowed
interval. Using `42` would require an additional restriction on `h*L`.

## Dead ends
Aristotle submission was blocked before any job was created. All five
`submit_file` calls failed with:
`SSL: CERTIFICATE_VERIFY_FAILED certificate has expired`.
Because no project IDs were returned, there were no Aristotle results to wait
for or incorporate.

## Discovery
For high-order AM scalar chains, the growth slack must be checked against the
actual smallness hypothesis, not just against `Σ|β|/(1-|β_s|)`. AM10's `37L`
matches `ceil(2*Σ|β|)`, and AM11 follows the same pattern with `61L`.

The 13-term scalar residual identity is fine with `ring` after extracting the
Taylor remainders as abstract scalar parameters and using `clear_value`.

## Suggested next approach
AM11 vector should remain deferred until the 13-witness vector/module wall is
split into smaller residual identities. A low-risk next scalar progression is
to reuse this AM11 scalar shape for later Adams scalar chains, while keeping
the corrected growth-constant calculation explicit.
