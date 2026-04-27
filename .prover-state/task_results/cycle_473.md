# Cycle 473 Results

## Worked on
Adams-Moulton 9-step scalar quantitative convergence:
- Upstream `LMM.adamsMoulton9` infrastructure in `OpenMath/AdamsMethods.lean`.
- Scalar AM9 trajectory, local truncation equation, one-step Lipschitz/error
  recurrence, residual bound, local residual theorem, and headline global error
  theorem in `OpenMath/LMMAM9Convergence.lean`.
- `plan.md` frontier and current-target bookkeeping.

## Approach
Verified the AM9 coefficients before writing the trajectory predicate. With
common denominator `7257600`, the coefficients from oldest sample to newest
implicit sample are
`[57281, -583435, 2687864, -7394032, 13510082, -17283646, 16002320, -11271304, 9449717, 2082753]`.
They sum to `7257600`, so the method is consistent. The implicit leading
coefficient is `2082753/7257600`.

Added `adamsMoulton9_consistent`, `adamsMoulton9_implicit`,
`adamsMoulton9_order_ten`, and `adamsMoulton9_zeroStable` by mirroring the AM8
shape in `AdamsMethods.lean`. Then built a sorry-first AM9 scalar chain
mirroring `OpenMath/LMMAM8Convergence.lean` and reusing the public eleventh-order
Taylor helpers from `OpenMath/LMMAB10Convergence.lean`:
`iteratedDeriv_eleven_bounded_on_Icc`, `y_eleventh_order_taylor_remainder`, and
`derivY_tenth_order_taylor_remainder`.

Per the Aristotle-first rule, after the sorry-first scaffold compiled I submitted
five jobs and slept for 30 minutes before a single status check:
- `4655c339-d43d-4188-81a9-edd7e11b44ce` for `am9_localTruncationError_eq`
- `2c403891-78e6-4a74-8fa0-39a44ecd32a6` for `am9_one_step_lipschitz`
- `cf723af6-26eb-4805-9a73-ae5211008e14` for `am9_pointwise_residual_bound`
- `022df2e7-9843-4388-b8d7-8ff5c872b069` for `am9_local_residual_bound`
- `26748701-7356-4225-8e43-01b45433340a` for `am9_global_error_bound`

All five jobs were still `QUEUED` at the single post-sleep check, so no Aristotle
bundle was incorporated.

## Result
SUCCESS. The AM9 scalar chain is closed with no live `sorry`s.

The AM9 absolute weight sum is `40161217/3628800 ≈ 11.06735`, so the smallest
integer satisfying `G ≥ 2 * Σ|β_k|` is `G = 23`. The one-step proof uses the
small-step hypothesis `(2082753 / 7257600) * h * L ≤ 1 / 2`, divides by the
implicit contraction factor, and slackens to growth `23L` with residual
coefficient `2`.

The pointwise residual coefficient is exactly
`88212037990481513/48283361280000 ≈ 1826.96556`, slackened to `1827`, giving
`|τ_n| ≤ 1827 * M * h^11` and the headline bound
`|y_N - y(t0 + N*h)| ≤ exp (23*L*T) * ε0 + K*h^10` for `(N+8)*h ≤ T`.

Verification:
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/LMMAM9Convergence.lean`
  passed.
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/AdamsMethods.lean`
  passed.
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build` completed
  successfully (`8068` jobs). Existing warnings appeared in older modules; the
  targeted AM9 and AdamsMethods checks were clean.
- `rg -n "^\s*sorry" OpenMath/` returned no matches.
- File-size guardrail remains satisfied: `OpenMath/AdamsMethods.lean` has 832
  lines and `OpenMath/LMMAM9Convergence.lean` has 1566 lines.

## Dead ends
Aristotle did not return usable results within the mandated 30-minute wait; all
submitted jobs remained queued at the single allowed status check.

Some local AM9 arithmetic goals were too large when left inline. Splitting the
growth proof into a coefficient inequality and keeping the residual combination
in a separate private lemma avoided kernel timeouts without raising
`maxHeartbeats`.

## Discovery
The public AB10 eleventh-order scalar Taylor helpers are sufficient for AM9
without duplication.

The AM9 growth slack can be proved via the identity
`(1 - (2082753/7257600)*x) * (1 + 23*x) - (1 + (78239681/7257600)*x)
 = x/7257600 * (86602366 - 47903319*x)`, with the small-step bound
`x ≤ 3628800/2082753`.

The residual proof remains kernel-friendly with the cycle-468 pattern: introduce
the eleven Taylor remainders as `R0` through `R10`, immediately `clear_value`
them, and pass their abstract bounds to an extracted `am9_residual_combine`
lemma.

## Suggested next approach
Cycle 474 should mirror this scalar AM9 chain in
`OpenMath/LMMAM9VectorConvergence.lean`, reusing the public vector eleventh-order
Taylor helpers from `OpenMath/LMMAB10VectorConvergence.lean`.
