# Cycle 472 Results

## Worked on
`OpenMath/LMMBDF5VectorConvergence.lean` — BDF5 vector quantitative
truncation chain, mirroring the cycle-461 scalar BDF5 truncation file in
finite-dimensional normed vector spaces.

## Approach
Manual port from the cycle-463 BDF6 vector template, swapping the BDF6
coefficients `(360, 450, 400, 225, 72, 10)/147` and leading coefficient
`60/147` for the BDF5 coefficients `(300, 300, 200, 75, 12)/137` and
leading coefficient `60/137`. Six-term residual instead of seven, sixth-
order Taylor remainders instead of seventh, AB5-vector helpers instead of
AB6-vector helpers.

Declarations added:
- `LMM.IsBDF5TrajectoryVec` — supplied implicit vector trajectory.
- `LMM.bdf5VecResidual` + `LMM.bdf5Vec_localTruncationError_eq` — textbook
  vector residual unfolding (closes by `rfl`).
- `LMM.bdf5Vec_one_step_lipschitz` — vector one-step error recurrence.
- private `LMM.bdf5Vec_pointwise_residual_alg` — abstract `(A, B, C, D, E', F)`
  norm-bound algebraic core, kernel-friendly `clear_value` pattern.
- `LMM.bdf5Vec_pointwise_residual_bound` — `‖τ_n‖ ≤ 48·M·h⁶`.
- `LMM.bdf5Vec_local_residual_bound` — finite-horizon wrapper.

## Helpers reused (no Taylor ladder duplication)
Pulled directly from the public AB5-vector module:
- `iteratedDeriv_six_bounded_on_Icc_vec` (`LMMAB5Convergence.lean:1679`)
- `y_sixth_order_taylor_remainder_vec` (`LMMAB5Convergence.lean:2214`)
- `derivY_fifth_order_taylor_remainder_vec` (`LMMAB5Convergence.lean:2444`)

No new Taylor lemmas introduced.

## Residual coefficient and slack
Exact algebraic core sum:
```
M·(5h)^6/720
+ (300/137)·M·(4h)^6/720
+ (300/137)·M·(3h)^6/720
+ (200/137)·M·(2h)^6/720
+ (75/137)·M·h^6/720
+ (60/137)·h·M·(5h)^5/120
= (59075/1233)·M·h^6
```
Exact coefficient `59075/1233 ≈ 47.911` slacked to `48` via
`norm_num` and `mul_le_mul_of_nonneg_right`. This matches the BDF5 scalar
slack from cycle 461 exactly, as expected.

## Kernel-budget extraction pattern used
Followed cycle 442/444/450/461/463 discipline:
1. `set R₀ := …` for each of the six Taylor remainders A, B, C, D, E2, F.
2. `clear_value A B C D E2 F` immediately after the set block.
3. Residual algebra discharged through the private
   `bdf5Vec_pointwise_residual_alg` helper that takes the `R_i` as
   abstract real / vector-norm inputs.
4. Slack `(59075/1233) ≤ 48` closed via `norm_num` then `linarith`.

The LTE algebraic identity `hLTE_eq` is closed by
`simp only [smul_sub, smul_smul]; module`, the same vector-module tactic
combination used in BDF6 vector. No `nlinarith` required.

## Aristotle disposition
Followed strategy: did **not** open any of the seven listed Aristotle
bundles. Per the cycle audit:
- `a32132c6` (Lyapunov norm equivalence) targets the deferred BDF4/5/6
  global seam (out of scope for the truncation chain).
- `2ebbd920` and `8ea0d162` (`LMMBDF5Convergence.lean` etc.) targeted the
  scalar BDF5 file already closed in cycle 461.
- `60407b4a` / `9ae09f0d` / `30089745` / `8303e116`
  (`LMMBDF3VectorConvergence.lean`) targeted a file already closed in
  cycle 457.

The strategy explicitly authorized skipping these and going directly to
the manual port. No new Aristotle batch submitted: the manual port
finished within a single 30-minute window via direct adaptation of the
existing BDF6-vector template, so a 30-minute Aristotle wait would have
strictly delayed completion without adding signal.

## Result
SUCCESS. `lake env lean OpenMath/LMMBDF5VectorConvergence.lean` returns
zero diagnostics. Full `lake build` reports `Build completed successfully
(8068 jobs)` with no new warnings tied to this module. File is 432 lines,
well under the 3000-line soft cap.

## Deviations from the BDF6-vector template
None of substance. Differences are purely arithmetic:
- 5 starting samples instead of 6.
- BDF5 coefficients `(300, 300, 200, 75, 12)/137` (with the alternating
  signs from the scalar BDF5 file) instead of BDF6's `(360, 450, 400,
  225, 72, 10)/147`.
- One fewer norm-bound term in the private alg lemma (`6` terms instead of
  `7`).
- Sixth-order Taylor remainders / fifth-order derivative-Taylor instead of
  seventh / sixth.

## plan.md update
- Added a new `[x] BDF5 vector truncation chain` bullet under §1.2 BDF
  block, immediately after the BDF5 scalar entry.
- Added a paragraph for `OpenMath/LMMBDF5VectorConvergence.lean` in the
  "live Lean files" prose.
- Updated the "Active frontier" paragraph: BDF4, BDF5, BDF6, and BDF7 now
  each have closed scalar and vector truncation chains; BDF5 no longer
  flagged as "scalar-only".

## Discovery
The BDF6-vector template is structurally identical (modulo coefficient
table) to what BDF5 vector needs. The `simp only [smul_sub, smul_smul];
module` closer for `hLTE_eq` ports verbatim — this confirms cycle 463's
finding that `module` handles the vector residual algebraic identity
without `clear_value` discipline at the LTE-equation step (only the
`bdf5Vec_pointwise_residual_alg` helper needs the discipline). This makes
the BDF-vector ladder (BDF1, BDF2, BDF3, BDF4, BDF5, BDF6, BDF7) entirely
mechanical to write at this point.

## Suggested next approach
The BDF truncation table is now uniform from BDF1 to BDF7 (scalar + vector
each). The remaining BDF stack work is:
- BDF4/BDF5/BDF6 Lyapunov global theorems — blocked by the Perron
  obstruction in `.prover-state/issues/bdf4_lyapunov_gap.md`. The
  long-term answer is the generic quadratic Lyapunov framework
  (`a32132c6` Aristotle bundle hints at this seam), but that is a
  multi-cycle effort and is explicitly out of scope per the issue file.

So the next worker should not pick a BDF target. Options that are
genuinely on the active frontier:
- AM9 / AM10 step extension (continuing AM2–AM8 pattern; previous AB-style
  extensions scored a 2 on the scalar/vector pair, so this is a fairly
  predictable two-cycle chunk if the planner wants to ramp the AM ladder).
- Begin scaffolding the generic quadratic Lyapunov framework that would
  unblock BDF4/5/6 globally (high-risk, multi-cycle, but the only path
  off the Perron wall).
- A non-LMM target from later chapters, e.g. closing remaining gaps in
  the §3.5 BN-stability scaffold or pushing on Theorem 359D once the
  Iserles §3.5.10 source statement is available.

Lean a slight preference for AM9 since it matches the recent cycle cadence
and keeps the AM/AB symmetry explicit. The Lyapunov framework is the
higher-leverage target but probably wants a planning cycle of its own
before any worker attacks it.
