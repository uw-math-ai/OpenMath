# Cycle 474 Results

## Worked on
Adams–Moulton 9-step **vector** quantitative convergence chain — vector mirror
of the cycle-473 scalar AM9 chain (`OpenMath/LMMAM9Convergence.lean`).

New file: `OpenMath/LMMAM9VectorConvergence.lean` (1806 lines, compiles clean,
zero `sorry`/`axiom`).

## Approach
Followed the AM8 scalar→vector port pattern (cycle 455), ported AM9-scalar
structure (cycle 473) to finite-dimensional normed vector spaces:

- Imported `OpenMath.LMMAM8VectorConvergence` and
  `OpenMath.LMMAB10VectorConvergence`, reused the public eleventh-order vector
  Taylor helpers `iteratedDeriv_eleven_bounded_on_Icc_vec`,
  `y_eleventh_order_taylor_remainder_vec`,
  `derivY_tenth_order_taylor_remainder_vec` from `LMMAB10VectorConvergence`.
- Defined `IsAM9TrajectoryVec` (9 starting samples, supplied implicit
  trajectory with the AM9 weights `(2082753, 9449717, -11271304, 16002320,
  -17283646, 13510082, -7394032, 2687864, -583435, 57281)/7257600`).
- Built `am9VecResidual` and proved `am9Vec_localTruncationError_eq`.
- Closed `am9Vec_one_step_lipschitz` and `am9Vec_one_step_error_pair_bound`
  (9-window implicit recurrence under `(2082753/7257600)hL ≤ 1/2`, slackened
  to growth `23L` and residual coefficient `2` after dividing out the implicit
  factor — minimum integer `G ≥ 2Σ|β_k| ≈ 22.13` is 23).
- Extracted private kernel-friendly helpers:
  `am9Vec_residual_alg_identity` (proved by
  `simp only [smul_sub, smul_add, smul_smul]; module`),
  `am9Vec_residual_bound_alg_identity` (proved by `ring`),
  `am9Vec_residual_eleven_term_triangle` (11-letter triangle A,B,C,D,F,G,I,J,K,L,P),
  `am9Vec_residual_combine`.
- Used `set` + `clear_value` discipline after the eleven Taylor `set`s to keep
  kernel `whnf` budget under 200000 heartbeats.
- Proved `am9Vec_pointwise_residual_bound`, `am9Vec_local_residual_bound`
  (`‖τ_n‖ ≤ 1827·M·h¹¹`, exact coefficient
  `88212037990481513/48283361280000 ≈ 1826.97`).
- Closed the headline `am9Vec_global_error_bound`
  (`‖y_N − y(t₀+Nh)‖ ≤ exp(23L·T)·ε₀ + K·h¹⁰` for `(N+8)·h ≤ T`)
  via `lmm_error_bound_from_local_truncation`-style routing with 9 epsilon
  initial bounds and a 9-case match (`0..8` plus `N' + 9`).

## Result
SUCCESS. `lake env lean OpenMath/LMMAM9VectorConvergence.lean` exits 0 with
no errors, warnings, or sorries. Independent grep verifies all 13 expected
declarations are present.

## Dead ends
None this cycle — the AM8 vector port (cycle 455) and the AM9 scalar chain
(cycle 473) gave a fully concrete blueprint, and the eleventh-order vector
Taylor helpers were already public from `LMMAB10VectorConvergence` so no new
helper infrastructure was needed.

The pre-existing Aristotle bundle `f3701dca-5054-4323-8540-8db30a271f69`
(off-target BDF3-vector + stub VecTaylorHelpers) was rejected per strategy.

## Discovery
The combination of (a) public vector Taylor helpers shared between the AB10
and AM9 vector chains and (b) the cycle-473 scalar AM9 file as a near-line-
by-line guide makes the scalar→vector port for AM-step `s ≥ 8` chains
essentially mechanical: replace `*` with `•`, `|·|` with `‖·‖`, prove the
algebraic identity with `simp only [smul_sub, smul_add, smul_smul]; module`,
and the residual bound identity stays scalar (`ring`).

## Suggested next approach
The active frontier shifts to:

- **AM2–AM9 scalar AND vector chains all closed** — Adams–Moulton convergence
  stack is now complete through the 9-step (10th-order) method in both
  scalar and vector forms. Continuing the AM stack to AM10 (11-step,
  11th-order) is technically possible but would need 12th-order Taylor
  helpers, which would require new infrastructure beyond the AB10/AM9 share.
- More valuable next directions: BDF4/BDF5/BDF6 Lyapunov/global theorems
  (currently deferred by the spectral obstruction in
  `.prover-state/issues/bdf4_lyapunov_gap.md`) — closing those would unlock
  global error bounds for the full BDF1–BDF6 stack and is the largest open
  hole in the LMM convergence frontier on `main`.
