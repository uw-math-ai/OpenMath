# Cycle 490 Results

## Worked on
Continued the BDF4 quantitative global convergence chain in
`OpenMath/BDFQuadraticLyapunov.lean`, landing all three acceptance
targets from the cycle 490 strategy: the initial Lyapunov bound, the
readouts for `|e_n|`, `|e_{n+1}|`, `|e_{n+2}|` in terms of `W_n`, and
the headline `LMM.bdf4_global_error_bound`.

## Approach
Three layered building blocks:

1. **Energy upper bound from coordinate maxima**
   `bdf4StableEnergy_le_of_max e n hM h0 h1 h2 : E ≤ 6·M`,
   proved by combining the upper coercive estimate
   `Q ≤ 9·(x₀² + x₁² + x₂²)` with `Real.sqrt_sq` on `(6·M)² = 36·M²`.

2. **Coordinate lower bounds from the energy**
   `bdf4_abs_X{0,1,2}_le_2E : |X_i| ≤ 2·E`, derived from the lower
   coercive estimate `(1/4)·‖x‖² ≤ Q` and `√(4·Q) = 2·√Q`.

3. **Readouts** `bdf4_eIdx{0,1,2}_le_W : |e_{n+i}| ≤ W_n`. Decompose
   `e_{n+i} = X_i + U/12`, then
   `|e_{n+i}| ≤ 2·E + |U|/12 ≤ 6·E + |U| = W_n` (using `W = |U| + 6·E`).
   `linarith` closes with `|U| ≥ 0` and `E ≥ 0`.

4. **Initial bound** `bdf4LyapW_initial_bound`: with `M = (76/12)·ε₀`,
   `|U_0| ≤ 64·ε₀`, each `|X_i(0)| ≤ M`, so `E_0 ≤ 6·M = 38·ε₀` and
   `W_0 ≤ 64·ε₀ + 6·E_0 ≤ 64·ε₀ + 228·ε₀ = 292·ε₀`. Constant `C₀ = 292`.

5. **Headline `bdf4_global_error_bound`**: mirrored
   `bdf3_global_error_bound` with one extra base case (`N = 3`) and
   the index shift `N = N''+4 = (N''+2)+2`. Step bound at parameter
   `(L = 61·L, C = 122·C, p = 4)` plumbed into
   `lmm_error_bound_from_local_truncation`, then
   `bdf4_eIdx2_le_W e (N''+2)` gives the final readout.
   Horizon hypothesis `((N : ℝ) + 1) · h ≤ T` is the tightest viable
   condition (BDF4 needs `(n+4)·h ≤ T` for the residual at the largest
   Gronwall step `n = N''+1`). Conclusion:
   `|yseq N - y(t₀ + N·h)| ≤ 292·exp((61·L)·T)·ε₀ + K·h⁴`
   with `K = 122·T·exp((61·L)·T)·C`.

## Result
**SUCCESS.** All three acceptance targets closed:
- `LMM.bdf4LyapW_initial_bound` (sorry-free)
- `LMM.bdf4_eIdx0_le_W`, `bdf4_eIdx1_le_W`, `bdf4_eIdx2_le_W` (sorry-free)
- `LMM.bdf4_global_error_bound` (sorry-free)

`OpenMath/BDFQuadraticLyapunov.lean` grew from 473 → 720 lines.
Full `lake build` is green; no other files modified.

## Aristotle usage
None this cycle. The cycle 490 strategy explicitly directed not to
re-incorporate the listed Aristotle results (already reflected in
prior cycles or off-topic). The closed-form proof was short enough
(BDF3 mirror + minor index shift) that direct manual closure was
faster than another Aristotle round trip.

## Dead ends
None. The constants C₀ = 292 (initial bound) and C₁ = 1 (readouts)
fell out cleanly from the existing `bdf4CubicQuad_lower` /
`bdf4CubicQuad_upper` coercive estimates and the `W = |U| + 6·E`
weight. The `Real.sqrt_sq` / `Real.sqrt_mul` rewrites went through
without needing `Real.sqrt_lt` slack manipulation suggested in the
strategy's "if the sqrt step is awkward" branch.

## Discovery
The readout `|e_{n+i}| ≤ W_n` holds with constant `C₁ = 1` rather
than the strategy-suggested `C₁ = 3`, because the stable-block
energy `bdf4StableEnergy = √Q` is multiplied by 6 inside `W`.
That tighter constant feeds directly into the headline `K₁ = 292`
without further slack.

## Suggested next approach
- The BDF4 chain is now closed. Plan the analogous BDF5/BDF6
  Lyapunov certificates (different spectral structure required —
  the BDF4 prototype demonstrates the quadratic Lyapunov path
  works where weighted ℓ¹ fails).
- Or pivot to a different Iserles chapter target — `plan.md`
  should be checked for the next priority once the multistep
  convergence series is complete.
- Optional polish: extract the three `bdf4_abs_X{0,1,2}_le_2E`
  helpers into a single parameterized lemma; not blocking.
