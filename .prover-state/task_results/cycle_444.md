# Cycle 444 Results

## Worked on
Adams-Moulton 7-step (AM7) scalar quantitative convergence chain — new file
`OpenMath/LMMAM7Convergence.lean`, plus `adamsMoulton7` definition added to
`OpenMath/AdamsMethods.lean`.

## Approach
Mirrored the AM6 scalar chain (`OpenMath/LMMAM6Convergence.lean`) line-for-line,
extending from a 6-window/8th-order/8 weights structure to a 7-window/9th-order/8
weights structure. Concrete numeric work:
- Verified AM7 weight sum is 120960 (consistency check).
- Computed the explicit Lipschitz weight sum
  `S = (36799+139849+121797+123133+88547+41499+11351+1375)/120960 = 527551/120960 ≈ 4.36`.
- Implicit slack: `β₇ = 36799/120960 ≈ 0.304`. Setting growth bound to `G·L`
  and using `(1 − β₇·hL)·… ≥ (1/2)·…` on the implicit side, the divided form
  gives `G ≥ 2(β + S) ≈ 9.33` so the smallest valid integer is `G = 10`
  (strategy suggested 8L→9L; numeric analysis bumped to 10L).
- Factoring for `am7_one_step_error_bound`:
  `(D, N₁, N₂) = (120960, 645250, 367990)` with
  `367990·(60480/36799) = 604800`, leaving slack `645250 − 604800 = 40450 > 0`
  for `linarith` closure.
- Residual coefficient: exact algebraic identity gives
  `84361887977/348364800 ≈ 242.17`, slackened to `243`.

## Result
SUCCESS — `OpenMath/LMMAM7Convergence.lean` compiles sorry-free
(`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean
OpenMath/LMMAM7Convergence.lean` exits 0; `lake build` completes 8068/8068).
Headline theorem:
```
LMM.am7_global_error_bound :
  ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
    ∀ {h : ℝ}, 0 < h → h ≤ δ →
    (36799 / 120960 : ℝ) * h * L ≤ 1/2 →
    ∀ {yseq : ℕ → ℝ} {ε₀ : ℝ}, IsAM7Trajectory h f t₀ yseq → 0 ≤ ε₀ →
    (7 starting bounds eᵢ ≤ ε₀ for i = 0..6) →
    ∀ N : ℕ, ((N : ℝ) + 6) * h ≤ T →
    |yseq N − y (t₀ + N·h)| ≤ exp((10·L)·T) · ε₀ + K · h^8
```

## Dead ends
- Initial proof of `am7_pointwise_residual_bound` carried 7 dead
  `0 ≤ (β·h)/120960` `linarith` proofs (copied from AM6) that were not used
  (the triangle helper takes only `hh : 0 ≤ h`). The kernel `whnf` and
  `isDefEq` heartbeat budget timed out at lines 1225 / 1444:49 inside the
  giant 27-`set` context. Removing the seven dead `_nn` lines (linarith
  scanning all 27 `_def` hypotheses for trivial nonnegativities) cleared
  both timeouts. (AM6 has the same dead lines but a smaller — 23 — context,
  so it stays inside the budget.)
- Strategy doc claimed `adamsMoulton7` already lived in `AdamsMethods.lean`;
  it did not. Added the definition (α with last entry +1, β with eight
  entries summing to 120960) before importing into the new convergence file.

## Discovery
- For 7-step (k=7) Adams-Moulton, the dead-`_nn`-lines pattern that AM6
  tolerated tips over the 200000 heartbeat budget. Watch for this in any
  k≥7 mirror — strip dead `linarith` proofs aggressively when `set` count
  passes ~25.
- The minimum integer growth constant `G` for AMₖ at order `k+1` is
  `⌈2(βₖ + S)⌉` where `S = Σ|βᵢ|/D` (sum of absolute weights / common
  denominator); for AM7 this is `⌈9.33⌉ = 10`. AM6 sits at 7; AM5 at 5;
  AM4 at 4; AM3 at 3; AM2 at 3. Pattern: roughly linear in k for large k,
  consistent with explicit Adams stability constants.
- Slackened residual coefficient `243` is the smallest integer ≥
  `84361887977/348364800` and gives `linarith` clean closure of the
  `am7_residual_combine` helper from the algebraic identity coefficient.

## Suggested next approach
- **AM7 vector chain** (`OpenMath/LMMAM7VectorConvergence.lean`): mirror
  cycle 444 to finite-dimensional normed spaces using the AM6 vector chain
  (cycle 443) as the line-for-line template. Reuse public ninth-order
  vector Taylor helpers if they exist; otherwise add private versions
  `iteratedDeriv_nine_bounded_on_Icc_vec`, `y_ninth_order_taylor_remainder_vec`,
  `derivY_eighth_order_taylor_remainder_vec`. Same growth constant
  `10L`, same residual coefficient `243`.
- After AM7 vector closes, the textbook §1.2 LMM convergence stack is
  fully covered for AB2–AB6 and AM2–AM7. Next frontier choices:
  (a) BDF1–BDF6 quantitative convergence chains, (b) push AB7+/AM8+
  (mostly mechanical), (c) move to §1.3+ Runge–Kutta convergence.

## Aristotle batch
Skipped — the AM6 mirror produced a sorry-free file on first elaboration
attempt (modulo the dead-`_nn` cleanup), so no sorries existed to delegate.
Aristotle is most useful when sorries persist after the manual pass.
