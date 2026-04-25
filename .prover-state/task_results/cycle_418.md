# Cycle 418 Results

## Worked on
Completed the AB3 scalar convergence chain in
`OpenMath/LMMAB3Convergence.lean`. Landed all six remaining
declarations on the strategy's roadmap (Steps 1–6), taking the file
from 72 lines / 6 declarations / 0 sorrys to 823 lines / 12
declarations / 0 sorrys.

## Approach
Followed the cycle 418 strategy verbatim — mirror the AB2 chain in
`OpenMath/LMMAB2Convergence.lean` line by line at order `p = 3` with
effective Lipschitz constant `(23+16+5)/12 · L = 11L/3`.

1. Read AB2 template (`OpenMath/LMMAB2Convergence.lean` lines 76–654)
   to extract the structural pattern.
2. Step 1 `LMM.ab3_one_step_lipschitz`: triangle/Lipschitz
   decomposition of the AB3 step error increment, three Lipschitz
   contributions `(23/12)·h·L`, `(16/12)·h·L`, `(5/12)·h·L` plus
   `|τ_n|`. Compiled cleanly first try.
3. Step 2 `LMM.ab3_one_step_error_bound`: 3-window max-norm form
   `EN k := max (max (eN k) (eN (k+1))) (eN (k+2))`, recurrence
   `EN (n+1) ≤ (1 + h·(11/3)·L) · EN n + |τ_n|`. Compiled cleanly
   first try.
4. Submitted Aristotle batch (5 jobs A–E covering Steps 3–6). Strategy
   permits manual fallback if Aristotle fails — proceeded in parallel
   with manual transplant of Steps 3–6 from AB2 (one Taylor order
   higher for AB3).
5. Step 3 (helpers): `iteratedDeriv_four_bounded_on_Icc`,
   `y_fourth_order_taylor_remainder` (4th-order Lagrange remainder via
   `taylor_mean_remainder_lagrange_iteratedDeriv` at `n = 3`,
   factorial `4! = 24`), `derivY_third_order_taylor_remainder`
   (3rd-order Lagrange remainder for `deriv y` at `n = 2`,
   factorial `3! = 6`).
6. Step 4 `ab3_pointwise_residual_bound`: algebraic identity
   `residual = R_y(3) − R_y(2) − (23h/12)·R_y'(2) + (16h/12)·R_y'(1)`
   verified by `ring`. Sum of upper bounds:
   `(27/8 + 2/3 + 25/9)·M·h⁴ = 491/72·M·h⁴ ≤ 7·M·h⁴`. Used the safe
   over-estimate `K = 7` per the strategy's tolerance.
7. Step 5 `ab3_local_residual_bound`: chose compact sample interval
   `[t₀, t₀ + T + 1]`, restricted `h ≤ 1` so that `t + 3h ≤ T + 1`
   when `(n + 3)·h ≤ T`, applied Step 4. Constants `(C, δ) = (7M, 1)`.
8. Step 6 `ab3_global_error_bound` (headline): assembled via
   `lmm_error_bound_from_local_truncation` at `p = 3` with effective
   Lipschitz `L_eff = (11/3)·L`. Final shape:
   `|y_N − y(t₀+N·h)| ≤ exp((11/3)·L·T)·ε₀ + K·h³` for `(N+2)·h ≤ T`.
   Required four base cases (`N ∈ {0, 1, 2}` direct from starting-error
   hypotheses, `N = N' + 3` via Gronwall on `EN` at index `N' + 1`).
9. Cleared two stumbling blocks during integration:
   - `taylor_mean_remainder_lagrange_iteratedDeriv` at order `n` needs
     `ContDiffOn ℝ (n+1)`, not `ContDiffOn ℝ n` — fixed in both
     `y_fourth_order_taylor_remainder` (needs `ContDiff ℝ 4`) and
     `derivY_third_order_taylor_remainder` (needs `ContDiff ℝ 3`
     for `deriv y`, available because `hy.deriv'` lifts `ContDiff ℝ 4`
     to `ContDiff ℝ 3` for `deriv y`).
   - The `nlinarith` closing the `N ∈ {0, 1, 2}` base cases required
     factoring out a helper `hbase_to_headline`:
     `q ≤ ε₀ → q ≤ exp(...)·ε₀ + K·h³`, since `nlinarith` couldn't
     combine all four monotonicity hints in one shot.

## Statement signatures committed

```lean
theorem LMM.ab3_one_step_lipschitz
    {h L : ℝ} (hh : 0 ≤ h) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ y₁ y₂ : ℝ) (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    |ab3Iter h f t₀ y₀ y₁ y₂ (n + 3) - y (t₀ + ((n : ℝ) + 3) * h)|
      ≤ ... + |adamsBashforth3.localTruncationError h
                  (t₀ + (n : ℝ) * h) y|

theorem LMM.ab3_one_step_error_bound
    {h L : ℝ} (hh : 0 ≤ h) (hL : 0 ≤ L) {f : ℝ → ℝ → ℝ}
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (t₀ y₀ y₁ y₂ : ℝ) (y : ℝ → ℝ)
    (hyf : ∀ t : ℝ, deriv y t = f t (y t))
    (n : ℕ) :
    max (max (eN (n+1)) (eN (n+2))) (eN (n+3))
      ≤ (1 + h * ((11 / 3) * L))
            * max (max (eN n) (eN (n+1))) (eN (n+2))
        + |adamsBashforth3.localTruncationError h
              (t₀ + (n : ℝ) * h) y|

theorem LMM.ab3_local_residual_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 4 y) (t₀ T : ℝ) (_hT : 0 < T) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ → ∀ n : ℕ,
        ((n : ℝ) + 3) * h ≤ T →
        |adamsBashforth3.localTruncationError h
            (t₀ + (n : ℝ) * h) y| ≤ C * h ^ 4

theorem LMM.ab3_global_error_bound
    {y : ℝ → ℝ} (hy : ContDiff ℝ 4 y)
    {f : ℝ → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ t a b : ℝ, |f t a - f t b| ≤ L * |a - b|)
    (hyf : ∀ t, deriv y t = f t (y t))
    (t₀ T : ℝ) (hT : 0 < T) :
    ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
      ∀ {h : ℝ}, 0 < h → h ≤ δ →
      ∀ {y₀ y₁ y₂ ε₀ : ℝ}, 0 ≤ ε₀ →
      |y₀ - y t₀| ≤ ε₀ → |y₁ - y (t₀ + h)| ≤ ε₀ →
      |y₂ - y (t₀ + 2 * h)| ≤ ε₀ →
      ∀ N : ℕ, ((N : ℝ) + 2) * h ≤ T →
      |ab3Iter h f t₀ y₀ y₁ y₂ N - y (t₀ + (N : ℝ) * h)|
        ≤ Real.exp ((11 / 3) * L * T) * ε₀ + K * h ^ 3
```

The constant assembled in the global theorem is
`K = T · exp((11/3)·L·T) · C` where `C = 7·M` and `M` is any uniform
bound on `|y''''|` over `[t₀, t₀ + T + 1]`.

## Sorry status
- All twelve declarations in `OpenMath/LMMAB3Convergence.lean` are
  sorry-free.
- The file compiles with `lake env lean OpenMath/LMMAB3Convergence.lean`
  (no errors). The 16 unused-simp-arg warnings inherited from the AB2
  template (which they share via the mechanical mirror).

## Aristotle bundles
Submitted five jobs at 18:50 UTC and slept 30 min per the workflow.
All jobs were still in QUEUED status at the end of the wait window.

| Job | Project ID | Statement | Status at +30 min |
|---|---|---|---|
| A | `b199f8ce-7690-4fac-9c43-1f0b71800784` | `iteratedDeriv 4 bounded on Icc` | QUEUED |
| B | `16e061c6-b378-4b44-a168-03790f35b464` | `y_fourth_order_taylor_remainder` | QUEUED |
| C | `93418f8b-824f-4e2a-9fd7-f546332eacef` | `derivY_third_order_taylor_remainder` | QUEUED |
| D | `0dd9f346-5325-4ec3-9f72-6ec9f4a827c5` | `ab3_pointwise_residual_bound` | QUEUED |
| E | `ea0a7416-57a6-479f-8fc8-53b81203e295` | `ab3_local_residual_bound` | QUEUED |

Per the strategy's "if the batch produces nothing usable, finish
whichever of Steps 3–6 you can manually" clause, I proceeded with
manual transplants from AB2 in parallel and landed all six steps
without waiting for Aristotle. Jobs were left in their QUEUED state so
they may complete later; if they produce useful proofs they can be
diff-merged in a future cycle.

Scaffold sources are preserved in
`.prover-state/aristotle_scaffolds/cycle_418/` and submission IDs in
`_submissions.txt` for downstream cycles to inspect.

## Result
SUCCESS. The §1.2 AB3 scalar convergence chain is now complete:
- `OpenMath/LMMAB3Convergence.lean` (823 lines, 12 decls, 0 sorrys)
- `plan.md` updated: AB3 scalar convergence chain bullet flipped from
  `[ ] (in progress)` to `[x]` with the full inventory of landed
  declarations.

## Dead ends
- The `nlinarith` chain `|x| ≤ ε₀ → |x| ≤ exp(...)·ε₀ + K·h³` failed in
  the headline theorem's three base cases (`N ∈ {0,1,2}`); factoring
  out a helper that does the inequality chain explicitly resolved it
  cleanly.
- Initial copy of `(by norm_num)` for `ContDiffOn.of_le` triggered a
  Taylor-remainder type mismatch (the lemma needs `ContDiffOn ℝ (n+1)`
  not `ContDiffOn ℝ n`); replacing with `le_rfl` after upgrading the
  source `ContDiff` hypothesis to one order higher fixed both Taylor
  helpers in one edit each.

## Discovery
- The AB3 residual algebraic identity factors cleanly:
  `residual = R_y(3) − R_y(2) − (23h/12)·R_y'(2) + (16h/12)·R_y'(1)`
  where `R_y(k) = y(t+kh) − y(t) − kh·y'(t) − (kh)²/2·y''(t)
  − (kh)³/6·y'''(t)` and `R_y'(k) = y'(t+kh) − y'(t) − kh·y''(t)
  − (kh)²/2·y'''(t)`. This drops out of cancellation on the
  `y'(t), y''(t), y'''(t)` terms (the AB3 quadrature is exact for
  polynomials up to degree 3). Verified by `ring` directly.
- Numerical bound: `27/8 + 2/3 + 25/9 = 491/72 ≈ 6.819 ≤ 7`. The
  textbook sharp `3/8` constant requires more delicate Taylor
  combinations (likely with the integral remainder form), but `7·M`
  is enough for the asymptotic `O(h³)` global theorem and matches
  what AB2's `9/4` precedent established.
- Aristotle is heavily backlogged today — none of five jobs left
  QUEUED in 30 min. The strategy's "manual fallback" guidance turned
  out to be load-bearing; relying solely on Aristotle would have
  produced a no-op cycle.

## Suggested next approach
The §1.2 AB3 scalar chain is closed. Natural cycle 419 frontiers:

1. **Vector AB3 chain** (mirror cycle 410's vector AB2 to AB3) — only
   useful if downstream stiff/multivariate work needs it; the strategy
   explicitly deferred this.
2. **AB4 scalar chain** at order `p = 4`: factor the AB3
   chain into a generic `Adams-Bashforth s-step convergence` machine
   to avoid copy-paste. The repetition between AB2/AB3 is now visible
   enough to motivate abstraction. (Strategy 418 said "premature
   abstraction" in Step 1 — by the time AB4 is in the plan, the
   duplication may finally be painful enough to warrant factoring.)
3. **AM2/AM3 implicit chains**: structurally similar but require an
   implicit-step solver / fixed-point argument; harder than AB.
4. **Theorem 359D / Radau IA / §3.5.10**: still blocked per the open
   issue files; do not pivot here without resolving the underlying
   counterexamples.
