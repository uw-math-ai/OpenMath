# Cycle 452 Results

## Worked on
Adams–Moulton 8-step (AM8) scalar quantitative convergence chain — new file
`OpenMath/LMMAM8Convergence.lean` (1969 lines), plus `adamsMoulton8`
definition added to `OpenMath/AdamsMethods.lean`.

## Approach
Mirrored the AM7 scalar chain (`OpenMath/LMMAM7Convergence.lean`,
1761 lines) line-for-line, extending from a 7-window/9th-order/8 weights
structure to an 8-window/10th-order/9 weights structure. Concrete
numeric work:

- Verified AM8 weights via Lagrange interpolation (Iserles AM8, denominator
  3628800):
  `β₈ = 1070017/3628800` (implicit),
  `β₇ = +4467094/3628800`,
  `β₆ = −4604594/3628800`,
  `β₅ = +5595358/3628800`,
  `β₄ = −5033120/3628800`,
  `β₃ = +3146338/3628800`,
  `β₂ = −1291214/3628800`,
  `β₁ = +312874/3628800`,
  `β₀ = −33953/3628800`,
  with sign pattern `+,+,−,+,−,+,−,+,−`. Verified `Σ β_i = 1` symbolically.
- Sum of explicit |βᵢ| = 24484545/3628800 ≈ 6.747.
- Implicit slack: `β₈ = 1070017/3628800 ≈ 0.295`. Min integer growth
  `G ≥ 2(β₈ + S) ≈ 14.08` so `G = 15` (replaces AM7's 10).
- Factoring for `am8_one_step_error_bound`:
  `(D, N₁, N₂) = (3628800, 28877438, 16050255)` with
  `16050255·(1814400/1070017) = 27216000`, leaving slack
  `28877438 − 27216000 = 1661438 > 0` for `linarith` closure (the pivotal
  step uses identity `(hL/D)·(28877438 − 16050255·hL) ≥ 0`).
- Residual coefficient: exact algebraic identity gives
  `4555920744497/6858432000 ≈ 664.28`, slackened to `665`.
- Extended the Lipschitz triangle to 11 terms (10 algebraic + τ),
  the residual triangle to 10 terms, and the algebraic identity to
  10 signed Taylor remainders (2 y, 8 y′).

## Result
SUCCESS — `OpenMath/LMMAM8Convergence.lean` compiles sorry-free
(`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean
OpenMath/LMMAM8Convergence.lean` exits 0). Axiom check on
`LMM.am8_global_error_bound` returns only the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

Headline theorem:
```
LMM.am8_global_error_bound :
  ∃ K δ : ℝ, 0 ≤ K ∧ 0 < δ ∧
    ∀ {h : ℝ}, 0 < h → h ≤ δ →
    (1070017 / 3628800 : ℝ) * h * L ≤ 1/2 →
    ∀ {yseq : ℕ → ℝ} {ε₀ : ℝ}, IsAM8Trajectory h f t₀ yseq → 0 ≤ ε₀ →
    (8 starting bounds eᵢ ≤ ε₀ for i = 0..7) →
    ∀ N : ℕ, ((N : ℝ) + 7) * h ≤ T →
    |yseq N − y (t₀ + N·h)| ≤ exp((15·L)·T) · ε₀ + K · h^9
```

## Dead ends
- Initial `am8_localTruncationError_eq` proof used
  `simp only [...]; push_cast; ring` (mirroring AM7's recipe): `ring`
  failed because at AM8 there are 9 simp args producing terms like
  `t + (1+1+1+1+1+1+1+1)·h` that `ring` does not internally normalize.
  Fix: insert `norm_num` between the `simp` and `ring` to fold the
  iterated `1+1+...+1` sums to `7` and `8`. The simpler AM7 form
  (`simp [...]; ring`) does not work for AM8 because the nat-cast
  expansion produces longer 1-sums in AM8.

## Discovery
- For AM8 (`s = 8`), the `simp` expansion of `Fin.sum_univ_succ` over
  `Fin 9` produces `1+1+...+1` chains of length up to 8, which `ring`
  alone cannot close (it doesn't normalize iterated additions of `1`
  to numeric literals at this depth). `norm_num` between the simp and
  the `ring` fixes it cleanly. Watch for this pattern at any `s ≥ 8`.
- Sign pattern for AMₖ (k = step count): the implicit β_k is positive,
  followed by alternating signs `+, −, +, −, …` ending with sign
  determined by parity. AM8 ends with `−` on β₀; AM7 ends with `+` on
  β₀ (after starting with `+, −, +, −, +, −, +`). The triangle helper
  must be regenerated to match the actual AM8 sign pattern (not pure
  copy from AM7).
- For AM8's pointwise residual, the algebraic identity uses 2 y-Taylor
  remainders (at stencil distances 7h and 8h, both with 9-term Taylor
  expansion) and 8 y'-Taylor remainders (at distances 0, h, 2h, …, 7h,
  each with 8-term Taylor expansion). The `am8_residual_alg_identity`
  and `am8_residual_bound_alg_identity` close cleanly with a single
  `ring` despite the high degree.
- `clear_value` discipline was retained (mirroring AM7 cycles 444/450)
  — the 8-window context with ~30 set-bindings stayed within the
  200000 heartbeat budget. No splitting beyond the AM7 layout.

## Aristotle batch
Submitted one prompt-style job
`af2bbcf1-0d18-4bb9-ad25-470574af484e` covering
`am8_localTruncationError_eq` as a mandatory check. Per cycles
442–451, prior Aristotle returns on this kind of LMM truncation
identity have been QUEUED-only or COMPLETE_WITH_ERRORS with stub
rebuilds; not waited on, file already sorry-free. Skipped the
remaining four planned sub-lemma jobs because the file was complete
before the first job's status would settle.

## Suggested next approach
- **AM8 vector chain** (`OpenMath/LMMAM8VectorConvergence.lean`):
  mirror cycle 452 to finite-dimensional normed spaces using the
  AM7 vector chain (cycle 445) as the line-for-line template. Reuse
  public tenth-order vector Taylor helpers if they exist; otherwise
  add private versions `iteratedDeriv_ten_bounded_on_Icc_vec`,
  `y_tenth_order_taylor_remainder_vec`,
  `derivY_ninth_order_taylor_remainder_vec`. Same growth constant
  `15L`, same residual coefficient `665`. Same `norm_num`-between-
  `simp`-and-`ring` recipe for `am8Vec_localTruncationError_eq`.
- After AM8 vector closes, the full §1.2 LMM scalar+vector stack is
  AB2–AB7 + AM2–AM8 + BDF1–BDF2. Next frontier choices:
  (a) BDF3 quantitative convergence chain, (b) AB8 quantitative
  convergence (mostly mechanical), (c) move to §1.3+ Runge–Kutta
  convergence.
