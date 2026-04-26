# Cycle 436 Results

## Worked on
AM4 quantitative scalar convergence chain — new tracked file
`OpenMath/LMMAM4Convergence.lean`, mirroring AM3 (cycle 435) one
stencil step up.

## Approach
1. **Promoted three AB5 sixth-order Taylor helpers from `private` to public** in
   `OpenMath/LMMAB5Convergence.lean`:
   - `iteratedDeriv_six_bounded_on_Icc`
   - `y_sixth_order_taylor_remainder`
   - `derivY_fifth_order_taylor_remainder`

   Refreshed the olean via `lake build OpenMath.LMMAB5Convergence`.
2. **Ported the AM3 file directly to AM4**, using the AM4 coefficients
   `(251, 646, −264, 106, −19) / 720`:
   - `IsAM4Trajectory` predicate
   - `am4_localTruncationError_eq` (textbook unfolding via
     `Fin.sum_univ_five`)
   - `am4_one_step_lipschitz` (5-term abs-triangle, implicit factor on
     LHS)
   - `am4_one_step_error_bound` (divided form on the 4-window
     `max(en, en1, en2, en3)`)
   - `am4_one_step_error_pair_bound` (rolling 4-window recurrence)
   - `am4_pointwise_residual_bound` (sixth-order Taylor identity)
   - `am4_local_residual_bound` (uniform `|τ_n| ≤ C·h^6`)
   - `am4_global_error_bound` (headline, `O(ε₀ + h^5)` on
     `(N+3)·h ≤ T`, via `lmm_error_bound_from_local_truncation` at
     `p = 5`)

## Result
**SUCCESS** — file compiled cleanly on the first attempt with **zero
sorrys**.  No Aristotle round-trip was needed: every proof step
ported one-for-one from the AM3 template once the new abs-triangle
shape (7 terms instead of 6) and the additional `set en4` /
`set tn4` / `set zn4` / `hcast4` / 4-window `max_le` chain were
threaded through.

## Key numerical facts (recorded for future cycles)
- Implicit-coefficient side condition: `(251/720)·h·L ≤ 1/2`,
  equivalent to `h·L ≤ 360/251 ≈ 1.434`.
- Explicit-history weight sum: `(646 + 264 + 106 + 19)/720 =
  1035/720 = 23/16` (used in the `(1 + 23/16 · hL) · E + τabs` row
  of `am4_one_step_error_bound`).
- Divided growth slack: `3L` was checked algebraically and **does
  not** close `nlinarith` over the full `hL ≤ 360/251` regime — the
  required upper bound is `hL ≤ 874/753 ≈ 1.16 < 1.434`.  Bumped to
  `4L`, which gives a closure window `hL ≤ 1594/1004 ≈ 1.587 >
  1.434`. ✓.  This justifies the "fall back to `4L`" branch flagged
  in the strategy.
- Pointwise residual coefficient (exact rational): `M·h^6` factor is
  `1001556/86400 = 250389/21600 ≈ 11.59`; slackened to `12` (the
  smallest integer above).
- Headline rate: `Real.exp ((4L)·T)·ε₀ + K·h^5` with
  `K = T · exp((4L)·T) · (2C)`.

## Dead ends
None — direct AM3 port closed everything.

## Discovery
- The "fall back to `4L`" knob the strategy flagged is genuinely
  required at AM4: the explicit-weight ratio `1035/720 ≈ 1.4375` is
  comparable to the upper bound on `hL` from the implicit side
  condition, so the divided form needs a fatter growth constant.
  AM5/AM6 will likely need `5L`/`6L` respectively because the
  weight ratios continue to grow (`1901/720`, `4277/1440` etc.).
- The AM3-style 7-term abs-triangle helper `htri_terms (A B C D E F G : ℝ)`
  is now used at AM4 and will generalize to AM5 / AM6 with one
  additional term per step (8-term, 9-term).
- `Fin.sum_univ_five` worked directly inside the `simp` for
  `am4_localTruncationError_eq`, mirroring the AM3 use of
  `Fin.sum_univ_four`.

## Suggested next approach
- **AM5 quantitative scalar convergence chain** is the natural next
  target: same template at one more stencil step, with the AB6
  seventh-order Taylor helpers already public in
  `OpenMath/LMMAB6ScalarConvergence.lean`.  Coefficients are
  `β = (475, 1427, −798, 482, −173, 27)/1440`; explicit weight sum
  is `(1427 + 798 + 482 + 173 + 27)/1440 = 2907/1440 ≈ 2.018`, so
  the divided slack will need to be at least `5L` (the weight sum
  alone exceeds `2L`, and the implicit factor only cuts `(475/1440)
  ·hL`).
- Stretch (cycle 436 closed early enough that this could be a
  parallel target): begin a `LMMAM4VectorConvergence.lean`
  scaffold mirroring the AB5 vector chain (vector AM4 has not been
  built yet).  Per-strategy guidance: scaffold only, do not push the
  full vector residual identity in the same cycle.
- The Adams–Moulton chain is now closed up to AM4. AM6 would need
  AB7 helpers, which do not exist yet — it would either gate on
  building `LMMAB7Convergence` first, or on extracting `derivY` /
  `y` Taylor remainders at order 7/8 directly inside the AM6 file.
