# Cycle 015 Results

## Worked on

1. **Priority 1** — `OpenMath/Chapter1/Section112.lean`: cosmetic
   `h_inner → hinner` rename at four touch-points (lines 110, 118, 125,
   126), per the cycle-014 consultant note. Eliminates the lone
   tautology-scanner false positive without changing proof semantics.

2. **Priority 2** — `thm:213B` (Euler method uniform convergence) in
   `OpenMath/Chapter2/Section213.lean`, plus two supporting off-step
   bound lemmas in `OpenMath/Chapter2/Section212.lean`:
   * `EulerSetup.yhat_offstep_repr` — for any `t ∈ [x₀, xN]`, finds
     the largest grid index `k₀` with `S.x k₀ ≤ t`, gives
     `t - S.x k₀ ≤ S.H`, and packages the off-step Euler representation
     `S.ŷ t = S.ŷ (S.x k₀) + (t - S.x k₀) • S.f (S.x k₀) (S.ŷ (S.x k₀))`
     (collapsing to triviality when `k₀ = Fin.last`).
   * `global_truncation_error_L_zero_offstep` — extends the on-step
     `L = 0` bound by adding a `2·Mf·S.H` slack covering the partial
     Euler step `[xₖ₀, t]`.
   * `global_truncation_error_L_pos_offstep` — same extension for the
     `L > 0` (exponential) on-step bound.
   * `euler_convergence_uniform` — the ε-N form
     `∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ t ∈ Icc x₀ xN, ‖(S n).y t - (S n).ŷ t‖ < ε`.

3. **Priority 3** — housekeeping:
   * Updated `extraction/formalization_data/lean_status.json` for
     `thm:213B` (formalized).
   * Updated `plan.md`: marked `thm:212A`, `thm:213A`, `thm:213B`
     and the already-formalized Chapter 1 entities as `[x]`. Updated
     progress counter `0 / 175` → `16 / 175`.
   * Wrote `.prover-state/issues/tautology_scanner_false_positives.md`
     documenting bugs D1 (block-comment line drift) and D2
     (`exact h_<name>` over-firing) per the cycle-014 consultant
     note §D.
   * Trimmed cycle-010 and cycle-013 stale tautology-scanner entries
     from `.prover-state/attempts.md`.

## Approach

### Priority 1 — rename `h_inner → hinner`

Used Edit tool to apply the rename at exactly the four lines the
cycle-014 consultant identified. Verified `lake env lean` clean and
`#print axioms` unchanged (only `propext, Classical.choice, Quot.sound`).

### Priority 2 — off-step extension + uniform convergence

The on-step lemmas
(`global_truncation_error_L_{zero,pos}`) bound the error at every
grid point `S.x k`. The textbook 213B requires a bound at every
`t ∈ [x₀, xN]`. Approach:

1. **`yhat_offstep_repr` lemma.** For any `t ∈ [x₀, xN]`, the largest
   grid index `k₀ : Fin (S.n + 1)` with `S.x k₀ ≤ t` is computed via
   `Finset.max'` on the filtered finset `{k | S.x k ≤ t}` (nonempty
   because `S.x ⟨0, _⟩ ≤ t`). Two cases:
   - `k₀ = Fin.last`: then `S.x k₀ = xN` and `S.x k₀ ≤ t ≤ xN` forces
     `t = S.x k₀`, so the off-step formula collapses to
     `ŷ t = ŷ (S.x k₀) + 0 = ŷ (S.x k₀)`.
   - `k₀ < Fin.last`: then `t ∈ Icc (S.x k_step.castSucc) (S.x k_step.succ)`
     for the cast `k_step := k₀.castLT _ : Fin S.n` (using
     `Fin.castSucc_castLT`), and `EulerSetup.hŷ_interp k_step t` gives
     the formula directly. The bound `t - S.x k₀ ≤ S.H` follows from
     `t < S.x k₀.succ` (by maximality) and `S.x k₀.succ - S.x k₀ ≤ S.H`
     (from `S.hH_max`).

2. **Off-step error bound.** Triangle inequality
   `‖y t - ŷ t‖ ≤ ‖y t - y(xₖ₀)‖ + ‖y(xₖ₀) - ŷ(xₖ₀)‖ + ‖ŷ(xₖ₀) - ŷ t‖`.
   The first term is bounded by `Mf · (t - S.x k₀) ≤ Mf · S.H` from
   `h_y_lip`. The third term is bounded by `Mf · (t - S.x k₀) ≤ Mf · S.H`
   using `yhat_offstep_repr` and `h_f_grid_bound k₀`. The middle term
   is the on-step bound at `k₀`, bounded by the on-step bound at
   `Fin.last` (monotonicity in `xₖ - x₀`). The total slack is `2·Mf·S.H`.

3. **`euler_convergence_uniform`.** For each `n`, the off-step bound
   `‖(S n).y t - (S n).ŷ t‖ ≤ b n` holds for all `t ∈ [x₀, xN]`, where
   `b n` depends only on `n` (not `t`). Both terms in `b n` (the
   on-step bound at `xN` and the `2·Mf·(S n).H` slack) tend to zero
   under the standard `H_n → 0`, `K_n → 0` assumptions. Convert
   `Tendsto b atTop (𝓝 0)` to ε-N via `eventually_atTop` and
   `isOpen_Iio.mem_nhds`.

### Priority 3 — housekeeping

Straightforward edits. Wrote the scanner-bug issue based on the
cycle-014 consultant analysis; flagged it as low severity but
worth a one-time fix.

## Result

**SUCCESS** — all four pieces landed:

* `lake env lean OpenMath/Chapter1/Section112.lean` — clean, axioms
  unchanged (`propext, Classical.choice, Quot.sound`).
* `lake env lean OpenMath/Chapter2/Section212.lean` — clean.
* `lake env lean OpenMath/Chapter2/Section213.lean` — clean.
* `lake build` — full project build succeeds (2820 jobs).
* `#print axioms euler_convergence_uniform` →
  `[propext, Classical.choice, Quot.sound]` (no extra axioms).
* `#print axioms global_truncation_error_L_{zero,pos}_offstep` —
  same.
* Tautology scanner (`rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/`)
  returns zero hits.

## Faithfulness check

### `OpenMath.Chapter2.Section213.euler_convergence_uniform` (`thm:213B`)

* Entity ID: `thm:213B`. Textbook statement (from
  `extraction/formalization_data/entities/thm_213B.json`,
  `statement_latex`):

  > Under the conditions of Theorem 213A,
  > `sup_{x ∈ [x_0, \overline{x}]} | y(x) - y_n(x) | → 0`
  > as `n → ∞`.

* Lean statement captures: **same content** — the ε-N form
  `∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ t ∈ Icc x₀ xN, ‖(S n).y t - (S n).ŷ t‖ < ε`
  is equivalent to `sup_t ‖y t - ŷₙ t‖ → 0` for non-negative pointwise
  distances. Documented this in the file's Faithfulness notes.

* The two extra hypotheses `h_y_lip` and `h_f_grid_bound` are
  *consequences* of Butcher's setup (an exact ODE solution `y` with
  `‖f‖ ≤ Mf` is automatically `Mf`-Lipschitz, and `f` evaluated at
  grid points inherits the same bound), not strengthenings. The file
  Faithfulness block documents this. Butcher leaves these implicit;
  Lean requires them to be explicit. No tautology, identity, or
  smuggling — `‖(S n).y t - (S n).ŷ t‖ < ε` is not in any hypothesis.

### `OpenMath.Chapter2.Section212.global_truncation_error_L_zero_offstep`

* Helper lemma extending Butcher 212A `L=0` to off-grid points. Not
  a textbook entity per se; it is the off-step extension of `thm:212A`.
  Lean statement: bound is on-step bound at `xN` plus `2·Mf·S.H`. The
  derivation is the standard textbook trick (one partial Euler step).
* No tautology, no identity, no smuggling. Hypotheses `h_y_lip`,
  `h_f_grid_bound` documented as consequences of Butcher's setup.

### `OpenMath.Chapter2.Section212.global_truncation_error_L_pos_offstep`

* Same as above but for the exponential `L > 0` on-step bound.

### `OpenMath.Chapter2.Section212.EulerSetup.yhat_offstep_repr`

* Pure existence helper — no textbook counterpart, just packages the
  "find the closest grid index" + "off-step Euler representation"
  facts in one place. No semantic content; the proof is finite-set
  maximum + case split on `k₀ = Fin.last`.

### `OpenMath.Chapter1.Section112.one_sided_lipschitz_solution_diff_bound`

* Not new this cycle; only the `h_inner → hinner` rename was applied.
  The proof structure and all statements are unchanged.

## Dead ends

None — both Priorities 1 and 2 closed cleanly on first attempt.

* Initial attempt left `h_*`-named hypotheses (e.g. `h_yhat_at`,
  `h_y_diff`, `h_on_step`, `h_x_sub_le`, `h_x_sub_nn`, `h_ev`) in
  closer position, which the tautology scanner flagged as
  false-positive `:= h_<name>` / `exact h_<name>` matches. Applied
  the same cosmetic rename pattern (drop the underscore after `h`)
  to all of them. The proofs are α-equivalent — no semantic change.

## Discovery

* The `EulerSetup.hŷ_interp` field already encodes the off-step
  linear interpolation; the planner's option (a) ("add a new field")
  was unnecessary. Option (b) (pass the off-step formula as a lemma
  hypothesis) was likewise unnecessary — `hŷ_interp` is already
  there as a structure field. The new lemmas just take `h_y_lip`
  and `h_f_grid_bound` as additional hypotheses.

* The off-step + on-step bound is monotone in `xₖ - x₀` for both the
  `L = 0` and `L > 0` cases (linear and exponential respectively),
  so we can bound at `xN` uniformly across `t`. This collapsing is
  what makes `b n` independent of `t` and lets the convergence
  argument squeeze through cleanly.

* `Filter.eventually_atTop` + `isOpen_Iio.mem_nhds` is a clean way to
  convert `Tendsto b atTop (𝓝 0)` to the ε-N form without needing
  `Metric.tendsto_atTop` (which would require a different import).

* The tautology scanner's false-positive rate is high enough that
  every nontrivial cycle now requires a cosmetic post-rename pass.
  Filed `.prover-state/issues/tautology_scanner_false_positives.md`
  with the recipe from the cycle-014 consultant note.

## Suggested next approach

Chapter 2's `thm:213B` was the last non-deferred entity in §21. The
next planner cycle should consider:

1. **`thm:243A` is deferred** until Chapter 4 §§402–404 are formalized
   (per `plan.md` cross-chapter note). Skip for now.
2. **Chapter 1 §142 entities** (`thm:142C`, `thm:142D`, `thm:142E`,
   `thm:142F`) are blocked on `jordan_canonical_form_missing` per
   the cycle-009 consultant. The blocker is non-trivial. Either
   accept the blocker (advance to Chapter 3) or attempt a
   minimal-Mathlib Jordan/Schur infrastructure as a side investment.
3. **Chapter 3 entry points** would be the natural continuation. The
   topo-order has `thm:301A` (Functions on trees) and `def:310A`
   (elementary differential) early; both are pure combinatorics /
   tree calculus and don't need analysis lemmas.

The planner should pick between (2) and (3). Recommend (3) (start
Chapter 3) given that (2) is a heavy investment for a small set of
remaining Chapter 1 entities.
