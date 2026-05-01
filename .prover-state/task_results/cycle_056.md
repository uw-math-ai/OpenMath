# Cycle 056 Results

## Worked on

Outer-assembly Tendsto helpers for `thm:406D`
(`LinearMultistepMethod.stable_consistent_isConvergent`):

* **Priority 1 (mandatory)** — integrated the 5 closed-proof helpers
  from cycle 055's Aristotle batch
  (`.prover-state/aristotle_results/cycle_055/`):
  1. `Dbase_tendsto_at_zero` — re-parameterised from
     `α β : Fin (k+1) → ℝ` to `M : LinearMultistepMethod k`,
     using the long-form `set N := …` template from the existing
     `Cbase_tendsto_at_zero` (the original Aristotle one-liner
     `convert Filter.Tendsto.div … using 2 <;> norm_num` is fragile
     across the parameter rewrite, and the strategy explicitly
     authorises the long-form fallback).
  2. `tendsto_const_div_one_sub_mul` — replaced the suspicious
     `le_trans (… .div …) (by norm_num)` with the recommended
     `Tendsto.div tendsto_const_nhds h_denom (by norm_num)` plus
     a `simpa` to reduce `c / 1 = c`.
  3. `tendsto_h_squared_zero` — copied verbatim.
  4. `tendsto_finset_sum_abs_zero` — copied verbatim.
  5. `tendsto_real_exp_at` — copied verbatim.

* **Priority 2** — built `b_tendsto_at_zero` (the `b = (Θ+1)·Cbase + 1`
  multiplier from the linear-recurrence form) and `c_tendsto_at_zero`
  (the `c = (Θ+1)·Dbase` quadratic coefficient) as direct
  `.const_mul` / `.add_const` lifts of `Cbase_tendsto_at_zero` and
  `Dbase_tendsto_at_zero`.

All seven helpers are placed as a contiguous "§406D outer-assembly
Tendsto helpers" cluster in `OpenMath/Chapter4/Section404.lean`,
inserted at lines 2010–2150 between the existing
`Cbase_tendsto_at_zero` (line 1982) and `recentSum_swap_bound`.

* **Priority 3 (stretch)** — skipped. Cycle stayed within scope to
  preserve the small-blast-radius edit profile the planner asked for.
* **Aristotle batch this cycle** — skipped per the planner's
  "optional, only if Priority 1+2 finish in under 30 min and there is
  bandwidth" guidance. Cycle 057 will plan its own batch.

## Approach

1. Re-parameterisation. The Aristotle-submitted
   `Dbase_tendsto_at_zero` uses generic `α β : Fin (k+1) → ℝ`
   parameters because the submission file was an isolated stub.
   For consistency with `Cbase_tendsto_at_zero` (which already takes
   `M : LinearMultistepMethod k`), the integrated version uses
   `M.α i.succ` and `M.β i` directly. Substituting the
   long-form `set N := …` proof template makes the proof robust to
   how Lean elaborates `((i.val + 1 : ℕ) : ℝ)` casts.
2. `tendsto_const_div_one_sub_mul` — Aristotle's `le_trans` chain
   could not close a `Filter.Tendsto` goal (it needs a `≤` ordering,
   not a topological convergence). Replaced with a clean
   `Tendsto.div` of `tendsto_const_nhds` over the affine denominator,
   reducing `c / 1` to `c` via `simpa`.
3. `b_tendsto_at_zero` — chained `.const_mul (Θ + 1)` then
   `.add_const 1` on top of `Cbase_tendsto_at_zero M L`. `simpa` reduces
   the unfolded RHS to the named target.
4. `c_tendsto_at_zero` — single `.const_mul (Θ + 1)` lift of
   `Dbase_tendsto_at_zero M L M_bound`.

## Result

**SUCCESS** — all 7 new helpers compile cleanly; `lake build` is green.

* `lake env lean OpenMath/Chapter4/Section404.lean` — passes
  (only pre-existing unused-variable warnings on lines 568, 627, 1204,
  and the tracked `sorry` at line 2878).
* `lake build OpenMath.Chapter4.Section404` — succeeds (8029 jobs).
* **Sorry count**: 1 → 1 (unchanged; the line-2878 stub for
  `stable_consistent_isConvergent` is the same theorem the planner
  said NOT to touch — it shifted from line 2739 to line 2878 due to
  ~140 lines of new helpers added before it).
* **Tautology-scanner check**: the regex flags two pre-existing
  patterns (line 1950 in cycle-055's `yPrime_sum_abs_tendsto_zero`,
  and line 2517 in cycle-053's `globalError_recurrence_form`).
  Neither was introduced this cycle, and they sit inside `have`
  blocks, not as theorem closers — both are within compound
  `by` blocks where they are legitimately consuming intermediate
  hypotheses. None of the 7 cycle-056 helpers contain a
  closing `:= h_<name>`, `exact h_<name>` at end of line, or `:= id`
  pattern. The cycle-056 deliverable does NOT introduce any new
  tautology-scanner regressions.

## Faithfulness check

None of the new helpers are top-level Butcher entities — they are
private analytic infrastructure toward `thm:406D`. All seven sit
in the `OpenMath.Chapter4.Section404` namespace as `private lemma`s
and exist purely to bootstrap the outer-assembly squeeze argument
for `LinearMultistepMethod.stable_consistent_isConvergent`.

For each new helper:

* `Dbase_tendsto_at_zero` — analytic helper (no Butcher entity).
  Mirrors the shape of `globalError_recurrence_form`'s `Dbase`
  (line 2266 of the file), so it is faithful to the very
  recurrence form whose convergence we are trying to establish.
  Lean statement captures: matches the `Dbase` shape verbatim.
* `tendsto_const_div_one_sub_mul` — generic Mathlib-style helper,
  no Butcher counterpart.
* `tendsto_h_squared_zero` — generic Mathlib-style helper.
* `tendsto_finset_sum_abs_zero` — generic Mathlib-style helper.
* `tendsto_real_exp_at` — generic Mathlib-style helper, just
  re-states `Real.continuous_exp.tendsto c`.
* `b_tendsto_at_zero` — analytic helper for the `b` constant in
  `globalError_recurrence_form` (line 2292). Lean statement
  captures: same content as `Cbase_tendsto_at_zero` lifted by
  `· * (Θ + 1) + 1`.
* `c_tendsto_at_zero` — analytic helper for the `c` constant
  (line 2293). Same as `Dbase_tendsto_at_zero` lifted by
  `· * (Θ + 1)`.

No `def`s introduced this cycle. No new `class`/`structure`s.
No new top-level theorems with Butcher IDs. Hypothesis-strength
audit: each helper's hypotheses are exactly the parameters needed
to define the function under `Tendsto`; no extras.

## Dead ends

* The original Aristotle proof of `tendsto_const_div_one_sub_mul`
  used `le_trans (… .div …) (by norm_num)`, which is type-incorrect
  for a `Filter.Tendsto` goal. The planner had already flagged this
  as suspicious; the recommended replacement worked first try.
* For `Dbase_tendsto_at_zero` I tried briefly to keep the original
  `convert … using 2 <;> norm_num` Aristotle one-liner with the
  re-parameterised `M.α i.succ` / `M.β i.succ` shapes, but did not
  invest in tuning it — fell back immediately to the long-form
  `set N := …` template since it was a known-good pattern from
  `Cbase_tendsto_at_zero`. No diagnostic transcript captured here;
  the long-form path was so cheap it wasn't worth iterating on
  the one-liner.

## Discovery

* `Tendsto.add_const` exists and works exactly as named —
  `(hf : Tendsto f l (nhds a)) → Tendsto (fun x => f x + c) l (nhds (a + c))`.
  No need for `.add tendsto_const_nhds`.
* `Tendsto.const_mul` likewise works in the natural direction:
  `(hf : Tendsto f l (nhds a)) (c : ℝ) → Tendsto (fun x => c * f x) l (nhds (c * a))`.
* The pattern `simpa using hX` is the right closer for these
  combinator-stack lifts — it absorbs the algebraic simplification
  of `0 * L * |β 0| = 0` and `c / 1 = c` that would otherwise
  require an explicit `convert`.
* The cycle-055 Aristotle batch is *highly* reusable — 4 of the 5
  proofs went in verbatim, only `Dbase_tendsto_at_zero` needed
  re-parameterisation. The Aristotle batch is the single biggest
  efficiency win of the past 5 cycles.

## Suggested next approach

Cycle 057 should target the next layer of helpers needed for the
outer squeeze of `stable_consistent_isConvergent` (line 2878 stub).
Candidate batch (suitable for an Aristotle submission, since the
analytic content is concrete):

1. **`m_h_constancy`** — for `h_m := (x − x₀)/m` and `m > 0`,
   show `(m : ℝ) · h_m = x − x₀`. Pure `field_simp` / `linarith`.
2. **`exp_b_k_m_h_bounded`** — `Real.exp(b_h · k · m · h_m)` is
   eventually bounded uniformly in `m` for `h` near 0, given that
   `b_h → b∞` (Priority 2 deliverable of cycle 056) and
   `m · h_m = x − x₀` is constant.
3. **`a_m_tendsto_zero`** — combines cycle-055
   `yPrime_sum_abs_tendsto_zero` with cycle-055 / cycle-056
   `Cbase_tendsto_at_zero` to show `a_m → 0` along `h → 0`.
4. **`c_h_h_squared_tendsto_zero`** — the cycle-056 stretch goal
   (Priority 3, skipped this cycle); should fall out of
   `c_tendsto_at_zero` ⊗ `tendsto_h_squared_zero` via `Tendsto.mul`.
5. **`globalError_outer_squeeze`** — combine the above into the
   actual squeeze: for any sequence `h_m ↘ 0` with `m · h_m` constant,
   `|yex(x) − Y_m m| → 0`.

The cycle-058 cycle should then attempt the actual closure of the
`stable_consistent_isConvergent` `sorry`, threading the squeeze
through the `IsConvergent` predicate's Mathlib `Filter.Tendsto`
encoding (likely an `(at_top : Filter ℕ).comap …` or analogous shape;
verify against `IsConvergent`'s definition first).
