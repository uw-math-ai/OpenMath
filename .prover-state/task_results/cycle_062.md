# Cycle 062 Results

## Worked on

Two new top-level pieces in `OpenMath/Chapter4/Section404.lean`:

1. **Priority 1**: `aOf_tendsto_zero` (cycle-061 missing wrapper) — the
   per-`h` Tendsto fact `aOf M Θ L h yex (Yh h) x₀ → 0` as `h → 0`,
   given that the per-`h` starting-data error converges. This is the
   cycle-060 `aOf` analog of cycle 061's `bOf_tendsto_at_zero`,
   `cOf_tendsto_at_zero`, and `yPrimeSumOf_tendsto_zero`.

2. **Priority 2**: `LinearMultistepMethod.stable_consistent_isConvergent_autonomous`
   — the full autonomous-IVP form of Butcher Theorem 406D. For a stable
   consistent LMM solving `y' = f(y)` with `f` Lipschitz and `f∘yex`
   bounded on the trajectory, the global error tends to zero as the
   step size shrinks.

   This is **not** the textbook `IsConvergent` predicate (which is
   non-autonomous, taking `f : ℝ → ℝ → ℝ`); it is the autonomous
   specialisation, which is the analytical core. The lift to the
   non-autonomous form (`stable_consistent_isConvergent`) remains a
   `sorry` — that is the cycle 063+ deliverable.

   Also added `bOf_limit_pos` (one-line `positivity`-closed helper for
   the squeeze's `0 < bInf` requirement).

## Approach

Followed the cycle 062 strategy verbatim:

- **§B priority 1**: `unfold aOf CbaseOf yPrimeSumOf` then
  `exact a_m_tendsto_zero M Θ L (u := …) hstart` — the §B "fallback"
  (with `CbaseOf` in the `unfold` list) was needed because the
  `Cbase`-style ratio doesn't auto-unfold from `aOf` alone. The
  resulting proof is 5 lines; no `convert` needed.

- **§D priority 2**: full proof following the strategy's 5-step
  skeleton:
  1. extract canonical `Θ` once via `theta_bounded_of_isStable`;
  2. per-`m` closed-form bound via `globalError_recurrence_form_explicit`
     + `discrete_gronwall_exp_bound` (the explicit-`(a, b, c)` form
     threads `Θ` through, so all `m` get the same `Θ`);
  3. step-size collapse `m·h_m → x − x₀` via `m_h_constancy`,
     bridging the LHS `yex(x₀ + m·h_m)` to `yex x`;
  4. squeeze: cycle 059's `globalError_outer_squeeze_a_term` and
     `_c_term`, fed cycle 061's `bOf_tendsto_at_zero` /
     `cOf_tendsto_at_zero` / `aOf_tendsto_zero` (the new cycle 062
     wrapper) and `bOf_limit_pos`;
  5. `squeeze_zero'` to conclude `Tendsto (fun m => |Yh h_m m − yex x|)`
     `→ 0`, then `tendsto_zero_iff_abs_tendsto_zero.mpr` to drop
     the abs.

- **`hstart` shape decision**: per the strategy's §D "design decision
  1" recommendation, used the per-`h` shape `Yh : ℝ → ℕ → ℝ` rather
  than the per-`m` `Y : ℕ → ℕ → ℝ`. This makes the squeeze helpers
  compose directly: `aOf` is naturally a function of `(h, Yh h)`, so
  cycle 062's `aOf_tendsto_zero` plugs straight into
  `globalError_outer_squeeze_a_term`. The per-`m` reformulation
  would require defining a partial inverse `m = ⌈(x−x₀)/h⌉`, which
  the strategy correctly flags as "clumsy and obscures the squeeze".

## Result

**SUCCESS** — both new pieces compile and the autonomous theorem is
fully proved (no internal `sorry`s, no `axiom`s).

The line-3818-or-equivalent `sorry` on the non-autonomous
`stable_consistent_isConvergent` is **intentionally left in place**
per the strategy's §E.1 "do not close" instruction — that is the
cycle 063+ non-autonomous lift target.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `bOf_limit_pos` (private lemma)
- Entity ID: not a Butcher-named entity. Internal scaffolding for
  cycle 062's `globalError_outer_squeeze_c_term` requirement
  `0 < bInf`.
- Lean statement captures: a positivity bound. Reason: the squeeze
  helper needs `bInf > 0` to divide by `bInf · k`. Hypotheses:
  `0 ≤ Θ`, `0 ≤ L`. Conclusion: positivity of the limit value
  (`+ 1` makes it unconditional).
- Tautology check: hypotheses are non-negativities; conclusion is
  positivity of a derived expression. Not the same. ✓
- Identity check: `positivity` (closed by Aristotle batch). Doing
  real work via standard non-negativity reasoning. ✓
- Hypothesis strength: minimal — only the two non-negativities
  required by `positivity`. ✓

### `aOf_tendsto_zero` (private lemma)
- Entity ID: not a Butcher-named entity. Internal scaffolding —
  the cycle-060 `aOf` analog of cycle 061's three `*Of` Tendsto
  wrappers. Closes the cycle-061 deferred deliverable explicitly
  flagged in cycle 061 task results.
- Lean statement captures: per-`h` `aOf → 0` Tendsto fact, requiring
  per-`h` starting-data convergence. Same content as cycle 057's
  `a_m_tendsto_zero` but threaded through cycle 060's `aOf` and
  `yPrimeSumOf` defs.
- Tautology check: hypotheses give per-`j` Tendsto of starting-data
  error; conclusion is Tendsto of the bracket·sum product. Different
  functions. ✓
- Identity check: 5-line proof using `unfold` + `exact`. The
  `exact` is the named-argument-instantiated `a_m_tendsto_zero`,
  not a hypothesis re-export. ✓
- Hypothesis strength: only the per-`j` starting-data Tendsto. ✓

### `LinearMultistepMethod.stable_consistent_isConvergent_autonomous` (theorem)
- Entity ID and textbook statement (`extraction/formalization_data/entities/thm_406D.json`):
  > "A stable consistent linear multistep method is convergent."
- Lean statement captures: **strictly weaker** content than the
  textbook (which is the non-autonomous form). This is the
  autonomous-IVP specialisation: `f : ℝ → ℝ` (no `x`-dependence),
  `Yh : ℝ → ℕ → ℝ` per-`h` iterate (matches autonomous closed-form
  bound), per-`h` starting-data convergence.
- Justification for divergence: the cycle 045–062 helper chain (per
  cycle 053+ task results) is built for autonomous `f : ℝ → ℝ`. The
  full non-autonomous `IsConvergent` predicate requires lifting
  `LipschitzInSecond Set.univ L f` to a per-`x` `LipschitzWith L`
  on the autonomous restriction `fun y => f x y`. That lift, plus
  threading `x`-dependence through the global-error helper chain,
  is the cycle 063+ scope. The autonomous form proves the full
  analytical core; the lift is a Lipschitz-bookkeeping cycle.
- Tautology check: hypotheses are stability, consistency, Lipschitz,
  C¹ smoothness, IVP solution, step-size smallness, LMM iterate,
  per-`h` starting-data Tendsto. Conclusion is `Tendsto (Yh h_m m −
  yex x) atTop (nhds 0)`. None of the hypotheses asserts this
  Tendsto. ✓
- Identity check: ~80-line proof through the squeeze chain — not
  re-exporting any single hypothesis. ✓
- Hypothesis strength check: documented adds beyond the bare textbook:
  - `ContDiff ℝ 1 yex` — implicit in Butcher's "exact solution of
    `y' = f(y)` with `f` Lipschitz" (Picard-Lindelöf gives at least
    C¹). Faithful.
  - `hf_yex_bound` — Butcher's `M = max |f(y)|` over the trajectory.
    Without Picard-Lindelöf existence in the formalisation, this
    must be supplied as a hypothesis. Faithful.
  - `hxx : x₀ < x` — strict inequality so `(x − x₀) > 0` and
    `m_h_constancy hm` applies cleanly. Could weaken to `x₀ ≤ x` at
    the cost of an extra positivity branch; not done since strict
    is the natural Tendsto setting.
  - `hsmall : ∀ m > 0, h_m · L · |β 0| < 1` — required by
    `globalError_recurrence_form_explicit` to control the
    `(1 − h L |β 0|)` denominator in the per-step bound. This is the
    "for `h` sufficiently small" condition Butcher invokes
    informally. Faithful.

### Other introduced facts (none — only the three above)

## Dead ends

None. The proof followed the strategy's §B and §D blueprints
without major detours. Two minor fixes during drafting:

1. The proposed `unfold aOf` (without `CbaseOf yPrimeSumOf`) didn't
   expose the right shape for `a_m_tendsto_zero`. Adding `CbaseOf`
   and `yPrimeSumOf` to the `unfold` list (the strategy's §B
   "fallback") fixed it on first try.

2. The strategy's Step 5 "squeeze + abs juggling" sketch used
   `tendsto_of_tendsto_of_tendsto_of_le_of_le'`, but `squeeze_zero'`
   is more direct (just two args: `0 ≤ f` eventually, `f ≤ g`
   eventually, `g → 0`). Used the latter.

## Discovery

- The cycle 060 explicit-Θ shape (`globalError_recurrence_form_explicit`,
  threading `Θ` as an external parameter) was the right design call:
  it lets the autonomous theorem extract `Θ` once via
  `theta_bounded_of_isStable` and reuse it across all `m`. Without
  this, the cycle 057 / 060 wrappers would have re-derived `Θ` per-`m`,
  giving potentially-different `Θ`s and breaking the squeeze
  (since the squeeze helpers need a fixed limit). The strategy's
  §C job 4 "subtle point" anticipated this; bypassing the cycle 060
  wrapper for the per-`m` bound (and calling
  `globalError_recurrence_form_explicit` directly) was the clean fix.

- `tendsto_zero_iff_abs_tendsto_zero` (`Mathlib.Topology.Algebra.Order.Group`)
  is a clean 1-arg lemma for "Tendsto to zero ↔ |·| Tendsto to zero" in
  ordered groups. Used at the very end to drop abs from the squeezed
  result. Useful pattern for any future Tendsto-to-zero squeeze.

- `squeeze_zero'` (Mathlib.Topology.MetricSpace.Pseudo.Lemmas) is the
  cleanest squeeze helper for "f → 0" given `0 ≤ f ≤ g` eventually
  with `g → 0`. Three args, no order ambiguity.

## Suggested next approach

Cycle 063: lift the autonomous `stable_consistent_isConvergent_autonomous`
to the non-autonomous `stable_consistent_isConvergent` (the
`IsConvergent` predicate with `f : ℝ → ℝ → ℝ`).

The lift requires:
1. **Lipschitz adapter**: for fixed `x`, `LipschitzInSecond Set.univ L f`
   gives `LipschitzWith L (fun y => f x y)`. Mathlib likely has a
   one-liner for this; if not, build it as a helper lemma.
2. **Threading `x`-dependence through the helper chain**: the cycle
   045–052 helpers all bake in `f : ℝ → ℝ`. The straightforward path
   is to introduce a parametrized version `f x_n` at each timestep
   `x_n = x₀ + n·h`. The autonomous bound `globalError_recurrence_form`
   then becomes a per-`n`-`f`-evaluation bound, requiring
   `LipschitzInSecond` to give uniform-in-`x` Lipschitz constant.
3. **Adapting the bound**: `hf_yex_bound : ∀ t, |f t (yex t)| ≤ M_bound`
   replaces the autonomous `∀ t, |f (yex t)| ≤ M_bound`. The cycle
   058 `f_yex_bound` proof should adapt directly since it only uses
   the bound at `(t, yex t)` points.
4. **Per-`h` start as before**: cycle 062's `Yh : ℝ → ℕ → ℝ` shape
   transfers directly; the autonomous `start h j → y₀` lifts via
   `start := fun h j => Yh h j` (already in shape).

Estimated cost: 200–400 lines, mostly Lipschitz bookkeeping. No
deep new mathematics; the analytical core is all in place.

If the bookkeeping turns out to be load-bearing (e.g.
`LipschitzInSecond` doesn't trivially adapt the cycle 045 contraction),
file a `non_autonomous_lift_blocker.md` issue documenting the
specific gap and propose either (a) a Mathlib helper to build, or
(b) a refactor of the cycle 045–052 chain to take a `LipschitzInSecond`
hypothesis directly.
