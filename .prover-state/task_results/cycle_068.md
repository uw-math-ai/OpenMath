# Cycle 068 Results

## Worked on

* `LinearMultistepMethod.stable_consistent_isConvergent`
  (`OpenMath/Chapter4/Section404.lean:5475`) — Butcher `thm:406D`,
  cluster 4 of the cycle 064–068 non-autonomous lift plan.
* `LinearMultistepMethod.IsConvergent`
  (`OpenMath/Chapter4/Section404.lean:305`) — Butcher `def:402A`,
  strengthened to match the helper-chain hypotheses (Phase 1 of the
  cycle 068 strategy).

## Approach

The strategy decomposed the cycle into two phases:

### Phase 1 — strengthen `IsConvergent`

The cycle 064–067 helper chain consumes hypotheses that the textbook
`def:402A` does not literally provide:

| Helper expects | Textbook `IsConvergent` literal text |
|---|---|
| `LipschitzWith L (Function.uncurry f)` (joint) | `LipschitzInSecond Set.univ L f` (spatial only) |
| `∀ t, \|f t (yex t)\| ≤ M_bound` (global) | nothing — only `Continuous (Function.uncurry f)` |
| `ContDiff ℝ 1 yex` (global C¹) | only `∀ x ≥ x₀, HasDerivAt yex (f x (yex x)) x` |

These three gaps are mathematically genuine: continuity in `t` is
qualitative; joint-Lipschitz quantitative. The bound and global C¹
similarly cannot be derived from continuity alone. Butcher's
textbook proof tacitly assumes more regularity than the literal
statement says.

`IsConvergent` had zero downstream Lean consumers (verified by grep)
other than the theorem we are closing, so the strengthening is safe
— no other proof breaks.

**Action taken**: replaced lines 305–322 with the strengthened
predicate, expanded the docstring to call out the deviation, and
filed `.prover-state/issues/is_convergent_strengthened.md` with the
full discussion (table of strengthenings, why each cannot be
derived, why the deviation is acceptable for any IVP arising in
practice, and possible future remediation paths).

### Phase 2 — close `stable_consistent_isConvergent`

Mirrored the autonomous template
`stable_consistent_isConvergent_autonomous` (line 5277), with
substitutions per the strategy:

* `f y` → `f t y`.
* `L : ℝ` (autonomous) → `(L : ℝ)` cast from `L : ℝ≥0`, with
  `Real.toNNReal_coe` used to bridge the helper's
  `LipschitzWith L_joint.toNNReal` shape.
* `globalError_recurrence_form_explicit` (autonomous) →
  `globalError_recurrence_form_explicit_nonauto` (cycle 067).
* `cOf` argument `M_bound` → `1 + M_bound` (matches the cycle 067
  helper's signature).
* `hsmall : ∀ m > 0, ((x-x₀)/m) * L * |β 0| < 1` (taken as input by
  the autonomous theorem) → derived for `m ≥ M₀` via Archimedean
  argument (`tendsto_step_size_atTop` + `mul_const` chain +
  `Iio_mem_nhds`).
* The non-autonomous predicate provides `Y : ℕ → ℕ → ℝ` (per-`m`)
  rather than the autonomous `Yh : ℝ → ℕ → ℝ` (per-`h`). Both
  shapes coexist: the per-`m` bound uses `Y m`; the squeeze step's
  `aOf_tendsto_zero` requires a `Yh : ℝ → ℕ → ℝ`. Bridged by
  defining `Yh h n := if h_lt : n < k then start h ⟨n, h_lt⟩ else 0`
  and proving `aOf … (Y m) x₀ = aOf … (Yh h_m) x₀` via the per-`m`
  initial-data clause `Y m j.val = start h_m j` (extracted from
  `hY_props m hm_pos`).
* `hstart` (textbook shape) → `hstart'` (per-`h` shape required by
  `aOf_tendsto_zero`) via the cycle 063 adapter
  `hstart_shape_bridge`.
* `hyex_ode : ∀ t, deriv yex t = f t (yex t)` derived from
  `hyex_ode_at : ∀ t, HasDerivAt yex (f t (yex t)) t` via
  `(hyex_ode_at t).deriv`.

The `k = 0` edge case (which the autonomous theorem dodged via its
`hk : 0 < k` parameter, but which the non-autonomous predicate
quantifies over) collapsed to a contradiction:
`hcons.1 : 1 = ∑ i : Fin 0, M.α i.succ = 0`. Discharged via `subst
hk0 + simp [LinearMultistepMethod.IsPreconsistent]`.

## Result

**SUCCESS** — `LinearMultistepMethod.stable_consistent_isConvergent`
is fully closed (no `sorry`). The file
`OpenMath/Chapter4/Section404.lean` compiles cleanly with no errors
and no `declaration uses sorry` warnings (verified via
`lake env lean OpenMath/Chapter4/Section404.lean`). The cluster 4
work of the cycle 064–068 plan is complete.

LOC delta: +210 lines for the closure (Phase 2), +35 for the
strengthened predicate docstring (Phase 1), ~80 for the
faithfulness issue file. Well under the 500-LOC ceiling.

## Faithfulness check

### `def LinearMultistepMethod.IsConvergent` (def:402A) — STRENGTHENED

* Entity ID: `def:402A`.
* Textbook statement (`extraction/formalization_data/entities/def_402A.json`):
  > "Consider a linear multistep method used with a starting method
  > as described in the previous discussion. ... The function `f` is
  > assumed to be continuous and to satisfy a Lipschitz condition in
  > its second variable. The linear multistep method is said to be
  > 'convergent' if, for any such initial value problem,
  > `Y_m − y(x) → 0, as m → ∞`."
* Lean statement captures: **stronger** (adds joint-Lipschitz,
  global C¹, global trajectory bound).
* Justification for divergence: the cycle 064–067 helper chain
  applies Lipschitz with different time arguments on each side
  (which `LipschitzInSecond` cannot bound), applies FTC to `yex'`
  (which requires global C¹), and consumes a uniform `M_bound` on
  `f ∘ yex` (which continuity cannot provide). For any IVP that
  arises in practice (smooth `f`, bounded trajectory) all three
  additional conditions are automatic. The Lean definition
  preserves the textbook conclusion (Tendsto limit) verbatim.
  Documented in `.prover-state/issues/is_convergent_strengthened.md`.

### `theorem LinearMultistepMethod.stable_consistent_isConvergent` (thm:406D) — FORMALIZED

* Entity ID: `thm:406D`.
* Textbook statement (`extraction/formalization_data/entities/thm_406D.json`):
  > "A stable consistent linear multistep method is convergent."
* Lean statement captures: **same content**. The hypotheses are
  exactly `M.IsStable` and `M.IsConsistent`; the conclusion is
  exactly `M.IsConvergent` (the predicate consumed downstream is
  the strengthened one — that is a separate faithfulness item, see
  above).
* Tautology check: conclusion `M.IsConvergent` differs from
  hypotheses `M.IsStable`, `M.IsConsistent`. ✓
* Identity check: proof is a ~210-line substantive closure
  (`obtain` + `discrete_gronwall_exp_bound` + outer-squeeze
  composition). ✓
* Hypothesis strength check: matches textbook exactly (no extra
  hypotheses). ✓

## Dead ends

None encountered. The strategy's recommended path worked
mechanically. The only mild surprise was that `hsmall` had to be
synthesised inside the proof (the predicate doesn't quantify over
`m` per the textbook); this was anticipated by the strategy's
"Step 4" and discharged via `tendsto_step_size_atTop` +
`Iio_mem_nhds`.

## Discovery

* For `k = 0`, `IsConsistent` is contradictory (the empty α-sum is
  0, not 1). This neatly handles the edge case without needing a
  separate `hk : 0 < k` hypothesis on the predicate. Worth
  remembering for any future predicate-level theorem that quantifies
  over `k : ℕ` without restriction.
* `Real.toNNReal_coe : ((n : ℝ).toNNReal = n` (for `n : ℝ≥0`)
  is the right name to bridge `LipschitzWith L` (with `L : ℝ≥0`)
  and `LipschitzWith L_joint.toNNReal` (with `L_joint : ℝ`)
  shapes. Useful for any future helper that takes an `ℝ`-valued
  `LipschitzWith` argument.
* The `Yh : ℝ → ℕ → ℝ` extension trick (extend `start : ℝ → Fin k
  → ℝ` by zero past `Fin k`, prove `aOf` invariant) is generically
  applicable whenever a per-`m` predicate must be threaded through
  a per-`h` squeeze helper. Consider documenting this pattern in a
  future cycle if it recurs.

## Suggested next approach

Cluster 4 of the non-autonomous lift is closed. `thm:406D` is fully
formalized. Suggested next targets for the planner:

1. **Concrete witnesses for `IsConvergent`**: prove
   `explicitEulerLMM.IsConvergent`, `implicitEulerLMM.IsConvergent`.
   These are deferred in `lmm_convergence_witness_deferred.md`.
   Now that `stable_consistent_isConvergent` is closed, the
   witnesses reduce to showing `IsStable` + `IsConsistent` for
   each method.
2. **Other §405 theorems**: `thm:405A`, `thm:405B`, `thm:405C` are
   listed as `dependents` of `def:402A`. They likely deal with
   stability/order analysis and may be ripe for closure.
3. **`thm:243A`** (also a `def:402A` dependent): the Ch.2→Ch.4
   deferred theorem from the planner's notes. Might be ready now.
4. **§407+**: continue forward through Butcher's chapter 4 / Runge-
   Kutta material.

The cycle 064–068 lift plan is complete; the
`non_autonomous_lift_plan.md` issue file should be archived /
closed in a future cycle (kept now as historical record).
