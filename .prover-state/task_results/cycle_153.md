# Cycle 153 Results

## Worked on

**Priority 1 — def:530B Path A Step 3** (primary, single-cycle target):
* `HasOrderRelativeTo_explicit` predicate added to
  `OpenMath/Chapter5/Section530.lean`.
* `explicitEulerGLM_hasOrderZero_trivialStarting` — axiom-clean `p = 0`
  non-vacuity witness for explicit Euler GLM × `trivialStartingMethod`
  under `LipschitzWith L f`, `HasDerivAt yex (f y₀) x₀`, `yex x₀ = y₀`.

**Aristotle housekeeping**: single-polled project
`2c4630b2-2998-4d4a-af88-c2f83fbd9eda` (general-`n` thm:550A). Status:
**CANCELED at 21%** as of 2026-05-06T03:04 UTC. Per strategy §
"FAILED / CANCELLED / errored", left §550 alone; no replacement
Aristotle job submitted.

**Priority 2 (bookkeeping)**: updated `plan.md` (def:530B `[ ]` → `[~]`),
`extraction/formalization_data/lean_status.json` (lean_symbol →
`HasOrderRelativeTo_explicit`, cycle: 153, expanded notes), and
`.prover-state/issues/def_530B_scaffold_strategy.md` with a "Cycle 153
update — Path A Step 3 complete" sub-section mirroring the cycle-152
update format.

## Approach

### Aristotle poll (one call only, per strategy)

Called `mcp__aristotle__get_status 2c4630b2-...`; returned
`status: CANCELED, percent_complete: 21`. Did not poll again or submit
new jobs.

### Predicate `HasOrderRelativeTo_explicit`

Quantified `∀ i : Fin r` over the Lipschitz-/derivative-free statement

```
(fun h : ℝ => SM[i] h - ES[i] h) =O[nhds 0] (fun h => h ^ (p+1))
```

with `SM = applyStartingThenStep_explicit`, `ES =
applyExactThenStarting_explicit` (cycle-152 operators). Imports added:
`Mathlib.Analysis.Asymptotics.Defs`,
`Mathlib.Analysis.Calculus.Deriv.Basic`,
`Mathlib.Topology.MetricSpace.Lipschitz`.

The predicate does NOT bake in `S.IsNonDegenerate`; consumers compose
it at the use site. The strategy's docstring on this design choice was
followed verbatim.

### `p = 0` non-vacuity witness — proof structure

Five-step decomposition of the strategy's Step 3d sketch:

1. **`hSM` closed form** — reduce SM[0] to
   `(y₀ + h·f y₀) + h·f(y₀ + h·f y₀)` via `show` (to canonicalize the
   eta-expanded `applyStartingThenStep_explicit` body), then
   `rw [trivialStartingMethod_applyExplicit]` (reuses cycle 152), then
   `unfold` the GLM-side `explicitStageValue` (recursive `def`, not a
   simp lemma — `rw` failed; `unfold` and one round of
   `simp [explicitEulerGLM, Matrix.mulVec, dotProduct]` plus `ring`
   closes it).

2. **`hES` closed form** — direct one-line reuse of cycle 152's
   `trivialStartingMethod_applyExactThenStarting_explicit`.

3. **`hcongr` + `change`** — `change` to rewrite the goal into the
   canonical `0 : Fin 1` index form (`fin_cases i` produced
   `(fun i => i) ⟨0, ⋯⟩` which blocks `rw [hcongr]`); then `funext h`
   + `rw [hSM, hES]; ring` produces the `T1 + T2` shape.

4. **T1 = O(h)** — `hasDerivAt_iff_isLittleO_nhds_zero.mp hyex_deriv`
   gives `(fun h => yex(x₀+h) - yex x₀ - h • f y₀) =o[nhds 0] (fun h
   => h)`. Rewrite via `hyex_x₀` and `simpa [smul_eq_mul]` to clear
   `yex x₀ = y₀` and `smul = mul`. Negate via `.neg_left` (matching
   the goal's sign convention `(y₀ + h·f y₀) - yex(x₀+h)`), then
   `.isBigO` to promote.

5. **T2 = O(h)** via `IsBigO.of_bound (↑L)`:
   * Continuity of `a(h) := y₀ + h·f y₀` and `b(h) := yex(x₀+h)` at
     `h = 0` with `a(0) = b(0) = y₀` gives `(a − b) → 0`. Used
     `(continuous_const.add continuous_id).continuousAt` for the
     `x₀ + h` inner map (the strategy's recommended `continuity` tac
     produced `aesop` failures inside `ContinuousAt.comp`); composed
     with `hyex_deriv.continuousAt` via explicit `simpa`-driven
     rewriting of `(x₀ + 0)` to `x₀`.
   * `Metric.tendsto_nhds.mp` + `Real.dist_0_eq_abs` extracts the
     eventual `|a − b| < 1` bound.
   * Inside `filter_upwards`: `LipschitzWith.dist_le_mul` +
     `Real.dist_eq` gives `|f a − f b| ≤ L · |a − b|`; the final
     `calc` chain shows
     `|h · (f a − f b)| ≤ |h| · (L · |a − b|) ≤ |h| · (L · 1) = L · |h|`.

6. **Combine** — `hT1.add hT2`, with `simp` collapsing
   `h ^ (0 + 1)` to `h` via a separate `hpow` rewrite.

### Bookkeeping (Priority 2)

Updated `plan.md` def:530B entry `[ ]` → `[~]` with a Cycle 153 paragraph
documenting Path A Step 3 completion, T1+T2 decomposition technique,
file LOC delta (573 → 776), and the partial-status rationale (Path B
implicit variant deferred).

Updated `extraction/formalization_data/lean_status.json` def:530B row:
`lean_symbol` advanced from `applyExactThenStarting_explicit` →
`HasOrderRelativeTo_explicit` (the predicate is the cycle-153
deliverable), added `"cycle": 153`, expanded notes to summarize the
Path A Step 3 work + IVP hypotheses signature.

Updated `.prover-state/issues/def_530B_scaffold_strategy.md` with a
"Cycle 153 update — Path A Step 3 complete" sub-section: predicate
type signature, witness proof outline, verification commands, notes
for cycle 154+ (p=1 stretch via ContDiff 2 + Taylor; Path B implicit
branch still pending).

## Result

**SUCCESS — score 2 outcome.**

* `lake env lean OpenMath/Chapter5/Section530.lean` exits 0 (~5 s).
* `lake build OpenMath.Chapter5.Section530` succeeds (3.8 s build,
  total 2772 jobs cached).
* `grep -c sorry OpenMath/Chapter5/Section530.lean` → `0`.
* `lean_verify
  OpenMath.Chapter5.Section530.explicitEulerGLM_hasOrderZero_trivialStarting`
  → `[propext, Classical.choice, Quot.sound]` only — axiom-clean.
* Aristotle housekeeping handled (CANCELED branch); no new submissions.
* All three bookkeeping files (plan.md, lean_status.json, scaffold
  strategy) updated.
* Commit message will summarize Path A Step 3 alongside the §550
  CANCELED outcome.

LOC delta: 573 → 776 (+203). Slightly above the strategy's 50–80 LOC
estimate, dominated by the `hSM` closed-form reduction (which required
explicit `show` canonicalization due to eta-expansion of
`applyStartingThenStep_explicit`'s body) and the T2 `calc` chain plus
its supporting continuity lemmas.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `HasOrderRelativeTo_explicit` (def:530B)

* Entity ID: `def:530B`.
  Textbook statement (quoted from `entities/def_530B.json`):
  > Consider a general linear method M and a non-degenerate starting
  > method S. The method M has order p relative to S if the results
  > found from SM and ES agree to within O(h^{p+1}).
* Lean statement captures: **same content** for the explicit-method
  branch, with two scoped restrictions documented in the docstring:
  1. Both `M` and every `S_i` are required to be explicit (so that
     SM/ES use the cycle-152 explicit operators rather than the
     implicit fixed-point operators, which remain unformalized).
  2. The `f, yex, x₀, y₀` IVP data is exposed as parameters rather
     than being existentially absorbed; this is a faithful mechanism
     for "results from SM and ES agree to within O(h^{p+1})": the
     textbook statement applies to the data of the IVP that defines
     `SM(y₀, h)` and `ES(y₀, h)`, so making it explicit is necessary.
  3. The non-degeneracy of `S` is NOT baked into the predicate
     (per strategy §"Do NOT strengthen ..."); consumers add it at
     the use site. Documented in the predicate's docstring.
* The predicate is captured via `Asymptotics.IsBigO`, which is the
  standard formalization of the textbook's `O(h^{p+1})` notation in
  Mathlib.

### `explicitEulerGLM_hasOrderZero_trivialStarting`

* Not a textbook entity; a Lean-internal non-vacuity witness for
  `HasOrderRelativeTo_explicit`. The textbook does not state this
  specific lemma — it is the per-CLAUDE.md "every new predicate be
  witnessed" mandate.
* Lean statement captures: a substantive (not vacuous) instance of
  `HasOrderRelativeTo_explicit` at `(s, r) = (1, 1), p = 0`, under
  natural IVP regularity hypotheses (Lipschitz `f`, derivable `yex`
  matching `f y₀` at `x₀`, initial value matched).
* Strength of hypotheses: `LipschitzWith L f` is mildly stronger than
  the textbook's implicit "f sufficiently regular" but is the
  standard Mathlib idiom for "f doesn't grow too fast"; required
  here for the T2 bound. `HasDerivAt yex (f y₀) x₀` plus
  `yex x₀ = y₀` together encode "yex is the exact solution at
  initial time x₀", which is the standard IVP setup. None of these
  is stronger than the textbook's de-facto regularity assumptions in
  §530's neighborhood.
* No tautology / definition-smuggling concerns: the proof does
  genuine analytic work (T1 = o(h) via HasDerivAt → IsLittleO; T2 =
  O(h) via Lipschitz + continuity bound). Conclusion is not a
  hypothesis verbatim (`=O[nhds 0] (fun h => h ^ (0+1))` is not
  among `hf_lip`, `hyex_x₀`, `hyex_deriv`).

## Dead ends

1. **`rw [Section510.GeneralLinearMethod.explicitStageValue]`** failed
   with "Failed to rewrite using equation theorems". The recursive
   `def` doesn't reduce via `rw` directly. Fix: use `unfold`, which
   does reduce the WF recursion. Lesson: for noncomputable WF
   recursions, `unfold` is the right tactic, not `rw`.

2. **`fin_cases i` left an unreduced `(fun i => i) ⟨0, ⋯⟩`** in the
   goal after splitting on `i : Fin 1`, which prevented
   `rw [hcongr]` from matching the lambda body of the predicate
   unfolding. Standard tricks `simp only []` (β-reduction) and
   `simp only [Fin.isValue]` did not eliminate the residual lambda.
   Fix: `change` the goal to the explicit application form with
   `0 : Fin 1` literally; `rw [hcongr]` then succeeds.

3. **`(hyex_deriv.continuousAt).comp (by continuity).continuousAt`**
   for the `ContinuousAt (fun h => yex (x₀+h)) 0` lemma failed: the
   inferred outer `ContinuousAt yex (x₀ + 0)` did not unify with
   `ContinuousAt yex x₀`. Fix: rebuild the outer continuity manually
   with `simpa using hyex_deriv.continuousAt` (which definitionally
   reduces `x₀ + 0` to `x₀`).

4. **`continuity` tactic** for the inner `ContinuousAt (fun h => x₀ + h) 0`
   produced an `aesop failed` error nested inside
   `ContinuousAt.comp`. Fix: use the explicit
   `(continuous_const.add continuous_id).continuousAt` instead.

5. **`Real.dist_zero_right`** does not exist; the polymorphic version
   is `dist_zero_right : dist a 0 = ‖a‖`, but the more direct form
   over `ℝ` is `Real.dist_0_eq_abs : dist x 0 = |x|`. Used the
   latter.

## Discovery

1. **`unfold` vs `rw` on noncomputable WF recursions**: even when
   the equation lemma `<recursion>.eq_1` exists, `rw` may fail to
   apply it inside the goal because the body has match-patterns or
   `Fin` index arithmetic that don't trigger the equation. `unfold`
   side-steps this by directly substituting the body. For chapter-5
   recursive definitions like `explicitStageValue`, prefer `unfold`
   over `rw` or `simp only [<def>]` for the first step.

2. **`change` is reliable when `fin_cases` leaves residual lambdas**.
   The pattern is: after `fin_cases i` on a `Fin 1` (or any small
   `Fin n`), if subsequent `rw` fails to match the goal, write
   `change <explicit goal with 0 : Fin 1>` to canonicalize. This is
   a more direct fix than chasing `simp only []`-style β-reductions.

3. **`hasDerivAt_iff_isLittleO_nhds_zero`** is the cleanest entry
   point for "f is differentiable at x₀ with derivative D" → "f(x₀+h)
   = f(x₀) + h·D + o(h) near 0". Avoid going through the `HasFDerivAt`
   layer if you can — the extra unfolding tax for the scalar case is
   not worth it.

4. **`Tendsto.eventually` extraction pattern**: when you need
   `∀ᶠ h in nhds 0, |f h| < ε` from `f → 0`, the cleanest path is
   `Metric.tendsto_nhds.mp f_tendsto ε ε_pos` followed by
   `Real.dist_0_eq_abs` to convert the ball-based formulation to
   absolute-value form. Cleaner than unfolding `Filter.Tendsto`
   manually.

5. **`IsBigO.of_bound`** is the right lemma when you have a concrete
   constant `C` and want to show `f =O[l] g`. Don't try to use the
   polymorphic `Asymptotics.isBigO_iff_…` family — `of_bound` takes
   the constant directly and reduces the goal to
   `∀ᶠ x, ‖f x‖ ≤ C · ‖g x‖`, which is what you actually have.

## Suggested next approach

### Cycle 154 candidates (in priority order)

1. **`p = 1` refinement of the cycle-153 witness** (def:530B Path A
   Step 4): under `ContDiff ℝ 2 yex` + a Lipschitz-on-bounded-set
   condition for `f` (or `ContDiff ℝ 1 f`), promote
   `explicitEulerGLM_hasOrderZero_trivialStarting` from `p = 0` to
   `p = 1`. This matches the textbook classification of explicit
   Euler as order 1 relative to the canonical starting method.
   Estimated +60–100 LOC. Key Mathlib pieces: `taylor_within_apply`
   or `HasDerivAt`-based second-order remainder bounds.

2. **`def:530C` (variants of order)** — currently `[ ]` in plan.md.
   With Path A Step 3 in hand, the def:530C predicate (almost
   certainly a "p-relative-to-some-S" formulation) becomes
   approachable.

3. **Path B (implicit branch) of def:530B** — substantial
   multi-cycle infrastructure (`ContractingWith` / fixed-point
   stage equations). Not recommended as the cycle 154 target unless
   the planner wants to commit to the multi-cycle branch.

### What NOT to attempt next cycle

1. Don't widen the cycle-153 witness to a *different*
   GLM × starting-method pair (e.g. `implicitMidpointGLM` ×
   `mixedStartingMethod`) — the cycle-153 witness already
   demonstrates non-vacuity; new witnesses are bookkeeping rather
   than progress.

2. Don't re-poll Aristotle project `2c4630b2` again — it is
   CANCELED, no further evolution will occur. If the planner wants
   another long-run for thm:550A general-`n`, it should weigh that
   against the two prior failed long-runs (cycle 138 cancelled at
   6%, cycle 148 cancelled at 21%).

3. Don't go after thm:530A or other §530 theorems before def:530C
   lands — the dependency graph hasn't been re-walked since
   def:530B's partial status was upgraded.
