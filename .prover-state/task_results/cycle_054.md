# Cycle 054 Results

## Worked on

`globalError_recurrence_form` slack-removal refactor (Step A) and
`stable_consistent_isConvergent_autonomous` declaration (Step B), both in
`OpenMath/Chapter4/Section404.lean`. Target: `thm:406D`.

## Approach

### Step A — slack removal (REQUIRED, completed)

Applied the five planned edits to drop the trailing `+ 1` slack on the
constant `a` inside `globalError_recurrence_form` so that
`a = (Θ + (Θ+1)·Cbase·h·k + 1) · y'sum` (now scales linearly with
`y'sum`, which is essential for cycle 055's squeeze argument).

* **A1 (line 2153):** `a := (...) * y'sum + 1`  →  `a := (...) * y'sum`.
* **A2 (`ha_nn`):** simplified to a one-line `mul_nonneg`.
* **A3 (`hu0`):** rewrote as a `calc` chain
  `|yex x₀ - Y 0| ≤ y'sum = 1 * y'sum ≤ (factor) * y'sum`, no `+ 1`
  slack needed.
* **A4 (`h_Θy_le_a`):** dropped `+ 1` on RHS; the existing `nlinarith`
  call still closes.
* **A5 (`h_a_expand` / `h_a_target`):** dropped trailing `+ y'sum + 1`,
  recomputed the algebraic identity to `Θ·y'sum + (Θ+1)·Cbase·h·k·y'sum
  + y'sum`. The remaining `+ y'sum` slack absorbs the off-by-one in the
  inequality `Θ·y'sum + (Θ+1)·Cbase·h·k·y'sum ≤ a` (this was already
  the form planned in the strategy).

The single consumer `globalError_closed_form_autonomous` (line ~2548)
needed no modification — it just destructures `⟨a, b, c, …⟩`.

### Step B — autonomous Tendsto theorem (STRETCH, declared with sorry)

Stated `LinearMultistepMethod.stable_consistent_isConvergent_autonomous`
just before the existing non-autonomous scaffold. The signature mirrors
the proof skeleton in the planner's strategy: autonomous
`f : ℝ → ℝ`, Lipschitz hypothesis, `f∘yex` bounded, starting values
converging to `y₀`, and the final
`Tendsto (fun m => Y m m - yex x) atTop (𝓝 0)` conclusion.

Body is `sorry` with a docstring describing the five-phase squeeze
proof skeleton (set `h_m := (x-x₀)/m`; bound the closed-form pieces
using cycle 049's `starting_error_sum_tendsto_zero`, exponential
boundedness, and `squeeze_zero`).

### Verification

* `lake env lean OpenMath/Chapter4/Section404.lean` — clean compile
  (3 pre-existing unused-variable warnings + 2 expected `sorry`
  warnings on lines 2620 and 2660).
* `lake build OpenMath.Chapter4.Section404` — build successful (8029
  jobs).
* `#print axioms LinearMultistepMethod.globalError_closed_form_autonomous`
  → `[propext, Classical.choice, Quot.sound]`. Axiom-clean.
* Sorry count: 2 (the line-2620 autonomous Tendsto target, and the
  line-2660 non-autonomous scaffold). Step A removed no sorrys; Step B
  added one.

## Result

SUCCESS — Step A landed cleanly and the closed-form theorem remains
axiom-clean. Step B declared the autonomous Tendsto theorem; closure is
the cycle 055 target as planned.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

* **`stable_consistent_isConvergent_autonomous` (NEW, body = `sorry`)**
  * Entity ID: `thm:406D`. Textbook statement (quoted from
    `extraction/formalization_data/entities/thm_406D.json`):
    > "A stable consistent linear multistep method is convergent."
  * Lean statement captures: **weaker** (autonomous `f : ℝ → ℝ` only,
    not the full non-autonomous `f : ℝ → ℝ → ℝ` of `IsConvergent`).
  * Justification for divergence: the cycle 045–052 helper chain is
    autonomous-only by construction (each lemma takes `f : ℝ → ℝ`).
    Generalising to non-autonomous `f` is multi-cycle infrastructure
    work; the autonomous theorem is the analytical core and a faithful
    subset that requires no axioms beyond Mathlib's. The non-autonomous
    bridge target stays as `stable_consistent_isConvergent` (sorry, on
    line 2660) for cycle 056+.
  * **TAUTOLOGY check:** conclusion is
    `Filter.Tendsto (fun m => Y m m - yex x) Filter.atTop (nhds 0)`,
    not any hypothesis. ✓
  * **IDENTITY check:** body is currently `sorry`; cycle 055 will close
    via a substantive squeeze argument composing five separate analytical
    facts. Not vacuous. ✓
  * **HYPOTHESIS STRENGTH:** the autonomous restriction is documented in
    the docstring; the `hsmall` requirement of
    `globalError_closed_form_autonomous` becomes "eventually true as
    h_m → 0" inside the proof — no extra hypothesis on the user.

* **`globalError_recurrence_form` (refactored, NOT new):** signature
  unchanged; only the internal definition of the constant `a` was
  tightened (slack removed). No faithfulness divergence.

* **`globalError_closed_form_autonomous` (unchanged consumer):**
  no modification. Still axiom-clean.

* **`stable_consistent_isConvergent` (existing scaffold):** still
  `sorry`. The docstring was updated to reflect that the autonomous
  Tendsto form now exists at line 2620 and that cycle 056+ takes the
  non-autonomous bridge.

No definition smuggling, no Prop-field smuggling, no extra hypotheses
beyond what the textbook proof requires.

## Dead ends

None this cycle — the planner's edit list was precise and the slack
removal landed on the first attempt. Step B is intentionally left as a
sorry-with-docstring because the squeeze argument is multi-helper work
better factored across cycle 055 rather than crammed in here.

## Discovery

* The `nlinarith` inside `h_Θy_le_a` (line 2240–2242) survives the slack
  removal without modification: dropping `+ 1` on the RHS just removes a
  redundant constant term that `nlinarith` was happy to absorb either
  way. No other proof tactics needed updating; the slack was truly
  unused everywhere except `h_a_expand`.
* The `lake env lean <file>` workflow reads the source fresh but does
  NOT update `.lake/build/lib/lean/.../*.olean`. To make `#print axioms`
  via `import` see new theorems, a `lake build` is still required.
* Stale-olean caveat: cycle 053 added `globalError_closed_form_autonomous`
  but did not run `lake build`, so importing it from a scratch file
  threw "Unknown constant" until `lake build` ran in this cycle. Future
  cycles that introduce new theorems and want to verify with `#print
  axioms` should `lake build OpenMath.Chapter4.Section404` once before
  that verification.

## Suggested next approach

Cycle 055 should close `stable_consistent_isConvergent_autonomous`. The
docstring lays out the five-phase plan; the concrete subgoals are:

1. **`v_a_tendsto_zero`** (helper): `a_m → 0`. Compose cycle 049's
   `starting_error_sum_tendsto_zero` with continuity of
   `(Θ + (Θ+1)·Cbase·h·k + 1)` at `h = 0`. (The cycle 054 slack
   removal makes this a multiplicative `(bounded factor) · (→ 0)`
   product, hence → 0.)
2. **`v_b_bounded`** (helper): `b_m` is bounded, hence
   `exp(b_m · k · m · h_m) = exp(b_m · k · (x - x₀))` is bounded.
3. **`v_c_h_tendsto_zero`** (helper): `c_m · h_m / (b_m · k) → 0`.
   Bounded × (→ 0).
4. **Squeeze**: combine via `Filter.Tendsto.add`, `Filter.Tendsto.mul`,
   `squeeze_zero`.
5. **Eventual `hsmall`**: `h_m · L · |M.β 0| < 1` eventually, since
   `h_m → 0`. Use `Filter.eventually_atTop` and
   `tendsto_const_div_atTop_nhds_zero_nat`.

If cycle 055 succeeds in closing the autonomous form, cycle 056 should
begin generalising the cycle 045–052 helper chain (currently
autonomous-only) to non-autonomous `f : ℝ → ℝ → ℝ`. The candidate
strategy: replicate each helper with `f` taking `(x, y)`, treating
the explicit-x dependence symmetrically with the y-dependence (both
contribute to the truncation error and Lipschitz bound).

The line-2660 `stable_consistent_isConvergent` scaffold is the eventual
target; do not delete it. Its docstring was updated this cycle to
point at the autonomous form as the analytical core.
