# Cycle 057 Results

## Worked on
Three new outer-assembly Tendsto helpers for `thm:406D`
(`LinearMultistepMethod.stable_consistent_isConvergent`,
`OpenMath/Chapter4/Section404.lean:2956`):

- **P1.1** `m_h_constancy` (line 2159): pure-algebra fact
  `m · ((x − x₀)/m) = x − x₀` for `m > 0`. Substitution prerequisite
  for the squeeze.
- **P1.2** `c_h_h_squared_tendsto_zero` (line 2171): lifts
  `c_tendsto_at_zero` (cycle 056) through `· * h^2` via `Tendsto.mul`
  with `tendsto_h_squared_zero` (cycle 056). The product tends to
  `c∞ · 0 = 0`.
- **P2** `a_m_tendsto_zero` (line 2202): the parametric Tendsto
  fact about the `a` constant produced by
  `globalError_recurrence_form`. Threads `Cbase_tendsto_at_zero`
  through `const_mul (Θ + 1) → mul tendsto_id → mul_const k → const_add Θ → add_const 1`
  to get `bracket(h) → Θ + 1`, then combines with
  `yPrime_sum_abs_tendsto_zero` via `Tendsto.mul`. Limit:
  `(Θ + 1) · 0 = 0`.

In parallel, submitted an Aristotle batch of 5 generic Tendsto
combinators (Priority 3) that the cycle-058 squeeze will consume:

- `tendsto_id_squared_zero`        (project `aa899fc5-…`)
- `tendsto_const_mul_h_zero`       (project `bc1d3a46-…`)
- `tendsto_real_exp_lift`          (project `ed2246ea-…`)
- `tendsto_exp_sub_one_at_zero_aux` (project `e5ad3830-…`)
- `tendsto_div_at_pos`             (project `6b913333-…`)

## Approach
- **P1.1**: `field_simp` after `(m : ℝ) ≠ 0` from `hm.ne'` via `exact_mod_cast`.
- **P1.2**: `Tendsto.mul` of `c_tendsto_at_zero` with `tendsto_h_squared_zero`,
  then `simpa` to flatten `c∞ · 0 = 0`.
- **P2**: chained `Tendsto` combinators on `Cbase_tendsto_at_zero`
  to build `bracket(h) → Θ + 1`, then `Tendsto.mul` with
  `yPrime_sum_abs_tendsto_zero` to get the final `(Θ + 1) · 0 = 0`.
  The `simpa` flattens both the constant fold and the Lean-level
  `id` from `Filter.tendsto_id`.
- **Aristotle batch**: each helper is a small generic Tendsto fact
  (no LMM data, no `yPrime`, no `IsStable`). Submitted as standalone
  `.lean` files importing only `Mathlib`. Templates per cycle 055.

## Result
**SUCCESS — all three manual helpers compile.**

`lake env lean OpenMath/Chapter4/Section404.lean` reports only
warnings (three pre-existing unused-variable warnings) and the
expected single `sorry` at line 2960 (the `stable_consistent_isConvergent`
body, untouched this cycle).

Aristotle batch results (single check after 30 min):
- `tendsto_id_squared_zero` — **CLOSED**.
  Proof: `simpa using hf.mul (Filter.tendsto_id.pow 2)`.
- `tendsto_const_mul_h_zero` — **CLOSED**.
  Proof: `simpa using hf.mul Filter.tendsto_id`.
- `tendsto_real_exp_lift` — **CLOSED**.
  Proof: `exact (Real.continuous_exp.tendsto c).comp hg`.
- `tendsto_exp_sub_one_at_zero_aux` — **CLOSED**.
  Proof:
  `simpa using Filter.Tendsto.sub_const (Filter.Tendsto.comp (Real.continuous_exp.tendsto _) hp) 1`.
- `tendsto_div_at_pos` — **CLOSED**.
  Proof: `simpa using hf.div hg hc.ne'`.

All five are in
`.prover-state/aristotle_submissions/cycle_057/result_*/*.lean`.
Per strategy, integration into `Section404.lean` is **deferred to cycle 058**
(where they will be consumed by the `globalError_outer_squeeze`).

## Faithfulness check
The three new declarations are infrastructure `private lemma`s, not
Butcher-named entities — no `formalization_data/entities/<id>.json`
exists. Faithfulness obligations from CLAUDE.md §"Pre-Commit
Faithfulness Checklist" reduce to:

- **No new `def`/`structure`/`class`** introduced. All three are
  `private lemma`s.
- **Tautology check**: none of P1.1, P1.2, P2 has its conclusion
  appearing verbatim as a hypothesis. P1.1 is an algebraic
  identity. P1.2 and P2 are Tendsto combinator chains whose
  conclusion `Tendsto … (nhds 0)` is not present in any hypothesis.
- **Identity check**: no proof is `:= h_*` or `:= id`. All three
  use combinator chains plus `simpa`.
- **Hypothesis-strength check**: P2 takes the minimal
  `hu : ∀ j, Tendsto (fun h => u h j) (nhds 0) (nhds 0)` premise
  (the same shape `yPrime_sum_abs_tendsto_zero` consumes). No
  `M.IsStable` / `M.IsConsistent` / `M.IsPreconsistent` hypotheses
  appear anywhere.
- **Definition-smuggling check**: N/A (no new structures).

Tautology scanner
(`rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/`):
two pre-existing hits in `Section404.lean` (lines 1950, 2595), both
from prior cycles and not from cycle-057 deliverables. Zero new
hits introduced.

## Dead ends
None encountered this cycle. The strategy's Plan-A approach
(combinator chain + `simpa`) closed all three lemmas on the first
build attempt. No fall-back to `convert ... using 1; ring` or
`mul_div_cancel_left₀` was needed.

## Discovery
- The `bracket(h) = Θ + (Θ + 1) · Cbase(h) · h · k + 1` chain decomposes cleanly as
  `hCbase.const_mul (Θ + 1) |>.mul Filter.tendsto_id |>.mul_const (k : ℝ) |>.const_add Θ |>.add_const 1`.
  This 5-combinator pattern is the canonical way to fold a constant-Tendsto
  through `· const → · h → · const → const + · → · + const`. Reusable for the
  cycle-058 squeeze, where similar `·_h · h · const` shapes recur.
- `simpa` handles all the `Cbase∞ · 0` and `(Θ + 1) · 0` reductions
  on the limit side without requiring an explicit `convert` or `ring`.
- The `open OpenMath.Chapter1.Section141 in` qualifier on `a_m_tendsto_zero`
  matches the convention from `yPrime_sum_abs_tendsto_zero` (line 1872)
  — keeping the `open` local rather than file-wide avoids name
  pollution in unrelated lemmas.

## Suggested next approach
Cycle 058 should attempt the actual `globalError_outer_squeeze` —
the central squeeze lemma whose conclusion is the
`Tendsto (fun h => |yex(x) - y_n h|) (nhds 0) (nhds 0)` shape that
`IsConvergent` consumes. Inputs already in place:

- Cycle 053 `globalError_closed_form_autonomous` (line ~2829) —
  the autonomous closed-form bound.
- Cycles 054–055 `globalError_eq_linRec` and
  `globalError_recurrence_form` — the existential-threading lemmas.
- Cycle 056 `b_tendsto_at_zero`, `c_tendsto_at_zero` (lines 2114,
  2138) — the Tendsto facts about the linear-recurrence
  coefficients.
- Cycle 057 P1.1 `m_h_constancy` — substitution adapter.
- Cycle 057 P1.2 `c_h_h_squared_tendsto_zero` — `c · h^2 → 0`.
- Cycle 057 P2 `a_m_tendsto_zero` — `a · y'sum → 0`.
- Cycle 057 Aristotle batch — generic combinators
  (`tendsto_id_squared_zero`, `tendsto_const_mul_h_zero`,
  `tendsto_real_exp_lift`, `tendsto_exp_sub_one_at_zero_aux`,
  `tendsto_div_at_pos`), assuming Aristotle closes them.

Cycle 058's missing pieces: (a) the autonomous → non-autonomous
lift of `globalError_closed_form_autonomous` (a separate
medium-size refactor; likely warrants its own cycle plus an issue
file), and (b) the squeeze itself, weaving the seven Tendsto
helpers together. Recommend the planner sequence cycle 058 as
"autonomous → non-autonomous lift" and cycle 059 as "squeeze
assembly", with cycle-058's deliverable being the lift lemma
`globalError_closed_form_nonautonomous` and an updated strategy
file pointing at the squeeze.

If the planner prefers to skip the autonomous → non-autonomous
lift (e.g. by routing the squeeze through the autonomous form and
specialising the textbook statement), that is also viable but
requires either a new entity ID or a documented relaxation in the
faithfulness section of `thm:406D`.
