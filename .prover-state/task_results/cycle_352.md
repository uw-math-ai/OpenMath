# Cycle 352 Results

## Worked on

§404 / §422 trapezoidal-rule wire-up — three new public declarations
shipped per the cycle 352 strategy P1 + P2 (P3 deferred):

1. `OpenMath.Chapter4.Section404.trapezoidalLMM` (1-step LMM, `α 0 = -1,
   α 1 = 1, β 0 = 1/2, β 1 = 1/2`).
2. `OpenMath.Chapter4.Section404.trapezoidalLMM_isPreconsistent` /
   `_satisfiesEq404b` / `_isConsistent` — three structural witnesses.
3. `OpenMath.Chapter4.Section422.trapezoidalLMM_hasOrderAtLeast_two`
   — order-2 verification at `j ∈ {0, 1, 2}`.
4. `OpenMath.Chapter4.Section422.trapezoidalLMM_coef_β_eq_half_sum_i_sq_alpha`
   — one-line instantiation of cycle 351's
   `coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two` at the
   trapezoidal rule.

P3 (BDF3 wire-up in `Section451.lean`) was **deferred**: P1 + P2 took
~50 min on warm caches due to back-to-back full Chapter4 rebuilds
after each edit (the first `lake env lean` invocation does not
update the `.olean`, so Section422 picked up the *old* Section404
on its first attempt — fixed by switching to `lake build`).

## Approach

**P1.** Followed the strategy template verbatim. The only surprise:
`trapezoidalLMM` needed `noncomputable` (Real division on `1/2`
contributes `Real.instDivInvMonoid`); fixed in v2. Both
`_isPreconsistent` and `_satisfiesEq404b` close via plain `simp` —
no `norm_num`/`ring` fallback needed despite the rational
coefficient.

**P2.a.** `trapezoidalLMM_hasOrderAtLeast_two` follows cycle 351's
`bdf2LMM_hasOrderAtLeast_two` recipe (`intro j hj; interval_cases j;
show C M j = 0; simp [..., trapezoidalLMM, Nat.factorial]`).
Notable deviation from the strategy template: `simp` closes each
case **outright** (no `norm_num` fallback needed), and the
`Fin.sum_univ_one` / `Fin.sum_univ_two` hints were rejected by the
linter as unused (because `simp` already unfolds the LMM coefficients
to a closed form via the `if-then-else` branch, exposing only `Fin 2`
sums which `Finset.sum_univ` handles natively). Final form drops
those hints.

**P2.b.** One-liner per strategy template — `coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two`
applied to `trapezoidalLMM` + `trapezoidalLMM_hasOrderAtLeast_two`.

**Verification.** `lake build OpenMath.Chapter4.Section404` →
`lake build OpenMath.Chapter4.Section422` → `#print axioms` confirms
all three new public theorems depend on `[propext, Classical.choice,
Quot.sound]` only.

## Result

SUCCESS. All three new public theorems compile axiom-clean. The
`trapezoidalLMM_coef_β_eq_half_sum_i_sq_alpha` exhibits the cycle
351 identity at the first **non-trivial** value (`1/2 = 1/2`),
unlike BDF2 which trivializes to `0 = 0`.

## Faithfulness check

### `trapezoidalLMM`

Entity ID: none (standard implicit method; not a Butcher entity).
Textbook anchor: the trapezoidal rule (Crank–Nicolson) is a
universally-attested implicit 1-step method
`y_n - y_{n-1} = (h/2) · (f(x_n, y_n) + f(x_{n-1}, y_{n-1}))`.

Per the §404 normalisation `α 0 = -1`, this gives
`α 0 = -1, α 1 = 1, β 0 = β 1 = 1/2`, matching the Lean definition.

> *Lean definition captures*: **same content** as the textbook
> trapezoidal rule.
> *Non-vacuity*: `_isPreconsistent` (`1 = 1`) + `_isConsistent`
> (`1 = 1/2 + 1/2`) shipped in same cycle.

### `trapezoidalLMM_isPreconsistent` / `_satisfiesEq404b` / `_isConsistent`

Numerical witnesses of definitional content (Section404 lines
146–163 template for Euler methods).

> *Lean statement captures*: **same content** as the textbook
> claim "trapezoidal rule is consistent".

* Tautology check: PASS — neither conclusion equals a hypothesis.
* Identity check: PASS — `simp` does real arithmetic (`1/2 + 1/2 = 1`),
  not a hypothesis re-export.

### `trapezoidalLMM_hasOrderAtLeast_two`

Numerical statement (no textbook entity ID; textbook claim that the
trapezoidal rule is order 2 is standard). Verified by direct
computation: `C trapezoidalLMM j = 0` for `j ∈ {0, 1, 2}`.

> *Lean statement captures*: **same content** as the textbook
> numerical claim "trapezoidal rule has order 2".

* Tautology / identity / strength / absent-theorem checks: PASS.

### `trapezoidalLMM_coef_β_eq_half_sum_i_sq_alpha`

One-line specialisation of cycle 351's
`coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two`.

> *Lean statement captures*: **same content** as the cycle 351
> identity at the trapezoidal rule. Both sides evaluate to `1/2`,
> providing the first **non-zero** witness (BDF2 was `0 = 0`).

* Identity check: proof is `:= coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two
  trapezoidalLMM trapezoidalLMM_hasOrderAtLeast_two` — a specialisation
  application, not a hypothesis re-export. The mathematical work is in
  the cycle 351 theorem; this is a non-vacuity instantiation. PASS.

## Dead ends

**v1 attempt: `def trapezoidalLMM`** (without `noncomputable`) hit
`error(lean.dependsOnNoncomputable)` at the definition site because
`1/2 : ℝ` uses `Real.instDivInvMonoid`. (BDF2 already used
`noncomputable def`, but explicit/implicit Euler — which use only
`-1, 0, 1` — do not.) Added `noncomputable` keyword; resolved.

**v1 P2 attempt: `simp ... ; norm_num`** produced
`error: No goals to be solved` on all three `interval_cases` branches
— `simp` already closes the goal with the unfolded `C` and `trapezoidalLMM`
definitions. Removed trailing `norm_num`; also dropped
`Fin.sum_univ_one, Fin.sum_univ_two` from the simp set (flagged
unused by the linter, since `simp` handles these via `Finset.sum_univ`
of the auto-unfolded if-then-else). Final form: each branch is
just `simp [Section410.C, trapezoidalLMM (, Nat.factorial)]`.

## Discovery

* `simp` on a *single* `if-then-else` LMM (k = 1) already closes
  `C M j = 0` goals without needing explicit `Fin.sum_univ_*`
  hints. This may simplify future small-k LMM order witnesses
  (cycle 351's BDF2 case needed `Fin.sum_univ_two, Fin.sum_univ_three`
  because BDF2 uses `![…]` vector notation; trapezoidal uses
  `fun i => if i = 0 then … else …`, which `simp` unfolds further).
* `lake env lean <file>` does *not* update `.olean`. Must use
  `lake build <Module>` between edits to a file and consumer-file
  builds. This is the reason cycle 352 wasted ~25 min on a stale
  Section404 olean.

## Suggested next approach

Per the strategy footer's cycle 353+ outlook:

1. **`bdf3LMM` wire-up** (~40 LOC, single cycle): ship `bdf3LMM` +
   `_isPreconsistent` + `_isConsistent` + `_hasOrderAtLeast_3` in
   `Section451.lean`. Provides a third-order witness for future
   `def:422B` Phase E work. **Lowest-risk option** — extends the
   small-cycle ship cadence.
2. **`trapezoidalLMM_isStable`** (~50 LOC, at-boundary case;
   substantive): the trapezoidal `ρ(z) = z - 1` has a single simple
   root at `z = 1` on the unit-circle boundary, so the cycle 346
   `bdf2LMM_isStable` recipe (interior roots) won't port directly.
   May need a new lemma path. Substantive but higher risk.
3. **Phase D′.2.2 Step 2 scoping** (Markdown doc; multi-cycle plan):
   prepare a dedicated scoping doc for the `ρ''(1)` bridge to
   `0 ≤ Σᵢ i²·αᵢ` under stable + preconsistent + order ≥ 2. Useful
   *only* once a single-cycle decomposition is in hand.

**Recommend (1)** — BDF3 ship matches cycle 352's small-cycle bar
and supplies the Phase E order-3 witness that's currently absent
from the LMM witness surface (currently capped at order 2 via
BDF2 + trapezoidal).
