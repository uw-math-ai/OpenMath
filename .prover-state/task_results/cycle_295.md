# Cycle 295 Results

## Worked on
§342 (342g) — Branch B fired (Aristotle 16% progress, healthy):
* `butcherShiftedLegendre_three_roots` — three distinct roots of `P_3^*`
  in `(0, 1)` via IVT (B.2 deliverable).
* `butcherShiftedLegendre_eval_half_eq_zero_of_odd` — reusable parity
  helper, `Odd n → P_n^*(1/2) = 0` (B.3 stretch deliverable).

## Approach

### Priority 0 — Aristotle poll
Polled project `5939f28b-c890-4b7f-be4f-ed0f31f0d0b5` exactly once at
the start of the cycle (per CLAUDE.md). Status: `IN_PROGRESS`,
`percent_complete = 16`, `last_updated_at = 2026-05-15T22:41:20Z`.
Growth from cycle 294's `QUEUED` (0%) ⇒ **Branch B fires** (healthy
progress, leave running, ship `n = 3` anchor).

### Branch B.2 — `butcherShiftedLegendre_three_roots` (IVT)
Strategy (per cycle 294 task results "Branch B" guidance):

1. **Middle root via parity.** `(342c)` instantiated at `x = 1/2` gives
   `P_3^*(1 - 1/2) = (-1)^3 · P_3^*(1/2)`, i.e.
   `P_3^*(1/2) = - P_3^*(1/2)`, so `2 · P_3^*(1/2) = 0` ⇒
   `P_3^*(1/2) = 0`. Proof: `butcherShiftedLegendre_eval_one_sub 3 (1/2)`
   + `rw show (1 : ℝ) - 1/2 = 1/2` + `(-1)^3 = -1` + `linarith`.
2. **Left root via IVT on `[0, 1/5]`.** Using cycle 273's
   `butcherShiftedLegendre_three` closed form
   `P_3^* = 20X³ - 30X² + 12X - 1`:
   - `P_3^*(0) = -1` (direct `simp` + `norm_num`).
   - `P_3^*(1/5) = 9/25 > 0` (direct `simp` + `norm_num`).
   - Continuity from `Polynomial.continuous` (Mathlib).
   - `intermediate_value_Ioo (0 ≤ 1/5) (Continuous.continuousOn …)`
     applied at `0 ∈ Ioo (-1) (9/25)` ⇒ `∃ x₁ ∈ Ioo 0 (1/5), P_3^*(x₁) = 0`.
3. **Right root via IVT on `[4/5, 1]`.**
   - `P_3^*(4/5) = -9/25 < 0` (direct `simp` + `norm_num`).
   - `P_3^*(1) = 1` (direct `simp` + `norm_num`).
   - Same IVT call with `0 ∈ Ioo (-9/25) 1`.
4. **Distinctness via interval disjointness.** `x₁ < 1/5 < 1/2 < 4/5 < x₃`
   gives all three pairwise inequalities by `linarith`.

### Branch B.3 — `butcherShiftedLegendre_eval_half_eq_zero_of_odd`
The midpoint-root argument used in (1) above generalises verbatim to
all odd `n` via `Odd.neg_one_pow`. Shipped as a 5-line reusable
helper so future odd-`n` anchors (e.g. `n = 5, 7, 9`) get the middle
root automatically.

## Result
SUCCESS — both theorems compile cleanly and are axiom-clean.

* `lake env lean OpenMath/Chapter3/Section342.lean` exits 0 (warnings
  only — all pre-existing from cycles 281+, none from cycle 295).
* `lake build OpenMath.Chapter3.Section342` succeeds (2795 jobs).
* `#print axioms butcherShiftedLegendre_three_roots`
  → `[propext, Classical.choice, Quot.sound]` (Mathlib-standard).
* `#print axioms butcherShiftedLegendre_eval_half_eq_zero_of_odd`
  → `[propext, Classical.choice, Quot.sound]`.
* 0 sorries.
* `Section342.lean`: 3641 → 3754 LOC (113 LOC added).

The Aristotle project `5939f28b-…` remains running; per strategy, no
second poll this cycle.

## Faithfulness check

### `butcherShiftedLegendre_three_roots`
This is an **empirical anchor** for `lem:342A` clause (342g) at `n = 3`,
not a new entity. Per cycle 295 strategy hard constraints, no
`lean_status.json` / `plan.md` row for `lem:342A` is touched on
Branch B/C.1 (only Branch A closes the entity).

Textbook statement (from
`extraction/formalization_data/entities/lem_342A.json`, clause 342g):

> P_n* has n distinct real zeros in the interval (0, 1),
> n = 0, 1, 2, … .

At `n = 3`: "P_3* has 3 distinct real zeros in (0, 1)". The Lean
statement captures exactly this in the existential form already used
by cycle 294's `butcherShiftedLegendre_two_roots` (for `n = 2`):

```
∃ x₁ x₂ x₃ : ℝ,
  x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃ ∧
  x_i ∈ Set.Ioo (0:ℝ) 1 ∧ ... ∧
  (butcherShiftedLegendre 3).eval x_i = 0 ∧ ...
```

Lean statement captures: **same content** as the `n = 3` instance of
(342g), in the existential anchor form consistent with cycle-294's
`butcherShiftedLegendre_two_roots`. The full (342g) for general `n`
remains pending Aristotle return or manual Branch C.2 closure (out
of scope for cycle 295).

### `butcherShiftedLegendre_eval_half_eq_zero_of_odd`
Reusable helper, not a textbook entity. Direct corollary of (342c).
No `lean_status.json` row applies.

Lean statement captures: a **strictly weaker** specialisation of
(342c) (it asserts only the `x = 1/2` value for odd `n`), serving as a
proof-engineering shortcut for the midpoint-root step of any
future odd-`n` anchor. The full (342c) is already closed at cycle 272
(`butcherShiftedLegendre_eval_one_sub`), so this is a derived
specialisation, not a re-statement.

### Spot-checks (per Pre-Commit Faithfulness Checklist)
* **TAUTOLOGY**: neither theorem conclusion equals any hypothesis verbatim.
  `butcherShiftedLegendre_three_roots` is closed (no hypotheses);
  `butcherShiftedLegendre_eval_half_eq_zero_of_odd` has hypothesis
  `Odd n` and concludes `P_n^*(1/2) = 0` — distinct.
* **IDENTITY**: neither proof is a single `exact h`. Both do real
  arithmetic via `simp` + `norm_num` + `linarith` + `intermediate_value_Ioo`.
* **DEFINITION SMUGGLING**: no new `def`/`structure`/`class` introduced
  this cycle.
* **HYPOTHESIS STRENGTH**: `butcherShiftedLegendre_three_roots` has no
  hypotheses (matches the textbook's `n = 3` instance of (342g)).
  `butcherShiftedLegendre_eval_half_eq_zero_of_odd` requires `Odd n`,
  which is essential — the conclusion would be false at `n = 0` (since
  `P_0^* = 1`, so `P_0^*(1/2) = 1 ≠ 0`) and at `n = 2` (since
  `P_2^*(1/2) ≠ 0` for the symmetric quadratic with roots
  `(3 ± √3)/6`).

## Dead ends
None this cycle — the `simp [Polynomial.eval_*]` + `norm_num` recipe
hit the four evaluation points (`x = 0, 1/5, 4/5, 1`) on the first
try, IVT instantiation was a one-shot, and distinctness via `linarith`
on the disjoint intervals closed without iteration.

## Discovery

1. **`intermediate_value_Ioo` is in scope already.**
   `Mathlib.Topology.Algebra.Polynomial` (imported at line 6) pulls in
   `Mathlib.Topology.Order.IntermediateValue` transitively. No new
   import needed.
2. **`Polynomial.continuous` produces the lambda-form continuity
   statement.**
   `(p : Polynomial ℝ).continuous : Continuous fun x => p.eval x`,
   which matches Mathlib's IVT signature exactly. No
   `Continuous.comp` plumbing required.
3. **`Odd.neg_one_pow` is the textbook key.** The Mathlib lemma
   `Odd.neg_one_pow : Odd n → (-1)^n = -1` collapses the odd-`n`
   sign factor in (342c) cleanly. Future cycles' odd-`n` anchors
   (`n = 5, 7, 9, …`) can use `butcherShiftedLegendre_eval_half_eq_zero_of_odd`
   directly to obtain the middle root in one line.

## Suggested next approach
The next planner cycle (296) should:

1. **Poll Aristotle `5939f28b-…` once at start.** Cycle 295's reading
   was `IN_PROGRESS` at 16% as of 2026-05-15T22:41:20Z. If cycle 296's
   poll shows ≥ 30% (steady ~+15% per ~30-min window since
   submission), continue Branch B (no resubmit).

2. **If Aristotle returns COMPLETE in cycle 296**: extract, integrate,
   and close `lem:342A` per cycle 295 strategy Branch A (the big win).

3. **If Aristotle stays IN_PROGRESS with growth**: ship another
   empirical anchor. Natural next target is `butcherShiftedLegendre_five_roots`
   using the new `butcherShiftedLegendre_eval_half_eq_zero_of_odd`
   helper plus IVT on four asymmetric sub-intervals. (`P_5^*` has
   one root at `1/2` and four others by parity-pairs of IVT zones.)
   Will require a `butcherShiftedLegendre_five` closed-form rung first
   (~60 LOC) plus four `simp [eval_*] + norm_num` interior evaluations
   plus IVT (~120 LOC total).

4. **If Aristotle stalls (no growth)**: cycle 295 was observation #1 of
   the three-stall protocol. Cycle 296 poll showing 16% still ⇒
   observation #2. Cycle 297 poll showing 16% still ⇒ observation #3,
   fire Branch C.2 (cancel and open
   `lem_342A_g_zeros_manual_closure_plan.md`).

5. **§342 (342g) auxiliary**: a "card_roots_eq_n at small `n`"
   corollary combining `butcherShiftedLegendre_card_roots_le n`
   with the explicit `n`-element root witnesses (cycle 293's
   `butcherShiftedLegendre_one_root` + cycle 294's
   `_two_roots` + cycle 295's `_three_roots`) would give
   `(P_n^*).roots.toFinset.card = n` at `n ∈ {0, 1, 2, 3}`. Low
   priority — it does not advance closure of the general (342g)
   statement, but tightens the empirical base.
