# Cycle 296 Results

## Worked on
§342 (342g) — Branch B fired (Aristotle 25%, healthy growth from
cycle 295's 16%):
* `butcherShiftedLegendre_five_roots` — five distinct roots of
  `P_5^*` in `(0, 1)` via parity (middle, `r = 1/2`) + four IVT
  invocations + 10-way `linarith` distinctness.

## Approach

### Priority 0 — Aristotle poll
Polled project `5939f28b-c890-4b7f-be4f-ed0f31f0d0b5` exactly once
at the start of the cycle (per CLAUDE.md single-poll discipline).

* `status`: `IN_PROGRESS`
* `percent_complete`: `25`
* `last_updated_at`: `2026-05-15T23:01:44.766590Z`
* Growth from cycle 295 (16% at `22:41:20Z`): +9 percentage points
  over ≈20 minutes.

Branch decision: **Branch B** (`IN_PROGRESS` with `≥ 25%`). Healthy
growth ⇒ keep Aristotle running; ship `n = 5` anchor as the cycle's
substantive deliverable.

### Branch B — `butcherShiftedLegendre_five_roots` (IVT × 4 + parity)

Strategy mirrors cycle 295's `n = 3` recipe, scaled to five roots:

1. **Middle root via parity (cycle 295 helper)**. Since `Odd 5 = ⟨2, rfl⟩`,
   apply `butcherShiftedLegendre_eval_half_eq_zero_of_odd 5 ⟨2, rfl⟩`
   directly:
   ```lean
   have hf_half : (butcherShiftedLegendre 5).eval (1 / 2 : ℝ) = 0 :=
     butcherShiftedLegendre_eval_half_eq_zero_of_odd 5 ⟨2, rfl⟩
   ```
   One line — exactly the dividend cycle 295's helper was designed
   to pay.

2. **Closed-form evaluations.** Using cycle 278's
   `butcherShiftedLegendre_five` (i.e. `P_5^* = 252X^5 - 630X^4 +
   560X^3 - 210X^2 + 30X - 1`), compute six evaluations via
   `simp [Polynomial.eval_*]; norm_num`:
   - `P_5^*(0) = -1` (no `norm_num` needed).
   - `P_5^*(1) = 1`.
   - `P_5^*(1/10) = 2497/6250`.
   - `P_5^*(1/4) = -23/256`.
   - `P_5^*(3/4) = 23/256` (parity image of `1/4`).
   - `P_5^*(9/10) = -2497/6250` (parity image of `1/10`).

3. **Four IVT invocations.** Two ascending, two descending:
   - `r₁ ∈ Ioo 0 (1/10)`: ascending — `intermediate_value_Ioo`
     applied at `0 ∈ Ioo (-1) (2497/6250)`.
   - `r₂ ∈ Ioo (1/10) (1/4)`: descending (`f(1/10) > 0 > f(1/4)`) —
     `intermediate_value_Ioo'` applied at `0 ∈ Ioo (-23/256) (2497/6250)`.
   - `r₄ ∈ Ioo (3/4) (9/10)`: descending — `intermediate_value_Ioo'`
     applied at `0 ∈ Ioo (-2497/6250) (23/256)`.
   - `r₅ ∈ Ioo (9/10) 1`: ascending — `intermediate_value_Ioo`
     applied at `0 ∈ Ioo (-2497/6250) 1`.

   Used Mathlib's `intermediate_value_Ioo' : Ioo (f b) (f a) ⊆
   f '' Ioo a b` for the descending pair (verified via
   `lean_loogle`). Cycle-294 fallback note about argument order was
   the right call — Mathlib does ship the symmetric variant.

4. **Distinctness (10 pairs).** Disjoint intervals
   `(0, 1/10) < (1/10, 1/4) < {1/2} < (3/4, 9/10) < (9/10, 1)`
   give every pairwise inequality by `obtain ⟨_, _⟩ := hrᵢ_mem; linarith`.

5. **Final assembly.** `refine ⟨r₁, r₂, 1/2, r₄, r₅, …⟩` with five
   witnesses, ten distinctness holes, five Ioo-membership holes,
   and the five evaluation hypotheses inline.

## Result

**SUCCESS**. `OpenMath/Chapter3/Section342.lean` compiles via
`lake build OpenMath.Chapter3.Section342` (full Mathlib rebuild
clean; only pre-existing simp-arg lint warnings). All five anchors
report axiom-clean:

```
butcherShiftedLegendre_one_root        : [propext, Classical.choice, Quot.sound]
butcherShiftedLegendre_two_roots       : [propext, Classical.choice, Quot.sound]
butcherShiftedLegendre_three_roots     : [propext, Classical.choice, Quot.sound]
butcherShiftedLegendre_eval_half_…_odd : [propext, Classical.choice, Quot.sound]
butcherShiftedLegendre_five_roots      : [propext, Classical.choice, Quot.sound]
```

LOC count for the new theorem: 173 lines (within the 200-LOC budget
in the strategy). Zero sorries introduced. No new axioms / constants.

## Faithfulness check

For `butcherShiftedLegendre_five_roots`:

* This theorem is an **empirical anchor**, not the textbook clause.
  The textbook (342g) statement is universal (∀ `n`); the anchor
  asserts the `n = 5` instance.
* No `lem:342A` row update — anchors don't unlock the entity status
  per the strategy.

The cycle 295 helper `butcherShiftedLegendre_eval_half_eq_zero_of_odd`
already underwent its faithfulness check (cycle 295 results): it is
a strict corollary of (342c) applied at `x = 1/2`, not a
restatement.

No new `def`s or `structure`s this cycle.

**Tautology check**: conclusion is a 20-conjunct `∃ … ∧ …`; no
hypothesis matches the conclusion.

**Identity check**: the proof is a 173-line tactic block with five
non-trivial IVT applications — not an identity / re-export.

**Hypothesis strength check**: theorem statement has no hypotheses
beyond the trivial existential. Cannot be weakened.

## Dead ends

None this cycle. The strategy's recipe carried verbatim from the
`n = 3` template at `Section342.lean:3655`; the only adaptation
was selecting `intermediate_value_Ioo'` for the two descending
endpoint pairs (`(1/10, 1/4)` and `(3/4, 9/10)`).

The strategy flagged a fallback (3-root partial witness if `norm_num`
stalled on `2497/6250` arithmetic) but it was not needed — `norm_num`
handled all six evaluations without hesitation.

## Discovery

1. **`intermediate_value_Ioo'` is the right tool for descending IVT.**
   Mathlib's `Mathlib.Topology.Order.IntermediateValue` line 617
   ships it with signature
   `(hab : a ≤ b) → ContinuousOn f (Icc a b) → Ioo (f b) (f a) ⊆ f '' Ioo a b`.
   Note: still needs `a ≤ b` (not `b ≤ a`); only the codomain
   interval flips. Confirmed via `lean_loogle "intermediate_value_Ioo"`.

2. **Closed-form evaluation cost scales linearly in the number of
   anchor points, not in `n`.** The `n = 5` anchor's six
   `simp [Polynomial.eval_*]; norm_num` calls each completed without
   visible delay despite the larger polynomial — this confirms the
   strategy's note that `norm_num` on fraction arithmetic up to
   `2497/6250` and `23/256` is not a bottleneck.

3. **Cycle 295's odd-`n` parity helper paid its first dividend
   immediately.** The `n = 5` middle root reduced from a four-line
   parity argument (`eval_one_sub` + `rw` + `neg_one_pow` + `linarith`)
   to a one-line helper application. For every future odd-`n`
   anchor (n = 7, 9, …), the middle root is now a one-liner.

## Suggested next approach

**Top priority — single-poll Aristotle on cycle 297.** Current
trajectory: 0% → 16% → 25% over three cycles. If linear growth
holds, COMPLETE around 35-40%, i.e. ~cycle 300. Watch for:

* `COMPLETE` ⇒ Branch A integration (general (342g)).
* `≥ 35%` with continued growth ⇒ Branch B, ship `n = 7` anchor
  (mirror cycle 296 recipe).
* Same or lower % ⇒ stall observation #1 (cycle 297 reading is
  cycle 296's baseline now, not cycle 295's). Append to scoping
  doc, do not cancel.

**Next anchor rung — `n = 7`** if Aristotle still running:

* Middle root `r₄ = 1/2` via the parity helper (Odd 7 = ⟨3, rfl⟩).
* Six other roots via IVT on six subintervals. Hard part: needs
  `butcherShiftedLegendre_seven` closed form, which **does not yet
  exist** in the codebase (cycles 278+ stopped at `n = 5`). The
  closed-form rung would need to land first.

**Alternative if `n = 7` closed form is too expensive:** the
`card_roots_eq_n` corollary (cycle 295 "Suggested next approach")
becomes more attractive: given the upper bound
`butcherShiftedLegendre_card_roots_le n` (cycle 294) and an
existential `n`-distinct-roots witness for each anchor `n`, derive
`(butcherShiftedLegendre n).roots.toFinset.card = n` for
`n ∈ {1, 2, 3, 5}`. This is a low-LOC corollary that closes a
useful piece of the (342g) "exactly `n` roots" structure even
while the general statement waits on Aristotle.

**Do NOT** attempt manual closure of (342g) general while Aristotle
is healthy — would duplicate ~6 cycles of work that may complete
on its own.
