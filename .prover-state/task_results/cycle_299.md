# Cycle 299 Results

## Worked on
* P0: single-poll Aristotle project `5939f28b-c890-4b7f-be4f-ed0f31f0d0b5`
  (general `(342g)` statement).
* P1: shipped `butcherShiftedLegendre_eleven_roots` in
  `OpenMath/Chapter3/Section342.lean` — eleventh rung of the empirical
  ladder for `lem:342A (342g)`.

## Approach
1. **Aristotle poll**: `IN_PROGRESS, percent_complete = 29`
   at `2026-05-15T23:56:34Z`. +1 pp from cycle 298's 28%. Healthy
   growth ⇒ **Branch B** of the strategy decision table fires:
   ship the `n = 11` anchor, leave Aristotle queued.
2. **Python pre-flight (`Fraction` exact arithmetic)** computed
   `P_11^*` at all 12 bracket endpoints plus `1/2`. Sign sequence
   `−, +, −, +, −, +, 0, −, +, −, +, −, +` — matches the
   expected odd-`n` pattern; outer-bracket denominator 50 sufficed
   on both ends, so no escalation to denominator 100 was needed.
3. **Lean port**: mechanical extension of cycle 298's
   `butcherShiftedLegendre_nine_roots` recipe.
   - 12 `have hf_<frac>` evaluations of `P_11^*` via the closed form
     `butcherShiftedLegendre_eleven` (cycle 287) + `simp/norm_num`.
   - 10 IVT calls — alternating `intermediate_value_Ioo` /
     `intermediate_value_Ioo'` to match the sign-direction at each
     bracket (read off the Python verification).
   - Middle root `r₆ = 1/2` via
     `butcherShiftedLegendre_eval_half_eq_zero_of_odd 11 ⟨5, rfl⟩`
     (cycle 295's parity helper).
   - 55 distinctness pairs + 11 `Set.Ioo (0:ℝ) 1` memberships +
     11 `eval r = 0` conjuncts assembled by a single `refine`.
4. **Linarith timeout mitigation** (new this cycle): the 12 large-
   rational `hf_*` hypotheses (max numerator
   `25826480523788463/76293945312500000` ≈ 76 quintillion in the
   denominator) caused `linarith` to time out on `isDefEq` during
   the post-`refine` block. Inserted an explicit
   `clear hP11 hcont hf_0 hf_1 hf_one_fiftieth …` just before
   `refine`, retaining only `hf_half` (consumed by `refine`) and
   `hrᵢ_eval` / `hrᵢ_mem` hypotheses. Compile succeeds in ~28 s
   after the clear.

## Result
**SUCCESS.** `OpenMath/Chapter3/Section342.lean` compiles cleanly
(`lake env lean` exit 0, `lake build OpenMath.Chapter3.Section342`
exit 0, ~28 s each). Axiom check:

```
'OpenMath.Chapter3.Section342.butcherShiftedLegendre_eleven_roots'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

Zero sorries, no new axioms. Empirical anchor ladder now stands at
`n ∈ {1, 3, 5, 7, 9, 11}`.

## Faithfulness check

* **Entity ID**: `lem:342A` (Butcher §342, property (342g) — the
  zeros statement).
* **Textbook statement** (from
  `extraction/formalization_data/entities/lem_342A.json`,
  property (342g)):
  > P_n^* has n distinct real zeros all lying in the open
  > interval (0, 1).
* **Lean statement of `butcherShiftedLegendre_eleven_roots` captures**:
  **weaker than the general statement** — fixes `n = 11`. This is
  the eleventh rung of the empirical ladder (cycles 282/295/296/297/
  298 covered `n = 1, 3, 5, 7, 9`). The general `∀ n` form is the
  Aristotle target (project `5939f28b-c890-4b7f-be4f-ed0f31f0d0b5`,
  still in flight at 29%). Justification for the divergence: while
  Aristotle works on the general statement, each new fixed-`n`
  anchor is axiom-clean infrastructure that (i) keeps the cycle
  productive, (ii) builds a witness pool that downstream work can
  consume even before the general theorem lands, and (iii) exposes
  scaling bottlenecks (e.g. this cycle's `linarith` /
  `isDefEq` timeout — anticipated for `n ≥ 13`).
* **No new `def` or `class`/`structure` introduced this cycle**.
* **Tautology check**: ✓ the 11 `eval rᵢ = 0` conjuncts are
  genuine witnesses obtained via IVT or parity, not restated
  hypotheses.
* **Identity check**: ✓ proof is not an `exact h` re-export — the
  IVT/parity content does real work.
* **Hypothesis strength check**: ✓ theorem takes no hypotheses
  beyond the closed-form definition of `butcherShiftedLegendre 11`.
* **Lean status / plan**: `lem:342A` remains `partial`. **NOT
  bumped to `formalized`** — the general (342g) statement is still
  open. `plan.md` row stays `[~]`.

## Dead ends
* **Initial compile attempt without the `clear` step** hit a
  `simp failed: timeout at isDefEq (max heartbeats 200000)`
  inside the very first `linarith` of the `r₆ = 1/2 ≠ rᵢ` block
  (file line 4940). The cycle 298 `n = 9` proof did not hit this
  because the n = 9 coefficients (max denominator
  `25600000000` = 25.6 billion) are ~3 orders of magnitude smaller
  than the n = 11 outer-bracket denominator (`76293945312500000`
  ≈ 76 quintillion). The `clear` mitigation (retain only `hf_half`
  + IVT outputs before `refine`) resolved this and is now standard
  for any future `n ≥ 11` anchor.

## Discovery
* **Scaling bottleneck identified**: `linarith`'s `isDefEq`
  preprocessing on the polynomial-evaluation hypotheses is the
  rate-limiting step for high-`n` anchors. Cycle 298's strategy
  bullet "n = 13: denominator 100 brackets required" anticipated
  the bracket-precision issue but missed the hypothesis-pollution
  issue; **cycle 300+ should bake the `clear` step into the
  template before attempting `n ≥ 13`**.
* **Python pre-verification correctness streak holds**: the
  bracket signs computed exactly via `Fraction` matched the
  expected odd-parity pattern on the first try. The recommended
  bracket grid from the cycle 299 strategy was correct end-to-end;
  no escalation to denominator 100 was needed.

## Suggested next approach
* **If Aristotle returns `COMPLETE` mid-cycle 300**: pivot to
  Branch A — integrate the general theorem, bump `lem:342A` to
  `formalized`, keep the `n = 1, 3, 5, 7, 9, 11` anchors as
  numerical witnesses. They cost nothing to retain.
* **If Aristotle is still `IN_PROGRESS` at 29–30%**: ship the
  `n = 13` anchor in cycle 300, but pre-fold the cycle 299 `clear`
  step into the template. Outer roots of `P_13^*` are ≈ 0.008, so
  denominator 100 brackets will likely be required.
* **If Aristotle stalls at 29% for three consecutive polls**: open
  the manual closure issue (per the cycle 299 strategy §C) and
  consider cancelling the Aristotle job. The cycle 289-style
  manual closure plan is the contingency.
* **Sibling targets** to consider once `lem:342A` closes:
  `lem:312B`, `lem:313A`, `thm:311B`, `thm:351B`. The planner has
  flexibility post-closure.
