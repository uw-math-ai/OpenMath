# Cycle 350 Results

## Worked on

Phase D′.2.1 (Route E refinement of cycle 345) for `def:422B` per
the cycle 350 strategy. Three priority deliverables shipped + one
stretch:

* **Priority 1**: `Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened`
  in `OpenMath/Chapter4/Section422.lean`. A sibling theorem of
  cycle 345's `Eq422a_at_vertex_eta_eq_of_stable_preconsistent`
  with the **strictly weaker** non-vanishing side hypothesis
  `coef_α(M) + coef_β(M) ≠ 0` in place of cycle 345's
  `0 ≤ coef_β(M)`.

* **Priority 2**: `coef_α_plus_coef_β_eq_succ_weighted_β_of_isConsistent`.
  Algebraic identity bridging the §422 denominator
  `coef_α + coef_β` to the `(i+1)`-weighted β-sum `Σᵢ (i+1) · βᵢ`
  under consistency.

* **Priority 3**: `bdf2LMM_coef_α_plus_coef_β_ne_zero` + BDF2
  end-to-end example exercising Priority 1.

* **Priority 4 (stretch)**: `Eq422a_at_vertex_eta_eq_of_stable_consistent`.
  Cleaner consistent-form corollary pinning
  `η(τ) = sum_β / Σᵢ (i+1) · βᵢ` under `IsStable + IsConsistent` +
  non-vanishing `(i+1)`-weighted β-sum, signature matches Butcher
  §422 surface notation. Plus BDF2 end-to-end example.

Net Section422.lean delta: 1051 → 1204 LOC (+153 including
docstrings + BDF2 witnesses).

## Approach

Per the cycle 350 strategy directly:

* Priority 1 proof: a one-line call to cycle 342's
  `Eq422a_at_vertex_eta_eq` with the non-vanishing hypothesis
  supplied unconditionally as `h_denom_ne`. Underscore-marked
  `hk`/`hStab`/`hPre` retained for caller ergonomics — drop-in
  signature compatibility with cycle 345's lemma.

* Priority 2 proof: `rw [coef_α_eq_sum_β_of_isConsistent M hCons]`
  to convert the α-side to a β-sum, then
  `rw [← Finset.sum_add_distrib]` to merge the two β-sums, then
  `Finset.sum_congr rfl` + `push_cast` + `ring` to close the
  per-index `1·β + i·β = (i+1)·β` identity. Strategy's risk
  mitigation (`Finset.sum_add_distrib` name verification) was
  unnecessary — the name is canonical in this codebase (8
  occurrences) and fired on the first attempt.

* Priority 3: `simp` on BDF2 + `Fin.sum_univ_two/three` unfolds +
  `norm_num` for the `2/3 + 0 ≠ 0` arithmetic. End-to-end BDF2
  witness composes Priority 1 + Priority 3 + cycle 346's
  `bdf2LMM_isStable` + cycle 73-era `bdf2LMM_isPreconsistent`.

* Priority 4: applied Priority 2's identity to rewrite both
  `h_succ_β_ne` (hypothesis) and the goal denominator into
  `coef_α + coef_β` form, then dispatched to Priority 1.

## Result

**SUCCESS.** All four new public theorems compile and are
axiom-clean.

Verified via inline `#print axioms` lines (appended, run, captured
output, then reverted before commit per cycle 349 trap):

```
'Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened' depends on axioms: [propext, Classical.choice, Quot.sound]
'coef_α_plus_coef_β_eq_succ_weighted_β_of_isConsistent'    depends on axioms: [propext, Classical.choice, Quot.sound]
'bdf2LMM_coef_α_plus_coef_β_ne_zero'                       depends on axioms: [propext, Classical.choice, Quot.sound]
'Eq422a_at_vertex_eta_eq_of_stable_consistent'             depends on axioms: [propext, Classical.choice, Quot.sound]
```

Section422.lean compiles via both `lake env lean
OpenMath/Chapter4/Section422.lean` (no output, exit 0) and `lake
build OpenMath.Chapter4.Section422` (full olean refresh).

Sorry count in Section422.lean remains 0.

## Faithfulness check

For each new theorem introduced this cycle:

* **`Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened`**
  (Priority 1):
  * Entity ID: **not** a Butcher-named lemma. Structural
    refinement of cycle 345's
    `Eq422a_at_vertex_eta_eq_of_stable_preconsistent`.
  * Lean statement captures: same (422a) content as cycle 345
    with a strictly **weaker** side hypothesis. The textbook §422
    closed-form for `η(τ)` makes no commitment to whether the
    non-vanishing of `coef_α + coef_β` should be proved from
    stability+preconsistency alone or supplied as a hypothesis —
    cycle 350's Route E sibling exposes the latter as a separate
    public surface so cycle 345 callers and future Phase D′.2.2
    callers can use whichever signature matches their context.
  * Underscore-marked `_hk`/`_hStab`/`_hPre` retained for caller
    ergonomics (cycle 345 idiom; no scanner trigger per strategy
    risk-register row).

* **`coef_α_plus_coef_β_eq_succ_weighted_β_of_isConsistent`**
  (Priority 2):
  * Entity ID: **not** a Butcher-named lemma. Pure structural
    algebraic identity under (404b).
  * Lean statement captures: a per-index re-pairing
    `1·βᵢ + i·βᵢ = (i+1)·βᵢ` composed with cycle 345's
    `coef_α = sum_β` (under consistency). No textbook
    divergence; this is mechanical algebra.

* **`bdf2LMM_coef_α_plus_coef_β_ne_zero`** (Priority 3):
  * Entity ID: BDF2 numerical non-vacuity for Priority 1's
    weakened hypothesis. No textbook claim attached.
  * Numerical sanity matches: BDF2 has
    `coef_α = 1·(4/3) + 2·(-1/3) = 2/3`,
    `coef_β = 0·(2/3) + 1·0 + 2·0 = 0`, so the sum is `2/3 ≠ 0`.

* **`Eq422a_at_vertex_eta_eq_of_stable_consistent`** (Priority 4,
  stretch):
  * Entity ID: **not** a Butcher-named lemma. Structural
    refinement; signature matches Butcher §422 surface notation
    (`η(τ) = sum_β / Σᵢ (i+1) · βᵢ`) more closely than the
    cycle 345/Priority 1 `coef_α + coef_β` form.
  * Lean statement captures: same content as Priority 1 (and
    therefore as cycle 345 modulo non-vanishing-hypothesis form)
    under the consistency-equivalent denominator. No textbook
    divergence.

**No `lean_status.json` change.** `def:422B` row stays `partial`
per the cycle 350 strategy directive.

**Pre-commit checklist results:**
- TAUTOLOGY: none. No conclusion appears verbatim as a hypothesis.
- IDENTITY: Priority 1's body is a one-line call to
  `Eq422a_at_vertex_eta_eq`; this is real composition (supplying
  the non-vanishing hypothesis directly), not a re-export. Priority
  4's body is two `rw`s + a call to Priority 1; this is the
  composition of Priority 2's identity with Priority 1.
- DEFINITION SMUGGLING: no new `structure`/`class` introduced.
- HYPOTHESIS STRENGTH: Priority 1's `h_denom_ne` is **strictly
  weaker** than cycle 345's `0 ≤ coef_β` (under cycle 344's
  `coef_α > 0`, `0 ≤ coef_β` implies `coef_α + coef_β > 0` implies
  `≠ 0`; the converse fails when `coef_α + coef_β` is negative).
  Priority 1 satisfies the cycle 350 strategy's stated weakening
  direction.

## Dead ends

None this cycle — strategy-directed, all four targets shipped on
first attempt:

* No need to invoke the strategy's risk-register fallback
  (`Finset.sum_add` + `simp_rw [add_mul]`); the canonical
  `Finset.sum_add_distrib` name worked.
* Initial Priority 4 attempt had a spurious trailing `norm_num`
  after `simp [bdf2LMM, Fin.sum_univ_three]` that produced "No
  goals to be solved" errors (simp closes the BDF2 numerical goal
  outright). Removed the redundant `norm_num` calls and the
  example compiled. Total iteration cost: ~1 min.

## Discovery

* `simp [OpenMath.Chapter4.Section451.bdf2LMM, Fin.sum_univ_three]`
  alone closes the BDF2 `(1·(2/3) + 2·0 + 3·0 = 2/3)` goal without
  needing a separate `norm_num` step. The implicit `1 * (2/3) = 2/3`
  + `0 + 0 = 0` normalizations are within `simp`'s reach when the
  unfolded sum is fully concrete. Useful future BDF2 witness
  pattern: try `simp [bdf2LMM, Fin.sum_univ_three]` first, only
  add `norm_num` if the goal has fraction arithmetic that survives.

* Priority 4's two-step proof (`rw [← h_id] at h_succ_β_ne ⊢` to
  translate both hypothesis and goal denominators into the
  `coef_α + coef_β` form, then dispatch to Priority 1) is a clean
  pattern for shipping multiple equivalent-signature corollaries
  off a single weakest-form base theorem + an algebraic identity.

## Suggested next approach

Per the cycle 350 strategy §"Cycle 351+ outlook", three credible
directions for cycle 351:

1. **Phase D′.2.2 via hypothesis strengthening (Route D, order ≥ 2)**:
   add an `order ≥ 2` hypothesis to derive `0 ≤ Σᵢ i²·αᵢ`, then
   `coef_β = (1/2)·Σᵢ i²·αᵢ` under order-2 consistency. Risk:
   weakens target by adding a hypothesis beyond textbook signature;
   needs faithfulness documentation per cycle 250 `alphaWeight`
   precedent.

2. **Phase D.3 scoping** — pivot to the substantive `def:422B`
   inductive solver per the cycle 348 §4 Phase D.3 outline.
   Multi-cycle.

3. **Pivot to a fresh entity** — `def:451A`, `thm:535A`, `thm:541A`,
   or another candidate from
   `.prover-state/issues/cycle_336_pivot_options.md`. With cycle
   350 being the 15th consecutive `def:422B` cycle and Phase
   D′.2.1's natural completion (the next step is the multi-cycle
   D′.2.2/2.3 work), pivoting may be a reasonable planner choice.

My weakly held preference: **direction 3 (pivot)**. Cycle 350's
shipped weakened-hypothesis surface is genuinely useful for any
future caller — but the next D′-internal step (D′.2.2/2.3
unconditional drop) requires either Mathlib-gap closure (Routes A/C
per scoping doc §4) or a hypothesis-strengthening compromise that
weakens the textbook signature. Both are higher-friction than
shipping a fresh entity's Phase 0.
