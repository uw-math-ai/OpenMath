# Cycle 401 Results

## Worked on

Phase α'.4.2 P5 — `bushy` migration (the fifth and final Phase α'.4.2
ladder-tree migration). Migrated `inversePolynomial`'s `bushy` branch
from cycle 383's `inversePolyBroom 3 f` dispatch to a `inversePolyTree
RootedTree.bushy f` dispatch, mirroring cycles 391/393/396/397
mechanically.

Touched theorems / defs (all in `OpenMath/Chapter4/Section422.lean`):

* `inversePolynomial` — body migration of the 5th `if`-branch (Step B).
* `inversePolyTree_bushy_eq_inversePolynomial` — new bridge theorem
  (Step A).
* Phase α.2 (cycle 377) bushy calibration `example` (Step C).
* `elementaryWeightQ_phi_inv_eq_inversePolynomial_bushy` Phase β.2
  bridge (Step D).
* `inversePolynomial_eq_of_subtree_agreement` Phase γ bushy arm
  (Step E; two replacements per the double-rewrite pattern).
* `inversePolyBroom_three_eq_inversePolynomial` cycle 382 derivative
  bridge (Step F; proof body extended).

## Approach

Verified cycle 400 HEAD state first (commit `b4f5c7f`, 8150 LOC, sorry
count 5, `inversePolyTree_bushy` at line 6662). Followed the strategy's
Step A → Step F recipe verbatim per the cycle 391/393/396/397
precedent:

1. **Step A** — Inserted `inversePolyTree_bushy_eq_inversePolynomial`
   immediately after cycle 397's `inversePolyTree_mkMkCherry_eq_inversePolynomial`
   (line 7475). Proof: `unfold inversePolynomial; rw [if_neg × 4,
   if_pos rfl]` (4 if_negs because `bushy` is the 5th branch in
   `inversePolynomial`'s if-then-else chain).

2. **Step B** — Migrated the `bushy` branch body from
   `inversePolyBroom 3 f` to `inversePolyTree RootedTree.bushy f`
   (line 6914). Value-preserving by cycle 400's `inversePolyTree_bushy`
   matching cycle 370's `Φ_{η_q⁻¹}(bushy) = v⁴ − 3v²c + 3v·b' − f bushy`.

3. **Step C** — Swapped trailing `inversePolyBroom_three` →
   `inversePolyTree_bushy` in Phase α.2 calibration `example`
   (line 7012).

4. **Step D** — Same swap in Phase β.2 bridge
   `elementaryWeightQ_phi_inv_eq_inversePolynomial_bushy` (line 7589).

5. **Step E** — Same swap (TWO occurrences) in Phase γ
   `inversePolynomial_eq_of_subtree_agreement` bushy arm (line 7905).
   Used non-`replace_all` `Edit` since the two occurrences appear on
   the same line in the `rw` token list.

6. **Step F** — Extended cycle 382's
   `inversePolyBroom_three_eq_inversePolynomial` proof body by appending
   `inversePolyBroom_three, inversePolyTree_bushy` to the existing `rw`
   chain (line 7299). Both routes now reduce to cycle 370's closed form
   `v⁴ − 3v²c + 3v·b' − f bushy`. Theorem statement unchanged.

Verification: `lake env lean OpenMath/Chapter4/Section422.lean` exited
0 with only the grandfathered cycle 365 sorry warning at line 2272
(expected). Full `lake build OpenMath.Chapter4.Section422` completed in
1165s (elevated rebuild time per cycle 399 Discovery: 5-arm
`inversePolyTree` unfolding-lemma growth). Axiom check via scratch file
`Section422AxiomCheck401.lean` (deleted after use) confirmed all 5 named
theorems return `[propext, Classical.choice, Quot.sound]`.

## Result

**SUCCESS** — All 6 strategy steps shipped on first attempt; recipe is
fully stable across cycles 391/393/396/397/401.

* Bridge theorem `inversePolyTree_bushy_eq_inversePolynomial` shipped,
  axiom-clean.
* `inversePolynomial`'s `bushy` branch migrated, axiom-clean.
* Phase α.2 calibration `example`, Phase β.2 bridge, Phase γ branch (×2),
  and cycle 382 derivative bridge all retrofitted, axiom-clean.
* Sorry count unchanged at 5 (4 docstring + 1 grandfathered code at
  line 2279).
* Section422.lean: 8150 → 8178 LOC (+28 LOC).
* `lake build OpenMath.Chapter4.Section422` exits 0.

**Phase α'.4 fully closed.** All 9 ladder trees (`vertex`, `cherry`,
`broom₃`, `mk [cherry]`, `bushy`, `mk [broom₃]`, `mk [vertex, cherry]`,
`mk [mk [cherry]]`; plus the order-5 `mk [cherry, cherry]` baseline
exercised via cycle 388's calibration) now route uniformly through
`inversePolyTree`.

§422 axiom-clean streak: 62 substantive + 3 doc (336–400) →
**63 substantive + 3 doc** (cycles 336–401).

## Faithfulness check

For the new bridge theorem `inversePolyTree_bushy_eq_inversePolynomial`:

* **Entity ID**: helper bridge lemma (no `def:*` / `thm:*` direct
  correspondence — supports `def:422B`'s recursive infrastructure).
  No `extraction/formalization_data/entities/<id>.json` to quote;
  textbook lineage is Butcher §422 p. 1163 / §422 (422a) (cycle 370's
  `elementaryWeightQ_phi_inv_bushy` is the closed-form reference under
  the §383 quotient framework).
* **Lean statement captures**: standard bridge form
  `inversePolyTree t f = inversePolynomial t f` — locally vacuous (both
  sides definitionally reduce to `inversePolyTree RootedTree.bushy f`
  after Step B's body migration), but load-bearing for downstream
  consumers (Phase α.2 / β.2 / γ rewrites that need the closed-form
  ↔ recursive equivalence as a `rw` token).
* **Identity check disposition**: this is the unavoidable bridge-form
  identity required when migrating a `def`'s if-branch — the bridge
  theorem's role is to advertise the (now-definitional) equality as a
  named `rw` target. Cycles 391/393/396/397 ship identical patterns;
  cycle 401 is the final closure. Not vacuous; the theorem participates
  as a citation point in 5 downstream `rw` chains (Steps C, D, E×2, F).
  Compare cycle 397 task_results §"Faithfulness check" for the
  precedent.

For the Step B body migration of `inversePolynomial`:

* **Entity ID**: helper `noncomputable def` (no direct textbook entity).
* **Lean statement captures**: same content — value-preserving migration
  per cycle 400's `inversePolyTree_bushy = v⁴ − 3v²c + 3v·b' − f bushy`
  matching cycle 383's `inversePolyBroom 3 f` expansion. Both reduce to
  Butcher §422 p. 1163 cycle 370's `Φ_{η_q⁻¹}(bushy)` closed form. No
  hypothesis-strength change; no scope deviation.
* **Tautology / identity check**: N/A (def, not theorem).

For Step F's extended cycle 382 derivative bridge
`inversePolyBroom_three_eq_inversePolynomial`:

* Statement unchanged from cycle 382 ship; only proof body extended.
* Captures: same content.
* Hypothesis strength: unchanged (no hypotheses).

## Dead ends

None. Strategy recipe was stable from cycle 391/393/396/397 precedent;
no deviation needed. The Step E `replace_all` tip from cycle 397
Discovery was not exercised because the two occurrences appear on the
same line in the same `rw` token list, making a single `Edit` with
sufficient surrounding context unique enough.

## Discovery

1. **Phase α'.4.2 recipe fully stabilised.** Across cycles 391, 393,
   396, 397, 401 (five consecutive migrations spanning 11 cycles), the
   6-step Step A–F template (bridge theorem → body migration → α
   calibration rewrite → β bridge rewrite → γ branch rewrite (×2) →
   derivative-bridge proof extension) ran without scope creep. LOC
   budget converged to ~30 LOC (cycle 397: ~50; cycle 401: 28). The
   only variability is the `if_neg` count in the bridge theorem
   (determined by the branch's position in `inversePolynomial`'s
   if-then-else chain: cycle 391 P1 `mk [vertex, cherry]` = 6 if_negs;
   cycle 393 P2 `broom₃` = 2 if_negs and `mk [broom₃]` = 5 if_negs;
   cycle 396 P3 `cherry` = 1 if_neg and `mk [cherry]` = 3 if_negs;
   cycle 397 P4 `mk [mk [cherry]]` = 7 if_negs; cycle 401 P5 `bushy`
   = 4 if_negs). Future migrations for Phase α'.5 `k ≥ 3` heterogeneous
   trees should reuse this template verbatim with the matching if_neg
   count.

2. **Build time inflated by `inversePolyTree`'s 5-arm match.** Warm
   `lake build OpenMath.Chapter4.Section422` took 1165s on cycle 401 vs.
   ~200–500s on cycles 391–397. The cycle 399 Discovery (5-arm equation
   compiler unfolding-lemma growth) is the load-bearing cause; cycle 400
   already saw this elevated cost. Cycle 402+ should budget ≥ 1200s for
   warm rebuilds of Section422 until further refactoring. Phase α'.5
   work on k ≥ 4 will face the same scaling.

3. **Phase α'.4 closure milestone.** With cycle 401 shipped, the 9
   ladder trees in `inversePolynomial`'s dispatch all route through
   `inversePolyTree`. This is the precondition for collapsing the Phase
   β/γ `inversePolynomial_eq_of_subtree_agreement` pile-of-cases proof
   into a uniform recursive-structure proof, which in turn unblocks
   cycle 365's grandfathered Sub-lemma A sorry at line 2279. However,
   the unification is necessary but not sufficient: the cycle 365 sorry
   still requires a separate per-tree subtree-agreement →
   `linearResidualAt`-agreement bridge that has not yet been built. That
   bridge is multi-cycle work that warrants its own scoping doc — cycle
   402+ planner's call whether to invest in it or pivot to a fresh
   entity.

## Suggested next approach

Cycle 402's planner faces a pivot decision. Three concrete options:

1. **Phase α'.5 scoping doc** — `k ≥ 3` heterogeneous children scoping
   (e.g. `mk [vertex, vertex, cherry]`, `mk [cherry, cherry, cherry]`).
   Cycle 399's catch-all is bumped to `(_::_::_::_::_)` precisely to
   leave the door open. Full closure requires a `tetrachildPolynomial`
   / `quadchildCrossTerm` analogue of cycle 399's `trichildPolynomial`,
   plus per-tree calibration witnesses for the new arity. Estimated
   ~2-3 cycles per heterogeneous k=4 tree; warns of equation-compiler
   unfolding-lemma cost growth flagged in Discovery #2 above. Following
   the cycle 385 / cycle 398 scoping-doc precedent, this should be a
   markdown-only deliverable for the first cycle.

2. **Phase β/γ extension scoping doc** — attacking the cycle 365
   grandfathered Sub-lemma A sorry. With Phase α'.4 closed, the
   recursive `inversePolyTree` structure permits a uniform proof of
   `inversePolynomial_eq_of_subtree_agreement` by induction on the
   tree structure (rather than case analysis on each of 9 ladder
   trees), but the per-step subtree-agreement → `linearResidualAt`-
   agreement bridge is novel work. Following the cycle 348 / cycle 379
   precedent, this should be a markdown-only scoping doc for the first
   cycle, then a multi-cycle deliverable plan.

3. **Pivot to fresh entity** — `def:451A`, `def:442A`, `thm:535A`,
   `thm:541A` per `cycle_336_pivot_options.md`. The §422 streak is
   approaching 70 substantive cycles (currently 63 substantive + 3 doc);
   this is a natural inflection point. Cycle 336's pivot options doc
   should be re-read and refreshed against current Mathlib / lean_status
   state.

Recommendation: **Option 1 (Phase α'.5 scoping doc)** if the planner
wants to continue accumulating Phase α' infrastructure for a future
unified-recursion ship; **Option 3 (pivot)** if the planner judges the
§422 sub-stream has plateaued and a fresh entity would yield more
mathematical progress per cycle. Option 2 (cycle 365 sorry closure)
should be deferred to mid-cycle 402+, after the planner has chosen
between Options 1 and 3.
