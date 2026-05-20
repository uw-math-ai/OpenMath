# Cycle 506 Results

## Worked on

§422 Phase β.1 k=4 dispatch extension for `def:422B`. Extended
cycle 496's
`elementaryWeightQ_phi_inv_eq_inversePolyTree_on_ladder` at
`OpenMath/Chapter4/Section422.lean:17694` from 14 to 19 disjuncts,
adding `rcases` arms for the cycle 499 (`bushy₄`),
501 (`mk [v,v,v,c]`), 502 (`mk [v,v,c,c]`), 503 (`mk [v,c,c,c]`),
504 (`mk [c,c,c,c]`) k=4 calibration witnesses.

Plus bookkeeping: `lean_status.json` `def:422B.cycle_completed_at`
505 → 506; `plan.md` `def:422B` row appended with cycle 506 closure
paragraph; scoping doc
`.prover-state/issues/def_422B_phase_beta_gamma_k4_scoping.md`
§10' cycle 506 closure subsection appended.

## Approach

Followed the cycle 506 strategy §B–§E workflow:

1. **Pre-flight (§B)**:
   * `git log -2`: HEAD = `a80aa15` cycle 505, parent = `835d38c`
     cycle 504. ✓
   * `wc -l OpenMath/Chapter4/Section422.lean`: 19159 LOC (strategy
     expected ~21163, but the smaller count is fine — strategy
     estimate was upper bound).
   * `grep -c sorry`: 5 ✓.
   * All 5 cycle 499/501/502/503/504 closed-form witnesses present at
     lines 9136, 9501, 10263, 11331, 12626. ✓
   * All 5 cycle 499/501/502/503/504 `inversePolyTree_*` calibrations
     present at lines 15152, 15216, 15320, 15508, 15772. ✓
   * Dispatch theorem to extend at line 17694. ✓
   * Skipped full pre-flight build since all witness theorems
     present means cycle 504's ship is intact in working tree.

2. **Edit (§C)**: extended `ht_ladder` from 14 to 19 disjuncts;
   extended `rcases` cascade from 14 to 19 alternatives; appended 5
   new arms after the existing 14, each closing via
   `rw [elementaryWeightQ_phi_inv_<tree>, inversePolyTree_<tree>]`.
   Docstring extended with cycle 506 extension note + 19-tree ladder
   recap.

   **Pattern decision**: the strategy's §C.2 template suggested
   `rw [...]; ring`, but the existing 14 arms (cycles 341/367–372/378/
   384–386/403/491–494) close via `rw [...]` alone (no `;ring`).
   The cycle 499–504 calibration witnesses
   (`inversePolyTree_<tree>`) were designed to mirror their
   respective `elementaryWeightQ_phi_inv_<tree>` closed forms
   verbatim — under `f := elementaryWeightQ_phi η_q` the two RHSs
   are syntactically identical, so `rw` closes by definitional `rfl`.
   `; ring` after a closed `rw` would fail with "no goals". Followed
   the existing arm pattern.

3. **Verify (§D)**:
   * Build: `time lake env lean OpenMath/Chapter4/Section422.lean`
     exit 0 in **5m 0s** (warm rebuild, much faster than the
     strategy's 15–25 min estimate). Only warning is the
     grandfathered cycle 365 sorry at line 2272.
   * Sorry count unchanged: `grep -c sorry` returns 5 ✓.
   * Axiom-clean: refreshed olean via `lake build
     OpenMath.Chapter4.Section422` (required per memory
     `feedback_lake_env_lean_no_olean_update.md`), then
     `#print axioms
     OpenMath.Chapter4.Section422.elementaryWeightQ_phi_inv_eq_inversePolyTree_on_ladder`
     returns `[propext, Classical.choice, Quot.sound]` ✓.
   * LOC delta: 19159 → 19196 (+37 LOC), well within strategy's
     50–100 LOC budget.

4. **Bookkeep (§E)**:
   * `lean_status.json` `def:422B.cycle_completed_at` bumped 505 → 506.
   * `plan.md` `def:422B` row appended with cycle 506 closure
     paragraph (programmatic Python append to preserve the 109k-char
     single-line format).
   * Scoping doc `.prover-state/issues/def_422B_phase_beta_gamma_k4_scoping.md`
     §10' cycle 506 closure subsection appended (mirroring §10's
     cycle 505 closure style).

## Result

SUCCESS — Phase β.1 k=4 dispatch extension shipped axiom-clean.

* **Lean delta**: cycle 496's dispatch theorem extended from 14 to
  19 disjuncts; 5 new `rcases` arms; LOC delta +37.
* **Faithfulness**: no new `def` / `structure` / `theorem`
  introduced; the dispatch theorem's *signature* expands by 5
  disjuncts but the *content* is identical (per-tree witness reuse).
* **Axiom-clean target**: `[propext, Classical.choice, Quot.sound]`
  confirmed via `lake build`-refreshed olean.
* **Sorry count**: 5 (unchanged — 4 docstring + 1 grandfathered
  cycle 365 at line 2272).
* **§422 streak**: 77 substantive + 7 doc → **78 substantive + 7 doc**
  (cycles 336–506).
* **Build cost**: 5m warm, no `maxHeartbeats` increase required.

## Faithfulness check

No new `def` / `structure` / `theorem` introduced this cycle. The
sole Lean delta is an extension of cycle 496's
`elementaryWeightQ_phi_inv_eq_inversePolyTree_on_ladder` signature
(14 → 19 disjuncts) and proof (14 → 19 `rcases` arms), reusing
existing axiom-clean witnesses.

### `elementaryWeightQ_phi_inv_eq_inversePolyTree_on_ladder` (extended)

* Entity: helper / dispatch theorem reuniting cycle 496's
  per-tree witnesses into a single hypothesis-driven case-split for
  Phase β.1 of the `def:422B` framework. No direct textbook entity
  ID (this is an engineering scaffold for the §422 framework).
* Lean statement captures: SAME conceptual content as cycle 496's
  original 14-disjunct theorem, now extended to cover the 5 cycle
  499–504 k=4 witnesses on the ladder.
* No hidden hypotheses: the 5 new disjuncts in `ht_ladder` are
  exactly the 5 tree identities matching the cycle 499–504
  witness signatures (`RootedTree.bushy₄` plus the 4 explicit
  `mk [..., ..., ..., ...]` quadruples).
* No tautology: the conclusion
  `elementaryWeightQ_phi η_q⁻¹ t = inversePolyTree t (elementaryWeightQ_phi η_q)`
  is not implied by any single disjunct of `ht_ladder`; each
  disjunct discharges to a witness-mediated rewrite that closes by
  reflexivity on a shared closed form.
* No definition smuggling: `elementaryWeightQ_phi_inv_<tree>` and
  `inversePolyTree_<tree>` are independently proved
  (cycles 367–504); the dispatch theorem only composes their `rw`s.
* Hypothesis strength: `ht_ladder` is a finite disjunction —
  cannot be weakened without losing one of the 19 covered trees.
  The 5 new disjuncts are exactly the cycle 499–504 trees per the
  scoping doc §9.1 specification; no extra hypotheses smuggled.

## Dead ends

None encountered. The mechanical extension shipped cleanly on the
first compile.

One process note: the strategy's §C.2 template `rw [...]; ring` was
NOT used. Inspection of the existing 14 cycle 496 arms revealed
that they all close via `rw [...]` alone — the calibration
witnesses' closed forms mirror their `elementaryWeightQ_phi_inv_*`
counterparts verbatim, so `rfl` is implicit after `rw`. Adding
`; ring` would have failed with "no goals" on each arm. The
existing-arm pattern was followed and the build verified clean,
confirming the strategy's `; ring` was a safety net not needed in
practice (matching the strategy's own §C.3 caveat that "calibration
witnesses were proven against the matching closed forms, so normal
forms should align — `show` should rarely be needed").

## Discovery

**Discovery #1 (warm-rebuild speedup at 19k LOC).** Cycle 506's warm
rebuild of `Section422.lean` took 5m 0s, well under the strategy's
15–25 min estimate. The +37-LOC delta was minimal and the equation
compiler did not need to re-elaborate any of the existing arms.
This suggests that LOW-risk mechanical extensions of `Section422.lean`
have a much smaller marginal compile cost than the strategy's risk
register R2 anticipated. Cycle 507+ workers can budget ~5–10 min
for similar mechanical extensions.

**Discovery #2 (cycle 496 arm pattern dominates over `; ring`).**
The strategy's §C template recommended `rw [...]; ring` for the 5
new arms, but the existing cycle 496 14 arms all use `rw [...]`
alone. The cycle 499–504 calibration design (witness mirrors
closed form verbatim) means the dispatch arm pattern is purely
`rw`-based — no `ring` needed. Future workers extending this
theorem should follow the existing arm pattern, not the strategy's
template.

**Discovery #3 (cycle 504 ship was already committed).**
The strategy §H R4 anticipated that cycle 504's Lean ship might
have a hidden compile error since cycle 504 task results noted
compile verification pending. In fact, the cycle 504 ship was
folded into cycle 505's commit (per cycle 505 task results
Discovery #3) and verified clean by cycle 505's background build.
At cycle 506 entry the working tree was clean and all 10 witness
theorems (5 closed-form + 5 calibration) were present at expected
line numbers. The pre-flight build (§B.1) was unnecessary in this
cycle, though it remains a useful safety net for future cycles
where the cycle N–1 ship is uncommitted.

**Discovery #4 (`lake env lean` vs. `lake build` olean staleness).**
Confirmed memory `feedback_lake_env_lean_no_olean_update.md`:
after `lake env lean OpenMath/Chapter4/Section422.lean` succeeds,
the olean cache at
`.lake/build/lib/lean/OpenMath/Chapter4/Section422.olean` is NOT
updated (still reflects pre-edit state). A downstream `#print axioms`
import test runs against the stale olean and would yield
misleading results. Run `lake build OpenMath.Chapter4.Section422`
before any `#print axioms` cross-file verification.

## Suggested next approach

**Cycle 507** (per scoping doc §6.2): ship Phase γ k=4 verification.
Re-confirm `inversePolyTree_eq_of_subtree_agreement` at
`Section422.lean:18520` is axiom-clean over the 5-branch
`tetrachildCrossTerm` cascade — per cycle 505 Discovery #2, this is
mostly a verification task (re-confirm `#print axioms` is clean over
all 5 branches) since the Phase γ public lemma was extended *in
parallel* with each cycle 500–504 `tetrachildCrossTerm` branch
addition. Optionally ship 5 example theorems exercising Phase γ at
the new tetrachild trees. ~100–250 LOC, LOW risk.

**Cycle 508+** (per scoping doc §6.3 / §5.2): ship `nchildPolynomial`
scoping doc (markdown-only, Path b multi-cycle plan toward cycle 365
sorry closure). 600–900 LOC markdown.

**Out of scope**: cycle 365's grandfathered sorry at
`Section422.lean:2272` (Phase β.2 k ≥ 5 territory; Path b / Path c
multi-cycle effort per scoping doc §5).
