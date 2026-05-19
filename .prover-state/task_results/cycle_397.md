# Cycle 397 Results

## Worked on
Phase α'.4.2 migration of `inversePolynomial`'s `mk [mk [cherry]]` branch
from `inversePolyChain 3 f` to
`inversePolyTree (mk [mk [cherry]]) f`. Mechanical mirror of cycle
396's `mk [cherry]` migration with substitutions
`mk [cherry] → mk [mk [cherry]]`, `inversePolyChain 2 / _two →
inversePolyChain 3 / _three`,
`inversePolyTree_mkCherry → inversePolyTree_mkMkCherry`.

## Approach
Followed cycle 397 strategy's recipe verbatim:

* **Step 0**: Verified `mk [mk [cherry]]` is `inversePolynomial`'s 8th
  branch (after vertex, cherry, broom₃, mk [cherry], bushy,
  mk [broom₃], mk [vertex, cherry]) → 7 `if_neg`s + 1 `if_pos rfl`.
* **Step B (body migration)**: `inversePolynomial`'s 8th
  `if-then-else` branch body rewritten to dispatch through
  `inversePolyTree (mk [mk [cherry]]) f`.
* **Step A (new bridge)**:
  `inversePolyTree_mkMkCherry_eq_inversePolynomial` shipped
  immediately after cycle 396's `mk [cherry]` bridge with 7 `if_neg`
  discharges + `if_pos rfl`. Both sides reduce to
  `inversePolyTree (mk [mk [cherry]]) f`; closure by implicit `rfl`.
* **Step C (Phase α.2 calibration example)**: cycle 374's
  `mk [mk [cherry]]` calibration `example` trailing
  `inversePolyChain_three` swapped for `inversePolyTree_mkMkCherry`.
* **Step D (Phase β.4 bridge)**:
  `elementaryWeightQ_phi_inv_eq_inversePolynomial_mkMkCherry` (cycle
  378) similarly retrofitted.
* **Step E (Phase γ branch)**: in
  `inversePolynomial_eq_of_subtree_agreement` `mk [mk [cherry]]` arm,
  both `inversePolyChain_three` occurrences (f-side and g-side)
  replaced with `inversePolyTree_mkMkCherry` (replace_all on the
  matching f / g pattern in one Edit call).
* **Step F (cycle 380 bridge derivative fix)**:
  `inversePolyChain_three_eq_inversePolynomial` extended with
  `inversePolyChain_three, inversePolyTree_mkMkCherry` after the
  existing `if_pos rfl` so both routes reduce to the cycle 378 closed
  form.

Combined Steps C and D into a single `replace_all` Edit since the
trailing `rw` patterns were identical across the two sites — no
correctness loss since both genuinely needed the same swap.

## Result
SUCCESS — `lake build OpenMath.Chapter4.Section422` exits 0 (built in
200 s on first attempt; no Step F detection cycle needed since I
applied Step F preemptively per the strategy's explicit warning).
`grep -c sorry` returns 5 (unchanged — 4 docstring + 1 grandfathered
cycle 365 code at line 2272). All 6 verification symbols
(`inversePolyTree_mkMkCherry_eq_inversePolynomial`,
`elementaryWeightQ_phi_inv_eq_inversePolynomial_mkMkCherry`,
`inversePolynomial_eq_of_subtree_agreement`,
`inversePolyChain_three_eq_inversePolynomial`,
`inversePolyTree_mkMkCherry`, `inversePolyTree_mkCherry`) return
`[propext, Classical.choice, Quot.sound]` — axiom-clean.

§422 axiom-clean streak: 59 → **60 substantive + 2 doc** (cycles
336–397).

## Faithfulness check

**New `theorem` introduced this cycle:**

* `inversePolyTree_mkMkCherry_eq_inversePolynomial`
  - This is an internal bridge lemma asserting that the recursive
    `inversePolyTree` evaluation matches `inversePolynomial`'s
    post-migration body at `mk [mk [cherry]]`. NOT a textbook entity
    — no `extraction/formalization_data/entities/<id>.json` to quote.
  - The lemma equates two Lean expressions that, after Step B, are
    literally definitionally equal modulo the `if-then-else`
    dispatch. The proof closes by `unfold inversePolynomial` + 7
    `if_neg`s + `if_pos rfl` (no further rewrites needed since both
    sides reduce to `inversePolyTree (mk [mk [cherry]]) f`).
  - Tautology check: hypothesis-free; not a tautology.
  - Identity check: 1-line `rw` cascade closing by implicit `rfl`,
    not `exact h`; not vacuous — it is the structural alignment
    between the recursive helper and the closed-form table that
    downstream Phase β/γ consumers rely on.
  - Hypothesis strength check: only `f : RT → ℝ` (the elementary
    weight function); cannot be weakened.

**Touched theorems** (no signature changes — only proof body
adjustments to track the post-migration RHS):

* `inversePolyChain_three_eq_inversePolynomial` (cycle 380): proof
  body extended with `inversePolyChain_three, inversePolyTree_mkMkCherry`
  after `if_pos rfl`. Statement unchanged. Both routes now reduce to
  the cycle 378 closed form `v⁴ − 3v²c + c² + 2vm − M_mc`.
* `elementaryWeightQ_phi_inv_eq_inversePolynomial_mkMkCherry` (cycle
  378): final `rw` closer changed from `inversePolyChain_three` to
  `inversePolyTree_mkMkCherry`. Statement unchanged.
* `inversePolynomial_eq_of_subtree_agreement` (Phase γ): both
  `inversePolyChain_three` occurrences in the `mk [mk [cherry]]` arm
  replaced with `inversePolyTree_mkMkCherry`. Statement unchanged.
* Phase α.2 `example` for `mk [mk [cherry]]` calibration witness:
  trailing `inversePolyChain_three` swapped for
  `inversePolyTree_mkMkCherry`. RHS closed form unchanged.

No new `def`, `structure`, or `class` introduced. No new
`maxHeartbeats` bumps. No `axiom`/`constant` declarations. No new
hypotheses smuggled into existing theorems.

## Dead ends
None. The strategy's recipe was sufficient — no rework needed. I
applied Step F (derivative fix on cycle 380's bridge) preemptively
on the first edit pass per the strategy's explicit warning, so the
first `lake build` exited 0 without an unsolved-goals detection
cycle.

## Discovery
**`replace_all` collapses cycle 396's two-step pattern into one.**
The strategy listed Step C (Phase α.2 calibration `example`) and
Step D (Phase β.4 bridge) as two separate edits. But the trailing
`rw` patterns at the two sites were syntactically identical
(`if_neg`-cascade + `if_pos rfl, inversePolyChain_three`),
differing only in their docstring/theorem-name context above. A
single `Edit` with `replace_all: true` correctly retrofitted both.
This is safe because:

1. The pattern `... ≠ mk [vertex, cherry]), if_pos rfl,
   inversePolyChain_three]` is unique to the `mk [mk [cherry]]`
   migration sites (the only branches whose 7th `if_neg`'s RHS is
   `mk [vertex, cherry]`).
2. Both sites genuinely needed the same swap to
   `inversePolyTree_mkMkCherry`.

Future Phase α'.4.2 migrations (e.g., `bushy` in cycle 398) may
benefit from the same `replace_all` collapse if their Phase α.2
calibration + Phase β bridge end with identical trailing rewrites.

## Suggested next approach
**Cycle 398**: tackle `bushy` migration. `bushy =
mk [vertex, vertex, vertex]` is the sole remaining unmigrated
ladder tree; the previous Phase α'.4.2 migrations
(`mk [cherry]`, `mk [broom₃]`, `mk [vertex, cherry]`,
`mk [mk [cherry]]`) all had single- or two-children branches in
`inversePolyTree`. `bushy` is a three-leaf-children tree;
`inversePolyTree`'s current `(_ :: _ :: _ :: _)` recursive case
dispatches to `0` (placeholder per cycle 387's Phase α'.4.1 ship).
Closing the migration requires:

1. **A `trichildPolynomial` helper** analogous to cycle 387's
   `bichildPolynomial`. Its closed form will involve a 3-child
   cross-term + dispatch through `trichildCrossTerm` per pair
   `(t_i, t_j)` (cycle 387 / 388 / 389 pattern for the
   two-children case).
2. **A `inversePolyTree_bushy` calibration witness** that the
   recursive evaluation matches cycle 370's
   `elementaryWeightQ_phi_inv_bushy` closed form
   `v⁴ − 3v²c + 3v·b' − f bushy`.
3. **A Phase α'.4.3 scoping doc** is warranted given the new
   `trichildPolynomial` infrastructure.

Multi-cycle work — the strategy explicitly flagged this as cycle
398+ scope. After cycle 398, only the trivial Family A migrations
(`vertex`, `cherry` — currently still dispatching to
`inversePolyChain 0` / `_ 1`) remain (technically optional since
they're already in canonical form via `inversePolyChain`).

**Cycle 399+**: with `inversePolyTree` uniformly routing all 9
ladder trees, revisit cycle 365's grandfathered Sub-lemma A sorry.
The heterogeneous-stage obstacle identified in cycle 366 task
results may yield to the unified recursive structure composed with
cycle 362's
`derivativeWeightWithSrc_eq_of_strict_subtree_agreement`.

**Optional: collapse `inversePolynomial` body to a single
`inversePolyTree t f` call** once all 9 trees route uniformly. The
9-branch `if-then-else` cascade can then be replaced with a single
case where the rooted-tree pattern match is delegated entirely to
`inversePolyTree`. This is cycle 400+ refactor work.
