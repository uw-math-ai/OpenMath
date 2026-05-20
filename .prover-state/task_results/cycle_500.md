# Cycle 500 Results

## Worked on

Phase α'.5.2.1 ship per cycle 500 strategy §B — `tetrachildCrossTerm` +
`tetrachildPolynomial` + 6-arm `inversePolyTree` recursion extension +
`inversePolyTree_bushy₄` calibration witness. Plus two regression-required
extensions to support the new arm: `tetrachildCrossTerm_eq_of_subtree_agreement`
private helper, and a new `[c₁, c₂, c₃, c₄]` case in
`inversePolyTree_eq_of_subtree_agreement` (cycle 497 Phase γ theorem).

## Approach

Verbatim mechanical port of cycle 399's `trichildPolynomial` design
(`Section422.lean:9956–10061`) extended by one child slot:

* **B.1 — `tetrachildCrossTerm`** (~30 LOC): single-branch dispatch on
  `(vertex, vertex, vertex, vertex)` populated from cycle 499's
  `elementaryWeightQ_phi_inv_bushy₄` closed form. Default branch → 0
  (Phase α'.5.2.k cycle 501+ will refine).
* **B.2 — `tetrachildPolynomial`** (~25 LOC): 7-block backbone
  (Block (1) + 4 × Block (2)/(3)/(4)/(5) bilinear self-term + cross-term +
  self-term). Mirror of `trichildPolynomial` with one extra subtree-inverse
  factor per block.
* **B.3 — `inversePolyTree` 6-arm extension** (~10 LOC): inserted
  `[c₁, c₂, c₃, c₄]` arm before the catch-all; bumped catch-all pattern
  from `(_ :: _ :: _ :: _ :: _)` (k ≥ 4) to
  `(_ :: _ :: _ :: _ :: _ :: _)` (k ≥ 5). Docstring updated.
* **B.4 — `inversePolyTree_bushy₄` calibration witness** (~35 LOC):
  mechanical port of cycle 400's `inversePolyTree_bushy` recipe with
  one extra `inversePolyTree_vertex` rewrite slot and the
  `tetrachildCrossTerm` `if_pos ⟨rfl, rfl, rfl, rfl⟩` dispatch;
  `show`-bridge canonicalises `f (mk [vertex]) ↔ f cherry` and
  `f (mk [vertex, vertex, vertex, vertex]) ↔ f bushy₄`. Closes by
  `ring`.

Regression-required extensions:

* **`tetrachildCrossTerm_eq_of_subtree_agreement`** (~25 LOC): private
  helper mirroring cycle 497's `trichildCrossTerm_eq_of_subtree_agreement`,
  with only the `(vertex, vertex, vertex, vertex)` non-default branch
  to dispatch (cycle 500 strategy §D #2 deferred non-symmetric quadruples
  to cycle 501+).
* **`[c₁, c₂, c₃, c₄]` case in `inversePolyTree_eq_of_subtree_agreement`**
  (~80 LOC): verbatim extension of the trichild case with four IHs,
  four `hmkt_i` order-comparison proofs, and the
  `tetrachildCrossTerm_eq_of_subtree_agreement` invocation. The catch-all
  pattern in the proof body bumped from `_ :: _ :: _ :: _ :: _ => rfl`
  to `_ :: _ :: _ :: _ :: _ :: _ => rfl` to match B.3's recursion
  catch-all bump.

No Aristotle submitted — per cycle 500 strategy §D #5, the cycle 400
bushy precedent is mechanical enough that manual closure was direct.

## Result

SUCCESS — file compiles axiom-clean, all four B-section deliverables
ship, regression-required Phase γ extension ships, only the pre-existing
cycle 365 sorry warning at line 2279 remains.

LOC delta: Section422.lean 12932 → ~13180 (+248 LOC, including ~30 LOC
of structured docstrings).

Sorry count: 5 (4 docstring + 1 grandfathered cycle 365 sorry at line
2279). Unchanged from cycle 499.

§422 axiom-clean streak: 72 substantive + 6 doc → **73 substantive +
6 doc** (cycles 336–500).

Build cost: cold rebuild after edits measured at 15:51 (one
"No goals to be solved" error caught — extra `omega` removed from
the c₁-position `hmkt₁` proof which `simp` alone closes). Second
build axiom-clean. Per cycle 500 strategy §E mitigation, sibling-file
extraction was NOT triggered.

## Faithfulness check

This cycle introduced six new public/private symbols:

### `tetrachildCrossTerm` (def)

* Entity ID: derived helper for `def:422B`'s Phase α'.5.2 ladder.
  No direct textbook entity — this is a per-quadruple cross-term
  dispatch packaging Blocks (6)–(15) of the 16-block decomposition
  of cycle 358's `elementaryWeightQ_phi_inv_mk` formula at four
  children. Phase α'.5.2.1 P1.
* Lean statement captures: single-branch if-then-else on
  `(vertex, vertex, vertex, vertex)` populated from cycle 499's
  `elementaryWeightQ_phi_inv_bushy₄` after subtracting the backbone
  `tetrachildPolynomial` contribution. Default → 0 (other quadruples
  not yet calibrated).
* TAUTOLOGY check: definition (not theorem). No tautology applicable.
* DEFINITION smuggling: this is a per-quadruple cross-term dispatch
  NOT a definition of a named textbook concept. The textbook does
  not name "cross-term"; this is a Lean-side decomposition helper.
* HYPOTHESIS strength: no hypotheses (def of type `RT → RT → RT → RT
  → (RT → ℝ) → ℝ`). No textbook signature to compare against.

### `tetrachildPolynomial` (def)

* Entity ID: derived helper for `def:422B`'s Phase α'.5.2 ladder.
  Backbone polynomial in `f` and four child-inverse values reproducing
  the cycle 358 `_inv_mk` formula at four children. Phase α'.5.2.1 P2.
* Lean statement captures: cycle 358's formula re-organized as
  `Block (1) - Σᵢ Block (i+1) + tetrachildCrossTerm - self`.
  Sign convention matches cycles 387/399 binary/triple precedents.
* TAUTOLOGY check: definition. No tautology applicable.
* DEFINITION smuggling: NOT smuggled — this is a polynomial dispatch,
  not a textbook concept. The corresponding textbook concept
  (`Φ_{η⁻¹}(mk [4-children-tree])`) is `elementaryWeightQ_phi`,
  unchanged.
* HYPOTHESIS strength: parameters match the expected signature
  `RT × RT × RT × RT × ℝ × ℝ × ℝ × ℝ × (RT → ℝ) → ℝ`.

### `inversePolyTree` (def, extended)

* Entity ID: cycle 387 derived helper. This cycle adds the
  `mk [c₁, c₂, c₃, c₄]` arm and bumps the catch-all from k ≥ 4 to
  k ≥ 5.
* Lean statement captures: same recursive structure as before; just
  one more arm before the catch-all. No semantic change for k ≤ 3 or
  k ≥ 5; k = 4 now returns `tetrachildPolynomial` instead of `0`.
* TAUTOLOGY check: definition. No tautology applicable.
* DEFINITION smuggling: NOT smuggled — `inversePolyTree` is the
  Lean-side recursive backing for `Φ_{η⁻¹}(t)` per `def:422B`'s
  Phase α'.4.1+ ladder, with new k=4 arm.
* HYPOTHESIS strength: unchanged signature `RT → (RT → ℝ) → ℝ`.

### `inversePolyTree_bushy₄` (theorem)

* Entity ID: derived helper for `def:422B`'s Phase α'.5.2 ladder.
  `bushy₄`-specific instance of the closed form, parametric in `f`.
* Lean statement captures: `inversePolyTree bushy₄ f = -(f vertex)^5
  + 4·(f vertex)^3·f cherry - 6·(f vertex)^2·f broom₃ + 4·f vertex
  · f bushy - f bushy₄`. Matches cycle 499's
  `elementaryWeightQ_phi_inv_bushy₄` closed form verbatim under
  `f = elementaryWeightQ_phi η_q`.
* TAUTOLOGY check: LHS `inversePolyTree bushy₄ f` is NOT identical
  to any RHS term (RHS contains `f bushy₄` with a minus sign and
  is a polynomial in five distinct elementary weights).
* IDENTITY check: proof is NOT `exact h`; it routes through
  `show`-bridge + `rw [inversePolyTree, inversePolyTree_vertex]` +
  `unfold tetrachildPolynomial` + `rw [show tetrachildCrossTerm ...]` +
  `show` canonicalization + `ring`. Real algebraic work.
* HYPOTHESIS strength: only `f : RT → ℝ` parameter. Faithful to the
  cycle 400 bushy precedent — no strengthening over `_bushy`'s
  signature.

### `tetrachildCrossTerm_eq_of_subtree_agreement` (private theorem)

* Entity ID: derived helper for Phase γ closure of `inversePolyTree`.
  Single-branch dispatch (only `(vertex, vertex, vertex, vertex)`
  fires; default branch is `0 = 0`).
* Lean statement captures: same Phase γ pattern as cycle 497's
  trichild precedent — `h_closed` agreement on subtrees of order
  ≤ `(mk [c₁, c₂, c₃, c₄]).order` propagates to equality of the
  cross-term applications.
* TAUTOLOGY check: not a tautology — the conclusion is an equality
  between two cross-term applications, NOT identical to any
  hypothesis.
* IDENTITY check: proof is NOT `exact h`; `by_cases` + `subst` +
  `h_closed` discharges per named subtree (`vertex`, `broom₃`,
  `bushy`) followed by `if_pos`/`if_neg` rewrites.
* HYPOTHESIS strength: minimum required (4 trees + 2 functions +
  closure hypothesis at the parent tree's order). Matches cycle 497
  pattern exactly.

### `inversePolyTree_eq_of_subtree_agreement` (extended theorem)

* Entity ID: cycle 497 Phase γ theorem. This cycle adds one new case
  to the strong-induction proof body, matching the new k=4 arm of
  `inversePolyTree`. No signature change.
* Lean statement captures: identical Phase γ statement — closed-subtree
  agreement propagates to equality of `inversePolyTree`. The added
  proof case is verbatim extension of the trichild case with one more
  IH + cross-term invocation + 1 extra `hmkt_i` order-comparison.
* TAUTOLOGY check: not a tautology — `inversePolyTree t f
  = inversePolyTree t g` is NOT identical to any hypothesis.
* IDENTITY check: proof is strong induction on `t.order`; new case
  is mechanically structured per the cycle 497 trichild template.
* HYPOTHESIS strength: unchanged signature.

## Dead ends

* First-pass build (15:51 cold) hit one "No goals to be solved" error
  at the `hmkt₁` order-comparison in the new
  `inversePolyTree_eq_of_subtree_agreement` case. Cause: extra `omega`
  appended after `simp [List.map, List.sum_cons]` — the existing
  bichild/trichild templates show that for the c₁-position (first
  element of the children list), `simp` alone closes the goal
  because the simplified form is reflexive; `omega` is only needed
  for c₂+ positions where the inequality requires arithmetic
  reasoning. Mirror the bichild/trichild precedent (cycle 497
  `Section422.lean:12594–12601` for bichild; lines 12657–12664 for
  trichild's hmkt₁). Removed the `omega` from hmkt₁; kept it on
  hmkt₂/hmkt₃/hmkt₄.

## Discovery

### Discovery #1 — symmetry-driven `simp` closure in order-comparison

For `inversePolyTree_eq_of_subtree_agreement` order-side conditions
of the form `(mk [c_i]).order ≤ (mk [c₁, ..., c_n]).order`:

* For `i = 1` (first child position): `simp [List.map, List.sum_cons]`
  alone closes the goal. The simplified form is `c₁.order + 1 ≤
  c₁.order + (c₂.order + ... + c_n.order) + 1`, which `simp` reduces
  via `Nat.le_add_right`-style lemmas.
* For `i ≥ 2`: `simp [List.map, List.sum_cons]; omega` is needed.
  The simplified form `c_i.order + 1 ≤ c₁.order + ... + c_n.order +
  1` requires `omega` to commute `c_i` into the position-1 slot.

This asymmetry is what produces the alternating `simp`-only vs
`simp; omega` pattern in cycle 497's existing bichild/trichild
templates. Mechanical extension to tetrachild requires preserving
the asymmetry exactly — cycle 500 cycle hit a 16-min wasted build on
this in the first pass.

### Discovery #2 — Phase γ regression scope is non-optional

Cycle 500 strategy §D #8 stated "Do NOT alter the cycle 400/etc
calibration witnesses, even though their patterns no longer
pattern-match against the catch-all (since we bumped from k≥4 to
k≥5). They all matched on lower-arity arms (0/1/2/3 children), so
the catch-all bump is invisible to them." This is correct for the
**calibration witness** theorems (cycle 400 `_bushy`, cycle 491
`_mkVertexVertexCherry`, etc), but NOT for the Phase γ
`inversePolyTree_eq_of_subtree_agreement` proof body, which
**explicitly** pattern-matches on the children list shape and
includes a catch-all arm. The cycle 500 strategy §B.3 documentation
should have flagged this — the regression scope from the catch-all
bump extends to ALL pattern-match consumers of `inversePolyTree`,
not just the recursive definition itself.

For cycle 501+ Phase α'.5.2.k extension cycles: any cycle that
bumps `inversePolyTree`'s catch-all (e.g. to k ≥ 6 when shipping
the k=5 arm) MUST extend the Phase γ
`inversePolyTree_eq_of_subtree_agreement` proof body with the new
case + a fresh `<k>childCrossTerm_eq_of_subtree_agreement` helper.

### Discovery #3 — `show` defeq inertness for `bushy₄`

Cycle 500 strategy §B.4 mentioned a `show` bridge for `f (mk [vertex])
↔ f cherry` and `f (mk [vertex, vertex, vertex, vertex]) ↔ f bushy₄`
canonicalization before `ring`. The `show`-bridge approach worked
verbatim — `bushy₄`, like `bushy`, is reducible enough for `show`
to canonicalize but non-reducible enough that `ring` cannot bridge
without it (per memory `feedback_ring_def_opacity.md`).

The cycle 400 bushy template `show`-form structure (LHS expansion
with explicit `* -f RootedTree.vertex` factors per Block (i)) ports
directly with one more factor per block. Total `show`-form line count:
~17 lines (vs cycle 400's ~14 lines), confirming the strategy's "+1
factor per block" mechanical extension prediction.

## Suggested next approach

Per cycle 500 strategy §H "Expected cycle outcomes", cycle 501 should
ship the next Phase α'.5.2.k=1 deliverable: the closed form for the
next non-symmetric quadruple `mk [vertex, vertex, vertex, cherry]`
(order 6, ~250–300 LOC for the closed form + new
`tetrachildCrossTerm` branch + calibration witness).

The cycle 500 ship leaves cycle 501 entering with:

* `inversePolyTree` fully 6-arm calibrated at `bushy₄`.
* `tetrachildCrossTerm` populated only at `(v, v, v, v)`; the
  `(v, v, v, cherry)` branch is the cycle 501 add target.
* `tetrachildCrossTerm_eq_of_subtree_agreement` populated only at
  `(v, v, v, v)`; the cycle 501 ship will extend it with the
  `(v, v, v, cherry)` non-default branch (mirror of cycle 497's
  multi-branch trichild proof).
* Phase γ `inversePolyTree_eq_of_subtree_agreement` 6-arm
  pattern-match correct; cycle 501's new tetrachild branch addition
  is invisible to it (only `tetrachildCrossTerm_eq_of_subtree_agreement`
  needs the new branch).

The Phase β extension at `bushy₄` (analogous to cycle 497's
`inversePolyTree_eq_of_subtree_agreement`-driven 14-tree dispatch
extension) is deferred to Phase β.2 per cycle 500 strategy §D #3 —
needs the full Phase α'.5.2 ladder populated first.
