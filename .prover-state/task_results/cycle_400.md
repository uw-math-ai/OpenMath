# Cycle 400 Results

## Worked on

Phase α'.4.1 P9 — `inversePolyTree_bushy` calibration witness in
`OpenMath/Chapter4/Section422.lean` per cycle 398 scoping doc
(`.prover-state/issues/def_422B_phase_alpha_prime_family_bushy_scoping.md`)
§6.2 deliverable, completing the bushy infrastructure shipped in
cycle 399.

One new public theorem:

* **`inversePolyTree_bushy : ∀ f : RT → ℝ,
  inversePolyTree RootedTree.bushy f
    = (f vertex)^4 − 3 · (f vertex)^2 · f cherry
      + 3 · f vertex · f broom₃ − f bushy`** — confirms that cycle 399's
  `trichildPolynomial`/`trichildCrossTerm` backbone, when stepped through
  `inversePolyTree`'s new triple-children arm at `bushy = mk [vertex,
  vertex, vertex]`, reproduces cycle 370's `elementaryWeightQ_phi_inv_bushy`
  closed form (under `f := elementaryWeightQ_phi η_q`).

Inserted at line 6649 (immediately after cycle 395's
`inversePolyTree_mkMkCherry` ship, grouping all order-4 ladder-tree
calibrations).

## Approach

1. **Pre-flight verification** per strategy §0: confirmed cycle 399's
   trichild infrastructure is at HEAD (`git log` shows commit
   `bcb2b92`; `grep` confirms `trichildCrossTerm` at line 6410 and
   `trichildPolynomial` at line 6439; `wc -l = 8101`). Cycle 399
   supervisor verdict was the documented phantom-commit pattern;
   proceeded directly to §1.
2. **Followed strategy §1 recipe verbatim** initially: outer `show` to
   unfold `bushy := mk [vertex, vertex, vertex]`, then
   `rw [inversePolyTree, inversePolyTree_vertex × 3]`, then
   `unfold trichildPolynomial`, then inner `rw [show trichildCrossTerm
   vertex vertex vertex f = 3·f vertex·f broom₃ by …]`, inner `show`
   bridge for `f (mk [vertex]) ↔ f cherry` and `f (mk [vertex,
   vertex, vertex]) ↔ f bushy`, then `ring`.
3. **First build failed** on the triple `inversePolyTree_vertex`
   rewrite — `rw [inversePolyTree_vertex]` rewrites ALL three
   occurrences in a single step (default `rw` behavior is to rewrite
   all matches), so the 2nd and 3rd applications fail with "no
   occurrences". Fixed by collapsing to a single
   `rw [inversePolyTree_vertex]` (matches cycle 389's
   `inversePolyTree_broom₃` precedent — same pattern, two vertex
   children, single `rw [inversePolyTree_vertex]` covers both).
4. **Skipped Aristotle submissions** per strategy §3: no `sorry`s to
   mine; pure mechanical proof.
5. **Skipped explicit-Euler `example`** per strategy §2: redundant
   non-vacuity content given the calibration theorem already pins
   down the closed form symbolically.

## Result

SUCCESS — `lake env lean OpenMath/Chapter4/Section422.lean` exits 0
with only the pre-existing grandfathered cycle 365 sorry warning at
line 2272. Build time ~10 min on warm cache (consistent with cycle
399's discovery on 5-arm `inversePolyTree` recursion's elaboration
overhead).

LOC delta: 8101 → 8150 (+49 LOC, within the strategy's ~30–35 LOC
target after counting the full docstring). Sorry count unchanged at
5 (4 docstring + 1 grandfathered cycle 365 code at line 2272).

§422 axiom-clean streak advances: 61 substantive + 3 doc
(cycles 336–399) → **62 substantive + 3 doc** (cycles 336–400).
`#print axioms` verification on `inversePolyTree_bushy` returns the
canonical `[propext, Classical.choice, Quot.sound]` triple (no
`sorryAx`, no new axioms).

All 11 existing `inversePolyTree_*` calibration witnesses
(`_vertex, _cherry, _broom₃, _mkBroom₃, _mkCherry, _mkMkCherry,
_mkCherryCherry, _mkBroomCherry, _mkVertexCherry`) continue to pass
— their match patterns do not unify against the new triple-children
arm and were undisturbed.

## Faithfulness check

One new theorem introduced this cycle.

### `inversePolyTree_bushy`

* Entity ID: `def:422B` (continuing the §422 underlying one-step-method
  work track via Phase α' infrastructure).
* Textbook anchor: cycle 370's `elementaryWeightQ_phi_inv_bushy`
  closed form
  > `elementaryWeightQ_phi (η_q⁻¹) RootedTree.bushy
  >   = (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 4
  >     − 3 · (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
  >         · elementaryWeightQ_phi η_q RootedTree.cherry
  >     + 3 · elementaryWeightQ_phi η_q RootedTree.vertex
  >         · elementaryWeightQ_phi η_q RootedTree.broom₃
  >     − elementaryWeightQ_phi η_q RootedTree.bushy`
* Lean statement captures: **same content** — under `f :=
  elementaryWeightQ_phi η_q`, the cycle 400 RHS literally matches
  cycle 370's RHS verbatim. The cycle 400 theorem abstracts over `f`
  (so it applies to any `RT → ℝ` function, not just elementary-weight
  evaluations); the textbook closed form is recovered by specialising
  `f := elementaryWeightQ_phi η_q` and invoking cycle 370's bridge
  (to be wired up by cycle 401's `inversePolynomial` migration).
* Definition smuggling: PASS — the theorem is a pure consequence of
  cycle 399's `trichildPolynomial`/`trichildCrossTerm` definitions
  evaluated at `(vertex, vertex, vertex)` via the new triple-children
  arm of `inversePolyTree`. No structural fields encoded as
  hypotheses.
* Tautology check: PASS — the conclusion is a closed-form algebraic
  equation; no hypothesis appears verbatim in the conclusion.
* Identity check: PASS — the proof is a substantive 4-step
  `show + rw + unfold + ring` chain, not `exact h`.
* Hypothesis strength: PASS — no hypotheses (universally quantifies
  over `f : RT → ℝ` only); matches textbook's universal claim.

## Dead ends

* **Triple `rw [inversePolyTree_vertex]` failed** — the strategy
  recipe (and cycle 399's suggested-next-approach block) prescribed
  `rw [inversePolyTree, inversePolyTree_vertex, inversePolyTree_vertex,
  inversePolyTree_vertex]`, but `rw`'s default behavior rewrites all
  occurrences of the pattern in a single application. The first
  `rw [inversePolyTree_vertex]` consumed all three
  `inversePolyTree vertex f` calls; the 2nd and 3rd applications
  threw "Did not find an occurrence". Collapsing to a single
  `rw [inversePolyTree_vertex]` (cycle 389 broom₃ precedent) closed
  cleanly.

## Discovery

* **`rw` rewrites all occurrences in one go** — confirmed empirically
  on the triple-vertex pattern. For recursive-def proofs with k
  identical recursive calls (e.g. `bushy` with 3 vertex children,
  cycle 401+ work on `bushy₄ = mk [vertex × 4]` with 4 vertex
  children), prefer a single `rw [inversePolyTree_vertex]` regardless
  of k. The strategy's prescribed k-fold repetition was a literal
  mis-copy of the bichild template; the bichild template had 2
  vertex children but its `rw [inversePolyTree_vertex]` actually
  covers both. Future planner recipes should avoid the k-fold
  repetition pattern.
* **`show` bridges `cherry`/`bushy` cleanly in a single step** —
  per memory `feedback_ring_def_opacity.md`, `ring` cannot canonicalise
  `f (mk [vertex])` ↔ `f cherry` or `f (mk [vertex, vertex, vertex])`
  ↔ `f bushy` directly. The single inner `show ... = ...` bridge in
  cycle 400's proof handles BOTH foldings in one pass — `cherry` is
  single-layer defeq (one `mk` unfold) and `bushy` is also single-
  layer defeq (one `mk` unfold). Cycle 389's broom₃ proof used TWO
  inner `show`s but that appears to be a stylistic choice for
  readability; one-show works here.
* **No `bushy` defeq depth issues** — the bushy/cherry/broom₃ all
  flatten to one `mk` unfold each, so the planner's worry about
  "non-reducible def" depth doesn't bite at order ≤ 4. Cycle 401+
  work on `bushy₄` (order-5) will use the same one-show bridge
  pattern.

## Suggested next approach

**Cycle 401** (Phase α'.4.2 P5) per scoping doc §6.3 — migrate
`inversePolynomial`'s `bushy` branch from cycle 383's
`inversePolyBroom 3 f` dispatch to a `inversePolyTree bushy f`
dispatch. Mechanical mirror of cycle 397's `mk [mk [cherry]]`
migration recipe:

1. New bridge theorem `inversePolyTree_bushy_eq_inversePolynomial`
   via `unfold inversePolynomial + N if_neg + if_pos rfl` (count
   `if_neg`s based on `bushy`'s position in `inversePolynomial`'s
   if-then-else dispatch chain).
2. `inversePolynomial`'s `bushy` branch body migrated from
   `inversePolyBroom 3 f` to `inversePolyTree bushy f`.
3. Phase α.2 calibration `example` at `bushy` updated to trail
   `inversePolyTree_bushy`.
4. Phase β.3 bridge `elementaryWeightQ_phi_inv_eq_inversePolynomial_bushy`
   updated.
5. Phase γ branch in `inversePolynomial_eq_of_subtree_agreement` for
   `bushy` updated.
6. Cycle 382's `inversePolyBroom_three_eq_inversePolynomial` proof
   body extended.

Estimated ~50 LOC.

After cycle 401: all 9 ladder trees route uniformly through
`inversePolyTree`. Cycle 402+ revisits the grandfathered cycle 365
Sub-lemma A sorry under the unified recursive structure.
