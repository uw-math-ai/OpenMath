# Cycle 392 strategy — Phase α'.4.1 P5: `monochildCrossTerm` infrastructure + `inversePolyTree_mkBroom₃` calibration

## §A. Big picture

Cycle 391 closed Phase α'.4.2 partial migration of `mk [vertex, cherry]`
in `inversePolynomial`. Cycle 391's task-results §"Suggested next
approach" recommended cycle 392 ship the **`monochildCrossTerm`
infrastructure** — the single-child non-leaf cross-term machinery —
to fix `inversePolyTree`'s `mk [c]` branch at non-leaf children.

The structural gap:

* `inversePolyTree (mk [broom₃]) f` currently evaluates to
  `v⁴ − 2v²c + vb' − M_broom₃` via the single-child branch
  `-(v · inversePolyTree broom₃ f) - f (mk [broom₃])`.
* Cycle 371's closed form is `v⁴ − 3v²c + vb' + 2vm − M_broom₃`.
* **Delta: `−v²c + 2vm`**, where `v = f vertex`, `c = f cherry`,
  `m = f (mk [cherry])`, `M_broom₃ = f (mk [broom₃])`.

This delta is the per-pair `monochildCrossTerm broom₃ f` value
parallel to cycle 387's `bichildCrossTerm`. Cycle 392 ships the
infrastructure (def + cycle 371 calibration witness). The actual
Phase α'.4.2 migration of `inversePolynomial`'s `mk [broom₃]` branch
is the cycle 393 follow-up (1-cycle mechanical, parallel of cycle
391's `mk [vertex, cherry]` migration).

No Aristotle results pending; sorry count stable at 5 (4 docstring +
1 grandfathered cycle 365 sorry at line 2279). §422 axiom-clean
streak: **54 substantive + 2 doc** (336–391). Target: extend to
**55 substantive + 2 doc** with cycle 392 ship.

## §B. Priority 1 — DELIVERABLE

Five concrete ships in `OpenMath/Chapter4/Section422.lean` (after
cycle 387's `bichildCrossTerm` block, line ~6283, before
`bichildPolynomial` at line ~6333):

### B.1. New def `monochildCrossTerm c f : ℝ` (~30 LOC)

```lean
/-- *Phase α'.4.1 (cycle 392) — single-child non-leaf cross-term.*

Given a child subtree `c : RT` and an elementary-weight function
`f : RT → ℝ`, `monochildCrossTerm c f` is the per-`c` polynomial
correction term that must be added to the naive single-child
`mk [c]` body `-(v · inversePolyTree c f) - f (mk [c])` so that
`inversePolyTree (mk [c]) f` matches the closed form for
`Φ_{η⁻¹}(mk [c])`.

Empirical dispatch:

* `c = vertex` → `0`. Validated by cycle 367's `cherry = mk [vertex]`
  closed form `v² - c`, which matches the naive body `-(v · -v) - f
  cherry = v² - c` directly; no correction needed.
* `c = broom₃` → `-(v² · c) + 2v · m`, where `m = f (mk [cherry])`.
  Validated by cycle 371's `mk [broom₃]` closed form `v⁴ - 3v²c +
  vb' + 2vm - M_broom₃`, which differs from the naive body
  `-(v · (-v³ + 2vc - b')) - M_broom₃ = v⁴ - 2v²c + vb' - M_broom₃`
  by exactly `-(v² · c) + 2v · m`.
* Other `c` → `0` (default; refined in cycle 393+ as more
  single-child non-leaf witnesses surface, e.g., `mk [cherry]`,
  `mk [bushy]`, `mk [mk [cherry]]`).

Mirror of cycle 387's `bichildCrossTerm` design for the
single-child case. Phase α'.4.1 P5 deliverable. -/
noncomputable def monochildCrossTerm (c : RT) (f : RT → ℝ) : ℝ :=
  if c = RootedTree.broom₃ then
    -((f RootedTree.vertex) ^ 2 * f RootedTree.cherry)
      + 2 * f RootedTree.vertex *
          f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
  else 0
```

Place this immediately after the `bichildCrossTerm` def (line ~6312)
and before the `bichildPolynomial` def docstring (line ~6314).

### B.2. Refactor `inversePolyTree`'s `[c]` branch (~3 LOC change)

The current branch (line 6362–6364):

```lean
  | OpenMath.Chapter3.Section310.RootedTree.mk [c], f =>
      -(f RootedTree.vertex * inversePolyTree c f)
        - f (OpenMath.Chapter3.Section310.RootedTree.mk [c])
```

becomes:

```lean
  | OpenMath.Chapter3.Section310.RootedTree.mk [c], f =>
      -(f RootedTree.vertex * inversePolyTree c f)
        + monochildCrossTerm c f
        - f (OpenMath.Chapter3.Section310.RootedTree.mk [c])
```

Update the def's docstring to mention the cycle 392 cross-term
refinement (parallel to cycle 387's binary-children docstring).

### B.3. Re-verify cycle 387's `inversePolyTree_cherry`

Cycle 387's calibration (line ~6386) currently closes via
`rw [inversePolyTree, inversePolyTree_vertex]; ring`. After B.2,
the `inversePolyTree` unfold produces an extra `+ monochildCrossTerm
vertex f` term. Two cases:

**Case A (likely)**: `ring` still closes because `monochildCrossTerm
vertex f` reduces definitionally to `0` (the `if-then-else` reduces
when the discriminator is `vertex ≠ broom₃`). Try first.

**Case B (fallback)**: if `ring` doesn't reduce the `if-then-else`,
insert one `rw` to fold `monochildCrossTerm vertex f = 0` first.
Recipe:

```lean
theorem inversePolyTree_cherry (f : RT → ℝ) :
    inversePolyTree RootedTree.cherry f
      = (f RootedTree.vertex) ^ 2 - f RootedTree.cherry := by
  show inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.vertex]) f
        = (f RootedTree.vertex) ^ 2 - f RootedTree.cherry
  rw [inversePolyTree, inversePolyTree_vertex,
      show monochildCrossTerm RootedTree.vertex f = 0 by
        unfold monochildCrossTerm; rw [if_neg (by decide)]]
  ring
```

### B.4. New calibration witness `inversePolyTree_mkBroom₃` (~30 LOC)

```lean
/-- *Phase α'.4.1 (cycle 392) — `mk [broom₃]` calibration witness.*

`inversePolyTree (mk [broom₃]) f` matches cycle 371's
`elementaryWeightQ_phi_inv_mkBroom₃` closed form verbatim
(under `f = elementaryWeightQ_phi η_q`). The proof unfolds the
single-child branch of `inversePolyTree`, rewrites the recursive
`inversePolyTree broom₃ f` via `inversePolyTree_broom₃`, then
exposes `monochildCrossTerm broom₃ f` via its if-then-else branch
firing (`if_pos rfl`) and closes by `ring`. -/
theorem inversePolyTree_mkBroom₃ (f : RT → ℝ) :
    inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.broom₃]) f
      = (f RootedTree.vertex) ^ 4
        - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
        + f RootedTree.vertex * f RootedTree.broom₃
        + 2 * f RootedTree.vertex *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.broom₃]) := by
  rw [inversePolyTree, inversePolyTree_broom₃]
  rw [show monochildCrossTerm RootedTree.broom₃ f
        = -((f RootedTree.vertex) ^ 2 * f RootedTree.cherry)
          + 2 * f RootedTree.vertex *
              f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        by unfold monochildCrossTerm; rw [if_pos rfl]]
  ring
```

Place this immediately after cycle 389's `inversePolyTree_broom₃`
calibration (line ~6442) and before the cycle 388
`inversePolyTree_mkCherryCherry` block (line ~6454). This keeps the
calibration order: single-child → multi-child.

### B.5. Issue file update (`def_422B_phase_alpha_prime_scoping.md`)

Append a "Cycle 392 update" subsection (parallel to the existing
cycle 381/382/383 update subsections in
`.prover-state/issues/def_422B_phase_alpha_prime_scoping.md`)
documenting:

* Phase α'.4.1 P5 ship: `monochildCrossTerm` def + `inversePolyTree_mkBroom₃`
  calibration.
* `monochildCrossTerm` infrastructure now in place for Family A
  non-leaf chain migrations (cycle 393+ targets: `mk [broom₃]`,
  `mk [bushy]`, `mk [mk [cherry]]`).
* Phase α'.4.2 migration of `inversePolynomial`'s `mk [broom₃]`
  branch deferred to cycle 393 (mechanical 1-step parallel of cycle
  391's `mk [vertex, cherry]` migration).
* §422 streak update: 54 → 55 substantive + 2 doc.

## §C. Verification protocol (cycle 391 §F precedent)

After all B.1–B.4 edits land:

1. `lake env lean OpenMath/Chapter4/Section422.lean`
   — expected: exit 0, single sorry warning at line 2279 (cycle 365
   grandfathered). Cycle 391 precedent: ~10 min.

2. `lake build OpenMath.Chapter4.Section422`
   — refresh `.olean` cache for the axiom-check round. Cycle 391
   precedent: ~8 min.

3. `#print axioms` (via a separate scratch file) on:
   * `OpenMath.Chapter4.Section422.monochildCrossTerm` (new def —
     should report no axioms or `[propext]` only)
   * `OpenMath.Chapter4.Section422.inversePolyTree_vertex` (cycle
     387 — verify regression-clean)
   * `OpenMath.Chapter4.Section422.inversePolyTree_cherry` (cycle
     387 — VERIFY regression-clean after B.2 refactor)
   * `OpenMath.Chapter4.Section422.inversePolyTree_broom₃` (cycle
     389 — verify regression-clean, uses binary-child branch so
     should be unaffected)
   * `OpenMath.Chapter4.Section422.inversePolyTree_mkCherryCherry`
     (cycle 388 — binary-child, unaffected)
   * `OpenMath.Chapter4.Section422.inversePolyTree_mkBroomCherry`
     (cycle 389 — binary-child, unaffected)
   * `OpenMath.Chapter4.Section422.inversePolyTree_mkVertexCherry`
     (cycle 390 — binary-child, unaffected)
   * `OpenMath.Chapter4.Section422.inversePolyTree_mkBroom₃` (NEW
     cycle 392 — should report `[propext, Classical.choice,
     Quot.sound]` only)
   * `OpenMath.Chapter4.Section422.inversePolyTree_mkVertexCherry_eq_inversePolynomial`
     (cycle 391 bridge — verify regression-clean)

   Expected: `[propext, Classical.choice, Quot.sound]` on every
   non-def output (axioms typically empty on `def`s).

4. `grep -c sorry OpenMath/Chapter4/Section422.lean`
   — expected: 5 (unchanged: 4 docstring + 1 code sorry at line
   2279).

## §D. Pitfalls anticipated (and mitigations)

### D.1. `ring` over `monochildCrossTerm vertex f`

After B.2, cycle 387's `inversePolyTree_cherry` proof's
`rw [inversePolyTree, inversePolyTree_vertex]; ring` produces a goal
with `+ monochildCrossTerm vertex f` in it. If `ring` cannot reduce
this if-then-else, fall back to B.3 Case B (explicit
`monochildCrossTerm vertex f = 0` rewrite via `if_neg (by decide)`
before `ring`). Cost: 1 line of extra rewrite.

### D.2. Cycle 388/389/390 binary-child witnesses

`inversePolyTree_mkCherryCherry`, `inversePolyTree_mkBroomCherry`,
`inversePolyTree_mkVertexCherry` all use the `[c₁, c₂]` binary-child
branch via `bichildPolynomial`, not the `[c]` single-child branch.
**They should be UNAFFECTED by B.2** because B.2 modifies only the
single-child branch. Verify by `#print axioms` (Step 3 above).

### D.3. Cycle 391's `mk [vertex, cherry]` migration

The cycle 391-touched theorems
(`inversePolyTree_mkVertexCherry_eq_inversePolynomial` and its
downstream consumers in `inversePolynomial_eq_of_subtree_agreement`
and the calibration witness) all consume the binary-child branch
indirectly through `inversePolynomial`'s `mk [vertex, cherry]` body
which now dispatches to `inversePolyTree (mk [vertex, cherry]) f`.
Since `mk [vertex, cherry]` is binary, **unaffected by B.2**.

### D.4. Termination check

The new `monochildCrossTerm` does NOT recurse into `inversePolyTree`.
It only calls `f` (the elementary-weight function argument) at
named small trees (`vertex`, `cherry`, `mk [cherry]`). So
`inversePolyTree`'s termination (Lean's default `sizeOf` measure on
the tree argument) is preserved after B.2.

### D.5. Default `else 0` for unmatched `c`

`monochildCrossTerm` returns `0` for `c ∉ {broom₃}`, including
`c = bushy`, `c = mk [cherry]`, etc. This means `inversePolyTree
(mk [bushy]) f`, `inversePolyTree (mk [mk [cherry]]) f`, etc. will
still differ from cycle 370/378's closed forms. **Cycle 392 ships
infrastructure only; further `monochildCrossTerm` branches are cycle
393+ targets.** Phase α'.4.1 docstring should make this clear.

### D.6. `monochildCrossTerm` definition placement

Place B.1 *immediately after* `bichildCrossTerm`'s definition (line
~6312) and *before* `bichildPolynomial`'s docstring (line ~6314).
This gives the file a symmetric structure: both cross-terms first
(`bichildCrossTerm`, `monochildCrossTerm`), then both polynomials
(but actually we don't introduce a `monochildPolynomial` — keep it
inlined into `inversePolyTree`'s `[c]` branch).

## §E. What NOT to attempt (explicit dead-end fences)

* **Do NOT** add more than the `c = broom₃` branch to
  `monochildCrossTerm` in this cycle. Other branches (`c = bushy`,
  `c = mk [cherry]`, `c = mk [mk [cherry]]`, etc.) require their
  own per-tree calibration witnesses, which is cycle 393+ work.
* **Do NOT** attempt the Phase α'.4.2 migration of
  `inversePolynomial`'s `mk [broom₃]` branch in cycle 392. That is
  the cycle 393 deliverable — defer to keep the cycle scope focused.
* **Do NOT** refactor `bichildPolynomial` to use
  `monochildCrossTerm`. The two helpers are independent (different
  arity). Keep them separate.
* **Do NOT** modify cycle 391's `inversePolyTree_mkVertexCherry_eq_inversePolynomial`
  bridge or the `inversePolynomial` body for `mk [vertex, cherry]`.
* **Do NOT** touch the cycle 365 grandfathered sorry at line 2279.
  That closure requires the full Phase α'.4 recursion (Families A,
  B, C all migrated, plus k ≥ 3 children) — multi-cycle work.
* **Do NOT** submit to Aristotle. The deliverable is pure manual
  closure (mechanical if-then-else infrastructure + one calibration
  witness that mirrors the cycle 389 broom₃ proof recipe).
* **Do NOT** add `simp` attributes to `monochildCrossTerm`. Cycle
  382's Discovery shows `simp [recursive-def, name-eq-thm]`
  over-unfolds; targeted `rw` is the consistent pattern.
* **Do NOT** introduce a `monochildPolynomial` helper paralleling
  `bichildPolynomial`. The single-child case is already compact
  inline in `inversePolyTree`'s `[c]` branch (3 lines); adding a
  helper would inflate without benefit.

## §F. LOC budget and exit criteria

* B.1 (`monochildCrossTerm` def): ~30 LOC including docstring.
* B.2 (`inversePolyTree` body refactor): +3 LOC net.
* B.3 (re-verify `inversePolyTree_cherry`): 0 LOC if Case A works,
  +1 LOC if Case B needed.
* B.4 (`inversePolyTree_mkBroom₃` calibration): ~30 LOC.
* B.5 (issue file update): ~30 LOC (markdown only, not counted in
  Lean LOC budget).
* **Total Lean LOC delta: ~63 LOC** (within ~80 LOC budget).

Exit criteria (all must hold):

1. `lake env lean OpenMath/Chapter4/Section422.lean` exits 0 with
   single cycle 365 sorry warning.
2. `lake build OpenMath.Chapter4.Section422` exits 0.
3. `grep -c sorry` = 5 (unchanged).
4. New theorem `inversePolyTree_mkBroom₃` axiom-clean
   (`[propext, Classical.choice, Quot.sound]`).
5. All seven existing calibration witnesses
   (`_vertex`, `_cherry`, `_broom₃`, `_mkCherryCherry`,
   `_mkBroomCherry`, `_mkVertexCherry`,
   `_mkVertexCherry_eq_inversePolynomial`) re-verify axiom-clean.
6. Cycle 391's `inversePolynomial` body for `mk [vertex, cherry]`
   untouched.
7. Issue file update appended.

## §G. Graceful degradation

If the `ring` step in cycle 387's `inversePolyTree_cherry` does NOT
close even after B.3 Case B, the issue is a deeper reduction failure
in the `if_neg`-discharged `monochildCrossTerm` body. Mitigations
in order:

1. Try `simp only [monochildCrossTerm, if_neg (by decide)]; ring`
   instead of two separate `rw`s.
2. Try `conv_lhs => rw [show monochildCrossTerm RootedTree.vertex
   f = 0 from by ...]` to scope the rewrite cleanly.
3. As a last resort, split `monochildCrossTerm` into two named
   theorems `monochildCrossTerm_vertex` (= `0`) and
   `monochildCrossTerm_broom₃` (= explicit formula), and use those
   instead of the if-then-else dispatch in calibrations.

If B.4's `inversePolyTree_mkBroom₃` proof doesn't close on first
attempt, the most likely issue is the `show` form not matching the
LHS after the `rw [inversePolyTree, inversePolyTree_broom₃]` step.
Mitigation: insert a `show` block to canonicalise the goal before
the `monochildCrossTerm` rewrite. Cycle 389 `inversePolyTree_broom₃`
uses two `show` blocks (lines 6423 and 6434) for similar purposes;
follow that pattern if needed.

If the cycle stalls completely (>2 hours without a clean compile),
**ship B.1 + B.2 + B.3 only** (skip B.4); cycle 393 picks up the
calibration. Sorry count unchanged; the infrastructure ships axiom-
clean even without the new witness. This is the cycle 391 Step 5
precedent (consumer breakage handled in-cycle, calibration deferred
to next).

## §H. Cycle 393+ outlook

After cycle 392 ships `monochildCrossTerm` + `inversePolyTree_mkBroom₃`,
the natural next deliverables are:

* **Cycle 393 (Family A migration #1)**: ship Phase α'.4.2
  migration of `inversePolynomial`'s `mk [broom₃]` branch via a
  bridge theorem `inversePolyTree_mkBroom₃_eq_inversePolynomial`
  + consumer updates (calibration witness + Phase β bridge + Phase
  γ branch). Mechanical 1-cycle ship parallel to cycle 391. ~45 LOC.

* **Cycle 394 (extend `monochildCrossTerm`)**: add a branch for
  `c = mk [cherry]`. Cycle 378's closed form for `mk [mk [cherry]]`
  is `v⁴ - 3v²c + c² + 2vm - M_mkMkCherry`. Compute the delta from
  the naive body and ship `monochildCrossTerm_mkCherry`. Then ship
  `inversePolyTree_mkMkCherry` calibration.

* **Cycle 395 (Family A migration #2)**: ship Phase α'.4.2 migration
  of `inversePolynomial`'s `mk [mk [cherry]]` branch.

* **Cycle 396 (extend `monochildCrossTerm` for `c = bushy`)**: ship
  branch for `mk [bushy]` (Family A, cycle 370 closed form
  generalisation).

* **Cycles 397+**: Phase α'.4.2 migrations of `inversePolynomial`'s
  `bushy`, `broom₃`, etc. branches (Family B is already done by
  cycle 383). Eventually all 8 ladder trees use the recursive
  `inversePolyTree` dispatch, and the cycle 365 grandfathered sorry
  becomes attackable via the unified recursive `inversePolyTree`.

The cycle 365 sorry closure is still ~10+ cycles out per cycle 391
projection.

## §I. Self-reference

Cycle 392 worker: ship B.1–B.4 in order, verify with §C protocol,
update §B.5 issue file. Report all five exit criteria as either
PASS or specify the graceful-degradation fallback used.

Expected runtime: ~30 min wall (2× `lake env lean` + 1× `lake build`
+ axiom check round + minor edits per §C precedent).

§422 streak target: **54 → 55 substantive + 2 doc** (336–392).
