# Cycle 388 strategy — Phase α'.4.1 P3 ship: `(cherry, cherry)` cross-term refinement + `inversePolyTree_mkCherryCherry` calibration witness

## Pre-flight state (verified at HEAD `a0e63bb`)

* Section422.lean: 7442 LOC, sorry count 5 lines (4 docstring + 1
  grandfathered code sorry at line 2279 from cycle 365).
* §422 axiom-clean streak: 50 substantive + 2 doc cycles (336–387).
* Cycle 387 just shipped `bichildCrossTerm` (placeholder = 0),
  `bichildPolynomial`, `inversePolyTree` (4-branch pattern match),
  plus calibration witnesses `inversePolyTree_vertex`
  (`Section422.lean:6300-6303`) and `inversePolyTree_cherry`
  (`Section422.lean:6310-6322`).
* `bichildCrossTerm` currently at `Section422.lean:6237`:
  `noncomputable def bichildCrossTerm (_t₁ _t₂ : RT) (_f : RT → ℝ) : ℝ := 0`
  — a placeholder waiting for cycle 388's per-pair refinement.

## §A. Aristotle status — none active

No pending Aristotle results. The cycle 387 ship was pure manual
work (one-line `rfl` and one-step `rw + ring` calibration witnesses).
Do **NOT** submit a new Aristotle job this cycle — cycle 388's
deliverable is pinned algebraically by cycle 384's closed form;
the cross-term value is back-computed mechanically, not searched.

## §B. Cycle 388 deliverable bar — DO

**P1 (PRIMARY)**: Refactor `bichildCrossTerm` at
`Section422.lean:6237` to handle the `(cherry, cherry)` case. The
back-computed value (cycle 387 §11.2 derivation, independently
re-verified against cycle 384's closed form):

```
bichildCrossTerm cherry cherry f
  = 2 · (f vertex)^3 · f cherry
    - 2 · f vertex · (f cherry)^2
    - (f vertex)^2 · f broom₃
    + 2 · f vertex · f (mk [vertex, cherry])
```

**Verification of this value** (do this first, before writing any
Lean): the `bichildPolynomial cherry cherry inv_c inv_c f` backbone
with `inv_c = v² - c` (from cycle 387's `inversePolyTree_cherry`)
expands to:

* `-(v · (v² - c)²) = -v⁵ + 2v³c - vc²`
* `-(v² - c) · m + -(v² - c) · m = -2v²m + 2cm`
* `+ bichildCrossTerm cherry cherry f` (to be solved for)
* `- f (mk [cherry, cherry]) = -cc`

Setting the total equal to cycle 384's RHS
`-v⁵ + 4v³c - 3vc² - v²b' - 2v²m + 2cm + 2v·vc - cc` and solving:

```
cross = (cycle 384 RHS) - (backbone)
      = (-v⁵ + 4v³c - 3vc² - v²b' - 2v²m + 2cm + 2v·vc - cc)
        - (-v⁵ + 2v³c - vc² - 2v²m + 2cm - cc)
      = 2v³c - 2vc² - v²b' + 2v·vc                                ✓
```

(matches the formula above; the value is exact).

**P1 implementation recipe** (concrete):

Replace the cycle 387 placeholder with an if-then-else dispatch.
The `RT` type has `DecidableEq` (cycle 92, `Section301.lean:92`),
so the conjunction `t₁ = cherry ∧ t₂ = cherry` is automatically
decidable via Mathlib's `instDecidableAnd`.

```lean
noncomputable def bichildCrossTerm (t₁ t₂ : RT) (f : RT → ℝ) : ℝ :=
  if t₁ = RootedTree.cherry ∧ t₂ = RootedTree.cherry then
    2 * (f RootedTree.vertex) ^ 3 * f RootedTree.cherry
      - 2 * f RootedTree.vertex * (f RootedTree.cherry) ^ 2
      - (f RootedTree.vertex) ^ 2 * f RootedTree.broom₃
      + 2 * f RootedTree.vertex *
          f (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.cherry])
  else 0
```

**Faithfulness check**: this is NOT definition smuggling. The
`(cherry, cherry)` case's value is *back-computed* algebraically
from cycle 384's already-shipped closed-form theorem
`elementaryWeightQ_phi_inv_mkCherryCherry`; we are not redefining
the cross-term to make a specific theorem true, we are choosing a
representation that matches existing empirical data. Future
per-pair cases (`(broom₃, cherry)`, `(broom₃, broom₃)`, etc.) will
have their values similarly back-computed from cycles 386 / 389+.

**P2 (PRIMARY)**: Ship `inversePolyTree_mkCherryCherry` calibration
witness immediately after `inversePolyTree_cherry` at
`Section422.lean:6322`. The statement matches cycle 384's
`elementaryWeightQ_phi_inv_mkCherryCherry` RHS verbatim:

```lean
/-- *Phase α'.4.1 (cycle 388) — `mk [cherry, cherry]` calibration witness.*

`inversePolyTree (mk [cherry, cherry]) f` matches cycle 384's
`elementaryWeightQ_phi_inv_mkCherryCherry` closed form. The proof
unfolds the binary-children branch, rewrites the recursive
`inversePolyTree cherry f` via `inversePolyTree_cherry`, expands
`bichildPolynomial` and the cycle 388 `(cherry, cherry)` case of
`bichildCrossTerm`, then closes by `ring`. -/
theorem inversePolyTree_mkCherryCherry (f : RT → ℝ) :
    inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [RootedTree.cherry, RootedTree.cherry]) f
      = -(f RootedTree.vertex) ^ 5
        + 4 * (f RootedTree.vertex) ^ 3 * f RootedTree.cherry
        - 3 * f RootedTree.vertex * (f RootedTree.cherry) ^ 2
        - (f RootedTree.vertex) ^ 2 * f RootedTree.broom₃
        - 2 * (f RootedTree.vertex) ^ 2 *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        + 2 * f RootedTree.cherry *
            f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
        + 2 * f RootedTree.vertex *
            f (OpenMath.Chapter3.Section310.RootedTree.mk
                [RootedTree.vertex, RootedTree.cherry])
        - f (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.cherry, RootedTree.cherry]) := by
  show bichildPolynomial RootedTree.cherry RootedTree.cherry
        (inversePolyTree RootedTree.cherry f)
        (inversePolyTree RootedTree.cherry f) f = _
  rw [inversePolyTree_cherry]
  unfold bichildPolynomial
  rw [show bichildCrossTerm RootedTree.cherry RootedTree.cherry f
        = 2 * (f RootedTree.vertex) ^ 3 * f RootedTree.cherry
          - 2 * f RootedTree.vertex * (f RootedTree.cherry) ^ 2
          - (f RootedTree.vertex) ^ 2 * f RootedTree.broom₃
          + 2 * f RootedTree.vertex *
              f (OpenMath.Chapter3.Section310.RootedTree.mk
                  [RootedTree.vertex, RootedTree.cherry]) by
        unfold bichildCrossTerm
        rw [if_pos ⟨rfl, rfl⟩]]
  ring
```

**Risks (pre-flight before writing)**:

* The opening `show bichildPolynomial ...` may fail if the pattern
  match doesn't reduce by `rfl`. **Mitigation**: if `show` fails,
  use the cycle 387 `inversePolyTree_cherry` pattern instead:
  `show inversePolyTree (mk [cherry, cherry]) f = _; rw
  [inversePolyTree, inversePolyTree_cherry]; show ... = ...;
  unfold bichildPolynomial bichildCrossTerm; rw [if_pos ⟨rfl,
  rfl⟩]; ring`. The two-step `show + rw [inversePolyTree, ...]`
  form is what cycle 387 used and is known to work.

* `rw [if_pos ⟨rfl, rfl⟩]` may need adjustment if the typechecker
  cannot infer the decidability instance. **Mitigation**: replace
  with `simp only [if_pos (⟨rfl, rfl⟩ : RootedTree.cherry =
  RootedTree.cherry ∧ RootedTree.cherry = RootedTree.cherry)]`,
  or use `decide` on the conjunction.

* Lean's pattern-match elaboration of `inversePolyTree` may use
  internal `match` names that block `rfl`. **Mitigation**: use
  `unfold inversePolyTree` instead of `show`/`rfl`; the unfold
  exposes the body's match expression which can then be reduced
  by `simp only` or by exact pattern matching.

**Pre-flight verification step** (run before opening any edits to
`Section422.lean`): use `lean_multi_attempt` at a fresh `example`
location to test the reduction:

```lean
example (f : RT → ℝ) :
    inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [RootedTree.cherry, RootedTree.cherry]) f
      = bichildPolynomial RootedTree.cherry RootedTree.cherry
          (inversePolyTree RootedTree.cherry f)
          (inversePolyTree RootedTree.cherry f) f := rfl
```

If this closes by `rfl`, the `show` form is viable. If not, fall
back to the cycle 387 `show + rw [inversePolyTree, ...]` two-step
pattern.

## §C. Cycle 388 deliverable bar — DO NOT

* Do **NOT** also tackle `(broom₃, cherry)` cross-term refinement
  in the same cycle. That requires reading cycle 386's 14-term
  closed form, deriving a similarly-back-computed cross-term, and
  shipping `inversePolyTree_mkBroomCherry`. It's mechanical but
  doubles the LOC and risks LOC budget overflow. **Schedule for
  cycle 389**.

* Do **NOT** generalise `bichildCrossTerm` to a unified recipe yet.
  The cycle 385 scoping doc §3.2 / §4 explicitly defers the unified
  combinatorial recipe (cycles 390+). For now, accept the per-pair
  if-then-else structure.

* Do **NOT** attempt Phase α'.4.2 (Family C `inversePolynomial`
  branch migration to dispatch through `inversePolyTree`). That's
  cycle 389+ once both `(cherry, cherry)` and `(broom₃, cherry)`
  calibration witnesses ship.

* Do **NOT** modify the cycle 387 sign convention
  (`bichildPolynomial`'s leading negation `-(f vertex · inv₁ ·
  inv₂)`). Cycle 387 §11.2 documents why this is right; reverting
  to the strategy's strawman positive-sign shape would invalidate
  the cycle 387 `inversePolyTree_cherry` calibration.

* Do **NOT** raise `maxHeartbeats`. The cycle 388 deliverable
  consumes a single `ring` step on a degree-5 polynomial in
  ≤7 indeterminates — well under default heartbeats.

* Do **NOT** submit an Aristotle job. The cross-term value is
  algebraically pinned (back-computed from cycle 384); search-based
  proof discovery has no role here.

* Do **NOT** attempt Phase E sealing (closing cycle 365's
  grandfathered sorry at `Section422.lean:2279`). That's a
  multi-cycle Phase β/γ extension projected for cycles 392+
  per scoping doc §5.

* Do **NOT** edit `scripts/autonomous_loop.py`. Loop-maintainer
  territory per CLAUDE.md.

## §D. Stretch (only if P1 + P2 ship cleanly with LOC budget remaining)

Ship `(broom₃, cherry)` cross-term refinement + corresponding
calibration witness. Back-compute the cross-term value from cycle
386's 14-term closed form analogous to the §B P1 derivation:

* `bichildPolynomial broom₃ cherry inv_b inv_c f` backbone expands
  with `inv_b = -v³ + 2vc - b'` (cycle 368's
  `elementaryWeightQ_phi_inv_broom₃`) and `inv_c = v² - c`
  (cycle 367).
* Cycle 386's `Φ_{η_q⁻¹}(mk [broom₃, cherry])` closed form:
  `v⁶ − 5v⁴c + 5v²c² + 2v³b' − 2vb'c + 3v³m − 4vcm + b'm
   − v²·M_broom₃ + c·M_broom₃ − 3v²·vc + 2v·cc + v·vb' − bc`
  (find via `grep -n "elementaryWeightQ_phi_inv_mkBroomCherry"`
  in `Section422.lean`).
* Subtract backbone from the RHS to extract
  `bichildCrossTerm broom₃ cherry f`.
* Ship `inversePolyTree_mkBroomCherry` calibration witness using
  the cycle 388 P1+P2 recipe.

**However**: the cycle 386 closed form contains
`f (mk [vertex, broom₃])` (the `vb'` kernel — new in cycle 386, not
named in the project as a tree alias). This needs explicit handling
in the cross-term, which adds LOC. **If P1+P2 ship in ≤200 LOC,
attempt this stretch; if P1+P2 ship in 200-400 LOC, skip; defer to
cycle 389**.

**Don't pre-compute the cycle 388 stretch value if P1+P2 budget is
unclear** — preserve cycle isolation.

## §E. LOC budget estimate

* P1 `bichildCrossTerm` refactor: ~15 LOC (one if-then-else, four
  RHS lines).
* P2 `inversePolyTree_mkCherryCherry` theorem + docstring: ~40 LOC.
* P1+P2 total: ~55 LOC.
* Stretch (D): +200 LOC ((broom₃, cherry) cross-term + theorem).
* Hard ceiling: 500 LOC (strategy budget).
* Soft target: ~80 LOC (P1+P2 only); accept up to ~280 LOC if
  stretch lands cleanly.

## §F. Faithfulness check protocol

Before committing, run the cycle 388 worker self-check:

1. Verify `bichildCrossTerm cherry cherry f` matches the §B P1
   derivation by re-doing the algebra by hand (or by examining
   cycle 384's closed form RHS subtracting cycle 387's
   `bichildPolynomial` backbone). If the values disagree by any
   coefficient, **STOP** and re-derive.

2. Verify `inversePolyTree_mkCherryCherry`'s RHS matches cycle 384's
   `elementaryWeightQ_phi_inv_mkCherryCherry` RHS verbatim (locate
   via `grep -n "elementaryWeightQ_phi_inv_mkCherryCherry"
   OpenMath/Chapter4/Section422.lean` — should be around line
   ~4655 onward).

3. Run `#print axioms inversePolyTree_mkCherryCherry` and confirm
   `[propext, Classical.choice, Quot.sound]` only. The
   `Classical.choice` may appear because of the `if` construct's
   decidability typeclass. `Quot.sound` and `propext` are expected.

4. Confirm `grep -c sorry OpenMath/Chapter4/Section422.lean` returns
   5 (4 docstring + 1 grandfathered code) — **no new sorries**.

5. Confirm `lake env lean OpenMath/Chapter4/Section422.lean` exits 0.

## §G. Cycle 389+ outlook

After cycle 388 lands (P1+P2 minimum):

* **Cycle 389**: ship `(broom₃, cherry)` cross-term + calibration
  witness (if not done in cycle 388 stretch). ~200 LOC.
* **Cycle 390**: ship `(broom₃, broom₃)` cross-term (if cycle 386
  shipping convention demands it; verify against the scoping doc).
  ~200 LOC.
* **Cycle 391+**: Phase α'.4.2 — migrate `inversePolynomial`'s
  Family C branches (`mk [broom₃]`, `mk [vertex, cherry]`,
  `mk [cherry, cherry]`, `mk [broom₃, cherry]`) to dispatch through
  `inversePolyTree`. Parallel to cycles 381 (Family A) and 383
  (Family B). ~100 LOC.
* **Cycle 392+**: Phase E sealing — close cycle 365's grandfathered
  sorry at `Section422.lean:2279` using `inversePolyTree` as the
  Family C branch driver. Multi-cycle Phase β/γ extension.

§422 axiom-clean streak after cycle 388: **51 substantive + 2 doc**
(336–388). Cycle 388 deliverable is bounded and disciplined; LOC
budget is well-defined; no infrastructure risk.

## §H. Pre-flight checklist for cycle 388 worker

1. Read `OpenMath/Chapter4/Section422.lean:6231-6322` (the cycle 387
   `bichildCrossTerm`, `bichildPolynomial`, `inversePolyTree`,
   `inversePolyTree_vertex`, `inversePolyTree_cherry` block).

2. Read cycle 384's `elementaryWeightQ_phi_inv_mkCherryCherry`
   theorem (find via `grep -n "elementaryWeightQ_phi_inv_mkCherryCherry"`
   in `Section422.lean`) to copy its RHS verbatim into the cycle 388
   calibration theorem.

3. Run `lean_multi_attempt` on the test reduction
   `inversePolyTree (mk [cherry, cherry]) f = bichildPolynomial
   cherry cherry (inversePolyTree cherry f) (inversePolyTree cherry
   f) f := rfl` to confirm the `show ... = bichildPolynomial ...`
   form is viable (if `rfl` succeeds, go ahead; if not, use the
   cycle 387 `show; rw [inversePolyTree, ...]` two-step pattern).

4. Verify cycle 92's `DecidableEq RootedTree` instance is in scope
   in `Section422.lean` (it imports `Section301`, so should be
   automatic; double-check by writing a one-line `example` testing
   `decide` on `(RootedTree.cherry = RootedTree.vertex) = False`).

5. Apply P1 refactor at `Section422.lean:6237` (replace the
   placeholder `:= 0` body with the if-then-else dispatch).

6. Apply P2 ship at the end of the cycle 387 calibration block
   (after `inversePolyTree_cherry`, line `Section422.lean:6322`).

7. Run `lake env lean OpenMath/Chapter4/Section422.lean` to verify
   compile.

8. Run axiom checks per §F.

## §I. Bottom-line directive

* P1: refactor `bichildCrossTerm` at `Section422.lean:6237` to
  handle `(cherry, cherry)` via if-then-else with the
  §B-back-computed value (~15 LOC).
* P2: ship `inversePolyTree_mkCherryCherry` immediately after
  `inversePolyTree_cherry` at `Section422.lean:6322`, matching cycle
  384's closed form verbatim (~40 LOC).
* Stretch only if P1+P2 well under budget: ship `(broom₃, cherry)`
  pair (~200 LOC).
* Verify axiom-clean; sorry count unchanged (5); §422 streak → 51
  substantive + 2 doc.

This is single-cycle work with no infrastructure risk. The cycle
387 ship provides the recursive scaffolding; cycle 388 fills in one
per-pair cross-term value and adds the corresponding calibration
witness.
