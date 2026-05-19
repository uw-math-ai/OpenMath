# Cycle 394 Results

## Worked on
§422 Phase α'.4.1 P6 — extend `monochildCrossTerm` for `c = cherry`;
ship `inversePolyTree_mkCherry` calibration witness (`mk [cherry]`).

Files touched: `OpenMath/Chapter4/Section422.lean` only.

## Approach
Per cycle 394 strategy §B–§C, the planner identified that the cycle 393
worker's "Suggested next approach" (skip to `mk [mk [cherry]]`) would have
built on a broken foundation: `inversePolyTree (mk [cherry]) f` evaluates
to `-v³ + vc - m` (off by `+v · c` from cycle 369's target `-v³ + 2vc - m`)
because `monochildCrossTerm cherry` defaulted to `0`. Cycle 394 fixes the
recursion at the `cherry` layer first.

Steps executed:

1. **`monochildCrossTerm` extension** (Section422.lean ~line 6339): added one
   `else if c = RootedTree.cherry then f vertex * f cherry` branch between
   the existing `broom₃` branch and the default `else 0`. Updated the
   docstring with the new `c = cherry → v · c` bullet.

2. **`inversePolyTree_cherry` proof adjustment** (Section422.lean line 6428–6430):
   the existing `show monochildCrossTerm vertex f = 0 by unfold; rw [if_neg
   (by decide)]` block now needs two `if_neg`s (one for `vertex ≠ broom₃`,
   one for `vertex ≠ cherry`). One-line change: replaced
   `rw [if_neg (by decide)]` with `rw [if_neg (by decide), if_neg (by decide)]`.
   No other changes to the proof body. Both `by decide`s discharge via
   `RootedTree`-constructor disjointness (per
   `feedback_indexed_inductive_cases_disjoint.md`).

3. **`inversePolyTree_mkCherry` ship** (Section422.lean inserted after
   `inversePolyTree_mkBroom₃`): 25 LOC including docstring. Proof template
   from cycle 392:
   ```
   rw [inversePolyTree, inversePolyTree_cherry]
   rw [show monochildCrossTerm RootedTree.cherry f
         = f RootedTree.vertex * f RootedTree.cherry by
         unfold monochildCrossTerm
         rw [if_neg (by decide), if_pos rfl]]
   ring
   ```
   The `if_neg (by decide)` discharges `cherry ≠ broom₃`, then `if_pos rfl`
   fires the new branch.

4. **Verification (§D)**:
   - `lake env lean OpenMath/Chapter4/Section422.lean` exits 0 (only the
     expected cycle 365 grandfathered sorry warning at `:2272`).
   - `lake build OpenMath.Chapter4.Section422` exits 0 (8037 jobs).
   - `grep -c sorry OpenMath/Chapter4/Section422.lean` returns **5**
     (4 docstring `sorry` references + 1 grandfathered cycle 365 sorry —
     unchanged).
   - `#print axioms inversePolyTree_mkCherry` →
     `[propext, Classical.choice, Quot.sound]`. ✓
   - Regression: every prior `inversePolyTree_*` calibration
     (`_vertex, _cherry, _broom₃, _mkBroom₃, _mkCherryCherry,
     _mkBroomCherry, _mkVertexCherry`) remains axiom-clean. ✓
   - `inversePolyTree_cherry` proof body change verified clean (axiom set
     unchanged). ✓

## Result
**SUCCESS.** All 3 deliverables landed:
- `monochildCrossTerm` extension (Section422.lean `def` + docstring).
- `inversePolyTree_cherry` proof update (one `if_neg` added).
- `inversePolyTree_mkCherry` new public theorem (axiom-clean).

§422 streak: 56 → **57 substantive + 2 doc** (cycles 336–394).
Sorry count: unchanged at 5.
Cycle 365 grandfathered sorry: still at `:2272`.

## Faithfulness check

### New `def` — `monochildCrossTerm` extension (cherry branch)
- **Entity ID**: no textbook entity directly; infrastructure for Phase α'.4
  ladder consolidation. Mechanically derived from cycle 369's
  `elementaryWeightQ_phi_inv_mkCherry` closed form (an axiom-clean shipped
  theorem). NOT definition-smuggled.
- **Paper-derivation** (from strategy §B):
  ```
  inversePolyTree (mk [cherry]) f
    = -(v · inversePolyTree cherry f) + monochildCrossTerm cherry f - m
    = -(v · (v² - c)) + monochildCrossTerm cherry f - m            (cycle 387)
    = -v³ + vc + monochildCrossTerm cherry f - m
  ```
  Target (cycle 369): `-v³ + 2vc - m`. Delta: `monochildCrossTerm cherry f
  = +vc = f vertex * f cherry`.
- **Lean statement captures**: same content as the paper derivation.

### Modified `theorem` — `inversePolyTree_cherry` proof
- **Statement**: unchanged. Only the proof body was edited (one
  `if_neg (by decide)` added).
- **Axiom set**: unchanged (`[propext, Classical.choice, Quot.sound]`).
- **Tautology / identity / hypothesis-strength checks**: all pass — proof
  remains substantive (still bridges `inversePolyTree cherry f` to
  `v² - c` via the recursion); no hypothesis change.

### New `theorem` — `inversePolyTree_mkCherry`
- **Entity ID**: no textbook entity directly; calibration witness for
  Phase α'.4.1 ladder (corresponds to cycle 369's
  `elementaryWeightQ_phi_inv_mkCherry` at the unquotiented
  `inversePolyTree` level).
- **Lean statement** (LHS): `inversePolyTree (mk [cherry]) f`.
- **Lean statement** (RHS): `-(f vertex)^3 + 2 * f vertex * f cherry
  - f (mk [cherry])`.
- **Closed form quoted from cycle 369**:
  `-v³ + 2vc - m` where `v = f vertex`, `c = f cherry`, `m = f (mk [cherry])`.
- **Captures**: same content as cycle 369's closed form, evaluated at
  generic `f : RT → ℝ` rather than `f = elementaryWeightQ_phi η_q`.
- **Tautology check**: LHS is the recursive unfolding via
  `inversePolyTree` + `inversePolyTree_cherry` + new `monochildCrossTerm`
  branch + `ring`. RHS is a substantive polynomial. NOT vacuous.
- **Identity check**: proof is the canonical cycle 392 template (`rw`
  followed by `show … by unfold; rw [if_neg, if_pos rfl]` then `ring`).
  Substantive.
- **Hypothesis strength**: only `f : RT → ℝ`. Matches cycle 392 precedent.

## Dead ends
None — the strategy was prescriptive and the three steps executed
cleanly on the first compile.

## Discovery
- The cycle 392 template (`rw [if_neg (by decide), if_pos rfl]` inside a
  `show monochildCrossTerm <child> f = <value> by unfold; …`) generalizes
  trivially to k-th `else if` branches: prepend `(k-1)` `if_neg (by decide)`
  discharges before the `if_pos rfl` for the target branch. Cycle 395's
  `monochildCrossTerm (mk [cherry])` extension will need two `if_neg`s
  before the `if_pos rfl` (one for `broom₃`, one for `cherry`).
- Cycle 387's `inversePolyTree_cherry` proof's `show … by unfold; rw
  [if_neg (by decide)]` block is a *trailing-default-branch* discharge —
  every time `monochildCrossTerm` grows a new branch *before* the
  `else 0`, this proof needs one additional `if_neg (by decide)`. Future
  workers extending `monochildCrossTerm` (cycle 395+) must remember to
  update this proof in lock-step.

## Suggested next approach
**Cycle 395 (recommended substantive)**: extend `monochildCrossTerm` for
`c = mk [cherry]` branch using cycle 378's `mk [mk [cherry]]` closed form.
Per strategy §G, the paper-verified target is
`monochildCrossTerm (mk [cherry]) f = -v²c + c² + vm`. Concrete recipe:

1. Insert a third `else if c = mk [cherry]` branch in `monochildCrossTerm`
   between the `cherry` branch and the default `else 0`. Value:
   `-(f vertex)^2 * f cherry + (f cherry)^2 + f vertex * f (mk [cherry])`.

2. Update `inversePolyTree_cherry` to add a third `if_neg (by decide)`
   discharge in its `show monochildCrossTerm vertex f = 0` block (the
   pattern from this cycle).

3. Ship `inversePolyTree_mkMkCherry` calibration witness matching cycle
   378's closed form `v⁴ - 3v²c + c² + 2vm - M_mkMkCherry`. Proof template:
   ```
   rw [inversePolyTree, inversePolyTree_mkCherry]
   rw [show monochildCrossTerm (mk [cherry]) f = … by
         unfold monochildCrossTerm
         rw [if_neg (by decide), if_neg (by decide), if_pos rfl]]
   ring
   ```

LOC budget: ~30–40 LOC (parallel to cycle 394 deliverable size).

**Cycle 396+**: Phase α'.4.2 migration of `inversePolynomial`'s
`mk [cherry]` branch (parallel of cycles 391, 393). Position 4 in the
`inversePolynomial` if-chain → 3 `if_neg` bridges needed.
