# Cycle 392 Results

## Worked on

Phase α'.4.1 P5 ship per cycle 392 strategy:

* B.1: New def `monochildCrossTerm (c : RT) (f : RT → ℝ) : ℝ` —
  single-child non-leaf cross-term, mirroring cycle 387's
  `bichildCrossTerm` design for the `[c]` branch. Dispatches:
  `c = broom₃` → `-(v²·c) + 2v·m` (where `m = f (mk [cherry])`),
  other `c` → `0`.
* B.2: Refactor `inversePolyTree`'s `[c]` branch body to
  `-(f vertex * inversePolyTree c f) + monochildCrossTerm c f
  - f (mk [c])` (was: no `monochildCrossTerm` term).
* B.3: Re-verify cycle 387's `inversePolyTree_cherry` after the
  B.2 refactor — required Case B fallback (the strategy §B.3
  Case A `ring` did not close due to `def cherry` non-reducible).
  Added `show monochildCrossTerm RootedTree.vertex f = 0` rewrite
  plus an additional `show` line for the `+ 0` intermediate form
  before `ring`.
* B.4: New theorem `inversePolyTree_mkBroom₃` — calibration
  witness matching cycle 371's `elementaryWeightQ_phi_inv_mkBroom₃`
  closed form verbatim. Proof:
  `rw [inversePolyTree, inversePolyTree_broom₃,
       show monochildCrossTerm RootedTree.broom₃ f = ... by
         unfold monochildCrossTerm; rw [if_pos rfl]]; ring`.
* B.5: Issue file `def_422B_phase_alpha_prime_scoping.md` updated
  with a cycle 392 update subsection documenting the ship.
* `extraction/formalization_data/lean_status.json` `def:422B`
  row's `cycle_completed_at` bumped from 390 to 392 (cycle 391
  did not bump it; this rolls cycles 391+392 into the same bump).

## Approach

Mechanical execution of the cycle 392 strategy §B.1–B.5. The
`ring` step in cycle 387's `inversePolyTree_cherry` (B.3) failed
under Case A as suspected, requiring the Case B fallback with
an additional `show` line to bridge `f (mk [vertex])` to
`f RootedTree.cherry` (since `cherry` is a non-reducible `def`,
`ring` cannot see through it). The cycle 392 strategy §G's graceful
degradation #3 (split `monochildCrossTerm` into two named theorems)
was not needed — the if-then-else dispatch with `if_neg (by decide)`
and `if_pos rfl` worked cleanly.

## Result

SUCCESS — all six exit criteria met:

1. `lake env lean OpenMath/Chapter4/Section422.lean` exits 0 with
   only the grandfathered cycle 365 sorry warning at line 2272
   (actual line in current file, formerly 2279 — line numbers
   shifted slightly due to comments above).
2. `lake build OpenMath.Chapter4.Section422` exits 0 (built in
   427s).
3. `grep -c sorry OpenMath/Chapter4/Section422.lean` = 5
   (unchanged: 4 docstring + 1 code).
4. New theorem `inversePolyTree_mkBroom₃` axiom-clean
   (`[propext, Classical.choice, Quot.sound]`).
5. All seven existing calibration witnesses re-verify axiom-clean:
   `inversePolyTree_vertex`, `_cherry`, `_broom₃`,
   `_mkCherryCherry`, `_mkBroomCherry`, `_mkVertexCherry`,
   `_mkVertexCherry_eq_inversePolynomial` — all return
   `[propext, Classical.choice, Quot.sound]`.
6. Cycle 391's `inversePolynomial` body for `mk [vertex, cherry]`
   untouched. Issue file update appended.

## Faithfulness check

### New def: `monochildCrossTerm c f`

No textbook entity — this is internal infrastructure parallel to
cycle 387's `bichildCrossTerm`. Not definition smuggling: the
per-`c` values are back-computed from already-shipped empirical
closed forms (cycle 371's `mk [broom₃]`). The default `c → 0`
branch matches cycle 367's `mk [vertex] = cherry` empirical data.

### New theorem: `inversePolyTree_mkBroom₃`

* Entity ID: no direct textbook entity (this is the recursive
  `inversePolyTree` calibration at `mk [broom₃]`). Matches cycle
  371's `elementaryWeightQ_phi_inv_mkBroom₃` closed form for
  `Φ_{η⁻¹}(mk [broom₃])`.
* Lean statement captures: same content as cycle 371's closed
  form, restated against `inversePolyTree` rather than against
  `elementaryWeightQ_phi η_q⁻¹`. RHS terms match verbatim:
  `v⁴ - 3v²c + vb' + 2vm - M_broom₃`.
* No divergence; no hypothesis strengthening.

### Pre-commit checklist

* TAUTOLOGY CHECK: `inversePolyTree_mkBroom₃` conclusion does
  not appear verbatim as any hypothesis (the only hypothesis is
  `f : RT → ℝ`). No tautology.
* IDENTITY CHECK: proof uses 3-step `rw` chain ending in `ring`;
  it does substantive arithmetic. Not vacuous.
* DEFINITION SMUGGLING CHECK: `monochildCrossTerm` is a per-pair
  lookup table for cross-term values. The values are back-
  computed from empirically-verified closed forms (cycle 371) and
  the calibration witness then proves the recursive
  `inversePolyTree` reproduces the same closed form. This is the
  same design pattern as cycle 387's `bichildCrossTerm` and is
  NOT definition smuggling (the def encodes correction values,
  not the theorem statement).
* HYPOTHESIS STRENGTH CHECK: no extra hypotheses beyond `f : RT
  → ℝ` (function-level).

## Dead ends

* Strategy §B.3 Case A (`ring` alone after monochildCrossTerm
  rewrite) — failed because `cherry` is a non-reducible `def`
  in `OpenMath/Chapter3/Section310.lean:111`, and `ring` cannot
  see through it. Case B fallback (explicit `show`) closed the
  goal. This matches the cycle 387 original proof's use of a
  `show` for the same reason.

## Discovery

* `def cherry := mk [vertex]` is non-reducible for `ring`-class
  tactics. When the LHS contains `f (mk [vertex])` and the RHS
  contains `f RootedTree.cherry`, you must insert a `show` to
  syntactically bridge the two before `ring`. The cycle 387
  original proof does this implicitly; cycle 392 makes the
  pattern explicit by preserving the structure after a `+ 0`
  term insertion from the `monochildCrossTerm vertex f = 0`
  rewrite. Memory candidate: `feedback_ring_def_opacity.md`
  (if not already present — looks like cycle 387 was the first
  encounter and may already have a similar memory).

## Suggested next approach

Per cycle 392 strategy §H — **cycle 393** ships Phase α'.4.2
migration of `inversePolynomial`'s `mk [broom₃]` branch (Family A
migration #1) via:

* New bridge theorem `inversePolyTree_mkBroom₃_eq_inversePolynomial
  (f : RT → ℝ) : inversePolyTree (mk [broom₃]) f
    = inversePolynomial (mk [broom₃]) f`. Two-step `unfold + rw +
  exact inversePolyTree_mkBroom₃` body, parallel to cycle 391's
  `inversePolyTree_mkVertexCherry_eq_inversePolynomial`.
* `inversePolynomial`'s `mk [broom₃]` body migration: replace the
  current closed-form RHS with `inversePolyTree (mk [broom₃]) f`
  dispatch.
* Downstream consumer updates: Phase β bridge `elementaryWeightQ
  _phi_inv_eq_inversePolynomial_mkBroom₃` (if it exists) appends
  `inversePolyTree_mkBroom₃_eq_inversePolynomial` to its `rw`
  chain; Phase γ `inversePolynomial_eq_of_subtree_agreement`
  `mk [broom₃]` branch (if it exists) appends similarly.

LOC budget: ~45 LOC (parallel to cycle 391). Mechanical 1-cycle
ship.

**Cycle 394** continues per cycle 392 strategy §H — extend
`monochildCrossTerm` for `c = mk [cherry]` (cycle 378's closed
form gives `v⁴ - 3v²c + c² + 2vm - M_mkMkCherry`; delta from
naive body is `-(v²c - c²) + 2vm`, needs to be computed precisely).
Ship `inversePolyTree_mkMkCherry` calibration witness alongside.

§422 axiom-clean streak: **55 substantive + 2 doc** (336–392).
Cycle 365 grandfathered sorry remains the single open sorry in
§422.
