# Cycle 395 Results

## Worked on
§422 Phase α'.4.1 P7 — extend `monochildCrossTerm` for `c = mk [cherry]`;
ship `inversePolyTree_mkMkCherry` calibration witness.

Files touched: `OpenMath/Chapter4/Section422.lean` only (plus
bookkeeping: `lean_status.json`, `plan.md`,
`.prover-state/issues/def_422B_phase_alpha_prime_scoping.md`).

## Approach
Per cycle 395 strategy §"Priority 1", a mechanical extension of the
cycle 394 template (cycle 394 added the `cherry` branch + ship
`inversePolyTree_mkCherry`; cycle 395 adds the `mk [cherry]` branch +
ship `inversePolyTree_mkMkCherry`). Three steps executed verbatim
from the strategy recipe:

1. **`monochildCrossTerm` extension** (Section422.lean ~line 6351):
   inserted a third `else if c = OpenMath.Chapter3.Section310.RootedTree.mk
   [RootedTree.cherry]` branch between the cycle 394 `cherry` branch
   and the default `else 0`. Value:
   ```
   -((f RootedTree.vertex)^2 * f RootedTree.cherry)
     + (f RootedTree.cherry)^2
     + f RootedTree.vertex *
         f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
   ```
   Updated the docstring with the new `c = mk [cherry] → -(v²·c) + c² + v·m`
   bullet and cycle 395 deliverable tag. Used the fully-qualified
   `OpenMath.Chapter3.Section310.RootedTree.mk` per the convention
   already used elsewhere in this file (top-level `mk` can collide
   with Lean's universal-mk constructor naming).

2. **`inversePolyTree_cherry` proof one-line update**
   (Section422.lean line 6438): the cycle 394 worker's
   `rw [if_neg (by decide), if_neg (by decide)]` chain extended to
   `rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]`
   — three `if_neg`s for `vertex ≠ broom₃`, `vertex ≠ cherry`,
   `vertex ≠ mk [cherry]` before reaching the default `else 0`.
   Each `by decide` discharges via `RootedTree`-constructor
   disjointness per `feedback_indexed_inductive_cases_disjoint.md`.
   Reformatted to put `unfold monochildCrossTerm` on its own line
   for readability (no semantic change).

3. **`inversePolyTree_mkMkCherry` ship** (Section422.lean inserted
   after `inversePolyTree_mkCherry`): 30 LOC including docstring.
   Proof template from cycle 394:
   ```
   rw [inversePolyTree, inversePolyTree_mkCherry]
   rw [show monochildCrossTerm (mk [cherry]) f
         = -((f vertex)^2 * f cherry) + (f cherry)^2
           + f vertex * f (mk [cherry]) by
         unfold monochildCrossTerm
         rw [if_neg (by decide), if_neg (by decide), if_pos rfl]]
   ring
   ```
   Two `if_neg`s discharge `mk [cherry] ≠ broom₃` and
   `mk [cherry] ≠ cherry`, then `if_pos rfl` fires the new
   `mk [cherry]` branch.

4. **Verification** per strategy §"Verification commands":
   - `lake env lean OpenMath/Chapter4/Section422.lean` exits 0 (only
     the cycle 365 grandfathered sorry warning at line 2272).
   - `lake build OpenMath.Chapter4.Section422` exits 0 (8037 jobs,
     561 s cold).
   - `grep -c sorry OpenMath/Chapter4/Section422.lean` returns **5**
     (unchanged from cycle 394).
   - `#print axioms inversePolyTree_mkMkCherry` →
     `[propext, Classical.choice, Quot.sound]`. ✓ No `sorryAx`.
   - Regression: every prior `inversePolyTree_*` calibration
     (`_vertex, _cherry, _broom₃, _mkBroom₃, _mkCherry,
     _mkCherryCherry, _mkBroomCherry, _mkVertexCherry`) remains
     axiom-clean. ✓ Cycle 394's `inversePolyTree_cherry` proof
     update also verified axiom-clean.

## Result
**SUCCESS.** All 3 deliverables landed:
- `monochildCrossTerm` extension (Section422.lean `def` + docstring,
  +5 LOC delta).
- `inversePolyTree_cherry` proof update (one additional `if_neg`
  + reformat).
- `inversePolyTree_mkMkCherry` new public theorem, axiom-clean
  (`[propext, Classical.choice, Quot.sound]`).

§422 streak: 57 → **58 substantive + 2 doc** (cycles 336–395).
Sorry count: unchanged at 5 (4 docstring `sorry` references + 1
grandfathered cycle 365 sorry at line 2272).

## Faithfulness check

### New `def` — `monochildCrossTerm` extension (mk [cherry] branch)
- **Entity ID**: no textbook entity directly; infrastructure for
  Phase α'.4 ladder consolidation. Mechanically derived from cycle
  378's `elementaryWeightQ_phi_inv_mkMkCherry` closed form (an
  axiom-clean shipped theorem). NOT definition-smuggled.
- **Paper-derivation** (from strategy §"Concrete steps Step 1"):
  ```
  inversePolyTree (mk [mk [cherry]]) f
    = -(v · inversePolyTree (mk [cherry]) f) + monochildCrossTerm (mk [cherry]) f - M_mc
    = -(v · (-v³ + 2vc - m)) + monochildCrossTerm (mk [cherry]) f - M_mc  (cycle 394)
    = v⁴ - 2v²c + vm + monochildCrossTerm (mk [cherry]) f - M_mc
  ```
  Target (cycle 378): `v⁴ - 3v²c + c² + 2vm - M_mc`. Delta:
  `monochildCrossTerm (mk [cherry]) f = -(v²·c) + c² + v·m =
  -((f vertex)^2 · f cherry) + (f cherry)² + f vertex · f (mk [cherry])`.
- **Lean statement captures**: same content as the paper derivation.

### Modified `theorem` — `inversePolyTree_cherry` proof
- **Statement**: unchanged. Only the proof body was edited (one
  `if_neg (by decide)` added).
- **Axiom set**: unchanged (`[propext, Classical.choice, Quot.sound]`).
- **Tautology / identity / hypothesis-strength checks**: all pass —
  proof remains substantive (still bridges `inversePolyTree cherry f`
  to `v² - c` via the recursion); no hypothesis change.

### New `theorem` — `inversePolyTree_mkMkCherry`
- **Entity ID**: no textbook entity directly; calibration witness for
  Phase α'.4.1 ladder (corresponds to cycle 378's
  `elementaryWeightQ_phi_inv_mkMkCherry` at the unquotiented
  `inversePolyTree` level).
- **Lean statement** (LHS): `inversePolyTree (mk [mk [cherry]]) f`.
- **Lean statement** (RHS):
  `v⁴ - 3 · v² · c + c² + 2 · v · m - f (mk [mk [cherry]])`
  where `v = f vertex`, `c = f cherry`, `m = f (mk [cherry])`.
- **Closed form quoted from cycle 378's
  `elementaryWeightQ_phi_inv_mkMkCherry`**:
  `v⁴ - 3v²c + c² + 2vm - M_mc` where `M_mc = f (mk [mk [cherry]])`.
- **Captures**: same content as cycle 378's closed form, evaluated
  at generic `f : RT → ℝ` rather than `f = elementaryWeightQ_phi η_q`.
- **Tautology check**: LHS is the recursive unfolding via
  `inversePolyTree` + `inversePolyTree_mkCherry` + new
  `monochildCrossTerm` branch + `ring`. RHS is a substantive
  polynomial in 4 kernels. NOT vacuous.
- **Identity check**: proof is the canonical cycle 394 template (`rw`
  followed by `show … by unfold; rw [if_neg, if_neg, if_pos rfl]`
  then `ring`). Substantive.
- **Hypothesis strength**: only `f : RT → ℝ`. Matches cycle 394
  precedent. No hidden assumptions.

## Dead ends
None — the strategy was prescriptive and the three steps executed
cleanly on the first compile. The compile was slow (~5 min cold)
but no logical detours required.

## Discovery
- Cycle 394's Discovery #1 generalisation holds: every time
  `monochildCrossTerm` grows a new `else if` branch before the
  default `else 0`, the cycle 394 template for the corresponding
  `inversePolyTree_mk<child>` calibration witness needs **k**
  `if_neg (by decide)` discharges before the final `if_pos rfl`,
  where `k` is the number of branches preceding the target. For
  `inversePolyTree_mkMkCherry`, the target `mk [cherry]` branch is
  the 3rd, so 2 `if_neg`s precede the `if_pos rfl`.
- Cycle 394's Discovery #2 also confirmed: `inversePolyTree_cherry`'s
  `show monochildCrossTerm vertex f = 0` block needs **one
  additional `if_neg (by decide)`** for each new branch added before
  the default `else 0`. Cycle 395's addition of the `mk [cherry]`
  branch grew the discharge chain from 2 to 3 `if_neg`s. Future
  workers extending `monochildCrossTerm` (cycle 396+) must remember
  to update this proof in lock-step (e.g., if `c = bushy` is added
  in cycle 397, `inversePolyTree_cherry` needs a 4th `if_neg`).
- The `mk [cherry]` branch's value `-(v²·c) + c² + v·m` is the first
  cross-term in this infrastructure with **3 distinct kernel-product
  terms** (rather than 2 as in `broom₃` or 1 as in `cherry`); this
  reflects the depth-2 nature of `mk [cherry]` as a child — block (4)
  of the cycle 385 scoping doc taxonomy now surfaces a `c² = (f cherry)²`
  same-kernel-squared term at the single-child level for the first
  time.

## Suggested next approach
**Cycle 396 (recommended substantive)**: Phase α'.4.2 migration of
`inversePolynomial`'s `mk [cherry]` branch (parallel of cycles 391
and 393). Concrete recipe per strategy §"Priority 2":

1. Add bridge theorem `inversePolyTree_mkCherry_eq_inversePolynomial`
   (LHS: `inversePolyTree (mk [cherry]) f`; RHS:
   `inversePolynomial (mk [cherry]) f`). Proof:
   `unfold inversePolynomial; rw [if_neg, if_neg, if_neg, if_pos rfl]`
   — 3 `if_neg`s for `mk [cherry] ≠ vertex/cherry/broom₃`, then the
   `mk [cherry]` branch fires (4th in the `inversePolynomial`
   if-chain).
2. Migrate `inversePolynomial`'s `mk [cherry]` body from the
   explicit 3-term closed form (`-v³ + 2vc - m`) to
   `inversePolyTree (mk [cherry]) f` dispatch. Value-preserving via
   cycle 394's `inversePolyTree_mkCherry`.
3. Update 3 consumers (each trailing one extra rewrite to bridge):
   - The Phase α.1/α.2 calibration `example` for `mk [cherry]`.
   - The Phase β.1 bridge
     `elementaryWeightQ_phi_inv_eq_inversePolynomial_mkCherry`.
   - The Phase γ branch of
     `inversePolynomial_eq_of_subtree_agreement` (apply
     `inversePolyTree_mkCherry` twice, once per `f`/`g` side).

LOC budget: ~40–50 LOC.

**Cycle 397+**: Phase α'.4.2 migration of remaining single-child
ladder trees (`bushy`, `mk [mk [cherry]]`) — same template as cycle
391/393/396. Each ~40–50 LOC.

**Cycle 398+** (downstream): once all 9 ladder trees dispatch through
`inversePolyTree`, the Phase β/γ consumers can collapse to a single
dispatch through the recursive def, and the cycle 365 grandfathered
sorry at line 2272 becomes attackable via the unified recursive
structure (Sub-lemma A `powRep_sum_eq_of_strict_subtree_agreement`).
