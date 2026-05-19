# Cycle 391 Results

## Worked on

§422 Phase α'.4.2 Family C bridge migration in
`OpenMath/Chapter4/Section422.lean` — extension of cycle 381's Family
A and cycle 383's Family B bridge-migration precedents to the third
tree family (Family C heterogeneous-children).

Re-route the `mk [vertex, cherry]` branch of `inversePolynomial t f`
from an explicit polynomial body to a dispatch through the recursive
helper `inversePolyTree (mk [vertex, cherry]) f` (cycle 387–390
infrastructure), then thread the migration through all three
downstream consumers (calibration witness, Phase β bridge, Phase γ
subtree-agreement theorem) and ship one new public bridge theorem
`inversePolyTree_mkVertexCherry_eq_inversePolynomial`.

## Approach

Followed cycle 391 strategy §C Steps 1–5 verbatim:

1. **Step 1 — `inversePolynomial` body** (`Section422.lean:6667-6671`,
   was lines 6667-6676). Replaced the 6-term explicit polynomial body
   for the `mk [vertex, cherry]` branch with a single dispatch
   `inversePolyTree (mk [vertex, cherry]) f`. Net: −10 LOC at the
   def site.

2. **Step 2 — Bridge theorem ship**
   (`Section422.lean:7046-7088`, new — placed after
   `inversePolyBroom_three_eq_inversePolynomial` and before the
   Phase β.1 section header, mirroring cycle 381's
   `inversePolyChain_*_eq_inversePolynomial` and cycle 383's
   `inversePolyBroom_*_eq_inversePolynomial` placement). Statement
   `inversePolyTree (mk [vertex, cherry]) f = inversePolynomial
   (mk [vertex, cherry]) f`. Proof: `unfold inversePolynomial; rw
   [if_neg ×6, if_pos rfl]`. The 6 `if_neg` discharges match the
   six branches preceding `mk [vertex, cherry]` in the cycle 374/377/
   378 ladder (`vertex`, `cherry`, `broom₃`, `mk [cherry]`, `bushy`,
   `mk [broom₃]`).

3. **Step 3 — Phase β bridge consumer update** (`Section422.lean:7212-
   7253` cycle 377-era theorem
   `elementaryWeightQ_phi_inv_eq_inversePolynomial_mkVertexCherry`):
   appended `inversePolyTree_mkVertexCherry` (cycle 390's calibration
   witness) at the end of the existing `rw` chain after `if_pos rfl`.
   Now `if_pos rfl` exposes `inversePolyTree (mk [vertex, cherry])
   f` and the appended `inversePolyTree_mkVertexCherry` rewrite
   collapses it to the cycle 372 closed-form polynomial form, so the
   trailing `exact elementaryWeightQ_phi_inv_mkVertexCherry η_q`
   closes the goal as before. +1 token in the rw list.

4. **Step 4 — Phase γ subtree-agreement consumer update**
   (`Section422.lean:7549-7620` `mk [vertex, cherry]` branch of cycle
   376's `inversePolynomial_eq_of_subtree_agreement`): appended
   `inversePolyTree_mkVertexCherry, inversePolyTree_mkVertexCherry`
   (one per side `f`/`g`) after `if_pos rfl` and before the
   per-element substitution rewrites `hv, hc, hb, hmc, hmvc`. This
   matches the cycle 381 Family A and cycle 383 Family B Phase γ
   patterns exactly. +2 tokens in the rw list.

5. **Additional consumer update — calibration witness `example`**
   (`Section422.lean:6813-6856`). The cycle 377-era calibration
   witness for `mk [vertex, cherry]` (an anonymous `example` block)
   also breaks after Step 1 since its RHS is the explicit polynomial
   form. Appended `inversePolyTree_mkVertexCherry` to its `rw` chain
   after `if_pos rfl` to fold the new recursive form back to the
   explicit polynomial. +1 token. Not explicitly enumerated in
   strategy §C — discovered during the compile-verify protocol of
   strategy §F. Total of 3 broken consumers (within strategy §F's
   "≤ 2 broken consumers" threshold + 1 anonymous example; no
   strategy fallback triggered).

6. **Verification protocol** (strategy §C.5 + §F):
   * `lake env lean OpenMath/Chapter4/Section422.lean` after all
     four edits — exit 0 with the expected single warning at line
     2272 (grandfathered cycle 365 sorry). 10m05s.
   * `lake build OpenMath.Chapter4.Section422` — exit 0, refreshed
     `.olean` cache (built 8037/8037 jobs). 8m08s.
   * `#print axioms` on the three required theorems
     (`inversePolyTree_mkVertexCherry_eq_inversePolynomial`,
     `elementaryWeightQ_phi_inv_eq_inversePolynomial_mkVertexCherry`,
     `inversePolynomial_eq_of_subtree_agreement`) all return
     `[propext, Classical.choice, Quot.sound]`. 7m47s.
   * `grep -c sorry OpenMath/Chapter4/Section422.lean` = 5 (unchanged:
     4 docstring references + 1 actual code sorry at line 2279).

## Result

**SUCCESS.** All four edits land cleanly with no regressions:

* `lake env lean OpenMath/Chapter4/Section422.lean` exit 0 (single
  cycle 365 sorry warning).
* `lake build OpenMath.Chapter4.Section422` exit 0 (8037/8037).
* `grep -c sorry` = 5 (unchanged).
* All three required theorems axiom-clean
  `[propext, Classical.choice, Quot.sound]`.
* Section422.lean: 7721 → 7767 LOC (+46 LOC; within strategy's
  ~45 LOC budget).
* §422 axiom-clean streak: 53 substantive + 2 doc (336–390) → **54
  substantive + 2 doc** (336–391).

All cycle 391 strategy exit criteria met:

1. ✓ `inversePolynomial`'s `mk [vertex, cherry]` branch dispatches
   to `inversePolyTree (mk [vertex, cherry]) f`.
2. ✓ New public bridge theorem
   `inversePolyTree_mkVertexCherry_eq_inversePolynomial` ships
   axiom-clean.
3. ✓ Phase β bridge `elementaryWeightQ_phi_inv_eq_inversePolynomial
   _mkVertexCherry` still compiles axiom-clean.
4. ✓ Phase γ `inversePolynomial_eq_of_subtree_agreement` still
   compiles axiom-clean.
5. ✓ Calibration witness `example` still compiles.
6. ✓ `lake env lean Section422.lean` + `lake build` both exit 0.
7. ✓ `grep -c sorry` = 5 (unchanged).
8. ✓ The 1 code sorry at line 2279 (cycle 365 grandfathered) untouched.

## Faithfulness check

For each new `def`/`theorem` introduced this cycle:

**1. `inversePolyTree_mkVertexCherry_eq_inversePolynomial` (new theorem)**

- Entity ID: bridge lemma — no Butcher entity ID. Pure infrastructure
  internal to the Phase α'.4 recursion bridging cycle 387's recursive
  `inversePolyTree` and cycle 374's pattern-match `inversePolynomial`
  on the `mk [vertex, cherry]` tree (parallel of cycle 383's
  `inversePolyBroom_{two,three}_eq_inversePolynomial`).
- Textbook statement: not applicable (infrastructure lemma).
- Lean statement captures: structural identity of the two
  representations on this specific tree. The two routes (recursive
  vs pattern-match) are designed to compute the same polynomial; the
  bridge theorem formally certifies the agreement.
- Tautology / identity check: NEGATIVE. The conclusion does not
  appear as a hypothesis (theorem has no hypotheses except `f : RT
  → ℝ`). Proof is non-trivial: 7-step rewrite pipeline (`unfold` +
  6 `if_neg` discharges + `if_pos rfl`), exploiting the structure
  of `inversePolynomial`'s pattern-match chain and the fact that
  the cycle 390 calibration witness `inversePolyTree_mkVertexCherry`
  already certified the recursive form's value.

**2. Definition: `inversePolynomial` (modified body, not new def)**

- The `mk [vertex, cherry]` branch's body changed from an explicit
  polynomial to a dispatch `inversePolyTree (mk [vertex, cherry])
  f`. Cycle 390's calibration witness `inversePolyTree_mkVertexCherry`
  formally certifies that this evaluates to the same cycle 372
  closed-form polynomial. So `inversePolynomial`'s *meaning* on
  `mk [vertex, cherry]` is unchanged, only its computational route.
- Definition smuggling check: NEGATIVE. The change is a pure
  refactoring — the closed form is recovered via the cycle 390
  calibration witness whenever consumer code needs it (as
  demonstrated in Steps 3, 4, and 5 of the migration).
- Hypothesis strength check: not applicable (definition, not
  theorem).

## Dead ends

None this cycle. All four mechanical edits landed on first attempt.
The strategy's Fallback A (ship only the bridge theorem without
migrating) and Fallback B (revert and ship a different deliverable)
were not needed — the primary recipe worked cleanly.

The strategy §D pitfall #2 ("definitional folding `mk [vertex] ↔
cherry`") — relevant to the cycle 390 calibration-witness ship —
did NOT apply to cycle 391 because the consumer updates work at the
goal-shape level where `inversePolyTree_mkVertexCherry`'s LHS
already matches the post-migration `if_pos rfl` exposure. No `show`
block was needed for the folding.

The strategy §D pitfall #1 ("`if_neg` chain forward-compatibility")
DID apply but was anticipated: counted the chain length in the file
(7-branch `inversePolynomial` ladder, `mk [vertex, cherry]` is the
7th, so 6 `if_neg` discharges before `if_pos rfl`) before writing
the bridge theorem. Matched on first attempt.

## Discovery

**1. Three-consumer breakage, not two.** Strategy §C enumerated two
consumers (Phase β bridge in Step 3, Phase γ branch in Step 4) but
the cycle 377-era calibration witness `example` block at line
6813-6856 is also a consumer of the explicit polynomial form. The
`example` ships an anonymous lemma equating
`inversePolynomial (mk [vertex, cherry]) f` to the cycle 372 6-term
closed form, so after Step 1's migration this witness needs the
same fix (one extra `inversePolyTree_mkVertexCherry` in the `rw`
chain) as Step 3's named consumer. Total broken consumers: 3 named
+ 1 anonymous `example` = 4 sites, all fixed by the same
`inversePolyTree_mkVertexCherry` rewrite append.

**2. Bridge theorem placement matters.** The new bridge theorem
`inversePolyTree_mkVertexCherry_eq_inversePolynomial` MUST be
placed *after* `inversePolynomial`'s definition (line 6649) because
its proof unfolds `inversePolynomial`. Tried placing it right after
cycle 390's calibration witness `inversePolyTree_mkVertexCherry`
(line 6569) initially — this would compile-fail due to forward
reference. Final placement: after `inversePolyBroom_three_eq_
inversePolynomial` (line 7044), grouping it with the existing
Family A/B bridge theorems for symmetric readability.

**3. `mk [vertex, cherry]` is the *7th* branch in `inversePolynomial`,
not the 6th or 8th.** The branch chain at lines 6650-6682 is:
`vertex` (1st), `cherry` (2nd), `broom₃` (3rd), `mk [cherry]` (4th),
`bushy` (5th), `mk [broom₃]` (6th), `mk [vertex, cherry]` (7th),
`mk [mk [cherry]]` (8th). So the bridge theorem proof requires 6
`if_neg` discharges (one per prior branch) before `if_pos rfl`.
This is consistent with cycle 377's original Phase β bridge proof
(`Section422.lean:7212-7253`, 6 `if_neg` + 1 `if_pos`); the
migration preserves the if-count.

**4. Cycle 381/383 migration pattern generalises cleanly.** Cycle
381 used `inversePolyChain k f` to migrate Family A (4 trees, k=0,1,
2,3); cycle 383 used `inversePolyBroom n f` to migrate Family B (2
trees, n=2,3); cycle 391 uses `inversePolyTree t f` to migrate
Family C (1 tree so far: `mk [vertex, cherry]`). The same
post-migration consumer pattern applies in all three cases:
* Calibration witness: append the helper-name lemma after `if_pos
  rfl` in the `rw` chain.
* Phase β bridge: append the helper-name lemma to the `rw` chain
  before the trailing `exact closedForm_thm`.
* Phase γ subtree-agreement: append two copies of the helper-name
  lemma after the `if_pos rfl` of each side, before the per-element
  rewrites.

This three-pattern recipe is now codified across three cycles and
five trees — robust for future Family C migrations.

**5. Compile time budget.** Strategy §C.5 estimated ~30 min for the
verification chain; actual was ~26 min:
* `lake env lean` after all four edits: 10m05s.
* `lake build` for `.olean` cache refresh: 8m08s.
* `lake env lean` for axiom check: 7m47s.

The axiom check needed the explicit `lake build` cache refresh
between the source-file compile and the import-based check —
otherwise the axiom check uses stale `.olean` and reports "Unknown
constant" for the new theorem. This is the same pattern as cycles
388/389/390.

## Suggested next approach

Per cycle 391 strategy §H, the next-cycle path branches as follows:

**Cycle 392 primary recommendation — `monochildCrossTerm`
infrastructure**: design and ship the single-child non-leaf
cross-term machinery to fix `inversePolyTree`'s `mk [c]` branch at
non-leaf children. Currently `inversePolyTree (mk [broom₃]) f =
v⁴ - 2v²c + vb' - M` vs cycle 371's `v⁴ - 3v²c + vb' + 2vm - M`
(differs by `-v²c + 2vm`). This is the structural blocker preventing
`mk [broom₃]` migration (and by extension `mk [bushy]`, `mk [mk
[cherry]]` migration). Multi-cycle work (~150 LOC). Unblocks
Family A non-leaf chain migrations across cycles 393–396.

* Scoping doc: write a parallel of cycle 379's Family A scoping doc
  (`.prover-state/issues/def_422B_subLemmaA_inductive_plan.md` §6)
  for the `mk [c]` non-leaf case.
* Lean ship: define `monochildCrossTerm c f : ℝ` as an `if`-then-`else`
  dispatch on the inner tree `c`'s shape, parallel to cycle 387's
  `bichildCrossTerm`. Pin its value at `c = cherry` (cycle 369's
  `mk [cherry]` requires the term `0`, current code OK) and `c =
  broom₃` (cycle 371's `mk [broom₃]` requires the term `-v²c +
  2vm`, missing from current code).
* Refine `inversePolyTree`'s `mk [c]` branch to add the new term:
  `-(f vertex * inversePolyTree c f) + monochildCrossTerm c f - f
  (mk [c])`.
* Re-prove cycle 387's `inversePolyTree_cherry` (currently uses
  the `c = vertex` branch which yields `monochildCrossTerm vertex
  f = 0`); should still close.
* Ship a new calibration witness `inversePolyTree_mkBroom₃` (cycle
  371 closed form via the recursive route) plus the
  Phase α'.4.2 migration of `inversePolynomial`'s `mk [broom₃]`
  branch + the three-pattern recipe for its consumers.

Estimated cycle 392 budget: ~150 LOC, 2-3 file rebuilds.

**Cycle 392 alternative (simpler) — `(broom₃, broom₃)` cross-term
addition**: extend `bichildCrossTerm` with a third branch for the
symmetric pair, enabling `mk [broom₃, broom₃]` migration once
cycle 376's order-7 closed form ships. Lower priority than the
`monochildCrossTerm` because no immediate consumer (the order-7
closed form requires cycle 393+ work).

**Cycle ~400+ — cycle 365 grandfathered sorry at line 2279**: still
deferred per cycle 366 closure notes. Requires the full Phase α'.4
recursion (covering Families A, B, C non-leaf chains, and 3+ child
trees). Cycle 391's migration is one step of that closure; the full
target needs ~10+ more cycles of `inversePolyTree`/`inversePolynomial`
ladder expansion.

**Stretch for cycle 392 — verify non-vacuity end-to-end**: write an
`example` exercising `inversePolynomial ⟦explicitEuler⟧
(elementaryWeightQ_phi η_q) = 1` for the `mk [vertex, cherry]`
branch post-migration (parallels cycle 372's pattern). Not necessary,
but reassures that the recursive route reduces to the same value
as the pre-migration polynomial.

**Cycle 391 streak update**: 54 substantive + 2 doc.

**Planner recommendation for cycle 392**: ship the
`monochildCrossTerm` infrastructure. Higher infrastructure investment
than cycle 391's mechanical migration, but unblocks the Family A
non-leaf chain (3-4 trees) for cycles 393–396. Highest-EV cycle 392
move per strategy §H.
