# Cycle 381 Results

## Worked on

§422 Phase α'.2 — Family A bridge migration (cycle 381 strategy
Option A from cycle 380 task results). Migrated the four Family A
branches (`vertex`, `cherry`, `mk [cherry]`, `mk [mk [cherry]]`) of
`inversePolynomial` (`OpenMath/Chapter4/Section422.lean:~4790`) to
dispatch to cycle 380's recursive helper `inversePolyChain k f` for
`k = 0, 1, 2, 3`. Family B / Family C branches (`broom₃`, `bushy`,
`mk [broom₃]`, `mk [vertex, cherry]`) remain as explicit
`if-then-else` polynomial bodies and were not touched.

Files modified:
* `OpenMath/Chapter4/Section422.lean` (~+30 LOC net; reorder + 1 def
  + 4 calibration witnesses + 4 Phase β bridges + 4 Phase γ branches
  + 4 cycle 380 bridge theorems).

## Approach

Followed the cycle 381 strategy Steps 0–5 in order, verifying
compilation between Step 0 (the reorder) and Steps 1–5:

* **Step 0 — Reorder.** Moved the cycle 380 block (`chainTree`
  definition + `chainTree_one/_two/_three` + `inversePolyChain`
  definition + `inversePolyChain_zero/_one/_two/_three` closed-form
  theorems plus their shared docstring) from after `inversePolynomial`
  to before it. The bridge theorems
  `inversePolyChain_{k}_eq_inversePolynomial` stayed in their original
  location (after `inversePolynomial`). The cycle 380 block docstring
  was lightly edited to drop the now-outdated paragraph claiming the
  cycle 374 pattern-match remains unchanged; replaced with a paragraph
  documenting the cycle 381 migration. After the reorder,
  `lake env lean OpenMath/Chapter4/Section422.lean` exit 0 with only
  the cycle 365 grandfathered sorry warning at line 2272.

* **Step 1 — Def edit.** Replaced the four Family A polynomial bodies
  with calls to `inversePolyChain k f`. The four Family B/C bodies
  stay verbatim.

* **Step 2 — Calibration witnesses.** Appended `inversePolyChain_{k}`
  rewrites at the end of the `rw` block of each Family A witness, so
  after `if_pos rfl` exposes `inversePolyChain k f` on the LHS, the
  rewrite collapses it to the cycle 341/367/369/378 polynomial.

* **Step 3 — Phase β bridges.** Same pattern as Step 2: appended
  `inversePolyChain_{k}` rewrites after `if_pos rfl` to expose the
  polynomial form before the closing `exact
  elementaryWeightQ_phi_inv_{tree} η_q`.

* **Step 4 — Phase γ.** In
  `inversePolynomial_eq_of_subtree_agreement`, inserted
  `inversePolyChain_{k}, inversePolyChain_{k}` (one for each side)
  after the final `if_pos rfl` of each Family A branch and *before*
  the `h_closed`-derived equality rewrites. This exposes the
  polynomial form on both sides of the goal, then the `h_closed`
  equalities close the goal as before.

* **Step 5 — Bridge theorem simplification.** Removed the initial
  `rw [inversePolyChain_{k}]` from each of the 4 bridge theorems
  `inversePolyChain_{k}_eq_inversePolynomial`. After the migration,
  `inversePolynomial` on a Family A tree definitionally reduces (via
  `unfold + if_pos rfl`) to `inversePolyChain k f`, so the goal closes
  by reflexivity at the end of the final `rw`. Kept the
  `unfold + if_*` proof body intact for readability; could be
  shortened to `by rfl` only if the `if` chain reduces under
  `Decidable` (left as cycle 382 micro-optimization).

## Result

**SUCCESS.** `lake env lean OpenMath/Chapter4/Section422.lean` exit 0
with only the cycle 365 grandfathered `sorry` warning at line 2272.
`lake env lean OpenMath/Chapter4.lean` (aggregator) exit 0.
`grep -c sorry OpenMath/Chapter4/Section422.lean` returns 5 (unchanged
from cycle 380 — 4 docstring + 1 code). Tautology scanner regex
returns no hits.

Axiom-clean spot-check (via scratch file `/tmp/axiom_check.lean`):
* `inversePolynomial_eq_of_subtree_agreement`,
  `elementaryWeightQ_phi_inv_eq_inversePolynomial_vertex`,
  `elementaryWeightQ_phi_inv_eq_inversePolynomial_mkMkCherry`,
  `elementaryWeightQ_phi_inv_eq_inversePolynomial_on_ladder`,
  `inversePolyChain_three`,
  `inversePolyChain_three_eq_inversePolynomial`
* all depend on `[propext, Classical.choice, Quot.sound]` only.

All four cycle 381 exit criteria met:
1. ✓ `inversePolynomial`'s four Family A branches dispatch to
   `inversePolyChain k f` for `k = 0, 1, 2, 3`.
2. ✓ All 8 calibration witnesses still compile.
3. ✓ All 8 Phase β bridges still compile.
4. ✓ Phase γ `inversePolynomial_eq_of_subtree_agreement` still
   compiles (4 Family A branches updated, 4 Family B/C unchanged).
5. ✓ 4 cycle 380 bridge theorems still compile (simplified).
6. ✓ `lake env lean Section422.lean` exit 0.
7. ✓ `grep -c sorry` = 5 (unchanged).
8. ✓ All updated theorems axiom-clean.
9. ✓ The 1 code sorry at line 2272 (cycle 365 grandfathered) untouched.

## Faithfulness check

No new `def`, `class`, `structure`, or `theorem` was introduced this
cycle. The migration is a pure refactoring: the cycle 374/377/378
calibration witnesses, Phase β bridges, and Phase γ subtree-agreement
theorem retain their exact statements; only their proof bodies grow
by the trailing `inversePolyChain_{k}` rewrite that bridges between
the new `inversePolyChain k f` form and the previously-shipped
polynomial RHS.

`inversePolynomial`'s type signature `(t : RT) → (f : RT → ℝ) → ℝ` is
unchanged. The body's *meaning* on the eight matched ladder trees is
unchanged — the four Family A branches now compute the same
polynomial via the cycle 380 recursion rather than via an explicit
polynomial. Cycle 380's
`inversePolyChain_{zero,one,two,three}` theorems verify the recursion
matches the cycle 341/367/369/378 closed forms, so no faithfulness
divergence from the textbook.

The four bridge theorems
`inversePolyChain_{k}_eq_inversePolynomial` had their proof bodies
simplified (dropped a single redundant initial `rw [inversePolyChain_{k}]`
since the RHS now collapses directly to the LHS form via `unfold +
if_*`). The statement is unchanged, so no new theorem introduction.

## Dead ends

None. The strategy was conservatively scoped (cycle 380 worker noted
"low-risk, mechanical, ~50 LOC") and the migration completed in a
single attempt. None of the five risks (R1–R5) materialized:

* **R1 (forward reference)**: resolved by the Step 0 reorder.
* **R2 (`inversePolyChain_k` rewrite shape)**: the rewrites fired
  cleanly without needing `show` / `simp only` fallbacks.
* **R3 (Phase γ `mk [mk [cherry]]` branch)**: ported last as
  recommended; no `by decide` discharge interference.
* **R4 (`rw` shape after `if_pos rfl`)**: not needed — `if_pos rfl`
  produced `inversePolyChain k f` in the goal shape exactly matching
  the `inversePolyChain_{k}` lemma's LHS.
* **R5 (Chapter4 aggregator regression)**: aggregator built cleanly.

## Discovery

1. **Cycle 380 helper layering pays off.** The Family A migration was
   trivially mechanical because cycle 380 had already proved the 4
   closed-form theorems against `inversePolyChain`. The only new work
   in cycle 381 was to point `inversePolynomial`'s body at the helper
   and then bridge the goal-form difference at each call site via a
   trailing `inversePolyChain_{k}` rewrite.

2. **Phase γ migration cost is predictably small.** The strategy's
   key insight — that `inversePolyChain_{k}, inversePolyChain_{k}`
   must come *before* the `h_closed` rewrites (since `h_closed`
   discharges occurrences of `f vertex`, `f cherry`, etc., not
   occurrences of `inversePolyChain k f`) — was exactly the right
   ordering. No re-ordering experiments were needed.

3. **Bridge theorems simplify by deletion, not by `rfl`.** The
   simplest post-migration proof for
   `inversePolyChain_{k}_eq_inversePolynomial` is the original
   `unfold + if_*` proof minus the leading `rw [inversePolyChain_{k}]`
   — i.e. drop one rewrite line. A pure `by rfl` may or may not work
   (depends on whether `Decidable.decide` reduces eagerly under the
   `if` chain); cycle 381 did not test this since the
   `unfold + if_*` form is already short and readable.

## Suggested next approach

The cycle 380 task results listed three options for cycle 381+; cycle
381 shipped **Option A** (Family A migration). The remaining options
are:

* **Option B (cycle 382+, medium-risk, multi-cycle): Derive a Family
  B closed form.** The bushy / mk [broom₃] / mk [vertex, cherry]
  trees do not fit the single-child ladder recursion. The cycle 379
  scoping doc §6.G1 documented sign-convention errors in an early
  attempted broom-family recursion derivation; a careful per-tree
  derivation against the cycle 370/371/372 closed forms is needed.
  *Recommended cycle 382 deliverable*: write a Lean Family B
  closed-form helper `inversePolyBroom n f` (or similar)
  recursively, prove a closed-form theorem at `n = 0` (the cycle 368
  broom₃ closed form) as cycle 380 did for `inversePolyChain_zero`,
  and write a scoping doc explaining the Family B recursion shape
  (parallel to cycle 379's Family A scoping doc). Defer Family B
  bridge migration to cycle 383+ pending the closed-form ship.

* **Option C (cycle 384+, high-risk): Close the cycle 365
  grandfathered sorry** at `Section422.lean:2272`
  (`powRep_sum_eq_of_strict_subtree_agreement` general body). The
  recursion through `underlyingOneStepMethod_aux` needs `Phase α'.4`
  closure (full recursive `inversePolynomial` driven by
  `inversePolyChain` plus Family B/C helpers). This is the eventual
  target after Options A (done) and B (cycle 382+) are complete.

* **Stretch option for cycle 382+ if Option B is too ambitious:**
  Verify the depth-4 Family A closed-form conjecture from cycle 379
  scoping doc §4 (`-c_0⁵ + 4c_0³c_1 - 2c_0c_1² - 3c_0²c_2 + 2c_1c_2
  + 2c_0c_3 - c_4`) by adding a `chainTree 4` calibration witness
  and showing `inversePolyChain 4 f` evaluates to the conjectured
  polynomial. This is purely empirical and exercises the recursion
  one step beyond the cycle 380 / 381 deliverables.

**Planner recommendation for cycle 382**: Option B Phase α'.3 Family
B scoping (a parallel of cycle 379 Phase α' scoping for Family B
trees), targeting a Lean ship of `inversePolyBroom_zero` matching
the cycle 368 broom₃ closed form by cycle 383. This compounds the
Phase α' investment from cycles 379–381 and keeps the streak going
without committing to the much harder Family C analysis.
