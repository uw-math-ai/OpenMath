# Cycle 383 Results

## Worked on

Phase α'.3 Family B bridge migration in
`OpenMath/Chapter4/Section422.lean` — parallel of cycle 381's Family A
migration. Re-route the `broom₃` and `bushy` branches of
`inversePolynomial t f` from explicit polynomial bodies to dispatches
of cycle 382's closed-form helper `inversePolyBroom k f`, then thread
the migration through all downstream consumers (calibration witnesses,
Phase β bridges, Phase γ subtree-agreement theorem) and ship two new
public bridge theorems `inversePolyBroom_{two, three}_eq_inversePolynomial`.

## Approach

Eight mechanical edits, following the strategy verbatim:

1. **Inversepolynomial body** (lines ~4927–4965). Replaced
   `broom₃`/`bushy` arms' explicit polynomials with
   `inversePolyBroom 2 f` and `inversePolyBroom 3 f`.

2. **broom₃ calibration witness**. Appended `inversePolyBroom_two`
   to the `rw [...]` chain after `if_pos rfl` — exactly the cycle
   381 cherry-calibration pattern with `_two` in place of `_one`.

3. **bushy calibration witness**. Analogous: appended
   `inversePolyBroom_three`.

4. **Phase β broom₃ bridge** `elementaryWeightQ_phi_inv_eq_inversePolynomial_broom₃`
   — appended `inversePolyBroom_two` before the `exact
   elementaryWeightQ_phi_inv_broom₃ η_q` close.

5. **Phase β bushy bridge** — analogous with `inversePolyBroom_three`.

6. **Phase γ broom₃ branch** of `inversePolynomial_eq_of_subtree_agreement`
   — appended `inversePolyBroom_two, inversePolyBroom_two` (one per
   side `f`/`g`) before the per-element substitution `hv, hc, hb`.

7. **Phase γ bushy branch** — analogous with two
   `inversePolyBroom_three` rewrites before `hv, hc, hb, hbu`.

8. **Two new public bridge theorems** after
   `inversePolyChain_three_eq_inversePolynomial` (~line 5305):

   * `inversePolyBroom_two_eq_inversePolynomial (f : RT → ℝ) :
       inversePolyBroom 2 f = inversePolynomial RootedTree.broom₃ f`
     — three-step `unfold + rw` proof.
   * `inversePolyBroom_three_eq_inversePolynomial (f : RT → ℝ) :
       inversePolyBroom 3 f = inversePolynomial RootedTree.bushy f`
     — five-step `unfold + rw` proof.

Verified each edit by reading the affected blocks before mutating and
diffing carefully against the existing cycle 381 Family A bridge
patterns. The cycle 382 dead-end warning (avoid bundled
`simp [recursive-def, name-eq-thm]`) did not apply since the migration
uses *targeted single-name* `rw`s only.

## Result

**SUCCESS.** All eight steps land.

* `lake env lean OpenMath/Chapter4/Section422.lean` exits 0 with the
  expected single warning at line 2272 (grandfathered cycle 365
  sorry).
* `lake build OpenMath.Chapter4` exits 0 (built 8043/8043 jobs).
* `grep -c sorry OpenMath/Chapter4/Section422.lean` = 5 (unchanged:
  4 docstring references + 1 actual code sorry at line 2279).
* Tautology regex `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$` over
  Section422.lean — 0 hits.
* `#print axioms` on the two new public bridge theorems
  (`inversePolyBroom_two_eq_inversePolynomial`,
  `inversePolyBroom_three_eq_inversePolynomial`) and the three
  touched theorems
  (`elementaryWeightQ_phi_inv_eq_inversePolynomial_broom₃`,
  `elementaryWeightQ_phi_inv_eq_inversePolynomial_bushy`,
  `inversePolynomial_eq_of_subtree_agreement`) all return
  `[propext, Classical.choice, Quot.sound]`. No axiom regressions.

§422 axiom-clean streak: 46 substantive + 1 doc (336–382) → **47
substantive + 1 doc** (336–383).

Section422.lean: ~5973 → ~5999 LOC (net +26: branches shrank by
~12 lines; bridge theorems and trailing `rw`s added ~38 lines).

## Faithfulness check

This cycle is **infrastructure migration**, not a new textbook entity.
Two new public theorems and one definition modification.

### `inversePolyBroom_two_eq_inversePolynomial`

Not a textbook entity — internal Lean housekeeping (closed-form ↔
pattern-match bridge for `t = broom₃`).

* Closed-form RHS captured by both sides:
  `-(f vertex)^3 + 2·f vertex·f cherry - f broom₃`.
* Unchanged from cycle 368's `elementaryWeightQ_phi_inv_broom₃`
  textbook value at `broom₃` (the source of the original explicit
  polynomial body before the migration).
* Lean statement captures: **same content** (equality of two
  routes to the identical closed form).

### `inversePolyBroom_three_eq_inversePolynomial`

Not a textbook entity — analogous bridge for `t = bushy`.

* Closed-form RHS captured by both sides:
  `(f vertex)^4 − 3·(f vertex)^2·f cherry + 3·f vertex·f broom₃
  − f bushy`.
* Unchanged from cycle 370's `elementaryWeightQ_phi_inv_bushy`
  textbook value at `bushy`.
* Lean statement captures: **same content**.

### `inversePolynomial` body modification

The migration is **observationally invariant**: both
`inversePolyBroom_two_eq_inversePolynomial` and
`inversePolyBroom_three_eq_inversePolynomial` show that the new
`inversePolyBroom k f` dispatches are pointwise equal (over all
`f : RT → ℝ`) to the cycle 374/377 explicit polynomial bodies. The
`def`'s extensional behavior is unchanged.

* Lean definition captures: **same content** (provably equivalent
  to the pre-migration `def`).
* Tautology / hypothesis-strength check: pre- and post-migration
  proofs of `inversePolynomial broom₃ f = …` and
  `inversePolynomial bushy f = …` produce the same closed-form
  values; no hypothesis weakening or strengthening.
* Definition smuggling check: the new branches dispatch to
  `inversePolyBroom k f` which is `noncomputable def` shipped at
  cycle 382 with `inversePolyBroom_{zero, one, two, three}` proving
  the cycle 341/367/368/370 closed forms. The closed-form table
  matches Butcher's textbook entries verbatim. No definitional
  smuggling.

### Hypothesis check on the 5 touched/new theorems

| Theorem | Hypothesis change | Conclusion change |
|---|---|---|
| `inversePolyBroom_two_eq_inversePolynomial` | new theorem (none) | new theorem |
| `inversePolyBroom_three_eq_inversePolynomial` | new theorem (none) | new theorem |
| `…_eq_inversePolynomial_broom₃` (Phase β) | none | none |
| `…_eq_inversePolynomial_bushy` (Phase β) | none | none |
| `inversePolynomial_eq_of_subtree_agreement` (Phase γ) | none | none |

The Phase β/γ theorems' statements are byte-identical to the cycle
377/378 versions; only the proof bodies grew to thread the migration.

## Dead ends

None this cycle. The migration was mechanical and followed cycle
381's Family A pattern exactly. The dead-end warnings in the cycle
383 strategy (avoid `simp [recursive-def, name-eq-thm]`; avoid
touching `inversePolyBroom_{zero, one}`; avoid Family C scoping; avoid
cycle 365 grandfathered work) were all respected and none of them
were attempted.

The stale `.olean` cache initially showed
`inversePolyBroom_{two,three}_eq_inversePolynomial` as unknown
constants during the `#print axioms` check — resolved by running
`lake build OpenMath.Chapter4.Section422` after the edit (rebuilds in
~510s cold, ~160s warm) so the downstream importer sees the new
declarations.

## Discovery

**Single-name `rw` is faithful migration.** Trailing
`rw [inversePolyBroom_two]` or
`rw [inversePolyBroom_two, inversePolyBroom_two]` (one per side in
the Phase γ branch) cleanly bridges the migrated
`inversePolynomial t f` body to the pre-migration explicit
polynomial closed form. No `simp` overreach, no `ring` normalization
needed — the two routes are *definitionally* equal modulo the
`inversePolyBroom` unfold, which `rw [name-eq-thm]` performs in a
single beta-step. This is the cleanest possible migration cost
(zero new tactic surgery) and reaffirms the cycle 382 lesson that
`rw [name-eq-thm]` should be the default folding tool when both
sides share an explicit polynomial form.

**Phase γ bridge needs two rewrites, not one.** Unlike Phase β's
bridges (which only have one `inversePolynomial …` occurrence on
their RHS), the Phase γ `inversePolynomial_eq_of_subtree_agreement`
unfolds two `inversePolynomial` invocations (one per `f`, one per
`g`). Each broom₃/bushy branch therefore needs *two* trailing
`inversePolyBroom_k` rewrites in the `rw` chain, applied
left-to-right. This is the analog of the cycle 381 cherry/`mk
[cherry]` pattern where both sides also needed two rewrites.

## Suggested next approach

Cycle 384: ship the **Family C scoping doc** for the three
heterogeneous-children trees of the cycle 378 ladder that don't fit
either Family A (single-child ladder) or Family B (`mk [vertex^k]`
brooms):

* `mk [broom₃]` — single non-leaf child with arity 2 of leaves.
  Closed form: `v⁴ − 3v²c + vb' + 2vm − M` (from cycle 371).
* `mk [vertex, cherry]` — leaf + non-leaf with arity 1.
  Closed form: `v⁴ − 3v²c + c² + vb' + vm − mvc` (from cycle 372).
* (Re-scoping for `mk [mk [cherry]]`: this *is* already covered by
  Family A's `inversePolyChain 3 f` since it's a depth-3 single-child
  chain — but the closed form includes an `(f cherry)²` term not
  present in the recursive Family A formula's prediction.
  Probably the closed-form proof of `inversePolyChain_three`
  produces this `c²` via the chain's `_two` invocation, not via a
  Family C cross-term; needs verification.)

The Family C scoping doc should determine whether these three trees
share a unifying closed-form helper (e.g. a parameterised binomial
sum extension capturing cross-terms `f cherry · f vertex` and
`(f cherry)²`), or whether each tree needs an ad-hoc bespoke
helper. The cycle 379 Phase α' scoping doc §4 sketched a partial
analysis (the `+vb'` and `+2vm` mixed cross-terms in `mk [broom₃]`'s
closed form) but did not propose a unified Family C recipe.

After Family C ships, cycle 385+ should attempt the **unified
recursive `inversePolyTree : RT → (RT → ℝ) → ℝ`** that dispatches
by pattern-matching on the root's children list, calling the
appropriate Family A/B/C helper for each child subtree
recursively. This is the precondition for closing the cycle 365
grandfathered sorry at `Section422.lean:2279`
(`powRep_sum_eq_of_strict_subtree_agreement`), which needs the
global bridge `elementaryWeightQ_phi_inv_eq_inversePolynomial`
over all `t : RT`.

**Stretch task (optional)**: a concrete-`f` regression-test
`example` exercising
`inversePolyBroom_{two, three}_eq_inversePolynomial` on the
constant-1 method `(fun _ => 1)` would validate that the bridge
fires on a concrete `f`. Skipped this cycle to keep the diff
minimal; cycle 384 worker could ship as a 5-line drop-in
alongside the Family C scoping doc.
