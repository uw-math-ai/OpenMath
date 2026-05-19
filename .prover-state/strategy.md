# Cycle 401 Strategy: Phase α'.4.2 P5 — `bushy` migration

## Overview

Ship the **final** Phase α'.4.2 ladder-tree migration: route
`inversePolynomial`'s `bushy` branch from cycle 383's
`inversePolyBroom 3 f` dispatch to a `inversePolyTree bushy f`
dispatch. This is the 5th and last Phase α'.4.2 migration (after
cycles 391 `mk [vertex, cherry]`, 393 `mk [broom₃]`, 396 `mk [cherry]`,
397 `mk [mk [cherry]]`).

**After cycle 401, all 9 ladder trees route uniformly through
`inversePolyTree`.** This is a meaningful structural milestone for
the §422 Phase α' research track per scoping doc
`.prover-state/issues/def_422B_phase_alpha_prime_family_bushy_scoping.md`
§6.3.

## Priority 0 — Verify cycle 400 state (do this FIRST, <2 min)

Spot-check that cycle 400's `inversePolyTree_bushy` is at HEAD:

```bash
git log -1 --format='%H %s'  # Should show b4f5c7f Cycle 400 …
grep -n "^theorem inversePolyTree_bushy " OpenMath/Chapter4/Section422.lean
wc -l OpenMath/Chapter4/Section422.lean  # Expect ~8150
grep -c sorry OpenMath/Chapter4/Section422.lean  # Expect 5
```

If any disagrees with the expectation, investigate before proceeding
— canonical phantom-commit verdict pattern; see
`.prover-state/issues/phantom_commit_verdict_pattern.md`.

## Priority 1 — DELIVERABLE: bushy migration (6 edits)

All edits in `OpenMath/Chapter4/Section422.lean`. Execute in order.

### Branch ordering reference

Per cycles 374/377/378, `inversePolynomial`'s if-then-else chain is:

1. `vertex` (cycle 374)
2. `cherry` (cycle 374; migrated cycle 396)
3. `broom₃` (cycle 374; migrated cycle 393)
4. `mk [cherry]` (cycle 374; migrated cycle 396)
5. **`bushy`** ← this migration target
6. `mk [broom₃]` (cycle 377; migrated cycle 393)
7. `mk [vertex, cherry]` (cycle 377; migrated cycle 391)
8. `mk [mk [cherry]]` (cycle 378; migrated cycle 397)

So the bridge theorem needs **4 `if_neg`** discharges (positions 1–4)
before `if_pos rfl` fires on the `bushy` branch.

### Step A — Ship the bridge theorem

Insert immediately after cycle 397's
`inversePolyTree_mkMkCherry_eq_inversePolynomial`:

```lean
/-- *Phase α'.4.2 bridge (cycle 401, bushy):* `inversePolyTree`
applied to `bushy` agrees with `inversePolynomial bushy`, supporting
the migration of `inversePolynomial`'s `bushy` branch from the
Family B `inversePolyBroom 3` dispatch (cycle 383) to the unified
`inversePolyTree` dispatch. -/
theorem inversePolyTree_bushy_eq_inversePolynomial (f : RT → ℝ) :
    inversePolyTree RootedTree.bushy f
      = inversePolynomial RootedTree.bushy f := by
  unfold inversePolynomial
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_pos rfl]
```

Both sides reduce to `inversePolyTree RootedTree.bushy f` after the
`if_pos rfl` (post-Step B); closure is the implicit `rfl` after `rw`.

### Step B — Migrate `inversePolynomial`'s `bushy` branch

Locate the `bushy` branch (5th in the chain). Currently per cycle 383:

```lean
  else if t = RootedTree.bushy then
    inversePolyBroom 3 f
```

Replace with:

```lean
  else if t = RootedTree.bushy then
    inversePolyTree RootedTree.bushy f
```

**Value-preserving** by cycle 400's `inversePolyTree_bushy` matching
cycle 370's closed form `v⁴ − 3v²c + 3v·b' − f bushy`, which also
equals cycle 383's `inversePolyBroom 3 f` expansion.

### Step C — Update Phase α.2 calibration example for `bushy`

Locate the cycle-377-era calibration `example` that closes
`inversePolynomial bushy f = …` via `unfold inversePolynomial; rw […
inversePolyBroom_three]`. Replace the trailing `inversePolyBroom_three`
rewrite with `inversePolyTree_bushy`.

### Step D — Update Phase β.2 bridge

`elementaryWeightQ_phi_inv_eq_inversePolynomial_bushy` (cycle 377-era)
has a trailing `inversePolyBroom_three` in its `rw` chain. Replace
with `inversePolyTree_bushy`.

### Step E — Update Phase γ branch (TWO replacements)

In `inversePolynomial_eq_of_subtree_agreement`, the `bushy` arm has
TWO `inversePolyBroom_three` occurrences (one per `f` side, one per
`g` side per cycle 393's double-replacement pattern). Replace **both**
with `inversePolyTree_bushy`.

**Tip** (cycle 397 Discovery): try `Edit` with `replace_all: true` on
`inversePolyBroom_three` if both `bushy`-arm occurrences are the only
matches at that branch. If the file has other `inversePolyBroom_three`
references at unrelated locations (cycles 374/382/383 ships), use
targeted `Edit` calls with sufficient surrounding context to make
each `old_string` unique.

### Step F — Derivative fix on cycle 382's
`inversePolyBroom_three_eq_inversePolynomial`

After Step B lands, cycle 382's bridge theorem's goal becomes
`inversePolyBroom 3 f = inversePolyTree bushy f` (the post-migration
RHS of `inversePolynomial bushy`). Append `inversePolyBroom_three,
inversePolyTree_bushy` to its existing `rw` chain so both routes
reduce to cycle 370's closed form.

Theorem statement remains unchanged; only the proof body extends.
Cycle 393 / 396 / 397 precedent for this exact pattern.

## Priority 2 — Verification

```bash
lake build OpenMath.Chapter4.Section422
```

Should exit 0 with only the pre-existing grandfathered cycle 365
sorry warning at line 2272. Expected build time: 200–500 s warm
(cycle 397 baseline: 200 s; cycle 396: 502 s).

```bash
grep -c sorry OpenMath/Chapter4/Section422.lean  # Expect 5 (unchanged)
```

Run `#print axioms` on the new and touched theorems via a scratch
test file:

* `inversePolyTree_bushy_eq_inversePolynomial` (new, Step A)
* `elementaryWeightQ_phi_inv_eq_inversePolynomial_bushy` (Step D)
* `inversePolynomial_eq_of_subtree_agreement` (Step E)
* `inversePolyBroom_three_eq_inversePolynomial` (Step F)
* `inversePolyTree_bushy` (cycle 400, regression check)

All should return `[propext, Classical.choice, Quot.sound]`.

## Priority 3 — Bookkeeping updates

### `extraction/formalization_data/lean_status.json`

Bump `def:422B` `cycle_completed_at` from 400 to 401. Status stays
`partial`.

### `plan.md`

Append to the `def:422B` partial-row narrative:

> **Cycle 401** ships Phase α'.4.2 P5 (`bushy` migration) — last
> ladder migration; all 9 ladder trees route uniformly through
> `inversePolyTree`. 5 edits (bridge theorem, body migration, Phase
> α.2 + β.2 + γ rewrites, cycle 382 bridge fix); axiom-clean. §422
> streak: 63 substantive + 3 doc (cycles 336–401).

### `.prover-state/issues/def_422B_phase_alpha_prime_family_bushy_scoping.md`

Append a §12 Cycle 401 closure subsection (parallel to §11 cycle 399
closure). Document:

* Six edits landed; build clean; sorry count unchanged.
* §422 axiom-clean streak: 62 substantive + 3 doc (336–400) →
  **63 substantive + 3 doc** (336–401).
* All 9 ladder trees route uniformly through `inversePolyTree`.
* Phase α'.4 fully closed.
* Cycle 402+ candidates: Phase α'.5 (`k ≥ 3` heterogeneous children)
  scoping doc; Phase β/γ extension toward cycle 365 sorry closure
  scoping doc; pivot to fresh entity (`def:451A`, `def:442A`,
  `thm:535A`, `thm:541A` per `cycle_336_pivot_options.md`).

### `.prover-state/issues/def_422B_phase_alpha_prime_scoping.md`

Append a brief cycle 401 update note (parallels the cycle 393/396/397
update notes).

## What NOT to do

1. **Do NOT modify cycle 400's `inversePolyTree_bushy`.** It is the
   load-bearing calibration witness backing Step B's value-preservation.

2. **Do NOT introduce new `*CrossTerm` branches.** All needed
   infrastructure (cycle 399's `trichildCrossTerm` + `trichildPolynomial`,
   cycle 400's `inversePolyTree_bushy`) is at HEAD.

3. **Do NOT attempt Phase α'.5 (`k ≥ 3` heterogeneous children).**
   Multi-cycle work that needs its own scoping doc; cycle 402+.

4. **Do NOT attempt closing the cycle 365 grandfathered sorry at line
   2272.** Requires the now-unified `inversePolyTree` PLUS new
   infrastructure beyond Phase α'.4. Cycle 402+ work — likely needs a
   scoping doc first.

5. **Do NOT use `Polynomial.ext`-style proof patterns.** The bridge
   theorem closes by `unfold + if_neg × 4 + if_pos rfl`. Cycle
   391/393/396/397 recipe verbatim.

6. **Do NOT triple-up `rw [inversePolyTree_vertex]` in any new proof.**
   Cycle 400 confirmed `rw` rewrites all occurrences in one pass.

7. **Do NOT skip Step F.** Without it, cycle 382's bridge theorem
   fails to typecheck after Step B's migration. Hard build dependency.

8. **Do NOT submit anything to Aristotle.** No `sorry`s to mine; this
   is pure mechanical migration. Cycle 397 precedent: 100% manual.

9. **Do NOT touch files outside `OpenMath/Chapter4/Section422.lean`.**
   All cycle 401 Lean edits are confined to one file. Bookkeeping
   updates touch `.prover-state/` and `plan.md` + `lean_status.json`
   only.

10. **Do NOT introduce any new `noncomputable def` or `structure`.**
    All cycle 401 deliverables are theorems and body edits.

11. **Do NOT change cycle 383's `inversePolyBroom_three` calibration
    theorem statement.** Only the migration touchpoints (cycle 382's
    bridge in Step F) extend; cycle 383's `inversePolyBroom_three`
    closed-form witness stays untouched.

## Recipe stability

This is the **fifth and final** Phase α'.4.2 migration. The pattern
across cycles 391, 393, 396, 397, 401 has stabilised:

| Step | Action |
|------|--------|
| A | New bridge theorem `inversePolyTree_<tree>_eq_inversePolynomial` with N `if_neg` + `if_pos rfl` |
| B | `inversePolynomial`'s `<tree>` branch body migrated |
| C | Phase α.2 calibration example's trailing rewrite swapped |
| D | Phase β bridge's trailing rewrite swapped |
| E | Phase γ branch's TWO rewrites swapped |
| F | Cycle 380/382 derivative bridge's proof extended |

**LOC budget: ~50 LOC** (cycle 397 actuals; cycle 401 should match).

## Cycle 402+ outlook (informational, not for cycle 401)

Once all 9 ladder trees route through `inversePolyTree`, the Phase
β/γ infrastructure is positioned for collapse. The cycle 365
grandfathered Sub-lemma A sorry at line 2272 becomes attackable via
the unified recursive structure — but it remains multi-cycle work
that needs its own scoping doc.

Cycle 402 should likely produce that scoping doc rather than
attempting closure directly. Alternatively, cycle 402 may pivot to a
fresh entity (`def:451A`, `def:442A`, `thm:535A`, `thm:541A` per
`cycle_336_pivot_options.md`). The §422 streak is approaching 70
substantive cycles — natural inflection point for a pivot decision.

That decision belongs to cycle 402's planner. Cycle 401's job is to
land the last Phase α'.4.2 migration cleanly.
