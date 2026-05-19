# Cycle 395 Strategy

## Context

Cycle 394 closed Phase α'.4.1 P6 (`monochildCrossTerm` extended with
`cherry` branch + `inversePolyTree_mkCherry` calibration), axiom-clean,
sorry count unchanged at 5. §422 streak: **57 substantive + 2 doc**
(cycles 336–394).

No Aristotle results pending. No new blockers reported.

## Priority 1 — DELIVERABLE: Phase α'.4.1 P7 — extend `monochildCrossTerm`
for `c = mk [cherry]` + ship `inversePolyTree_mkMkCherry` calibration

This is the cycle 394 worker's explicit "Suggested next approach"
(`task_results/cycle_394.md` §"Suggested next approach"). Mechanical
extension of the cycle 394 template, ~30–40 LOC.

### Why this target

* **Concrete, well-scoped**: cycle 394 worker paper-derived the target
  value `monochildCrossTerm (mk [cherry]) f = -v²c + c² + vm` from cycle
  378's `mk [mk [cherry]]` closed form. No new mathematics; mechanical
  port of the cycle 394 template.
* **Preserves momentum**: extends the 57-cycle §422 axiom-clean streak
  by one more axiom-clean ship.
* **Unblocks downstream**: with `monochildCrossTerm` covering 3 branches
  (`broom₃`, `cherry`, `mk [cherry]`), Phase α'.4.2 can migrate
  `inversePolynomial`'s `mk [cherry]` branch in cycle 396.

### File touched (1 file only)

`OpenMath/Chapter4/Section422.lean`.

### Concrete steps

**Step 1 — Extend `monochildCrossTerm` (~10 LOC delta)**

Locate the existing `monochildCrossTerm` definition (cycle 394 has it
at ~line 6315–6346, with two `else if` branches: `c = broom₃` and
`c = cherry`). Insert a third `else if c = RootedTree.mk [RootedTree.cherry]`
branch between the `cherry` branch and the default `else 0`. Value:

```lean
-(f RootedTree.vertex)^2 * f RootedTree.cherry
  + (f RootedTree.cherry)^2
  + f RootedTree.vertex * f (RootedTree.mk [RootedTree.cherry])
```

Update the docstring to add a bullet documenting the new branch.

**IMPORTANT name-resolution gotcha** (per
`feedback_ring_def_opacity.md` and cycle 374's name-resolution note):
the `mk [...]` constructor at the top level can resolve to Mathlib's
`_root_.RootedTree.mk`, not our `OpenMath.Chapter3.Section310.RootedTree.mk`.
Use the qualifier convention already established by cycle 393's
`inversePolyTree_mkBroom₃` and cycle 394's `inversePolyTree_mkCherry`
ships — check those theorems first and mirror their qualified-name
choices exactly.

**Step 2 — Update `inversePolyTree_cherry` proof (~1 LOC delta)**

Cycle 394 currently has `inversePolyTree_cherry`'s proof body include
a `show monochildCrossTerm vertex f = 0` block that discharges with
`rw [if_neg (by decide), if_neg (by decide)]` (two `if_neg`s for
`vertex ≠ broom₃` and `vertex ≠ cherry`).

Adding the third `else if c = mk [cherry]` branch means `vertex ≠ mk
[cherry]` is now a third discharge. Update the `rw` chain to:

```lean
rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]
```

(Three `if_neg`s before reaching the default `else 0`.) Each `by decide`
discharges via `RootedTree`-constructor disjointness per
`feedback_indexed_inductive_cases_disjoint.md`.

**Step 3 — Ship `inversePolyTree_mkMkCherry` calibration (~25 LOC)**

Insert immediately after `inversePolyTree_mkCherry` (cycle 394's new
theorem). Statement matches cycle 378's `elementaryWeightQ_phi_inv_mkMkCherry`
closed form evaluated at generic `f : RT → ℝ`:

```
inversePolyTree (mk [mk [cherry]]) f
  = (f vertex)^4
    - 3 * (f vertex)^2 * f cherry
    + (f cherry)^2
    + 2 * f vertex * f (mk [cherry])
    - f (mk [mk [cherry]])
```

Proof template (mirror cycle 394's `inversePolyTree_mkCherry` proof
exactly, swapping the inner `cherry` for `mk [cherry]`):

```lean
rw [inversePolyTree, inversePolyTree_mkCherry]
rw [show monochildCrossTerm (mk [cherry]) f
      = -(f vertex)^2 * f cherry
        + (f cherry)^2
        + f vertex * f (mk [cherry]) by
      unfold monochildCrossTerm
      rw [if_neg (by decide), if_neg (by decide), if_pos rfl]]
ring
```

(Adjust qualified-name conventions to match cycle 394's
`inversePolyTree_mkCherry` precedent exactly. Inspect that theorem
first for the canonical qualified-name pattern.)

**Docstring** should reference cycle 378's
`elementaryWeightQ_phi_inv_mkMkCherry` as the target closed form being
matched at the unquotiented `inversePolyTree` level.

**Proof template explanation** (from cycle 394 task results §Discovery):

* `rw [inversePolyTree, inversePolyTree_mkCherry]` unfolds the
  single-child recursion at the outer `mk [mk [cherry]]` to expose
  `-(v · inversePolyTree (mk [cherry]) f) + monochildCrossTerm (mk
  [cherry]) f - f (mk [mk [cherry]])`, then substitutes cycle 394's
  `inversePolyTree_mkCherry = -v³ + 2vc - m`.
* The `show monochildCrossTerm (mk [cherry]) f = …` block evaluates
  the new `mk [cherry]` branch via `unfold + if_neg × 2 + if_pos rfl`
  (two `if_neg`s for `mk [cherry] ≠ broom₃` and `mk [cherry] ≠
  cherry`, then `if_pos rfl` fires the new third branch).
* `ring` collapses the resulting polynomial identity. Paper-verified:
  `-(v · (-v³ + 2vc - m)) + (-v²c + c² + vm) - M_mc
    = v⁴ - 2v²c + vm - v²c + c² + vm - M_mc
    = v⁴ - 3v²c + c² + 2vm - M_mc` ✓

### Verification commands (after writing)

1. `lake env lean OpenMath/Chapter4/Section422.lean` — must exit 0
   with only the cycle 365 grandfathered sorry warning at `:2272`.
2. `lake build OpenMath.Chapter4.Section422` — must exit 0.
3. `grep -c sorry OpenMath/Chapter4/Section422.lean` — must return
   **5** (unchanged from cycle 394).
4. `#print axioms inversePolyTree_mkMkCherry` — must return
   `[propext, Classical.choice, Quot.sound]`. No `sorryAx`.
5. Regression check: `#print axioms inversePolyTree_cherry` must
   still be `[propext, Classical.choice, Quot.sound]` (the one-line
   proof update preserves axiom-cleanliness).
6. Regression check: spot-check `#print axioms` on the other 7
   cumulative `inversePolyTree_*` calibration witnesses
   (`_vertex, _broom₃, _mkBroom₃, _mkCherry, _mkCherryCherry,
   _mkBroomCherry, _mkVertexCherry`) — all must remain axiom-clean.

### Bookkeeping (mandatory)

* `extraction/formalization_data/lean_status.json`: bump `def:422B`
  row's `cycle_completed_at` from 394 → 395. Status stays `partial`.
* `plan.md`: update the `def:422B` line — append cycle 395 closure
  note to the existing Phase α' narrative (parallel to cycle 394's
  entry).
* `.prover-state/issues/def_422B_phase_alpha_prime_scoping.md`:
  append a "Cycle 395 update" subsection documenting the third
  `monochildCrossTerm` branch and the new calibration witness.

### LOC budget

~30–40 LOC total. Hard cap: 60 LOC. If the deliverable exceeds 60
LOC, inspect for over-engineering and consider splitting Step 3
(the calibration witness) to cycle 396.

## Priority 2 — STRETCH (only if Priority 1 closes in < 60 min)

Phase α'.4.2 migration of `inversePolynomial`'s `mk [cherry]` branch
(parallel of cycles 391 and 393). Recipe:

1. Add bridge theorem `inversePolyTree_mkCherry_eq_inversePolynomial`:

   ```lean
   theorem inversePolyTree_mkCherry_eq_inversePolynomial (f : RT → ℝ) :
       inversePolyTree (mk [RootedTree.cherry]) f
         = inversePolynomial (mk [RootedTree.cherry]) f
   ```

   Proof: `unfold inversePolynomial; rw [if_neg ×3, if_pos rfl]`
   (3 `if_neg`s for `mk [cherry] ≠ vertex/cherry/broom₃`, then
   `if_pos rfl` fires the `mk [cherry]` branch). The `mk [cherry]`
   branch is currently the 4th in the `inversePolynomial` if-chain.

2. Migrate `inversePolynomial`'s `mk [cherry]` body from the
   explicit 3-term closed form (`-v³ + 2vc - m`) to `inversePolyTree
   (mk [cherry]) f` dispatch. Value-preserving via cycle 394's
   `inversePolyTree_mkCherry`.

3. Update 3 consumers (each trailing one extra rewrite to bridge):
   - The Phase α.1/α.2 calibration `example` for `mk [cherry]`.
   - The Phase β.1 bridge
     `elementaryWeightQ_phi_inv_eq_inversePolynomial_mkCherry`.
   - The Phase γ branch of
     `inversePolynomial_eq_of_subtree_agreement` (apply
     `inversePolyTree_mkCherry` twice, once per `f`/`g` side).

LOC budget for Priority 2: ~40–50 LOC. Total cycle 395 ceiling if
attempted: 110 LOC.

**Do NOT attempt Priority 2 unless Priority 1 verification passes
cleanly and the cycle has remaining time.** Cycle 395 worker should
not bundle Priority 2 if Priority 1 hits any unexpected friction.

## What NOT to attempt

* **Do NOT skip Priority 1's Step 2** (the one-line update to
  `inversePolyTree_cherry`'s proof). Per cycle 394 Discovery: every
  time `monochildCrossTerm` grows a new branch BEFORE the default
  `else 0`, the `show monochildCrossTerm vertex f = 0` block in
  `inversePolyTree_cherry` needs one additional `if_neg (by decide)`
  discharge. Forgetting this breaks the proof.

* **Do NOT touch the cycle 365 grandfathered sorry** at line 2272
  (`powRep_sum_eq_of_strict_subtree_agreement`). Per
  `def_422B_subLemmaA_inductive_plan.md` and
  `def_422B_phase_alpha_prime_scoping.md`, closing it is multi-cycle
  Phase α' completion work. Cycle 395 is one ladder rung among
  many.

* **Do NOT pivot to a fresh entity.** §422 streak (57 substantive +
  2 doc) is productive and compound momentum is on this track.
  Witness library accumulation continues to inform Phase α'.4
  design.

* **Do NOT attempt to compile `Section441.lean`**. 43+ consecutive
  GPFS timeouts since cycle 182 (see `cycle_182_gpfs_slowness.md`).
  Cycle 395 work is entirely in `Section422.lean`.

* **Do NOT raise `maxHeartbeats` above 200000.** The Priority 1
  proof is shallow (`rw + show + unfold + rw + if_neg × 2 + if_pos
  rfl + ring`); if it stalls, decompose or check for definitional
  opacity (per `feedback_ring_def_opacity.md`).

* **Do NOT introduce `axiom` or `constant` declarations.** Cycle
  200/201 and cycle 149/150 rollback precedents apply. Axiom-clean
  or bust.

* **Do NOT introduce new sorries.** Sorry count must stay at 5 (4
  docstring + 1 grandfathered cycle 365).

* **Do NOT use `simp [monochildCrossTerm, …]`** in the
  `inversePolyTree_mkMkCherry` proof. Per
  `feedback_simp_recursive_def_overunfolds.md`, `simp` on a
  recursive `def` plus name-eq theorems over-unfolds. Use the
  targeted `rw + show + unfold + rw [if_neg, if_pos rfl]` pattern
  established by cycles 392/393/394.

* **Do NOT submit to Aristotle.** Pure manual closure cycle. The
  Priority 1 proof has zero `sorry`s to mine; submitting is wasted
  compute.

## What to read before starting

1. **`task_results/cycle_394.md`** — particularly the §"Suggested
   next approach" section which spells out the exact recipe.

2. **`OpenMath/Chapter4/Section422.lean`** around the
   `monochildCrossTerm` definition (~line 6315–6346 per cycle 394)
   and the `inversePolyTree_*` calibration block. Inspect:
   - Current `monochildCrossTerm` body (note the 2 existing
     branches).
   - `inversePolyTree_cherry`'s proof body (note the `show
     monochildCrossTerm vertex f = 0` block with 2 `if_neg`s).
   - `inversePolyTree_mkCherry` (cycle 394's new theorem) — this is
     the canonical template for cycle 395's new
     `inversePolyTree_mkMkCherry`.
   - `inversePolyTree_mkBroom₃` (cycle 393) — same template.

3. **Memory files relevant to the task**:
   - `feedback_indexed_inductive_cases_disjoint.md` — `cases h` /
     `by decide` on disjoint `RootedTree`-constructor goals.
   - `feedback_ring_def_opacity.md` — `ring` cannot bridge `f (mk
     [...])` to `f namedTree` for non-reducible `def`s; use `show`
     to canonicalise.
   - `feedback_simp_recursive_def_overunfolds.md` — targeted `rw`
     pattern for `monochildCrossTerm`-style recursive defs.

## Success criteria summary

After cycle 395 worker completes:

1. ✅ `OpenMath/Chapter4/Section422.lean`: `monochildCrossTerm`
   extended with `c = mk [cherry]` branch; `inversePolyTree_cherry`
   proof updated with one additional `if_neg`; new theorem
   `inversePolyTree_mkMkCherry` shipped axiom-clean.

2. ✅ `lake build OpenMath.Chapter4.Section422` exits 0.

3. ✅ `grep -c sorry OpenMath/Chapter4/Section422.lean` returns 5
   (unchanged).

4. ✅ `#print axioms inversePolyTree_mkMkCherry` →
   `[propext, Classical.choice, Quot.sound]` only.

5. ✅ All other cumulative calibration witnesses + cycle 394's
   `inversePolyTree_cherry` regression-checked axiom-clean.

6. ✅ Bookkeeping updates: `lean_status.json`, `plan.md`,
   `def_422B_phase_alpha_prime_scoping.md`.

7. ✅ `task_results/cycle_395.md` written documenting deliverables,
   approach, faithfulness check, dead ends, discovery, and next
   steps.

8. §422 streak advances: 57 → **58 substantive + 2 doc** (336–395).
