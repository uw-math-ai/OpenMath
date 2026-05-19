# Cycle 397 strategy — Phase α'.4.2 `mk [mk [cherry]]` migration

## TL;DR

**Target**: Phase α'.4.2 migration of `inversePolynomial`'s
`mk [mk [cherry]]` branch from `inversePolyChain 3 f` to
`inversePolyTree (mk [mk [cherry]]) f`. **Strict mechanical mirror of
cycle 396** (which did the analogous `mk [cherry]` migration).
Calibration witness `inversePolyTree_mkMkCherry` already shipped
cycle 395.

**File**: `OpenMath/Chapter4/Section422.lean` only (plus bookkeeping).

**LOC budget**: ~40 LOC. Single-cycle, axiom-clean, sorry count
unchanged at 5.

**Streak preservation**: §422 streak stands at 59 substantive + 2 doc
(cycles 336–396). Cycle 397 must ship axiom-clean to extend to 60.

## State at HEAD (cycle 396)

* No pending Aristotle results.
* `inversePolyTree` is the recursive Family A/B/C dispatcher.
* `monochildCrossTerm` has three branches (`broom₃`, `cherry`,
  `mk [cherry]`) plus default `else 0`.
* All 9 ladder-tree calibration witnesses
  `inversePolyTree_{vertex, cherry, broom₃, mkBroom₃, mkCherry,
  mkMkCherry, mkCherryCherry, mkBroomCherry, mkVertexCherry}` shipped
  axiom-clean.
* `inversePolynomial` branch dispatch (per cycle 396 task results §State):
  1. `vertex` → `inversePolyChain 0 f`
  2. `cherry` → `inversePolyChain 1 f`
  3. `broom₃` → `inversePolyBroom 2 f` (cycle 383 Family B)
  4. `mk [cherry]` → `inversePolyTree (mk [cherry]) f` ✓ cycle 396
  5. `bushy` → `inversePolyBroom 3 f` (cycle 383)
  6. `mk [broom₃]` → `inversePolyTree (mk [broom₃]) f` ✓ cycle 393
  7. `mk [vertex, cherry]` → `inversePolyTree (...) f` ✓ cycle 391
  8. **`mk [mk [cherry]]` → `inversePolyChain 3 f`** ← cycle 397 TARGET
* Grandfathered sorry at line 2279 (cycle 365 Sub-lemma A) — DO NOT
  TOUCH.

## Priority 1 — DELIVERABLES (6 edits, in order)

The recipe is **identical to cycle 396's** modulo three substitutions:

* `mk [cherry]` → `mk [mk [cherry]]`
* `inversePolyChain 2 f` → `inversePolyChain 3 f`
* `inversePolyTree_mkCherry` → `inversePolyTree_mkMkCherry`
* `inversePolyChain_two` → `inversePolyChain_three`

### Step 0: determine `if_neg` count by grep

Before writing the bridge theorem, run

```
Grep pattern="else if t = OpenMath.Chapter3.Section310.RootedTree.mk \[OpenMath.Chapter3.Section310.RootedTree.mk \[RootedTree.cherry\]\]" path="OpenMath/Chapter4/Section422.lean"
```

(or a permissive variant — the exact dependency on namespace path
matters; cycle 395's literal `RootedTree.mk [...]` uses fully-qualified
forms — see memory `feedback_simp_recursive_def_overunfolds`'s sibling
mention of name resolution).

Then count the predecessor branches in `inversePolynomial`'s
`if-then-else` cascade BEFORE the `mk [mk [cherry]]` branch. Per the
State §dispatch above, `mk [mk [cherry]]` is the **8th branch** (after
vertex, cherry, broom₃, mk[cherry], bushy, mk[broom₃],
mk[vertex,cherry]). So the bridge needs **7 `if_neg`s + 1 `if_pos rfl`**.
Confirm by reading the file before writing.

### Step A: Ship `inversePolyTree_mkMkCherry_eq_inversePolynomial`

Insert IMMEDIATELY AFTER cycle 396's
`inversePolyTree_mkCherry_eq_inversePolynomial`. Find the insertion
location by Grep for `inversePolyTree_mkCherry_eq_inversePolynomial`
and append after its closing block.

Template (cycle 393's `mk [broom₃]` bridge, adapted; verify exact
`if_neg` count after Step 0):

```lean
/-- *Phase α'.4.2 bridge for `mk [mk [cherry]]`* (cycle 397).
Cycle 395 shipped `inversePolyTree_mkMkCherry` as the closed-form
calibration. This bridge says the recursive `inversePolyTree`
evaluation matches `inversePolynomial`'s post-migration dispatch
at `mk [mk [cherry]]`.

Mechanical mirror of cycle 396's
`inversePolyTree_mkCherry_eq_inversePolynomial`. -/
theorem inversePolyTree_mkMkCherry_eq_inversePolynomial
    (f : RT → ℝ) :
    inversePolyTree
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) f
      = inversePolynomial
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) f := by
  unfold inversePolynomial
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_pos rfl]
```

After Step B (body migration), both sides reduce to the same recursive
form and the proof closes by implicit `rfl` after the `rw` cascade.

**Recommendation**: ship Step A AFTER Step B, so the `if_pos rfl` step
sees the migrated body. Cycle 396 used this order successfully.

### Step B: Body migration

Find `inversePolynomial`'s 8th branch (mk [mk [cherry]]) and rewrite the
RHS from `inversePolyChain 3 f` to
`inversePolyTree (OpenMath.Chapter3.Section310.RootedTree.mk [OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]]) f`.
Use the EXACT same fully-qualified name as cycle 395's
`inversePolyTree_mkMkCherry` statement (Grep for it to copy verbatim) —
avoid name-resolution surprises (per memory
`feedback_simp_recursive_def_overunfolds`'s name-resolution pitfall on
recursive defs).

### Step C: Calibration `example` update (Phase α.2)

Phase α.2 (cycle 374-era) calibration `example` for
`mk [mk [cherry]]` currently closes via a chain ending in
`inversePolyChain_three`. Append `inversePolyTree_mkMkCherry` to the
trailing `rw [...]` so the post-migration RHS matches. Same pattern as
cycle 396's Phase α.1 calibration update.

### Step D: Phase β.1 bridge update

`elementaryWeightQ_phi_inv_eq_inversePolynomial_mkMkCherry`'s closer
similarly needs `inversePolyTree_mkMkCherry` appended.

### Step E: Phase γ branch update (twice)

In `inversePolynomial_eq_of_subtree_agreement`, the `mk [mk [cherry]]`
arm: replace both `inversePolyChain_three` occurrences with
`inversePolyTree_mkMkCherry` (twice — once per `f` and `g` side).
Mirrors cycle 396's double-replacement.

### Step F (REQUIRED, not optional): Derivative fix on cycle 380's bridge

Cycle 380's `inversePolyChain_three_eq_inversePolynomial` proof body
will break after Step B: the RHS evaluates to
`inversePolyTree (mk [mk [cherry]]) f` instead of the explicit
closed form. Fix as cycle 396 fixed `inversePolyChain_two_eq_inversePolynomial`:
append `inversePolyChain_three, inversePolyTree_mkMkCherry` to the
existing `rw` cascade so both sides reduce to their common closed form.

**Detection**: the first `lake build` after Steps A–E will fail with a
single unsolved-goal error at the
`inversePolyChain_three_eq_inversePolynomial` proof site. The error
location is the cue to apply Step F and rebuild.

## Verification (mandatory)

1. `lake build OpenMath.Chapter4.Section422` exits 0.
2. `grep -c sorry OpenMath/Chapter4/Section422.lean` returns `5`
   (unchanged — only the grandfathered cycle 365 sorry at line 2279).
3. `#print axioms` on these symbols via a temporary file that imports
   Section422 (`/tmp/verify_cycle_397_axioms.lean`):
   * `inversePolyTree_mkMkCherry_eq_inversePolynomial` (new)
   * `elementaryWeightQ_phi_inv_eq_inversePolynomial_mkMkCherry`
   * `inversePolynomial_eq_of_subtree_agreement`
   * `inversePolyChain_three_eq_inversePolynomial`
   * `inversePolyTree_mkMkCherry` (regression spot-check)
   * `inversePolyTree_mkCherry` (regression spot-check)

   All must return `[propext, Classical.choice, Quot.sound]`.

4. **`lake env lean` does NOT refresh `.olean`** — must run `lake build`
   before `#print axioms`. Cycle 396 confirmed this empirically: the
   first `#print axioms` attempt ran against stale oleans and reported
   `Unknown constant`. Run `lake build` first.

## Bookkeeping (post-ship)

* `extraction/formalization_data/lean_status.json`: bump `def:422B`'s
  `cycle_completed_at` from 396 → 397. Status remains `partial`.
* `plan.md`: append a cycle 397 entry to `def:422B`'s row, consistent
  in style with cycles 391/393/396 entries.
* `.prover-state/issues/def_422B_path.md`: append a §10 "Cycle 397
  update" subsection documenting the migration (mirror cycle 396
  subsection's structure).
* Write `.prover-state/task_results/cycle_397.md` with the standard
  CLAUDE.md sections.

## What NOT to do this cycle (forbidden)

* **Do NOT attempt `bushy` migration.** `bushy = mk [vertex, vertex,
  vertex]` is an arity-3 children tree; `inversePolyTree`'s current
  recursive case for `(_ :: _ :: _ :: _)` dispatches to `0`. A bushy
  migration requires extending `inversePolyTree` to handle 3+ children
  (with a `Finset.sum`-style closed form mirroring cycle 370's
  `elementaryWeightQ_phi_inv_bushy`). That is cycle 398+ scope and
  almost certainly needs its own scoping doc.
* **Do NOT close the cycle 365 grandfathered sorry.** Multi-cycle
  work; revisit cycle 400+ after all 9 ladder trees route through
  `inversePolyTree`.
* **Do NOT pivot to a fresh entity.** Cycle 396 worker's "Suggested
  next approach" §Cycle 397 explicitly recommends continuing Phase
  α'.4.2 — only 2 ladder trees remain unmigrated (`mk [mk [cherry]]`
  this cycle, `bushy` cycle 398+). Phase α'.4.2 completion unblocks
  Sub-lemma A closure.
* **Do NOT submit to Aristotle.** Bridge proof is a 3–4-line
  `unfold + rw [if_neg* + if_pos rfl]` — no search needed.
* **Do NOT use `simp [inversePolyTree, ...]`.** Per memory
  `feedback_simp_recursive_def_overunfolds`, `simp` over-unfolds
  recursive defs to raw `mk [...]` form before name-equality theorems
  can fire. Use targeted `rw [...]`.
* **Do NOT skip Step F.** Cycle 396 worker spent a build cycle
  discovering the need for the derivative fix to
  `inversePolyChain_two_eq_inversePolynomial`. Cycle 397 has the
  analogous obligation on `inversePolyChain_three_eq_inversePolynomial`.
* **Do NOT introduce any new sorry, axiom, or constant.** Cycle 200/201
  and 149/150 rollback precedents stand: sorry-first scaffolds for
  multi-cycle work get rolled back.
* **Do NOT touch `Section441.lean`** — 43+ consecutive GPFS timeouts;
  irrelevant to this cycle anyway.

## Failed approaches (do not repeat)

* `Polynomial.ext + simp + ring` for `Polynomial ℝ` constant arithmetic
  (cycles 172/173 stall) — irrelevant here but flagged for awareness.
* Block-`simp [recursive-def, name-eq-thm, ...]` over-unfolds before
  name theorems fire — use `rw` (memory
  `feedback_simp_recursive_def_overunfolds`).
* `norm_num` to bridge `-(((m+1):ℕ):ℤ) = Int.negSucc m` — leaves
  display-ambiguous unsolved goal. The bridge is definitional `rfl`
  (memory `feedback_neg_natCast_int_negsucc_rfl`).

## Recipe summary (literal command sequence)

1. `Grep` for the `mk [mk [cherry]]` branch in `inversePolynomial` to
   confirm the `if_neg` count (Step 0). Likely 7 `if_neg`s + 1 `if_pos
   rfl` since it's the 8th branch.
2. `Grep` for cycle 395's `inversePolyTree_mkMkCherry` to copy the
   fully-qualified tree name verbatim.
3. `Grep` for `inversePolyTree_mkCherry_eq_inversePolynomial` to locate
   the insertion point for Step A.
4. `Edit` Section422.lean for Step B (body migration of branch 8).
5. `Edit` Section422.lean for Step A (insert bridge theorem after
   cycle 396's bridge).
6. `Edit` Section422.lean for Step C (Phase α.2 calibration `example`).
7. `Edit` Section422.lean for Step D (Phase β bridge).
8. `Edit` Section422.lean for Step E (Phase γ branch — twice, f and g).
9. `Bash`: `time lake build OpenMath.Chapter4.Section422`. Expect a
   single unsolved-goal error at
   `inversePolyChain_three_eq_inversePolynomial` →
10. `Edit` Section422.lean for Step F (extend cycle 380's bridge proof).
11. `Bash`: `lake build OpenMath.Chapter4.Section422` — should now exit 0.
12. `Bash`: `grep -c sorry OpenMath/Chapter4/Section422.lean` should
    return 5.
13. Create `/tmp/verify_cycle_397_axioms.lean` with `import OpenMath.Chapter4.Section422`
    and `#print axioms` for each of the 6 verification symbols.
14. `Bash`: `lake env lean /tmp/verify_cycle_397_axioms.lean` — all six
    must return `[propext, Classical.choice, Quot.sound]`.
15. Bookkeeping: update `lean_status.json`, `plan.md`,
    `def_422B_path.md` §10, write `task_results/cycle_397.md`.

## Success criteria

* §422 axiom-clean streak: 59 → **60 substantive + 2 doc** (336–397).
* Phase α'.4.2 progress: 4 of 9 ladder trees migrated → **5 of 9**.
  (After cycle 397, only `bushy`, and the still-on-`inversePolyChain`
  trees `vertex`/`cherry` plus the still-on-`inversePolyBroom`
  `broom₃`/`bushy` remain. Note `vertex`/`cherry` migration is
  trivial; `bushy` is the substantive cycle 398+ work.)
* One new public theorem
  (`inversePolyTree_mkMkCherry_eq_inversePolynomial`), axiom-clean.
* Five touched theorems/examples re-verified axiom-clean.
* Sorry count unchanged at 5.

## After cycle 397 — cycle 398+ outlook (for context, not action)

* **Cycle 398**: tackle `bushy` migration. Requires extending
  `inversePolyTree`'s arity-3 case from `0` to a proper closed form.
  Likely needs a brief sub-scoping doc (Phase α'.4.3) and/or a
  `trichildPolynomial` helper analogous to cycle 387's
  `bichildPolynomial`. Multi-cycle if it includes the substantive
  Family B → C generalization.
* **Cycle 399+**: any remaining migrations (verify cycle 396 task
  results' branch enumeration is complete — `vertex`/`cherry` may
  also need migration via `inversePolyChain_zero`/`inversePolyChain_one`
  bridges, but those are arguably already in the canonical form).
* **Cycle 400+**: with uniform `inversePolyTree` routing, revisit
  cycle 365's grandfathered sorry. The heterogeneous-stage obstacle
  identified in cycle 365 task results may yield to the unified
  recursive structure composed with cycle 362's
  `derivativeWeightWithSrc_eq_of_strict_subtree_agreement`.
