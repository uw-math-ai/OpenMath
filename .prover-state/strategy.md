# Cycle 150 Strategy

## Status snapshot

- Sorry count: **3** (regression in cycle 149: def:530B sorry-first
  scaffold added 3 sorries — `applyStartingThenStep`,
  `applyExactThenStarting`, and the
  `explicitEulerGLM_hasOrderZero_trivialStarting` non-vacuity
  witness).
- Cycle 149 score: **−2** (sorry up).
- Last 5 cycles: 145 (n=4 +2) → 146 (r=2 negative witnesses +2) →
  147 (n=5 +2) → 148 (n=6 + Aristotle submission +2) → 149
  (def:530B scaffold **−2 reverted**).
- thm:515D capstone remains closed and axiom-clean since cycle 124.
- thm:550A: six concrete-`n` axiom-clean stepping stones
  (n = 1..6); general-n deferred. Aristotle project
  `2c4630b2-2998-4d4a-af88-c2f83fbd9eda` (cycle 148) is the active
  general-n attempt; status as of cycle 149 was IN_PROGRESS at 4%.

## Diagnosis of cycle 149

This is the **cycle 138 → cycle 139 pattern repeating exactly**:

* **Cycle 138** added a sorry'd general-n statement of thm:550A
  → scored −2 (sorry 0→1) → cycle 139 **rolled it back**, sorry
  count returned to 0, recovery was clean.
* **Cycle 149** added a sorry-first scaffold for def:530B
  (operators + predicate + witness, all sorry'd) → scored −2
  (sorry 0→3) → cycle 150 must follow cycle 139's recovery template.

The cycle 149 scaffold itself is mathematically sound, but the
sorry-first approach is **structurally not viable for def:530B**:
the operator bodies require multivariate fixed-point arguments to
solve implicit stage equations, which can't be left as placeholders
without making the predicate vacuous. Closing them needs either
Path A (explicit-only restricted operators with a new `IsExplicit`
predicate, ~2-3 cycles) or Path B (general implicit via
`ContractingWith` / `Function.IsFixedPt`, ~3-5 cycles). Both are
multi-cycle infrastructure work — out of scope for cycle 150.

## Cycle 150 plan

Two priorities, executed in order. Priority 0 is mandatory.
Priority 2 is conditional on Priority 0's outcome.

---

## Priority 0 (≤5 min) — Aristotle single-poll on thm:550A

**Action**: Run `mcp__aristotle__get_status` ONCE on project
`2c4630b2-2998-4d4a-af88-c2f83fbd9eda`. Per CLAUDE.md single-poll
discipline: this is the cycle's only allowed Aristotle poll;
do NOT re-poll within this cycle.

### Decision tree

* **If COMPLETE with a clean proof body**:
  1. `mcp__aristotle__extract_result` to retrieve the Lean code.
  2. Reinstate the general-`n` statement
     `doublyCompanionMatrix_det_factorization` in
     `OpenMath/Chapter5/Section550.lean`.
  3. Verify with `lake env lean OpenMath/Chapter5/Section550.lean`.
  4. `lake build OpenMath.Chapter5.Section550` then `lean_verify`
     on `OpenMath.Chapter5.Section550.doublyCompanionMatrix_det_factorization`
     to confirm `[propext, Classical.choice, Quot.sound]` only.
     REJECT if any other axiom appears (especially `sorryAx`).
  5. Update `extraction/formalization_data/lean_status.json`:
     `thm:550A` → `formalized` (drop `partial`).
  6. Update `plan.md` thm:550A row: `[~]` → `[x]`; trim the status
     comment to a single line referencing the general-n closure
     cycle. Keep the n=1..6 stepping stones in place as historical
     witnesses.
  7. Update `.prover-state/issues/thm_550A_general_n.md` with a
     "RESOLVED cycle 150 — Aristotle returned general-n proof"
     header.
  8. **Skip Priority 2.** Substantive deliverable is the thm:550A
     closure itself.
  9. Proceed to Priority 1 (rollback) regardless.

* **If FAILED, CANCELLED, or returns garbage** (uses `sorry`,
  invokes `axiom`, references missing definitions): do NOT spend
  cycle time debugging Aristotle output. Update the issue file
  `thm_550A_general_n.md` with a single-line cycle-150 status note,
  then proceed to Priority 1 + Priority 2 (n=7 stepping stone).
  Do NOT submit a fresh Aristotle job — cycle-148's submission was
  already a fire-and-forget attempt; another submission burns
  quota without new context.

* **If still IN_PROGRESS at any percentage**: leave it running,
  do NOT cancel. Proceed to Priority 1 + Priority 2. (Cycle 141's
  Job A was cancelled at 6% after 24h; cycle 148's submission has
  been running for ~24h at cycle-149's poll, so it's at the same
  expected-cancellation horizon — but cycle 150 should still let
  it run, and a future cycle can decide on cancellation.)

---

## Priority 1 (CRITICAL — single-cycle recovery): Roll back cycle 149's def:530B scaffold

**This is the cycle 139 precedent applied verbatim.**

### Specific edits to `OpenMath/Chapter5/Section530.lean`

The cycle 149 worker added four blocks. Remove all four:

1. **`noncomputable def applyStartingThenStep`** (the textbook
   `SM` operator with sorry'd body, around line 325–334).
2. **`noncomputable def applyExactThenStarting`** (the textbook
   `ES` operator with sorry'd body, around line 337–346).
3. **`def HasOrderRelativeTo`** (the
   `Asymptotics.IsBigO`-based predicate using (1) and (2), around
   line 350–390 — read the file to confirm the exact location).
4. **`theorem explicitEulerGLM_hasOrderZero_trivialStarting`**
   (the sorry'd non-vacuity witness, around line 395–400).

### Imports to consider removing

Cycle 149 added three imports near the top of `Section530.lean`:
* `Mathlib.Analysis.Asymptotics.Defs`
* `Mathlib.Analysis.Calculus.Deriv.Basic`
* `OpenMath.Chapter5.Section510`

After removing the four blocks above, **grep `Section530.lean`**
for `IsBigO`, `HasDerivAt`, and `explicitEulerGLM` /
`GeneralLinearMethod`. Remove only those imports whose symbols are
no longer referenced. `Section510` may still be transitively
needed — leave it if any remaining declaration references
`GeneralLinearMethod`, `explicitEulerGLM`, etc.

### Bookkeeping for Priority 1

* `extraction/formalization_data/lean_status.json` row for
  `def:530B`: revert `partial` → `unformalized`. Clear the
  `lean_file` and `lean_symbol` fields (set to empty strings or
  null per the schema convention used elsewhere in the file —
  check the schema before editing).
* `plan.md`: revert def:530B row from `[~]` to `[ ]`. Update the
  status note to: "Sorry-first scaffold attempted cycle 149,
  rolled back cycle 150 per cycle-139 precedent. Closure requires
  multi-cycle infrastructure (Path A explicit-only operators OR
  Path B general implicit fixed-point); not viable as a single-
  cycle sorry-first deliverable."
* Open new issue file
  `.prover-state/issues/def_530B_scaffold_strategy.md` documenting:
  - The cycle 149 attempt and cycle 150 rollback.
  - Path A (explicit-only restricted operators with `IsExplicit`
    predicate, ~2-3 cycles infrastructure).
  - Path B (general implicit via `ContractingWith` /
    `Function.IsFixedPt` machinery, ~3-5 cycles infrastructure).
  - The structural insight that sorry-first scaffolding doesn't
    work for def:530B because the operator bodies are not
    "decomposable into named sub-helpers" — they're indivisible
    fixed-point computations.
  - A note that `explicitEulerGLM_hasOrderZero_trivialStarting`
    has a clean closed-form analysis once the operators close: for
    `(s, r) = (1, 1)` explicit Euler with `b₀ = 1, b = 1, A = 0`
    + trivialStartingMethod, both `SM` and `ES` evaluate to
    closed-form scalar formulas, and Taylor expansion of `yex`
    gives `yex(x₀+h) = y₀ + h·f(y₀) + O(h²)`, so the difference
    vector has `O(h²)` sup-norm, dominating the required
    `O(h^{0+1}) = O(h)`.

### Verification for Priority 1

* `lake env lean OpenMath/Chapter5/Section530.lean` — clean
  compile, no errors.
* `grep -c '\bsorry\b' OpenMath/Chapter5/Section530.lean` — must
  return **0**.
* Other Section530 content **must remain intact**:
  - `GeneralizedRungeKuttaMethod` tableau (cycle 139)
  - `StartingMethod` structure (cycle 139)
  - `IsDegenerate` / `IsNonDegenerate` predicates (cycle 139)
  - `trivialStartingMethod`, `trivialStartingMethod_isNonDegenerate`
  - `zeroStartingMethod`, `zeroStartingMethod_isDegenerate`
  - `nontrivialTwoStageGRK`, `mixedStartingMethod`,
    `mixedStartingMethod_isNonDegenerate`,
    `mixedStartingMethod_stages_neq` (cycle 141)
  - `zero2StartingMethod`, `zero2StartingMethod_isDegenerate`
  Do NOT touch any of these.

---

## Priority 2 (substantive — only if Priority 0 was non-COMPLETE):
## thm:550A n=7 stepping stone

Apply the cycle-148 four-layer Laplace template, scaled by one
nesting level. This recipe has scored **+2 axiom-clean** four
cycles in a row (144, 145, 147, 148), and the algorithm is
mechanical. Estimated effort: 60-90 min including verification.

### Lemma to add to `OpenMath/Chapter5/Section550.lean`

```
theorem doublyCompanionMatrix_det_factorization_n_seven
    (α β : Fin 7 → ℂ) :
    (fun z : ℂ => (1 - z • doublyCompanionMatrix α β).det -
                  alphaPoly α z * betaPoly β z)
      =O[nhds (0 : ℂ)] (fun z : ℂ => z ^ 8) := by
  -- See recipe below
```

### Recipe (cycle-148 template scaled to n=7)

1. **Reduce `doublyCompanionMatrix α β` at n = 7 to an explicit
   `!![…]` form** via
   `ext i j; fin_cases i <;> fin_cases j <;> simp [doublyCompanionMatrix]`.

2. **Reduce `1 - z • X` to a second explicit `!![…]` form** via
   a second `fin_cases` block with
   `first | (simp; ring) | simp`.

3. **Expand the 7×7 determinant via four-layer nested Laplace
   expansion**: outer `Matrix.det_succ_row_zero` produces seven
   6×6 minors; each 6×6 expanded via
   `Matrix.det_succ_row_zero (n := 5)` produces five 5×5 minors;
   each 5×5 via `Matrix.det_succ_row_zero (n := 4)` produces four
   4×4 minors; each 4×4 via `Matrix.det_succ_row_zero (n := 3)`
   produces three 3×3 minors; close every 3×3 minor with
   `Matrix.det_fin_three`.

   The closing tactic should be a single one-shot `simp` over the
   nested expansion lemmas, followed by `ring`:

   ```
   simp [Fin.sum_univ_seven, Fin.sum_univ_six,
         Fin.sum_univ_five, Fin.sum_univ_four,
         Matrix.det_succ_row_zero (n := 5),
         Matrix.det_succ_row_zero (n := 4),
         Matrix.det_succ_row_zero (n := 3),
         Matrix.det_fin_three,
         alphaPoly, betaPoly,
         Fin.cons_succ, Fin.cons_zero,
         Matrix.cons_val_zero, Matrix.cons_val_succ]
   ring
   ```

4. **Close the `IsBigO`** via `Asymptotics.IsBigO.of_bound` with
   constant `‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ + ‖g‖`, where the
   residue factors as `z^8 · (a + z·b + z²·c + z³·d + z⁴·e + z⁵·f
   + z⁶·g)` with the seven convolution coefficients (each a negated
   sum of `α_i · β_j` products, following the cycle-148 n=6
   pattern):

   * `a := -(α 0·β 6) - α 1·β 5 - α 2·β 4 - α 3·β 3 - α 4·β 2 - α 5·β 1 - α 6·β 0`
   * `b := -(α 1·β 6) - α 2·β 5 - α 3·β 4 - α 4·β 3 - α 5·β 2 - α 6·β 1`
   * `c := -(α 2·β 6) - α 3·β 5 - α 4·β 4 - α 5·β 3 - α 6·β 2`
   * `d := -(α 3·β 6) - α 4·β 5 - α 5·β 4 - α 6·β 3`
   * `e := -(α 4·β 6) - α 5·β 5 - α 6·β 4`
   * `f := -(α 5·β 6) - α 6·β 5`
   * `g := -(α 6·β 6)`

   Bound the residue's magnitude via repeated `norm_add_le` +
   `mul_le_of_le_one_left` exploiting `‖z‖ ≤ 1` from the `nhds 0`
   neighborhood. The cycle-148 closure used a `‖y ^ 5 * f‖ ≤ ‖f‖`
   sub-bound; n=7 will need an analogous `‖y ^ 6 * g‖ ≤ ‖g‖`
   sub-bound.

### Verification for Priority 2

* `lake env lean OpenMath/Chapter5/Section550.lean` — clean
  compile.
* `lake build OpenMath.Chapter5.Section550` then `lean_verify` on
  `OpenMath.Chapter5.Section550.doublyCompanionMatrix_det_factorization_n_seven`
  must return `[propext, Classical.choice, Quot.sound]` exactly.
* Sorry count for `Section550.lean` stays at 0.

### Bookkeeping for Priority 2

* Update the `thm:550A` row in `plan.md` with a brief cycle-150
  note appended to the existing status comment: "n=7 stepping
  stone via 4-layer Laplace expansion (axiom-clean, cycle 150)".
* Update `extraction/formalization_data/lean_status.json` for
  `thm:550A` with the cycle-150 stepping-stone reference.
* Update issue file `thm_550A_general_n.md` with a "Status update
  (cycle 150) — n=7 STEPPING STONE ADDED" section, mirroring the
  cycle-148 n=6 update format. Note: "**Seven concrete n's
  (n = 1..7) now confirm the leading-coefficient pattern**".

---

## What NOT to try

* ❌ **Do NOT close the cycle-149 def:530B sorries via Path A or
  Path B in this cycle.** Both are multi-cycle infrastructure work
  per the cycle-149 worker's own analysis; attempting either in
  one cycle will stall and produce another −2 score. The rollback
  is the prescribed cycle-150 move.

* ❌ **Do NOT introduce `axiom` or `constant`** for the def:530B
  operators or anywhere else (per CLAUDE.md absolute rule).

* ❌ **Do NOT raise `maxHeartbeats` above 200000**. If the n=7
  Laplace expansion times out, factor the determinant expansion
  into a separate `private theorem` rather than crank the heartbeat
  ceiling. (Cycle 148's n=6 closed under default heartbeats, so
  n=7 likely will too.)

* ❌ **Do NOT poll Aristotle more than once.** Per CLAUDE.md, ONE
  check per cycle. Single-poll discipline.

* ❌ **Do NOT submit a fresh Aristotle job for thm:550A general-n.**
  Cycle 148's submission is the active attempt. Submitting another
  in parallel burns quota and creates project-list confusion.

* ❌ **Do NOT pursue option (a)/(b)/(c) for §514's `u' = u`
  bridge** — that's been resolved cycle 099 via option (iii)
  strengthening of `IsConvergent`; do not revisit.

* ❌ **Do NOT modify `scripts/autonomous_loop.py`.** Loop-maintainer
  territory, per cycle-014 consultant note and the standing
  `tautology_scanner_false_positives.md` issue.

* ❌ **Do NOT touch §513, §514, §515 files.** The §515D capstone
  is axiom-clean (cycle 124); the propagated `_hc_nn` /
  `_hc_le_one` faithfulness divergences are documented as accepted
  trade-offs. Any §515 edit risks cascade regression.

* ❌ **Do NOT remove the cycle-138/140/144/145/147/148 stepping
  stones** (n=1..6 doublyCompanionMatrix lemmas). They are
  independent axiom-clean witnesses and serve as templates for
  n=7. Retain them even if Aristotle returns a general-n proof
  in Priority 0.

* ❌ **Do NOT cherry-pick a different "easy" entity** (e.g.
  `thm:521B`, a Chapter-3 leaf) as the substantive deliverable.
  n=7 is the prescribed Priority 2 because the recipe is known-
  working (4 cycles × +2 score) and it's a contiguous extension
  of the cycle-148 work. Pivoting elsewhere would be freelancing.

* ❌ **Do NOT attempt to define a new `IsExplicit` predicate on
  `GeneralizedRungeKuttaMethod`** as part of cycle 150's def:530B
  rollback. That's Path A infrastructure for a future cycle, not
  cycle-150 work.

* ❌ **Do NOT define the cycle-149 operators with junk bodies**
  (e.g. `Function.const 0`) to make them total. That would render
  `HasOrderRelativeTo` vacuous (always trivially true), failing
  the CLAUDE.md "definition smuggling" check.

---

## Summary checklist for the cycle 150 worker

Run in order:

1. ☐ Single-poll Aristotle project
   `2c4630b2-2998-4d4a-af88-c2f83fbd9eda`. Branch on result.
2. ☐ If Aristotle COMPLETE: incorporate per Priority 0 decision
   tree. Skip Priority 2's n=7 step.
3. ☐ Roll back cycle 149's def:530B scaffold per Priority 1
   (4 deletions in `Section530.lean`, optional import cleanup,
   bookkeeping, new issue file
   `def_530B_scaffold_strategy.md`).
4. ☐ Verify Section530.lean: sorry count = 0,
   `lake env lean` clean.
5. ☐ If Aristotle non-COMPLETE: add n=7 stepping stone per
   Priority 2. Verify axiom-clean.
6. ☐ Verify Section550.lean: sorry count = 0,
   `lake env lean` clean.
7. ☐ Run pre-commit faithfulness checklist on any new theorems
   added (n=7 only — no new defs added; rollback removes content).
8. ☐ Write `.prover-state/task_results/cycle_150.md` documenting
   the rollback rationale (cycle 139 precedent), Aristotle poll
   result, and stepping-stone closure (or thm:550A general-n
   closure if Aristotle COMPLETE).
9. ☐ Update `plan.md` and `lean_status.json` per the rollback +
   stepping-stone bookkeeping notes above.
10. ☐ Single commit with both rollback AND n=7 stepping stone
    (or rollback + thm:550A general-n closure if Aristotle
    COMPLETE). Push.

Expected score: **+2** (sorry count restored to 0 + axiom-clean
substantive deliverable; matches cycle 145/146/147/148 pattern,
recovers from cycle 149's −2).
