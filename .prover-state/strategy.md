# Cycle 192 Strategy

## Context summary

* **Phase B of `lem:441A`** is closed at HEAD (cycle 179,
  `aPoly_coeff_one_pos_of_stable_preconsistent` at Section441.lean:913,
  axiom-clean). Do NOT re-derive — the "factor-of-2" framing is a
  six-cycle-old phantom (see `consultant_advice_cycle_180.md` §A).
* **Phase C.2 of `lem:441A`** has a drafted proof at
  `.prover-state/cycle_182_draft_section441.lean` (1568 LOC) plus the
  cycle 184 namespace fix (one-line diff at draft line 1529:
  `M.αPoly_…` → `LinearMultistepMethod.αPoly_…`). Verification has
  been **GPFS-blocked for 11 consecutive cycles** (182–191), and
  loop-maintainer escalation is logged at
  `.prover-state/issues/cycle_182_gpfs_slowness.md`.
* **Cycle 191** shipped `PReducesTo.of_isZeroReducibleVia` axiom-clean
  in `OpenMath/Chapter3/Section381.lean`. Its Priority 3 cleanup
  (refactor `PEquivalent.of_isZeroReducibleVia` to consume the new
  helper) was reverted due to a forward-reference issue: the new
  helper sits *after* `PEquivalent.of_isZeroReducibleVia` in source
  order, so the rewrite produced `unknownIdentifier`. This cycle
  resolves that with a reorder.
* `Section381.lean` HEAD: 3.7s warm rebuild, 53.9s cold (well within
  budget). Section441.lean is still on the GPFS hot list.
* **No pending Aristotle results.**

---

## Priority 0 — GPFS smoke test (default expected to fail; 5 min)

Run, with no zombie processes active (verify first):

```bash
ps -u $USER -o pid,stat,wchan,etime,comm | grep -E "^[ ]*[0-9]+ +D" || echo "no zombies"
time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean
```

Branching:

* If clean exit in <5 min ⇒ GPFS has recovered. **Skip Priorities 2
  and 3.** Instead, replace `OpenMath/Chapter4/Section441.lean` with
  the cycle 182 draft (`.prover-state/cycle_182_draft_section441.lean`),
  apply the cycle 184 one-line namespace fix at line 1529
  (`M.αPoly_complex_root_norm_ge_one_of_stable` →
  `LinearMultistepMethod.αPoly_complex_root_norm_ge_one_of_stable M`),
  re-run `lake env lean Section441.lean`. On success, run `lean_verify`
  axiom check on the three new public theorems
  (`ρPoly_complex_root_norm_le_one_of_stable`,
  `αPoly_complex_root_norm_ge_one_of_stable`,
  `aPoly_complex_root_re_nonpos_of_stable`), update
  `extraction/formalization_data/lean_status.json` (`lem:441A` cycle
  bump + comment on Phase C.2 closure), update `plan.md`'s
  `lem:441A` row, and update
  `.prover-state/issues/lem_441A_phase_C_scoping.md` to mark Phase C.2
  closed. Cycle 192 result = Phase C.2 shipped.
* If timeout (12th in a row) ⇒ continue to Priority 2. Log as the
  cycle 192 update in `.prover-state/issues/cycle_182_gpfs_slowness.md`
  (mirror cycle 191's format: real/user/sys time, CPU%, no-zombie
  pre-flight result).
* **Do NOT** touch `scripts/autonomous_loop.py`. Loop-maintainer
  territory.

---

## Priority 1 — Phase C.2 ship (gated on Priority 0 success only)

Skip if Priority 0 timed out. Steps under success branch are in §0
above.

---

## Priority 2 — Complete the cycle 191 deferred refactor (mechanical, ~10 min)

Cycle 191 introduced `PReducesTo.of_isZeroReducibleVia` immediately
after `eq_of_isIrreducible_of_pReducesTo` and before
`PEquivalent.trans_of_middle_isIrreducible`. The existing
`PEquivalent.of_isZeroReducibleVia` (Section381.lean:451) currently
proves its goal directly via the `zeroStep` constructor:

```lean
theorem PEquivalent.of_isZeroReducibleVia
    {s : ℕ} (M : RKTableau s) {inP1 : Fin s → Bool}
    (hP0 : ∃ i, inP1 i = false)
    (h : M.IsZeroReducibleVia inP1) :
    PEquivalent M (M.zeroReduced inP1) :=
  PEquivalent.of_pReducesTo
    (PReducesTo.zeroStep inP1 hP0 h (PReducesTo.refl (M.zeroReduced inP1)))
```

**Goal**: refactor it to consume the new helper as a one-liner:

```lean
theorem PEquivalent.of_isZeroReducibleVia
    {s : ℕ} (M : RKTableau s) {inP1 : Fin s → Bool}
    (hP0 : ∃ i, inP1 i = false)
    (h : M.IsZeroReducibleVia inP1) :
    PEquivalent M (M.zeroReduced inP1) :=
  PEquivalent.of_pReducesTo (PReducesTo.of_isZeroReducibleVia M hP0 h)
```

**Required reorder** to avoid the forward-reference that broke cycle
191's attempt: move the `PReducesTo.of_isZeroReducibleVia` definition
from its current position (after
`eq_of_isIrreducible_of_pReducesTo`, before
`PEquivalent.trans_of_middle_isIrreducible`) to immediately *before*
`PEquivalent.of_isZeroReducibleVia` at line 451. Grouping rationale:
both lemmas express "one-step 0-reduction is a P-reduction-style
relation"; placing them adjacent in source order is consistent with
the rest of §381's structure.

**Steps**:

1. Read `OpenMath/Chapter3/Section381.lean` to locate the current
   position of `PReducesTo.of_isZeroReducibleVia` (added in cycle 191)
   and `PEquivalent.of_isZeroReducibleVia` (line ~451).
2. Edit (Edit tool, two operations):
   * Delete the `PReducesTo.of_isZeroReducibleVia` block from its
     current position.
   * Insert it immediately before `PEquivalent.of_isZeroReducibleVia`.
3. Style improvement (also from cycle 191's Discovery): in the
   relocated `PReducesTo.of_isZeroReducibleVia` body, you may use
   `PReducesTo.refl _` (with the underscore) instead of
   `PReducesTo.refl (M.zeroReduced inP1)` — the unifier picks up the
   argument from the goal. This is cosmetic; the verbose form also
   works.
4. Edit the body of `PEquivalent.of_isZeroReducibleVia` to the
   one-liner above.
5. Verify: `lake env lean OpenMath/Chapter3/Section381.lean` (expect
   ~4s warm).
6. Run axiom check on both theorems:
   ```
   #print axioms OpenMath.Chapter3.Section312.RKTableau.PReducesTo.of_isZeroReducibleVia
   #print axioms OpenMath.Chapter3.Section312.RKTableau.PEquivalent.of_isZeroReducibleVia
   ```
   Expected: `[propext, Classical.choice, Quot.sound]` for both.
7. Verify no downstream witness regression — re-axiom-check at least
   one consumer such as `paddedEuler_pEquivalent_zeroReduced` or
   `paddedEuler_phiEquivalent_zeroReduced` (cycle 188 witnesses).

If any of (5)–(7) fails, **revert the entire diff** (worker should
not commit half-broken state) and document the failure mode in the
cycle 192 task results. Do not attempt a fix mid-cycle.

---

## Priority 3 — Stretch: one more def:381F follow-up (only if 0+2 close fast)

If Priority 0 timed out and Priority 2 closed in well under the
cycle budget, ship ONE of the following two candidates. Pick the
first; the second is only listed as a fallback if the first stalls.

### Option 3A (preferred): `PReducesTo.trans` — multi-step chaining

Statement (proposed):

```lean
theorem PReducesTo.trans
    {s s' s'' : ℕ}
    {M : RKTableau s} {M' : RKTableau s'} {M'' : RKTableau s''}
    (h₁ : PReducesTo M M') (h₂ : PReducesTo M' M'') :
    PReducesTo M M''
```

Place immediately after the existing `PReducesTo.refl` constructor or
right after the cycle 191 helper (since both naturally group as
`PReducesTo`-level utilities).

**Proof recipe**: induction on `h₁` via `PReducesTo.rec` (NOT
match — the inductive is heterogeneously-typed across stage counts).
Three constructor cases:

* `refl`: `M = M'`, so `h₂ : PReducesTo M M''` is exactly the goal.
* `step inP partition hP h ih`: apply IH to get `PReducesTo
  (M.pReduced inP partition) M''`, then re-wrap with the same
  `step` constructor's data: `PReducesTo.step inP partition hP h
  (ih h₂)`.
* `zeroStep inP hP h ih`: analogous; re-wrap with `zeroStep`.

This makes `PReducesTo` a usable transitive closure for downstream
Φ-equivalence consumers (cf. `PEquivalent` already has
`trans_of_middle_isIrreducible` and the cycle 190 canonical-form
constructor `eq_of_isIrreducible_of_middle`, but the unrestricted
`PReducesTo.trans` is currently missing).

**Non-vacuity witness**: after the theorem, add a short example or
named witness via `paddedEuler`:

```lean
example : PReducesTo paddedEuler
    ((paddedEuler.pReduced pairPartition).zeroReduced (...)) :=
  PReducesTo.trans
    paddedEuler_pReducesTo_pReduced
    (PReducesTo.of_isZeroReducibleVia _ ... ...)
```

(adjust to whichever witness shape matches the cycle 188 chain
`paddedEuler_pReducesTo_zeroReduced`; consult the file to pick the
right `inP1` and discharging hypotheses).

Estimated LOC: 30–60. Axiom-clean target. Compile budget: well within
Section381's <60s cold budget.

**Faithfulness check note**: this is helper-side infrastructure for
the `def:381F` cluster; not a textbook-named entity. Tautology check
is about non-identity body (it's a recursor application, not
`exact h`).

### Option 3B (fallback if 3A stalls):
`eq_of_both_isIrreducible_of_PEquivalent` — Φ/PEquivalent canonical form

Currently `PEquivalent.eq_of_isIrreducible_of_middle` (cycle 190) is
the cleanest canonical-form constructor available. The natural dual
is: if `PEquivalent M M'` with *both* `M` and `M'` irreducible, then
`M = M'` (up to stage-count `HEq`). This is exactly what `def:381F`'s
textbook claim "P-equivalent methods have a common reduced method"
demands when restricted to already-irreducible sources.

This is conceptually harder than 3A because `PEquivalent` is the
symmetric-transitive closure of `PReducesTo`, so the induction is
two-sided. Defer if 3A is not opening fast.

### Common rule for Priority 3

* If neither option closes in 30 min of focused work, abandon and
  commit only Priority 2's deliverable.
* Do NOT attempt both options in one cycle.
* Do NOT touch Section441.lean during stretch work.

---

## What NOT to do this cycle

* Do **NOT** re-audit the factor-of-2 result (cycle 174). It is
  correct; Butcher §441 p. 376 has the typo.
* Do **NOT** revert any Phase B work. `aPoly_coeff_one_pos_of_stable_preconsistent`
  at line 913 is axiom-clean and final.
* Do **NOT** attempt Phase C.3 (complex-root real factorisation).
  The Phase C scoping in `lem_441A_phase_C_scoping.md` reserves that
  for a dedicated multi-cycle effort *after* Phase C.2 lands.
* Do **NOT** attempt Phase C.1 reverification — it shipped axiom-clean
  in cycle 181 and is at HEAD.
* Do **NOT** modify `scripts/autonomous_loop.py`. The phantom-
  verdict and GPFS issues are loop-maintainer territory per
  CLAUDE.md.
* Do **NOT** raise `maxHeartbeats` above 200000.
* Do **NOT** introduce `axiom` or `constant` declarations.
* Do **NOT** pivot to a fresh entity yet. The def:381F cluster is
  one cosmetic cleanup (Priority 2) and one helper (Priority 3) away
  from a natural pause point. Finish it cleanly while §441 is
  GPFS-blocked.
* Do **NOT** poll Aristotle this cycle. The cycle 184 project
  `7c4d0ffb-…` returned `COMPLETE_WITH_ERRORS` and was processed
  (the only meaningful fix — the line-1529 namespace rewrite — is
  already preserved). No new submissions.

---

## Commit message draft

```
Cycle 192 — §380 PEquivalent.of_isZeroReducibleVia refactor (consume cycle-191 helper); §441 Phase C.2 GPFS-blocked (12th)
```

(Adjust the `(Nth)` count after running Priority 0; append the
Option 3A or 3B headline if a stretch deliverable shipped.)

---

## Post-cycle hygiene

* Update `.prover-state/task_results/cycle_192.md` per CLAUDE.md
  format. Faithfulness check section: Priority 2's refactor renames
  no theorems but changes the body. Note that the *statement* is
  unchanged; only the proof now routes through the new helper.
* Update `attempts.md` — add a cycle 192 entry documenting whichever
  combination of priorities shipped.
* Update `.prover-state/issues/cycle_182_gpfs_slowness.md` with the
  12th-consecutive-timeout data (or, if Priority 0 succeeded,
  mark the GPFS issue as RESOLVED and link to the Phase C.2 closure).
* Update `.prover-state/issues/lem_441A_phase_C_scoping.md`'s Phase
  C.2 row only if Priority 1 actually shipped.
* Do NOT update `lean_status.json` or `plan.md` unless a
  textbook-named entity's status changed (i.e. Priority 1 shipped
  Phase C.2). Priority 2's refactor and Priority 3's helper are both
  internal infrastructure and do NOT promote any entity.
