# Cycle 189 strategy

## TL;DR

1. **Priority 0** (≤5 min): GPFS smoke test on `Section441.lean` HEAD. 9th
   attempt; if it completes, ship Phase C.2 of `lem:441A` (Priority 1).
   If it times out (the overwhelmingly likely outcome — 8 consecutive
   timeouts), abort and proceed to Priority 2.
2. **Priority 1, conditional**: Phase C.2 of `lem:441A` from the
   preserved cycle 182 draft + cycle 184 namespace fix.
3. **Priority 2 (default, this is what you will almost certainly do)**:
   Ship `PEquivalent.toPhiEquivalent` — the headline `def:381F → def:381B`
   bridge that closes the easy direction of `thm:381H`. ~5–15 LOC,
   axiom-clean, exercises every cycle 184–188 deliverable. Plus
   `PEquivalent.of_isZeroReducibleVia` and a mixed-reduction witness
   chain using cycle 188's `zeroStep`.

There are no Aristotle results pending. There are 0 sorries in the
codebase. The cycle 188 deliverables are all axiom-clean and committed
at `0434ee0`. `Section381.lean` has substantial momentum (cycles
184–188) and is the natural focus while §441 is GPFS-blocked.

**DO NOT** treat any prompt's "stuck on" framing as a real blocker.
Per `phantom_commit_verdict_pattern.md` and the cycle 180 / 184 / 185
/ 186 / 187 / 188 update notes in `cycle_182_gpfs_slowness.md`, the
GPFS regression is loop-maintainer territory; you cannot fix it from
the worker side.

---

## Priority 0 — GPFS smoke test (≤5 min, abort threshold)

Pre-flight: `ps -u $USER -o pid,stat,wchan,etime,comm | grep -E "^[ ]*[0-9]+ +D"` — verify no D-state zombies are active before
running the smoke test (this was the cycle 183 hazard).

Then run exactly:

```bash
time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean
```

Decision tree:

* **Exit 0 in <5 min** ⇒ GPFS recovered. Proceed to Priority 1.
* **EXIT=124 (timeout) or EXIT=143** ⇒ 9th consecutive failure.
  Append a one-line update to
  `.prover-state/issues/cycle_182_gpfs_slowness.md` documenting
  the 9th timeout (CPU time, wall time), then proceed to Priority 2.
  Do NOT retry, do NOT increase the timeout, do NOT investigate
  the kernel. The pattern is well-established.

---

## Priority 1 — Phase C.2 closure of `lem:441A` (CONDITIONAL on GPFS healthy)

**Skip this section entirely if Priority 0 timed out.** Continue to
Priority 2.

If Priority 0 succeeded:

1. Replace `OpenMath/Chapter4/Section441.lean` with the cycle 182
   draft preserved at
   `.prover-state/cycle_182_draft_section441.lean`.
2. Apply the cycle 184 namespace fix on draft line 1529 (the only
   non-stub change Aristotle suggested):

   ```diff
   -      M.αPoly_complex_root_norm_ge_one_of_stable hStable hψ_ne hψ_isRoot
   +      LinearMultistepMethod.αPoly_complex_root_norm_ge_one_of_stable M
   +        hStable hψ_ne hψ_isRoot
   ```

3. Run `time timeout 1200 lake env lean OpenMath/Chapter4/Section441.lean`.
4. If clean: verify `#print axioms` on each new theorem returns
   `[propext, Classical.choice, Quot.sound]`.
5. Update `extraction/formalization_data/lean_status.json` row for
   `lem:441A` from `partial` (with the Phase C.2 deferral note) to
   reflect Phase C.2 closure (Phase C.3/C.4 still partial).
6. Update `plan.md` row for `lem:441A` accordingly.
7. Commit. Title: `Cycle 189 — §441 lem:441A Phase C.2: Re(ζ) ≤ 0 for stable a-roots`.

If the compile produces specific errors after the namespace fix:
fix them locally up to a 30-minute time budget. If you run past 30
minutes, revert and proceed to Priority 2 — the cycle 182 draft was
written carefully but Lean elaboration on a 1568-LOC file is
inherently fragile, and Section381 work is more valuable per cycle
than further Section441 wrestling.

---

## Priority 2 — Section381 follow-up (DEFAULT)

This is what you will almost certainly do. All deliverables below are
axiom-clean targets, sorry count remains 0, and exercise the cycle
184–188 infrastructure productively.

The relevant `Section381.lean` line numbers (verified at HEAD `0434ee0`):

* `PhiEquivalent.refl` line 127, `.symm` line 131, `.trans` line 137.
* `IsZeroReducibleVia` line 199, `IsZeroReducible` line 212.
* `zeroReduced_*` lemmas lines 243–260.
* `IsPReducibleVia` line 272, `IsPReducible` line 284.
* `IsIrreducible` line 353.
* `PReducesTo` (constructors `refl` / `step` / `zeroStep`) ~lines 380–425.
* `PEquivalent` def line 428: `∃ sBar Mbar, PReducesTo M Mbar ∧ PReducesTo M' Mbar`.
* `PEquivalent.refl` line 433, `.symm` line 437,
  `.of_pReducesTo` line 443.
* `eq_of_isIrreducible_of_pReducesTo` line 457.
* `PEquivalent.trans_of_middle_isIrreducible` line 483.
* `def:381A Equivalent` line 557.
* Non-vacuity witness block starts ~line 580 (`pairPartition`,
  `paddedEuler_*` witnesses).

### Deliverable A (HEADLINE) — `PEquivalent.toPhiEquivalent`

Ship the bridge from `def:381F` (P-equivalence) to `def:381B`
(Φ-equivalence). This is the easy direction of `thm:381H`
("Equivalent ↔ P-equivalent ↔ Φ-equivalent") and consumes every
cycle 184–188 §380 deliverable in a single 5-line proof.

**Statement** (place after `PEquivalent.trans_of_middle_isIrreducible`,
i.e. after line 497, in the `OpenMath.Chapter3.Section312.RKTableau`
namespace):

```lean
/-- Butcher §380 — `def:381F` ⇒ `def:381B`: P-equivalent methods are
Φ-equivalent. The easy direction of thm:381H. The reverse direction
(`PhiEquivalent → PEquivalent`) requires `thm:314A` (independence of
elementary differentials) and is genuinely harder; deferred. -/
theorem PEquivalent.toPhiEquivalent {s s' : ℕ}
    {M : RKTableau s} {M' : RKTableau s'} :
    PEquivalent M M' → PhiEquivalent M M'
  | ⟨_, _, hM, hM'⟩ =>
      (PhiEquivalent.of_pReducesTo hM).trans
        (PhiEquivalent.of_pReducesTo hM').symm
```

This composes:
* `PhiEquivalent.of_pReducesTo` (cycle 187, extended in cycle 188 to
  handle `zeroStep`) — gives `PhiEquivalent M Mbar`.
* `PhiEquivalent.of_pReducesTo` again — gives `PhiEquivalent M' Mbar`.
* `PhiEquivalent.symm` (line 131) — flips to `PhiEquivalent Mbar M'`.
* `PhiEquivalent.trans` (line 137) — composes.

The `PEquivalent` definition `∃ sBar Mbar, PReducesTo M Mbar ∧
PReducesTo M' Mbar` (line 428) destructures cleanly via pattern
matching.

**Verify with `lean_verify
OpenMath.Chapter3.Section312.RKTableau.PEquivalent.toPhiEquivalent`
that axioms = `[propext, Classical.choice, Quot.sound]` only.**

### Deliverable B — `PEquivalent.of_isZeroReducibleVia`

Direct corollary mirroring `PEquivalent.of_pReducesTo` but for
0-reduction (using cycle 188's `zeroStep` constructor). Place
immediately after `PEquivalent.of_pReducesTo` (line 446):

```lean
/-- A method is P-equivalent to its 0-reduction. Direct corollary
of cycle 188's `PReducesTo.zeroStep` constructor combined with
`PEquivalent.of_pReducesTo`. -/
theorem PEquivalent.of_isZeroReducibleVia {s : ℕ}
    (M : RKTableau s) {inP1 : Fin s → Bool}
    (hP0 : ∃ i, inP1 i = false)
    (h : M.IsZeroReducibleVia inP1) :
    PEquivalent M (M.zeroReduced inP1) :=
  PEquivalent.of_pReducesTo
    (PReducesTo.zeroStep inP1 hP0 h
      (PReducesTo.refl (M.zeroReduced inP1)))
```

Constructor signature reference (verified from cycle 188 prompt):

```lean
| zeroStep {s s'' : ℕ}
    {M : RKTableau s} {M'' : RKTableau s''}
    (inP1 : Fin s → Bool) (_hP0 : ∃ i, inP1 i = false)
    (_h : M.IsZeroReducibleVia inP1) :
    PReducesTo (M.zeroReduced inP1) M'' → PReducesTo M M''
```

so the explicit call shape is
`PReducesTo.zeroStep inP1 hP0 h (PReducesTo.refl (M.zeroReduced inP1))`.

### Deliverable C — Φ-equivalence witnesses for `paddedEuler` via the bridge

Ship two corollaries that exercise Deliverable A on existing cycle
184–188 witnesses. Place these in the `### Non-vacuity witnesses`
block (around line 580 onward, after
`paddedEuler_phiEquivalent_zeroReduced` from cycle 188):

```lean
/-- Cycle 189 — `paddedEuler` is Φ-equivalent to itself via the
`def:381F → def:381B` bridge applied to cycle 184's reflexive
P-equivalence witness. Trivial but exercises `toPhiEquivalent`. -/
theorem paddedEuler_phiEquivalent_self_via_PEquivalent :
    PhiEquivalent paddedEuler paddedEuler :=
  (PEquivalent.refl paddedEuler).toPhiEquivalent

/-- Cycle 189 — `paddedEuler` is Φ-equivalent to its 0-reduction via
the `def:381F → def:381B` bridge. Composes cycle 188's
`paddedEuler_pEquivalent_zeroReduced` with `toPhiEquivalent`,
giving an alternative derivation of cycle 188's
`paddedEuler_phiEquivalent_zeroReduced`. -/
theorem paddedEuler_phiEquivalent_zeroReduced_via_PEquivalent :
    PhiEquivalent paddedEuler
      (paddedEuler.zeroReduced ![true, false]) :=
  paddedEuler_pEquivalent_zeroReduced.toPhiEquivalent
```

The second of these is *not* a tautology vs. cycle 188's
`paddedEuler_phiEquivalent_zeroReduced` — it goes through the
P-equivalence intermediary, validating that the two derivations
agree.

If `paddedEuler_pEquivalent_zeroReduced` from cycle 188 used a
different partition spelling than `![true, false]`, copy whatever
cycle 188 used verbatim. Check via `grep -n
paddedEuler_pEquivalent_zeroReduced
OpenMath/Chapter3/Section381.lean` and read the surrounding context.

---

## Verification checklist

After Priority 2 deliverables A+B+C land:

1. `time timeout 1200 lake env lean OpenMath/Chapter3/Section381.lean`
   exits 0. Expected build time ~3 min (cycle 188 baseline).
2. `grep -c sorry OpenMath/Chapter3/Section381.lean` returns `0`.
3. Tautology scanner: `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter3/Section381.lean` returns no hits.
4. `lean_verify` on each new public theorem returns
   `[propext, Classical.choice, Quot.sound]`. Specifically:
   - `OpenMath.Chapter3.Section312.RKTableau.PEquivalent.toPhiEquivalent`
   - `OpenMath.Chapter3.Section312.RKTableau.PEquivalent.of_isZeroReducibleVia`
   - `OpenMath.Chapter3.Section381.paddedEuler_phiEquivalent_self_via_PEquivalent`
   - `OpenMath.Chapter3.Section381.paddedEuler_phiEquivalent_zeroReduced_via_PEquivalent`

   (Adjust namespace prefix if cycle 184–188 used `Section381` for
   the witness theorems — `grep -n "namespace OpenMath"
   OpenMath/Chapter3/Section381.lean` will show the actual ladder.)

5. No regression on cycle 184–188 theorems
   (`PhiEquivalent.of_pReducesTo`, `PEquivalent.refl`,
   `PEquivalent.symm`, `PEquivalent.trans_of_middle_isIrreducible`,
   `paddedEuler_phiEquivalent_zeroReduced`,
   `paddedEuler_pEquivalent_zeroReduced`,
   `eq_of_isIrreducible_of_pReducesTo`, etc.).

---

## What NOT to try

* **Do NOT attempt `PEquivalent.trans` (full version).** The general
  transitivity requires confluence of P-reduction (any two reduction
  sequences from a common source can be completed to a common
  target). Cycle 188's `PEquivalent.trans_of_middle_isIrreducible`
  covers the easy case; full transitivity is multi-cycle work and
  explicitly deferred per the cycle 184/188 docstrings.

* **Do NOT attempt `thm:381G`** ("Irreducible Runge Kutta Stage
  Distinguishability"). Per
  `extraction/formalization_data/entities/thm_381G.json`, it depends
  on `thm:314A` (Independence of the elementary differentials),
  which is `[ ]` not started in `plan.md`. You cannot ship a
  faithful `thm:381G` without first formalising `thm:314A` —
  multi-cycle infrastructure scope.

* **Do NOT attempt the reverse `PhiEquivalent → PEquivalent`
  direction of `thm:381H`.** Same blocker: textbook proof goes via
  `thm:381G`, which needs `thm:314A`.

* **Do NOT attempt `def:381E`'s `reducedMethod` fixed-point
  construction.** Multi-cycle work per
  `.prover-state/issues/reduced_method_deferred.md`. Cycle 188's
  `zeroStep` constructor extension is one of several building
  blocks; the construction itself requires strong induction on
  stage count + termination argument that is not in scope for
  cycle 189.

* **Do NOT modify `scripts/autonomous_loop.py`.** Per CLAUDE.md and
  every consultant note since cycle 014, the GPFS / prompt-builder
  / tautology-scanner issues are all loop-maintainer territory.
  If you observe new false-positive scanner hits or another
  phantom verdict, append to
  `.prover-state/issues/tautology_scanner_false_positives.md` or
  `phantom_commit_verdict_pattern.md` — do NOT patch the supervisor.

* **Do NOT raise `maxHeartbeats` above 200000.** None of the
  Priority 2 deliverables need it — they are all 5–15 LOC composing
  existing axiom-clean lemmas.

* **Do NOT chase an Aristotle batch this cycle.** Deliverables A+B+C
  are too small for Aristotle to add value (each is 5–10 LOC of
  pure composition). Reserve Aristotle slots for substantive proofs.

* **Do NOT poll the cycle 184 Aristotle project
  `7c4d0ffb-e6c1-4ef4-b8f5-688d256bac44`** further. It returned
  `COMPLETE_WITH_ERRORS` in cycle 184 with the namespace fix
  identified; the only remaining blocker is GPFS, which Aristotle
  cannot help with.

* **Do NOT re-derive Phase B of `lem:441A`.** It is closed at
  `Section441.lean:913` (`aPoly_coeff_one_pos_of_stable_preconsistent`,
  cycle 179), axiom-clean. Multiple consultant notes (cycles 174,
  180) verify this.

* **Do NOT add comments referencing the current cycle, "from
  cycle 188", "as discussed above", etc., inside *theorem
  statements* and *bodies*.** Docstrings on new theorems may
  reference Butcher § numbers and the cycle's textbook target
  (e.g. "thm:381H easy direction"); they should NOT include
  process narration. Per CLAUDE.md hygiene rules.

---

## Pre-commit faithfulness checklist (mandatory)

For each of Deliverable A, B, C:

* **Tautology check**: does the conclusion appear verbatim as a
  hypothesis? **No.** Deliverable A's conclusion `PhiEquivalent M M'`
  does not appear in `PEquivalent M M'`'s unfolding (different
  predicates with different definitions — one is a Φ-value
  pointwise equality, the other is the existence of a common
  reduct).
* **Identity check**: is the proof a single `exact h`? **No.**
  Deliverable A composes three named lemmas
  (`PhiEquivalent.of_pReducesTo`, `.symm`, `.trans`); B composes
  `PEquivalent.of_pReducesTo` + cycle 188's `PReducesTo.zeroStep`;
  C composes Deliverable A with cycle 184/188 named witnesses.
* **Hypothesis strength check**: are any hypotheses stronger than
  textbook? **No.** Deliverable A takes only `PEquivalent M M'`;
  Deliverable B takes the standard `IsZeroReducibleVia` +
  non-empty-P₀ pair (matching cycle 188's `zeroStep` constructor).
* **Definition smuggling check**: no new `def`/`structure`
  introduced. All deliverables are pure theorems.

---

## End-of-cycle deliverables

1. `OpenMath/Chapter3/Section381.lean` — four new public theorems
   (Deliverables A, B, plus two witnesses in C). LOC delta ~25–35.
2. `.prover-state/task_results/cycle_189.md` — standard format,
   document axiom-cleanliness verification on each new theorem
   (see `cycle_188.md` for the template).
3. `plan.md` — no row updates needed (Deliverables A+B+C are §380
   infrastructure that doesn't move any plan.md row from `[ ]` to
   `[x]`; the def:381F row stays `[~]` partial since `thm:381H`
   reverse direction remains deferred). Update the existing
   def:381F status note to add cycle 189's contribution.
4. `extraction/formalization_data/lean_status.json` — no row
   updates needed for the same reason.
5. Commit titled
   `Cycle 189 — §380 PEquivalent.toPhiEquivalent (def:381F → def:381B); zeroReducible corollary; mixed witnesses`.

If GPFS recovered and Priority 1 ran instead, replace the commit
title with
`Cycle 189 — §441 lem:441A Phase C.2: Re(ζ) ≤ 0 for stable a-roots`
and update `plan.md` + `lean_status.json` for `lem:441A` Phase C.2
closure.

---

## Branch back / fallback plans

### A: Deliverable A fails to elaborate

The most likely cause is a `PhiEquivalent.symm` type-class hiccup at
the cross-stage-count boundary (`PhiEquivalent {s s' : ℕ}` applied at
`{sBar, s'}`). Diagnose by:

1. `lean_goal` at the `(PhiEquivalent.of_pReducesTo hM').symm` step.
2. If the goal shape is `PhiEquivalent ?Mbar ?M'` instead of
   `PhiEquivalent ?M' ?Mbar`, swap the order: write the proof as
   ```lean
   PEquivalent.toPhiEquivalent
     | ⟨_, _, hM, hM'⟩ =>
         PhiEquivalent.trans
           (PhiEquivalent.of_pReducesTo hM)
           ((PhiEquivalent.of_pReducesTo hM').symm)
   ```
   with explicit parenthesization, or split into named `have` steps
   to expose intermediate types.

### B: Deliverable B fails (positional vs. named arguments to `zeroStep`)

Diagnose via `lean_hover_info` on `PReducesTo.zeroStep` to confirm
the exact signature. If named arguments are needed:
```lean
PReducesTo.zeroStep (inP1 := inP1) (_hP0 := hP0) (_h := h)
  (PReducesTo.refl (M.zeroReduced inP1))
```

### C: Deliverable C fails (witness regression)

The most likely cause is that `paddedEuler_pEquivalent_zeroReduced`
(cycle 188) used a *different* canonical partition than
`![true, false]`. Check the cycle 188 commit (`0434ee0`) for the
exact partition — `git show 0434ee0 -- OpenMath/Chapter3/Section381.lean
| grep -A2 paddedEuler_pEquivalent_zeroReduced`. Copy the literal
verbatim.

### D: All three deliverables fail and you have <30 min remaining

Backup deliverable: ship ONLY `PEquivalent.toPhiEquivalent`
(Deliverable A) and skip B + C. A on its own is the headline; B + C
are enrichments. Update the commit title and task_results
accordingly. Sorry count remains 0.

### E: All three deliverables succeed with 30+ min remaining

Optional stretch: scan `Section381.lean` for any other inline
`example`/`have` blocks that could be cleanly promoted to public
named theorems (cycle 186 promotion pattern). Do NOT introduce new
mathematical content beyond what's in this strategy.
