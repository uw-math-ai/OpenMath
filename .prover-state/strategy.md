# Cycle 199 strategy

## Context

Cycle 198 shipped `pEquivalent_iff_exists_common_irreducible_reduct`
axiom-clean (the def:381F existential characterization consuming cycle
197's `reducedMethod_exists` + cycle 192's `PReducesTo.trans`), plus a
`paddedEuler` non-vacuity example exercising the forward direction.
File `OpenMath/Chapter3/Section381.lean` is at 1657 LOC, 0 sorries,
all new declarations axiom-clean.

Section441 GPFS pathology is now at 18 consecutive cycles (17 calendar
days). It is loop-maintainer territory; worker-side smoke tests are
purely diagnostic.

No Aristotle jobs are pending.

Sorry count: 0 across the entire codebase.

## Priorities

### P0 — Section441 GPFS smoke test (mandatory, single attempt)

Run this command exactly once. Do NOT retry, do NOT vary the timeout,
do NOT attempt the cycle 182 draft. The 18-cycle pattern is fully
established; this is diagnostic logging only.

```bash
# Pre-flight: confirm no D-state zombies
ps -u $USER -o pid,stat,wchan,etime,comm | grep -E "^[ ]*[0-9]+ +D" \
  || echo "(no D-state processes)"

# Smoke test
time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean
```

Expected: EXIT=124, real ≈ 5m0.03s, near-zero CPU. Append the
result to `.prover-state/issues/cycle_182_gpfs_slowness.md` as the
"Cycle 199 update (19th timeout)" entry following the format of cycles
192–198. If by some miracle it completes in < 5 minutes, STOP and
pivot to applying the cycle 182 draft + cycle 184 namespace fix
(preserved at `.prover-state/cycle_182_draft_section441.lean`,
line 1529: `M.αPoly_…` → `LinearMultistepMethod.αPoly_…`).

### P1 — `pEquivalent_irreducible_reduct_unique` (canonical-form wrapper)

**This is the cycle 199 substantive deliverable.** Ship the
heterogeneous-stage uniqueness companion to cycle 198's iff, formalizing
"the common irreducible reduct of a P-equivalence is unique up to
heterogeneous-stage `HEq`".

This is the highest-confidence single-cycle deliverable available:
the strategy is fully specified by cycle 198's discovery #2 ("a
separate `pEquivalent_irreducible_reduct_unique` theorem... would be a
clean ~10-LOC follow-up"), and the closure path is mechanical given
the infrastructure already shipped:

* cycle 193's `PEquivalent.eq_of_both_isIrreducible` — two irreducible
  P-equivalent methods coincide up to `HEq`.
* cycle 198's iff — provides the two `PReducesTo M M''` reduction
  legs ending at an irreducible reduct.
* cycle 188's `eq_of_isIrreducible_of_pReducesTo` — irreducible
  endpoint extraction along a `PReducesTo` chain.

**Pre-flight: verify exact lemma names.** Before writing the proof,
run these `Grep` queries on `OpenMath/Chapter3/Section381.lean` to
confirm the actual names (cycle 198 task results occasionally
paraphrase from memory):

* `Grep -n "eq_of_both_isIrreducible" OpenMath/Chapter3/Section381.lean`
  — confirm cycle 193's heterogeneous-stage extraction lemma name and
  exact argument order.
* `Grep -n "eq_of_isIrreducible_of_pReducesTo" OpenMath/Chapter3/Section381.lean`
  — confirm cycle 188's lemma name. If the actual name differs, use
  whatever `Grep` reports.
* `Grep -n "paddedEuler_pReduced.*isIrreducible" OpenMath/Chapter3/Section381.lean`
  — confirm cycle 190's irreducibility witness for the non-vacuity
  example.

**Target statement** (insert at `OpenMath/Chapter3/Section381.lean`
immediately after cycle 198's iff, around line 870):

```lean
/-- The common irreducible reduct of a P-equivalence is unique up to
heterogeneous-stage `HEq`. Formalizes Butcher §380 def:381F's
"reduces to the same reduced method" beyond existence: when both legs
of a P-equivalence terminate at irreducible reducts, those reducts
coincide up to stage count.

Consumes cycle 198's iff to extract a common irreducible reduct, then
cycle 188's `eq_of_isIrreducible_of_pReducesTo` to identify each of
the user-supplied irreducible reducts with that common one. -/
theorem pEquivalent_irreducible_reduct_unique
    {s s' s₁ s₂ : ℕ} {M : RKTableau s} {M' : RKTableau s'}
    {M₁ : RKTableau s₁} {M₂ : RKTableau s₂}
    (h₁ : PReducesTo M M₁) (h₁irr : M₁.IsIrreducible)
    (h₂ : PReducesTo M' M₂) (h₂irr : M₂.IsIrreducible)
    (hEquiv : PEquivalent M M') :
    s₁ = s₂ ∧ HEq M₁ M₂ := by
  sorry  -- replace per proof recipe below; commit MUST be sorry-free
```

**Proof recipe** (target ~8-15 LOC, **no `sorry` in final commit**):

Step A. Apply cycle 198's iff to `hEquiv`:
```lean
obtain ⟨s₃, M₃, hMM₃, hM'M₃, hM₃irr⟩ :=
  (pEquivalent_iff_exists_common_irreducible_reduct M M').mp hEquiv
```

Step B. Identify `M₁` with `M₃` via cycle 188's lemma applied to the
two reduction paths from `M` (the `h₁` path ends at the irreducible
`M₁`; the `hMM₃` path ends at the irreducible `M₃`; both starting from
`M`):
```lean
-- The exact destructuring depends on whether cycle 188's lemma
-- returns `s₁ = s₃ ∧ HEq M₁ M₃` or some equivalent form.  Use Grep
-- to verify its signature before this step.
obtain ⟨hs₁₃, hM₁₃⟩ := eq_of_isIrreducible_of_pReducesTo … h₁ h₁irr hMM₃ hM₃irr
```

Step C. Symmetrically identify `M₂` with `M₃`:
```lean
obtain ⟨hs₂₃, hM₂₃⟩ := eq_of_isIrreducible_of_pReducesTo … h₂ h₂irr hM'M₃ hM₃irr
```

Step D. Combine: `s₁ = s₂` by `hs₁₃.trans hs₂₃.symm`; `HEq M₁ M₂` by
`hM₁₃.trans hM₂₃.symm` (or `HEq.trans` if `.trans` is not on `HEq`'s
dot-notation in current Mathlib — check via `Grep "HEq.trans"
$LAKE_HOME/packages/mathlib`).

**Fallback if cycle 188's lemma signature doesn't yield directly
matching `s = s' ∧ HEq`**: cycle 188's
`eq_of_isIrreducible_of_pReducesTo` may instead conclude `PReducesTo` is
reflexive in the irreducible-source case (its docstring per the
session context says "irreducible source forces every reduction
sequence to be reflexive"). In that case, the proof recipe shifts to:

* Step B': cycle 188 applied to `h₁` + `h₁irr` gives that the
  reduction is reflexive — i.e. `s = s₁` and `HEq M M₁`. But we
  need this on the `M --> M₁` and `M --> M₃` paths starting from a
  potentially-reducible `M`. The right invocation is via cycle 188
  applied at the *terminus* `M₁`, not the source `M`. **Inspect
  the cycle 188 lemma's signature carefully with `Grep -A 5
  "eq_of_isIrreducible_of_pReducesTo"` before committing to either
  proof recipe variant.**

**If the recipes above both stall**, the alternative closure path is
direct via cycle 193:

* Build `PEquivalent M₁ M₂` from `h₁` + `h₂` + `hEquiv` by composing
  `PEquivalent.of_pReducesTo h₁`'s `.symm` with `hEquiv` with
  `PEquivalent.of_pReducesTo h₂`. Verify which `PEquivalent.trans`
  variant exists in Section381 (cycle 185's
  `PEquivalent.trans_of_middle_isIrreducible` or cycle 188's
  successor) and route through the right one.
* Apply `PEquivalent.eq_of_both_isIrreducible h₁irr h₂irr` to that
  `PEquivalent M₁ M₂`. This returns `s₁ = s₂ ∧ HEq M₁ M₂` directly.

The cycle 193 route is preferred if any signature mismatches arise
because it bundles the goal shape exactly. **Use whichever recipe's
lemma signatures match cleanly after `Grep` verification.**

**Non-vacuity witness (P1 stretch, ship if proof closes cleanly)**:
add an `example` immediately after the theorem demonstrating the
trivial reflexive case on `paddedEuler.pReduced pairPartition`:

```lean
example :
    (1 : ℕ) = 1 ∧
    HEq (paddedEuler.pReduced pairPartition)
        (paddedEuler.pReduced pairPartition) :=
  pEquivalent_irreducible_reduct_unique
    (PReducesTo.refl _) paddedEuler_pReduced_pairPartition_isIrreducible
    (PReducesTo.refl _) paddedEuler_pReduced_pairPartition_isIrreducible
    (PEquivalent.refl _)
```

(Verify the exact name of cycle 190's irreducibility witness via the
`Grep` from the pre-flight checklist.)

### P2 — recon `thm:381G` for cycle 200+

This is **read-only** work this cycle. Do NOT attempt to ship
thm:381G in cycle 199 — it is the natural next textbook target but its
scope is unknown (the cycle 198 worker flagged it as the "highest-
leverage" but did not assess complexity).

Steps:

1. Read `extraction/formalization_data/entities/thm_381G.json` to get
   the textbook statement and dependency list.
2. Read the relevant Butcher §380 prose around the §380 / thm:381G
   discussion. Use `Grep -n "381G\|Irreducible Runge"
   extraction/raw_text/ch03.txt` to find the location, then read a
   ~50-line window around the hit.
3. Add a 5-10 line note to the cycle 199 task results documenting:
   * The textbook statement (verbatim quote).
   * Whether the dependencies are all satisfied (look up each in
     `extraction/formalization_data/lean_status.json`).
   * Rough LOC estimate (small / medium / large).
   * Whether it appears to be a single-cycle deliverable or
     multi-cycle infrastructure work.

This recon unblocks cycle 200's planner to make an informed pivot
decision. Do NOT start the proof.

## What NOT to do

1. **Do NOT attempt the Section441 cycle 182 draft.** 18 consecutive
   GPFS timeouts; the failure mode is fully systemic. One smoke test,
   one log entry, move on.

2. **Do NOT modify `scripts/autonomous_loop.py`.** Per CLAUDE.md
   and the standing
   `.prover-state/issues/tautology_scanner_false_positives.md` and
   `.prover-state/issues/phantom_commit_verdict_pattern.md` issues,
   prompt-builder bugs are loop-maintainer territory.

3. **Do NOT introduce `axiom` or `constant` declarations.** The
   cycle 199 target uses cycle 188/193/198 infrastructure that is
   already axiom-clean; the closure must remain axiom-clean.

4. **Do NOT raise `maxHeartbeats` above 200000.** The cycle 199 target
   is a ~10-LOC tactic proof; if it explodes elaboration-time-wise,
   decompose into named helpers rather than bumping the budget.

5. **Do NOT poll Aristotle.** No jobs are in flight, and one-shot
   single-cycle theorems do not benefit from batch submission.

6. **Do NOT attempt `thm:381G`'s proof.** P2 is recon only — read the
   entity data and Butcher prose, write a short summary, do NOT start
   tactic work. If P1 closes early, defer the proof to next cycle.

7. **Do NOT attempt the constructive `noncomputable def reducedMethod`.**
   This requires either a Σ-wrapper `WellFoundedRelation` or
   `Decidable IsPReducible`/`IsZeroReducible` instances — both
   multi-cycle engineering. Cycle 198's existential iff has reduced
   the demand for the constructive version (def:381F is now closed
   under the existential reading); the multi-cycle cost is not
   justified yet.

8. **Do NOT pack uniqueness into the cycle 198 iff itself.** Strategy
   reasoning: cycle 198's iff is a clean existential characterization
   matching Butcher's textbook prose. The uniqueness wrapper belongs
   as a separate theorem (cycle 199's P1 target) so consumers can pick
   the level of strength they need.

9. **Do NOT use underscore-prefixed unused hypothesis names without
   intentional rationale.** Per
   `.prover-state/issues/tautology_scanner_false_positives.md`, the
   underscore-prefix marks "unused on purpose" — apply it only when
   the hypothesis is genuinely propagated for signature symmetry or
   downstream caller convenience. Cycle 199's P1 theorem should
   actively consume all five hypotheses; if one becomes unused during
   proof, restructure the proof rather than silencing with `_`.

10. **Do NOT skip the GPFS smoke test even though we expect it to
    fail.** The single-attempt diagnostic log is the only signal the
    loop-maintainer has that the pathology continues; skipping it
    breaks the established 18-cycle pattern documented in
    `cycle_182_gpfs_slowness.md`.

11. **Do NOT guess lemma names from session-context summaries.** Cycle
    198's task results and the plan.md narrative sometimes paraphrase
    lemma names. ALWAYS verify via `Grep` against the actual source
    file before invoking a lemma in a tactic.

12. **Do NOT attempt `Polynomial.ext` skeletons or
    `Polynomial.coeff` per-coefficient closures** — those are
    Section441 territory and irrelevant to the Section381 cycle 199
    target. Listed here only because the cycle 172/173 stall pattern
    occasionally tempts return attempts; ignore.

## Verification checklist (run before commit)

1. `lake env lean OpenMath/Chapter3/Section381.lean` exits 0.
2. `grep -c sorry OpenMath/Chapter3/Section381.lean` returns 0.
3. `wc -l OpenMath/Chapter3/Section381.lean` shows file growth in the
   +15 to +40 LOC range (theorem + docstring + optional example).
4. `lean_verify` on
   `OpenMath.Chapter3.Section312.RKTableau.pEquivalent_irreducible_reduct_unique`
   returns axioms `[propext, Classical.choice, Quot.sound]` only.
5. Tautology scanner clean:
   `Grep -E ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter3/Section381.lean`
   returns nothing new.
6. `.prover-state/issues/cycle_182_gpfs_slowness.md` has the cycle 199
   update appended.
7. `.prover-state/task_results/cycle_199.md` documents:
   * P0 smoke test result (EXIT code, timing, CPU).
   * P1 deliverable (theorem signature, proof recipe used,
     non-vacuity witness if shipped).
   * P2 thm:381G recon summary.
   * Faithfulness check on the new theorem (def:381F textbook
     statement, how the uniqueness theorem captures "same reduced
     method").
8. Commit message follows the established format:
   `Cycle 199 — §380 pEquivalent_irreducible_reduct_unique
   (heterogeneous-stage canonical-form wrapper consuming cycle 198's
   iff + cycle 188/193 extraction lemmas); §441 Phase C.2
   GPFS-blocked (19th)`.

## Success criteria

* **Score-1 minimum**: P0 smoke test logged + P1 ships axiom-clean
  with 0 sorries.
* **Score-2 target**: P1 ships + non-vacuity witness ships + P2 recon
  written.
* **Score-0 failure**: P1 stalls on a tactic mismatch (most likely
  cause: misremembered name of cycle 188's extraction lemma or
  cycle 184/185's trans variant). Mitigation: use `Grep` to verify
  every lemma name before writing the proof.

If P1's proof stalls past 90 minutes of cumulative attempt time,
ROLLBACK and ship only the P0 smoke test + P2 recon, with the P1
attempt preserved as a draft at
`.prover-state/cycle_199_draft_uniqueness.lean` for cycle 200 to
salvage.
