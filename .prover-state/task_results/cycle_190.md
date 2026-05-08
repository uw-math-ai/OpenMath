# Cycle 190 Results

## Worked on

* Priority 0 — `OpenMath/Chapter4/Section441.lean` GPFS smoke test
  (10th attempt).
* Priority 2 (default path, expected) —
  `RKTableau.PEquivalent.eq_of_isIrreducible_of_middle`
  (canonical-form constructor for §380 def:381F P-equivalence
  through a common irreducible middle) and the non-vacuity witness
  `paddedEuler_pEquivalent_self_via_pReduced`, plus its private
  prerequisite `paddedEuler_pReduced_pairPartition_isIrreducible`.

## Approach

1. **Priority 0 smoke test (5 min hard cap)**: ran
   `time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean`.
   Pre-flight `ps` confirmed no D-state zombies. Result: EXIT=124,
   real 5m0.056s, user 0m0.321s, sys 0m0.533s — CPU = 0.28% of wall,
   identical near-zero pattern to cycles 182–189. 10th consecutive
   timeout. Logged to `cycle_182_gpfs_slowness.md` per strategy.
2. **Pivot to Priority 2 per strategy**.
3. **Deliverable A** — added
   `RKTableau.PEquivalent.eq_of_isIrreducible_of_middle` directly
   after `PEquivalent.trans_of_middle_isIrreducible`
   (`OpenMath/Chapter3/Section381.lean:495–510`). Body is the named
   existential constructor `⟨sBar, N, h₁, h₂⟩`. The
   `_hN : N.IsIrreducible` hypothesis is documentation-only
   (underscore-prefixed); the docstring spells out the contract
   ("hypothesis is documentation-only … the strength is a contract,
   not a logical requirement").
4. **Deliverable B prerequisite** — extracted the irreducibility
   witness for `paddedEuler.pReduced pairPartition` from the existing
   inline `example` proof at line 754 (cycle 188 era) into a private
   theorem `paddedEuler_pReduced_pairPartition_isIrreducible` at the
   end of the third `Section381` namespace block. The lifted body is
   verbatim from the inline witness (the `hMidPReducedB` lemma plus
   the `IsIrreducible := ⟨¬ IsZeroReducible, ¬ IsPReducible⟩`
   refinement). The cycle 188 inline example still exists at line 754
   unchanged, intentionally left as-is to minimize risk on a
   GPFS-degraded compile path.
5. **Deliverable B main** — added
   `paddedEuler_pEquivalent_self_via_pReduced` as the public witness,
   constructed via `PEquivalent.eq_of_isIrreducible_of_middle` with
   the new private helper supplying `_hN` and
   `paddedEuler_pReducesTo_pReduced` supplying both `h₁` and `h₂`.
6. **Skipped the stretch** (`PReducesTo.of_isZeroReducibleVia`).
   Strategy authorized it conditionally; primary deliverables already
   shipped clean and adding more code on a slow GPFS compile path
   trades risk for marginal scaffolding value. Documented in
   "Suggested next approach" so cycle 191 can pick it up if useful.
7. **Verification**:
   * `lake env lean OpenMath/Chapter3/Section381.lean` → exit 0,
     real 1m42.157s.
   * `lake build OpenMath.Chapter3.Section381` → exit 0, 4.8s
     (fully cached after the lean run).
   * `#print axioms` on both new public theorems →
     `[propext, Classical.choice, Quot.sound]` only:
     - `OpenMath.Chapter3.Section312.RKTableau.PEquivalent.eq_of_isIrreducible_of_middle`
     - `OpenMath.Chapter3.Section381.paddedEuler_pEquivalent_self_via_pReduced`
   * `grep -c sorry OpenMath/Chapter3/Section381.lean` → 0.

## Result

**SUCCESS** for both Priority 2 deliverables. Two new public,
axiom-clean theorems shipped; one new private helper. Section381.lean
remains sorry-free.

Priority 0 timed out as expected (10th consecutive); Priority 1A
(Phase C.2 of `lem:441A`) was skipped per strategy abort threshold.

## Faithfulness check

### `RKTableau.PEquivalent.eq_of_isIrreducible_of_middle`

* Entity: this is helper-side infrastructure for the def:381F
  encoding of "two Runge–Kutta methods are P-equivalent if each of
  them reduces to the same reduced method". Quoting `def_381F.json`
  `statement_text`:
  > Two Runge–Kutta methods are 'P-equivalent' if each of them
  > reduces to the same reduced method.
* Lean statement captures: **same content** (constructor side of
  the existential `def:381F`). The `IsIrreducible` decoration on
  `_hN` is a *non-binding documentation flag*: the proof body does
  not consume it, so the lemma is literally
  `(h₁ : PReducesTo M N) (h₂ : PReducesTo M' N) → PEquivalent M M'`
  with an extra `_hN` slot that signals to readers "the intermediate
  `N` is the canonical reduced form" without strengthening or
  weakening the conclusion. The textbook's "the same reduced method"
  is implemented as the existential `∃ sBar Mbar, …` of def:381F's
  Lean encoding, with the `_hN` flag aligning the source-code site
  with the textbook intuition that the common middle is irreducible.
* **Tautology check**: conclusion `PEquivalent M M'` is the
  existential `∃ sBar Mbar, PReducesTo M Mbar ∧ PReducesTo M' Mbar`.
  `_hN : N.IsIrreducible` is an `IsIrreducible` predicate on `N`,
  syntactically and semantically distinct. `h₁` and `h₂` are
  individual `PReducesTo` conjuncts. Neither hypothesis equals the
  conclusion. Pass.
* **Identity check**: not `exact h`. Body
  `⟨sBar, N, h₁, h₂⟩` constructs the four-tuple existential from
  three named arguments (`N` and the two reducts) plus the implicit
  `sBar`. Pass.
* **Hypothesis strength check**: `_hN` is *strictly extra* relative
  to the proof obligation (the proof goes through without it). This
  is intentional and documented in the docstring. The strategy
  explicitly authorized this as a documentation contract for
  downstream callers; future cycles that find the unused hypothesis
  is too risky vs the supervisor's tautology scanner can drop `_hN`
  with no proof impact. The `_` prefix on the binder marks it as
  intentionally unused (Lean convention).
* **Identity-vs-substantive judgement**: this is a *very* thin lemma
  — essentially renaming the four-tuple existential constructor of
  `PEquivalent` with an irreducibility decoration. It does real
  work in *naming*, not in *proving*: downstream callers can write
  `PEquivalent.eq_of_isIrreducible_of_middle hIrr h₁ h₂` instead of
  `⟨_, _, h₁, h₂⟩`, signaling intent. Cycle 188's
  `PEquivalent.trans_of_middle_isIrreducible` (a substantive lemma
  using `eq_of_isIrreducible_of_pReducesTo` to reduce the two
  PReducesTo witnesses to a common middle) and cycle 190's
  `eq_of_isIrreducible_of_middle` (a *constructor* for the
  irreducible-middle case) are complementary: trans handles the
  case where the middle is given via `PEquivalent`, eq_of_middle
  handles the case where the middle is given directly via
  `PReducesTo`. The latter is naturally where downstream witnesses
  will live, since most concrete reducts are constructed once and
  then cited.

### `paddedEuler_pReduced_pairPartition_isIrreducible` (private)

* Entity: helper non-vacuity ingredient. Lifted from existing inline
  proof at `Section381.lean:768–779` (cycle 188 era).
* Lean statement captures: **same content** as the inline witness;
  literal extraction.
* Faithfulness check: pass (identical to cycle 188's inline proof,
  which already passed faithfulness review at that cycle).

### `paddedEuler_pEquivalent_self_via_pReduced`

* Entity: non-vacuity witness for cycle 190's new constructor.
  Mirrors the existing `example : paddedEuler.PEquivalent paddedEuler`
  at `Section381.lean:754` (cycle 188 via
  `PEquivalent.trans_of_middle_isIrreducible`) but routes through the
  new direct constructor instead of the trans lemma. Both witnesses
  are valid; the new one is shorter and exercises the new
  constructor.
* Lean statement captures: **same content** as the cycle 188
  example's anonymous statement (`paddedEuler.PEquivalent
  paddedEuler`), now named so it can be referenced.
* **Tautology check**: conclusion `paddedEuler.PEquivalent
  paddedEuler` does not appear as any hypothesis (no hypotheses; the
  theorem body cites three named lemmas). Pass.
* **Identity check**: not `exact h`. Body is a three-argument
  application of `eq_of_isIrreducible_of_middle`. Pass.
* **Hypothesis strength check**: no hypotheses. Pass.

## Dead ends

None this cycle. Both deliverables type-checked first try. The only
dead end was the GPFS smoke test, which was a known-expected
timeout, not a real attempt.

## Discovery

* The cycle 188 inline `example` at line 754 is almost-but-not-quite
  Deliverable B: it has the same conclusion
  (`paddedEuler.PEquivalent paddedEuler`) but goes through
  `trans_of_middle_isIrreducible` rather than directly through
  `eq_of_isIrreducible_of_middle`. Cycle 190's named theorem and the
  cycle 188 example are *redundant in conclusion but distinct in
  exercise*: the new theorem is now the canonical citation point,
  and the cycle 188 example exists as documentation that the
  trans-style derivation also closes (small structural redundancy
  worth keeping).
* The strategy's stretch sketch
  `PReducesTo.zeroStep h h_nonempty PReducesTo.refl` had the
  argument order wrong: `zeroStep` takes
  `(inP1, _hP0, _h, recursive)` per
  `Section381.lean:418–422`. So the correct stretch body would be
  `PReducesTo.zeroStep inP1 h_nonempty h (PReducesTo.refl _)`.
  Recording this for cycle 191's use.

## Suggested next approach

Section381 is now within reach of a natural pause point:

1. **Cycle 191 — minor consolidation**: ship the stretch
   `PReducesTo.of_isZeroReducibleVia` (corrected body per the
   discovery above). 4–5 LOC, axiom-clean. Optionally consider
   replacing the inline composition in
   `PEquivalent.of_isZeroReducibleVia` (`Section381.lean:451–458`)
   with the new helper for code-style consistency.
2. **Cycle 191 — alternative**: pivot to a fresh witness in
   Section381 that exercises *both* directions of `PEquivalent`
   (a non-`paddedEuler` example, e.g. one constructing a 3-stage
   tableau that reduces to a 2-stage tableau via a non-trivial
   `PPartition`). This would be ~30–60 LOC and would test the
   constructor on a heterogeneous chain that genuinely uses both
   `step` and `zeroStep` constructors of `PReducesTo`.
3. **Cycle 192+**: enter pause mode while waiting for `thm:314A`
   (Independence of elementary differentials) infrastructure to
   start; the §380 P-equivalence cluster is essentially "done"
   modulo the reverse direction of `thm:381H`.
4. **Cycle 191 — Section441 monitoring**: continue the GPFS smoke
   test as Priority 0. If it ever recovers, the
   `cycle_182_draft_section441.lean` + namespace fix recipe is
   ready to ship Phase C.2.

Recommendation: prefer **cycle 191 option 1** (stretch consolidation)
for low-risk continued momentum on Section381, paired with the
Section441 smoke test as Priority 0 standby.
