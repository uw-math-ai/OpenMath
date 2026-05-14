# Cycle 192 Results

## Worked on

* Priority 0 — GPFS smoke test on `OpenMath/Chapter4/Section441.lean`
  (Phase C.2 of `lem:441A`).
* Priority 2 — Completed the cycle 191 deferred refactor: reordered
  `PReducesTo.of_isZeroReducibleVia` to precede
  `PEquivalent.of_isZeroReducibleVia` in source order, then refactored
  the body of `PEquivalent.of_isZeroReducibleVia` to consume the new
  helper as a one-liner. Both in `OpenMath/Chapter3/Section381.lean`.
* Priority 3 (Option 3A) — Shipped
  `OpenMath.Chapter3.Section312.RKTableau.PReducesTo.trans`
  (multi-step reduction concatenation) plus two `paddedEuler`
  non-vacuity `example` witnesses (one exercising the `step` case,
  one exercising the `zeroStep` case of the induction).

## Approach

* **Priority 0**: Pre-flight zombie check
  (`ps -u $USER -o pid,stat,wchan,etime,comm | grep "^[ ]*[0-9]+ +D"`,
  returned "no zombies"), then
  `time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean`.
* **Priority 2**: Located the cycle 191 helper
  `PReducesTo.of_isZeroReducibleVia` (Section381.lean:485 pre-edit)
  and the consumer `PEquivalent.of_isZeroReducibleVia` (line 451
  pre-edit). Single Edit operation: deleted the helper's old block
  (lines 478–490 pre-edit) and re-inserted it before line 448, then
  rewrote the consumer's body to
  `PEquivalent.of_pReducesTo (PReducesTo.of_isZeroReducibleVia M hP0 h)`.
* **Priority 3 (Option 3A)**: Wrote
  `theorem PReducesTo.trans (h₁ : PReducesTo M M') (h₂ : PReducesTo M' M'')
   : PReducesTo M M''` by `induction h₁ with`, three constructor
  cases (`refl ⇒ h₂`, `step ⇒ PReducesTo.step P hLt hVia (ih h₂)`,
  `zeroStep ⇒ PReducesTo.zeroStep inP1 hP0 hVia (ih h₂)`). Placed
  after `PEquivalent.of_isZeroReducibleVia` so the helper/consumer
  pair from Priority 2 stays adjacent. Added two `example` non-vacuity
  witnesses near the existing `paddedEuler_pReducesTo_*` lemmas
  (Section381.lean ≈line 730), exercising both inductive cases on
  concrete data.
* Verification: `lake env lean OpenMath/Chapter3/Section381.lean`
  (exit 0, 3.7–3.9s warm); axiom checks via `lean_verify` (the
  earlier `#print axioms` from a separate `/tmp/*.lean` file went
  stale on the build cache — `lean_verify` against the file under
  test is the reliable path).

## Result

* **Priority 0** — **12th consecutive GPFS timeout** (EXIT=143/124,
  real 5m0.030s, user 0m0.246s, sys 0m0.456s — CPU = 0.23% of wall,
  identical near-zero pattern as cycles 182–191). No zombies. 12
  consecutive timeouts spanning ~11 calendar days. Logged as the
  cycle 192 update in
  `.prover-state/issues/cycle_182_gpfs_slowness.md`.
* **Priority 1** — **Skipped** (precondition not satisfied — GPFS
  did not recover).
* **Priority 2** — **SUCCESS**. Both lemmas remain axiom-clean
  (`[propext, Classical.choice, Quot.sound]`). The downstream
  witnesses `paddedEuler_pEquivalent_zeroReduced` and
  `paddedEuler_phiEquivalent_zeroReduced` are also axiom-clean
  (regression check passed).
* **Priority 3 (Option 3A)** — **SUCCESS**.
  `PReducesTo.trans` compiles axiom-clean
  (`[propext, Classical.choice, Quot.sound]` via `lean_verify`).
  Both `example` witnesses compile without warnings; cumulative file
  warm compile remained at 3.7s.

## Faithfulness check

Two new declarations this cycle.

**`PReducesTo.trans`** (Priority 3 — Option 3A)

* Helper-side infrastructure for the `def:381F` P-equivalence
  cluster — *not* a textbook-named entity. No
  `formalization_data/entities/<id>.json` file.
* Statement: standard transitive-closure pattern lifted to the
  heterogeneous-stage-count reduction relation. Matches the
  reflexive-transitive structure already documented at the
  `PReducesTo` inductive declaration (Section381.lean:393–422).
* Tautology check: conclusion `PReducesTo M M''` does not appear
  verbatim as any hypothesis (`h₁ : PReducesTo M M'`,
  `h₂ : PReducesTo M' M''` — distinct middle indices). **Pass.**
* Identity check: proof is `induction h₁ with` — three distinct
  cases, the recursive case re-applies the matching constructor
  with `ih h₂`. Not `exact h`. **Pass.**
* Hypothesis strength check: both hypotheses are consumed. The
  `refl` case discharges via `h₂`; the recursive cases route
  `h₂` through the IH. No extras. **Pass.**
* Definition smuggling check: not a `def` or `structure`; not
  applicable. **Pass.**

**`PEquivalent.of_isZeroReducibleVia`** (Priority 2 — refactored,
*not* a new theorem)

* The *statement* (signature) is unchanged from cycle 189; only the
  proof body now routes through `PReducesTo.of_isZeroReducibleVia`
  instead of constructing `PReducesTo.zeroStep ... PReducesTo.refl
  ...` inline.
* The earlier faithfulness audit (cycle 189) still applies.
  Statement-level checks: **Pass** (no change). The refactor is
  purely cosmetic — same axioms, same downstream behavior.

**`PReducesTo.of_isZeroReducibleVia`** (Priority 2 — reordered,
*not* a new theorem)

* Reordered to precede its consumer. Body unchanged from cycle 191
  (one-line: `PReducesTo.zeroStep inP1 hP0 h (PReducesTo.refl _)`).
* The cycle 191 faithfulness audit still applies. **Pass.**

## Dead ends

* **`#print axioms` from a standalone `/tmp/*.lean` import**:
  initially attempted to axiom-check `PReducesTo.trans` via
  `cat > /tmp/axiom_check_192b.lean << EOF ... #print axioms ... EOF;
  lake env lean /tmp/axiom_check_192b.lean`. Lean reported
  `Unknown constant OpenMath.Chapter3.Section312.RKTableau.PReducesTo.trans`
  despite the symbol resolving correctly via `lean_hover_info` at
  the definition site. The cause is stale `.olean` cache: the
  freshly-edited Section381.lean had not been re-elaborated into
  its olean when the external file's import statement looked it up.
  Resolution: use `lean_verify` against the editing file directly —
  it queries the live LSP session, not the olean cache. **Lesson
  for future cycles**: prefer `lean_verify` for axiom checks during
  edit/check loops; only fall back to `#print axioms` after `lake
  build` has refreshed the cache.

* The cycle 191 forward-reference issue (deferred from Priority 3)
  vanished entirely with this cycle's reorder. No alternative
  routing was needed.

## Discovery

* `induction h₁ with` properly generalizes the heterogeneously-
  indexed targets (`s'`, `M'`) for `PReducesTo`'s indexed inductive
  form, and the dependent hypothesis `h₂ : PReducesTo M' M''` is
  auto-reverted so it tracks the index in each case. No explicit
  `generalizing h₂` was required, contrary to what one might
  expect for an indexed family — Lean 4's `induction` tactic
  handles this cleanly.
* Placement decision for `PReducesTo.trans`: putting it after
  `PEquivalent.of_isZeroReducibleVia` (rather than between the
  Priority 2 helper/consumer pair, as a literal reading of the
  strategy might suggest) keeps the cycle-189/192 helper-consumer
  pair adjacent. The strategy's grouping rationale ("PReducesTo-
  level utilities") still holds — `PReducesTo.trans` and
  `PReducesTo.of_isZeroReducibleVia` are both in the same broader
  cluster, just with one `PEquivalent`-level corollary in between.
* `Section381.lean` warm rebuild stayed at 3.7s after adding the
  trans theorem + 2 examples (≈40 LOC net). Still well within
  budget; the file is not yet near a split-point.
* 12 consecutive Section441 timeouts is now the longest unbroken
  streak in the project's history. The cycle 188 lesson holds: do
  not invest worker cycles trying to bypass it; loop-maintainer
  territory.

## Suggested next approach

1. **Priority 0 (5 min, expected to fail for 13th time)**: GPFS
   smoke test on Section441. If GPFS recovers, ship Phase C.2 per
   the cycle 182 draft + cycle 184 namespace fix.
2. **Priority 2 (~30–60 min, def:381F follow-up)**: ship Option
   3B from the cycle 192 strategy —
   `PEquivalent.eq_of_both_isIrreducible`. Statement: if
   `PEquivalent M M'` and *both* `M` and `M'` are irreducible,
   then `s' = s ∧ HEq M' M` (heterogeneous-stage equality).
   This is the natural dual to cycle 190's
   `PEquivalent.eq_of_isIrreducible_of_middle` and closes a piece
   of the def:381F canonical-form story. Proof: unpack the common
   reduct, apply `eq_of_isIrreducible_of_pReducesTo` twice (once
   per side). Now that `PReducesTo.trans` exists (cycle 192),
   variant proofs that chain reductions are also available if the
   straightforward path stalls.
3. **Priority 3 (stretch)**: Φ-equivalent lifting of
   `PReducesTo.trans` is *already* implicit in
   `PhiEquivalent.trans`'s existence as a transitive closure
   wrapper — no new theorem needed. A cleaner Priority 3 candidate
   would be a `PReducesTo.toPhiEquivalent` direct corollary
   (currently the path is `PEquivalent.of_pReducesTo` then
   `PEquivalent.toPhiEquivalent`; collapsing the two saves
   ergonomics for downstream consumers). ~10 LOC, trivial proof.
4. **Do NOT pivot to a fresh entity** while §441 is GPFS-blocked.
   The def:381F cluster still has 2–3 mechanical follow-ups before
   it's at a natural pause point.
5. **Do NOT touch `scripts/autonomous_loop.py`** — loop-maintainer
   territory.
