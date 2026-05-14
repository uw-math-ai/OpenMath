# Cycle 191 Results

## Worked on

* Priority 0 — GPFS smoke test on `OpenMath/Chapter4/Section441.lean`
  (Phase C.2 of `lem:441A`).
* Priority 2 — Shipped
  `OpenMath.Chapter3.Section312.RKTableau.PReducesTo.of_isZeroReducibleVia`
  in `OpenMath/Chapter3/Section381.lean` (the `PReducesTo`-level analog
  of the existing `PEquivalent.of_isZeroReducibleVia`).
* Priority 3 — Attempted the optional cosmetic refactor of
  `PEquivalent.of_isZeroReducibleVia` to consume the new helper.
  Reverted due to forward-reference issue (see Dead ends below).

## Approach

* Priority 0: Followed the strategy verbatim — pre-flight zombie
  check (`ps -u $USER -o pid,stat,wchan,etime,comm`), then
  `time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean`.
* Priority 2: Inserted the new theorem immediately after
  `eq_of_isIrreducible_of_pReducesTo` (Section381.lean:476) and
  before `PEquivalent.trans_of_middle_isIrreducible`, exactly as
  the strategy specified. Body is the corrected stretch sketch
  from cycle 190's Discovery section:
  `PReducesTo.zeroStep inP1 hP0 h (PReducesTo.refl _)`.
* Verification: `lake env lean OpenMath/Chapter3/Section381.lean`
  (exit 0, 53.9s cold, 3.7s warm), `lean_verify` axiom check.

## Result

* Priority 0 — **11th consecutive GPFS timeout** (EXIT=124, real
  5m0.047s, user 0m1.002s, sys 0m2.387s — CPU = 0.68% of wall).
  No zombies. Pattern entrenched. Logged as the cycle 191 update
  in `.prover-state/issues/cycle_182_gpfs_slowness.md`.
* Priority 1 — **Skipped** (precondition not satisfied — GPFS
  did not recover).
* Priority 2 — **SUCCESS**. Theorem compiles axiom-clean
  (`[propext, Classical.choice, Quot.sound]` only).
  `grep -c sorry OpenMath/Chapter3/Section381.lean` = 0.
* Priority 3 — **Reverted**. The refactor would have replaced the
  body of `PEquivalent.of_isZeroReducibleVia` (line 451) with
  `PEquivalent.of_pReducesTo (PReducesTo.of_isZeroReducibleVia M hP0 h)`,
  but the new helper is placed (per the strategy's grouping rule)
  *after* `PEquivalent.of_isZeroReducibleVia` in source order.
  Lean rejected the forward reference with
  `unknownIdentifier OpenMath.Chapter3.Section312.RKTableau.PReducesTo.of_isZeroReducibleVia`.
  Per the strategy's explicit "skip Priority 3 entirely" clause
  for any risk of breakage, reverted. Cycle 192 can pick this up
  if it also reorders the two lemmas.

## Faithfulness check

Single new theorem this cycle:
**`PReducesTo.of_isZeroReducibleVia`**.

* This is helper-side infrastructure for the `def:381F`
  P-equivalence cluster — *not* a textbook-named entity. It does
  not have a `formalization_data/entities/<id>.json` file. It
  mirrors the existing `PEquivalent.of_isZeroReducibleVia`
  (cycle 189, Section381.lean:451) at the `PReducesTo` level.
* Tautology check: conclusion `PReducesTo M (M.zeroReduced inP1)`
  does not appear verbatim as any hypothesis. **Pass.**
* Identity check: body is not `exact h`. It is a one-step
  application of the `zeroStep` constructor with a recursive
  `refl` argument as the continuation. **Pass.**
* Hypothesis strength check: both `hP0` and `h` are consumed by
  the `zeroStep` constructor. No extras. **Pass.**
* Definition smuggling check: not a `def` or `structure`; not
  applicable. **Pass.**

## Dead ends

* **Priority 3 forward-reference**: the strategy correctly noted
  that the refactor's only risk was breaking downstream
  witnesses; I expected those to be the failure mode. In
  practice the failure was much more local — the source-order
  placement directly. Lesson for cycle 192: if Priority 3 is
  attempted, either (a) move `PReducesTo.of_isZeroReducibleVia`
  to just before `PEquivalent.of_isZeroReducibleVia` (line ~450),
  or (b) accept a small docstring grouping deviation. Option (a)
  is the cleaner refactor since the strategy's stated grouping
  rationale ("group `PReducesTo`-level helpers together") still
  holds once `PEquivalent.of_isZeroReducibleVia` is also
  considered part of that group — both define a one-step
  P-reduction-to-0-reduction shape; only the wrapping codomain
  differs.

## Discovery

* 53.9s cold compile for `Section381.lean` after adding the new
  theorem; 3.7s warm. Both well within budget. The file remains
  in the "fast cold build" regime — no need to split it yet.
* `PReducesTo.refl _` (with an underscore) elaborates correctly
  even though the immediate goal is
  `PReducesTo (M.zeroReduced inP1) (M.zeroReduced inP1)`. The
  unifier picks up the argument from the goal's index, so the
  more verbose `PReducesTo.refl (M.zeroReduced inP1)` (as used
  in the existing `PEquivalent.of_isZeroReducibleVia` at line
  457) is not required. This is a small style improvement
  available for cycle 192's optional Priority 3 cleanup.
* The "11th consecutive timeout" data point is qualitatively the
  same as cycles 182–190: ~5m wall, ~1s user, no zombies. The
  GPFS regression is well past the threshold where worker-side
  debugging makes sense; loop-maintainer territory per CLAUDE.md.

## Suggested next approach

1. **Priority 0 (5 min, default expected to fail again)**: GPFS
   smoke test on Section441. If GPFS recovers, ship Phase C.2
   per the cycle 182 draft + cycle 184 namespace fix.
2. **Priority 2 (small, mechanical, ~5 min)**: do the Priority 3
   refactor cycle 191 deferred — but reorder
   `PReducesTo.of_isZeroReducibleVia` to *before*
   `PEquivalent.of_isZeroReducibleVia` (move from current
   ~line 478 to just before line 451). Then update the body of
   `PEquivalent.of_isZeroReducibleVia` to
   `PEquivalent.of_pReducesTo (PReducesTo.of_isZeroReducibleVia M hP0 h)`.
   Re-verify both theorems remain axiom-clean.
3. **Priority 3 (stretch, only if 1+2 close fast)**: explore the
   next def:381F follow-up. Candidates per the cycle 190 plan
   audit: (a) a `PReducesTo.trans` chaining lemma for composing
   multi-step reductions; (b) a Φ-equivalent lifting of
   `eq_of_isIrreducible_of_pReducesTo` to PEquivalent
   (i.e. eq_of_both_irreducible_of_PEquivalent — currently
   only the canonical-form constructor exists). Both are 1–2
   cycles of mechanical work each.
4. **Do NOT pivot to a fresh entity**. The def:381F cluster is
   one or two cosmetic deliverables short of a natural pause
   point. Finish it cleanly before opening a new front while
   §441 remains GPFS-blocked.
5. **Do NOT touch `scripts/autonomous_loop.py`**. Loop-maintainer
   territory.
