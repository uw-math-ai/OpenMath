# Cycle 208 Strategy

## Headline

Ship **`PEquivalent.toEquivalent`** — the natural corollary of cycle 207's
`PReducesTo.toEquivalent`, completing the def:381F → def:381A direction of
`thm:381H`. Bundle with two `paddedEuler` non-vacuity witnesses exercising the
new theorem through both `step` and `zeroStep` paths. Low-risk, ~15–25 LOC
total, sorry count stays at 0.

## Context snapshot

- Sorry count: **0** across the repo. Maintain this; do NOT introduce sorries.
- Last cycle (207) shipped `pReduced_equivalent`, `zeroReduced_equivalent`,
  and `PReducesTo.toEquivalent` axiom-clean. Source location:
  `OpenMath/Chapter3/Section381.lean:2121`.
- §441 Phase C.2 still GPFS-blocked (27th consecutive). **Skip; do NOT run
  smoke tests on `Section441.lean`.** See §A below.
- Cycle 200 attempted a `thm:381H` statement-only scaffold with 3 sorries
  and was rolled back in cycle 201 (supervisor policy: "sorry increase is
  bad"). With cycle 208's deliverable, only 2 of 4 iff directions remain
  blocked (both gated by `thm:381G`), so a scaffold would still introduce 2
  sorries. **Do NOT re-attempt `thm:381H` scaffold this cycle.**

## §A — §441 Phase C.2: SKIP

Do NOT run `lake env lean OpenMath/Chapter4/Section441.lean` or any
Section441 smoke test this cycle. 27 consecutive cycles (182–207) have
timed out at 5 min with near-zero CPU; the pathology is GPFS olean loading,
not a worker-resolvable issue. Per
`.prover-state/issues/cycle_182_gpfs_slowness.md` and
`.prover-state/issues/phantom_commit_verdict_pattern.md`, this is
loop-maintainer territory. The cycle-182 draft + cycle-184 namespace fix
remain preserved at `.prover-state/cycle_182_draft_section441.lean`.

Record the 28th-consecutive-skip in the cycle 208 task results under
"Dead ends" with a one-line citation; do not spend cycle budget verifying.

## §B — Priority 1 (PRIMARY): `PEquivalent.toEquivalent`

### Goal

Add the following theorem to `OpenMath/Chapter3/Section381.lean`,
immediately after `PReducesTo.toEquivalent` (currently at line 2121,
inside the `namespace OpenMath.Chapter3.Section312.RKTableau` block that
closes at line 2132):

```lean
/-- *§380 def:381F → def:381A bridge.* Every P-equivalent pair is
`def:381A`-equivalent. Composes cycle 207's `PReducesTo.toEquivalent` on
both legs of `PEquivalent`'s existential common reduct, then closes via
`Equivalent.trans` + `Equivalent.symm` (cycles 204, 206).

This is the second of four directions of `thm:381H`
(def:381F ↔ def:381A ↔ def:381B). The other closed direction is
`PEquivalent.toPhiEquivalent` (cycle 187); the remaining two
(`Equivalent → PEquivalent` and `PhiEquivalent → PEquivalent`) are
blocked on `thm:381G` per `.prover-state/issues/thm_381H_deferred.md`. -/
theorem PEquivalent.toEquivalent.{u}
    {s s' : ℕ} {M : RKTableau s} {M' : RKTableau s'}
    (h : PEquivalent M M') :
    @Equivalent.{u} s s' M M' := by
  obtain ⟨_, _, hM, hM'⟩ := h
  exact Equivalent.trans hM.toEquivalent hM'.toEquivalent.symm
```

### Why this works

- `PEquivalent M M'` unfolds to `∃ sBar Mbar, PReducesTo M Mbar ∧
  PReducesTo M' Mbar` (`Section381.lean:429–431`).
- `hM.toEquivalent : Equivalent M Mbar` via cycle 207
  (`PReducesTo.toEquivalent`, line 2121).
- `hM'.toEquivalent : Equivalent M' Mbar` via the same cycle 207 theorem.
- `hM'.toEquivalent.symm : Equivalent Mbar M'` via cycle 204
  (`Equivalent.symm`, line 1828).
- `Equivalent.trans hM.toEquivalent hM'.toEquivalent.symm
  : Equivalent M M'` via cycle 206 (`Equivalent.trans`, line 1863).

### Universe annotation

Cycle 204 discovered that `Equivalent.{u}` is universe-polymorphic and
`symm` / `trans` require explicit shared `.{u}` annotations to constrain
universes across multiple `Equivalent` references in the signature. Apply
the same discipline here: theorem is `.{u}`-annotated, the conclusion uses
`@Equivalent.{u}` to bind the universe parameter explicitly.

### Risks / fallbacks

- If `hM'.toEquivalent.symm` does not elaborate cleanly (universe issue
  on `.symm` dot-notation), fall back to an explicit application:
  ```lean
  exact Equivalent.trans hM.toEquivalent
    (Equivalent.symm hM'.toEquivalent)
  ```
- If even that fails on universe inference, expand to a full tactic body:
  ```lean
  intro N _ _ _ f L hL y₀
  obtain ⟨_, _, hM, hM'⟩ := h
  exact Equivalent.trans hM.toEquivalent
    (Equivalent.symm hM'.toEquivalent) f L hL y₀
  ```
- Expected LOC: 5–10 lines including the docstring. Should compile within
  Section381's warm-rebuild budget (~5–10s).

## §C — Priority 2 (STRETCH 1): paddedEuler non-vacuity witnesses

After the `PEquivalent.toEquivalent` theorem lands, add these two
witnesses inside the existing `namespace OpenMath.Chapter3.Section381`
block, immediately after `paddedEuler_equivalent_self` (around line 2241):

```lean
/-- *Non-vacuity witness for `PReducesTo.toEquivalent` (cycle 207)
exercising the `step` constructor.* `paddedEuler` is
`def:381A`-equivalent to its 1-stage P-reduction via cycle 207's
`PReducesTo.toEquivalent` applied to the heterogeneous-stage (2 ↦ 1)
P-reduction. Composition route: `paddedEuler_pReducesTo_pReduced`
(cycle 186) → `.toEquivalent`. -/
theorem paddedEuler_equivalent_pReduced :
    paddedEuler.Equivalent (paddedEuler.pReduced pairPartition) :=
  paddedEuler_pReducesTo_pReduced.toEquivalent

/-- *Non-vacuity witness for `PReducesTo.toEquivalent` (cycle 207)
exercising the `zeroStep` constructor.* `paddedEuler` is
`def:381A`-equivalent to its 1-stage 0-reduced form via cycle 207's
`PReducesTo.toEquivalent` applied to the 0-reduction. Composition
route: `paddedEuler_pReducesTo_zeroReduced` (cycle 188) → `.toEquivalent`. -/
theorem paddedEuler_equivalent_zeroReduced :
    paddedEuler.Equivalent (paddedEuler.zeroReduced ![true, false]) :=
  paddedEuler_pReducesTo_zeroReduced.toEquivalent
```

These are one-line bodies each (plus docstring). They confirm cycle 207's
`PReducesTo.toEquivalent` fires non-vacuously on both the `step` and
`zeroStep` constructor paths — not just the trivial `refl` case. Cycle
207's task results explicitly identified these as the next-cycle
exercise (suggestion §3).

### Use the `RKTableau` namespace

Both `paddedEuler_pReducesTo_pReduced` and
`paddedEuler_pReducesTo_zeroReduced` are declared inside
`namespace OpenMath.Chapter3.Section312.RKTableau` (around lines 1022 and
1071). The `.toEquivalent` dot-notation works because
`PReducesTo.toEquivalent` lives in the same namespace. If the witness
declarations need to live in the outer `Section381` namespace (per the
existing pattern around `paddedEuler_equivalent_self`), you may need
either an explicit `open OpenMath.Chapter3.Section312` block or a fully
qualified `RKTableau.PReducesTo.toEquivalent` reference. Mirror the
existing `paddedEuler_equivalent_self` style (line 2241) verbatim.

## §D — Priority 3 (STRETCH 2): umbrella corollary

If §B and §C both compile cleanly with budget remaining, add the packaged
two-directions corollary, immediately after `PEquivalent.toEquivalent`:

```lean
/-- *§380: the two closed directions of `thm:381H` bundled.* Every
P-equivalent pair is simultaneously `def:381A`-equivalent and
`def:381B`-equivalent. Combines `PEquivalent.toEquivalent` (cycle 208,
this file) with `PEquivalent.toPhiEquivalent` (cycle 187). The two
remaining iff directions (`def:381A → def:381F` and
`def:381B → def:381F`) are blocked on `thm:381G` per
`.prover-state/issues/thm_381H_deferred.md`. -/
theorem PEquivalent.toEquivalent_and_toPhiEquivalent.{u}
    {s s' : ℕ} {M : RKTableau s} {M' : RKTableau s'}
    (h : PEquivalent M M') :
    @Equivalent.{u} s s' M M' ∧ PhiEquivalent M M' :=
  ⟨h.toEquivalent, h.toPhiEquivalent⟩
```

Pure ergonomics convenience. If this does not compile due to a universe
mismatch between the two conjunction parts, drop it without retry —
it adds no substantive content beyond the two underlying theorems.

## §E — What NOT to try

1. **Do NOT attempt a `thm:381H` statement-only scaffold.** Even after
   cycle 208's new bridge lands, 2 of 4 iff directions remain blocked on
   `thm:381G`. A scaffold would introduce 2 sorries (count 0 → 2),
   regressing the invariant. Cycle 200 attempted this and was rolled
   back in cycle 201. Defer until `thm:381G` is closeable.

2. **Do NOT touch `Section441.lean` or run §441 smoke tests.** 27
   consecutive GPFS timeouts. Loop-maintainer territory. See §A above.

3. **Do NOT submit Aristotle jobs for `PEquivalent.toEquivalent`.** It is
   a 5–10 line proof composing existing theorems. Manual proof is
   strictly faster than Aristotle's polling overhead.

4. **Do NOT rewrite `Equivalent`, `PEquivalent`, or any cycle 203–207
   theorem.** All axiom-clean and load-bearing for §B's proof.

5. **Do NOT attempt full `Equivalent.trans` without an
   irreducible-middle hypothesis via a confluence argument.** That
   requires Newman's lemma for `PReducesTo`, which is 4–5 cycles of
   infrastructure per
   `.prover-state/issues/p_reduction_confluence_gap.md`. Not in scope.

6. **Do NOT introduce `axiom` or `constant` declarations.** CLAUDE.md
   absolute rule.

7. **Do NOT raise `maxHeartbeats`.** All target theorems are short
   compositions; default limits are ample.

8. **Do NOT chase the cycle 207 suggestion of opening `def:382A` /
   `thm:382A` (§382 composition group) this cycle.** New entity, new
   cluster, separate cycle of planning required. Save for cycle 209+.

## §F — Verification protocol

After landing P1 (and stretches P2, P3 if shipped):

1. `lake env lean OpenMath/Chapter3/Section381.lean` — must exit 0.
2. `grep -c sorry OpenMath/Chapter3/Section381.lean` — must return 0.
3. `lean_verify
   OpenMath.Chapter3.Section312.RKTableau.PEquivalent.toEquivalent`
   — must return `[propext, Classical.choice, Quot.sound]` only.
4. For each stretch theorem shipped: same `lean_verify` axiom check.
5. Regression check on cycle 207 theorems
   (`pReduced_equivalent`, `zeroReduced_equivalent`,
   `PReducesTo.toEquivalent`) via `lean_verify` — should still be
   axiom-clean.

## §G — Faithfulness check

For `PEquivalent.toEquivalent`:
- Entity: implicit consequence of `thm:381H` (Butcher §380, p. 304):
  *"Two methods M, M' are def:381A-equivalent iff they are
  def:381F-equivalent iff they are def:381B-equivalent."*
- The new theorem captures the def:381F → def:381A direction exactly
  via the diamond `M → Mbar ← M'` of P-reductions composed through
  `Equivalent`'s equivalence-relation structure (refl/symm/trans
  shipped in cycles 203/204/206).
- Hypothesis strength: no extras. Only `PEquivalent M M'` is required.

For the paddedEuler witnesses: same mathematical content as the
underlying `paddedEuler_pReducesTo_*` theorems lifted through cycle
207's bridge.

## §H — Documentation hygiene

After landing the deliverables, update:

1. `extraction/formalization_data/lean_status.json` — `thm:381H` row
   stays `unformalized` (still 2 of 4 directions deferred); add a note
   in the entity row referencing cycles 187 + 207 + 208 for the closed
   directions.

2. `plan.md` — `thm:381H` row stays `[ ]`. No change.

3. `.prover-state/issues/thm_381H_deferred.md` — add a "Cycle 208
   update" subsection noting that the `PEquivalent → Equivalent`
   direction is now closed via `PEquivalent.toEquivalent`, leaving 2
   blocked directions (both gated on `thm:381G`).

4. `.prover-state/task_results/cycle_208.md` — standard template;
   record the 28th-consecutive §441 skip in "Dead ends".

## §I — Expected outcome

- 1 axiom-clean theorem (`PEquivalent.toEquivalent`, ~10 LOC including
  docstring).
- 2 axiom-clean non-vacuity witnesses
  (`paddedEuler_equivalent_pReduced`,
  `paddedEuler_equivalent_zeroReduced`, ~6 LOC each).
- 0–1 axiom-clean stretch corollary
  (`PEquivalent.toEquivalent_and_toPhiEquivalent`, ~5 LOC).
- Sorry count: 0 → 0.
- File growth: Section381.lean ~+25–35 LOC.
- Warm rebuild: <10s.
- Cycle 207 regression check: clean.
- 28th-consecutive §441 GPFS skip recorded.
