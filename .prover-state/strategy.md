# Cycle 195 Strategy

## Context

Cycle 194 confirmed the 14th consecutive GPFS-blocked smoke test on
`OpenMath/Chapter4/Section441.lean` (Phase C.2 of `lem:441A` remains
draft-only at `.prover-state/cycle_182_draft_section441.lean` with
the cycle-184 namespace fix on line 1529). Section381 continued to
compile healthily; cycle 194 shipped three new axiom-clean theorems
(`PEquivalent.pReducesTo_of_left_isIrreducible`,
`PEquivalent.pReducesTo_of_right_isIrreducible`,
`PEquivalent.eq_of_both_isIrreducible_homogeneous`) plus two
non-vacuity `example` witnesses. Sorry count remains 0.

The cycle 194 task results §"Suggested next approach" §2 explicitly
names the cycle-195 target: a stage-count descent lemma for
`PReducesTo` that opens the path to def:381E `reducedMethod`.

## Priority 0 — MANDATORY: Section441 GPFS smoke test (15th attempt)

This must run FIRST. It is one-shot only (no retries, no longer
timeout) and the decision tree is binary:

```bash
ps -u "$USER" -o pid,stat,wchan,etime,comm | grep -E "^[ ]*[0-9]+ +D"
time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean
```

- **Branch A (expected, GPFS still degraded)**: `EXIT=124` (or 143),
  wall ≈ 300s, CPU < 1%. Log the 15th timeout in
  `.prover-state/issues/cycle_182_gpfs_slowness.md` under a new
  "Cycle 195 update (15th timeout)" section, then proceed to
  Priority 1.
- **Branch B (GPFS recovered)**: exit 0 in < 5 min. Apply the cycle
  184 namespace fix (line 1529:
  `M.αPoly_complex_root_norm_ge_one_of_stable …`
  →
  `LinearMultistepMethod.αPoly_complex_root_norm_ge_one_of_stable M …`)
  to the cycle 182 draft preserved at
  `.prover-state/cycle_182_draft_section441.lean`, then replace
  `OpenMath/Chapter4/Section441.lean` with the fixed draft and ship
  Phase C.2 of `lem:441A`. If Branch B fires, skip Priorities 1 and
  2 entirely — Phase C.2 is the much higher-value deliverable.

**Do NOT** spend more than the budgeted 5 min on this. Branch A has
fired 14 times in a row; expect it again.

## Priority 1 (substantive, Branch A path) — `PReducesTo` stage-count descent

### Goal

Ship the stage-count-descent infrastructure for `PReducesTo` in
`OpenMath/Chapter3/Section381.lean`. The cycle 194 results §2
identified this as a "small, single-cycle deliverable" that is a
genuine stepping stone toward the still-deferred def:381E
`reducedMethod` construction (see
`.prover-state/issues/reduced_method_deferred.md`).

### What to ship — three theorems, axiom-clean, in `OpenMath.Chapter3.Section312.RKTableau` namespace

Place them immediately after cycle 194's
`PEquivalent.eq_of_both_isIrreducible_homogeneous`
(`OpenMath/Chapter3/Section381.lean:619` area, before the
`end OpenMath.Chapter3.Section312.RKTableau` at line 691).

#### 1. `PReducesTo.size_le`

```lean
/-- Stage-count monotonicity: every P-reduction sequence is
non-increasing on the underlying stage-count parameter. The reflexive
case preserves it; the `step` and `zeroStep` cases strictly decrease
it (see `PReducesTo.size_lt_of_step` and `_of_zeroStep`). -/
theorem PReducesTo.size_le {s s' : ℕ}
    {M : RKTableau s} {M' : RKTableau s'}
    (h : PReducesTo M M') : s' ≤ s
```

**Proof shape**: `induction h with` over the three constructors.

* `refl _` ⇒ `Nat.le.refl` (or `le_refl s`).
* `step P hLt _h hRest ih` ⇒ `hLt : sBar < s` and `ih : s'' ≤ sBar`,
  combine via `le_trans ih (Nat.le_of_lt hLt)`.
* `zeroStep inP1 hP0 _h hRest ih` ⇒ need to show
  `(Finset.univ.filter (fun i : Fin s => inP1 i = true)).card < s`
  from `hP0 : ∃ i, inP1 i = false`, then chain
  `le_trans ih (Nat.le_of_lt ‹|P₁| < s›)`. The "filter card strictly
  less than universe card" fact may exist as a named Mathlib lemma —
  verify with `lean_local_search "Finset.card_filter"` /
  `lean_loogle "Finset.filter ?p ?s |>.card < ?s.card"` before
  committing. Likely candidate names: `Finset.card_filter_lt`,
  `Finset.card_lt_univ_iff_ne_univ`. If no direct lemma exists,
  build the inequality inline as a `have`:

  ```lean
  have h_partition :
      (Finset.univ.filter (fun i : Fin s => inP1 i = true)).card +
        (Finset.univ.filter (fun i : Fin s => inP1 i = false)).card =
        s := by
    rw [Finset.filter_card_add_filter_neg_card_eq_card]
    -- needs the predicate to be decidable; (· = true) is
    simp
  have h_neg_pos :
      0 < (Finset.univ.filter (fun i : Fin s => inP1 i = false)).card := by
    obtain ⟨i, hi⟩ := hP0
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  omega
  ```

  Verify the exact name `Finset.filter_card_add_filter_neg_card_eq_card`
  with `lean_local_search` before committing — Mathlib's
  partition-by-predicate lemma may be named differently (e.g.
  `Finset.filter_card_add_filter_neg_card`).

#### 2. `PReducesTo.size_lt_of_step`

```lean
/-- A single non-trivial P-reduction step (`step` constructor) strictly
decreases the stage count. Direct consequence of the constructor's
`sBar < s` hypothesis composed with `size_le` on the continuation. -/
theorem PReducesTo.size_lt_of_step {s sBar s'' : ℕ}
    {M : RKTableau s} {M'' : RKTableau s''}
    (P : PPartition s sBar) (hLt : sBar < s)
    (hRed : M.IsPReducibleVia P)
    (hRest : PReducesTo (M.pReduced P) M'') :
    s'' < s
```

**Proof**: `lt_of_le_of_lt hRest.size_le hLt`. One liner.

#### 3. `PReducesTo.size_lt_of_zeroStep`

```lean
/-- A single 0-reduction step (`zeroStep` constructor) strictly
decreases the stage count, because `hP0 : ∃ i, inP1 i = false` forces
`|P₁| < s`. -/
theorem PReducesTo.size_lt_of_zeroStep {s s'' : ℕ}
    {M : RKTableau s} {M'' : RKTableau s''}
    (inP1 : Fin s → Bool) (hP0 : ∃ i, inP1 i = false)
    (h : M.IsZeroReducibleVia inP1)
    (hRest : PReducesTo (M.zeroReduced inP1) M'') :
    s'' < s
```

**Proof**: extract `|P₁| < s` from `hP0` (use the same Finset
argument as in `size_le`'s `zeroStep` case; factor into a `have`
shared between the two if convenient — or expose as a separate
`private` lemma `card_filter_true_lt_of_exists_false` first).
Then `lt_of_le_of_lt hRest.size_le ‹|P₁| < s›`.

### Verification

After each Edit, run:

1. `time lake env lean OpenMath/Chapter3/Section381.lean` → expect
   `EXIT=0`. Cold compile took 1m22s in cycle 194; the warm rebuild
   should be faster but the new edits will invalidate the cached
   `.olean`.
2. `grep -c "^[^/-]*\bsorry\b" OpenMath/Chapter3/Section381.lean`
   → must print `0`.
3. `lean_verify
   OpenMath.Chapter3.Section312.RKTableau.PReducesTo.size_le` (and
   the two `size_lt_of_*` siblings) → each must return
   `[propext, Classical.choice, Quot.sound]`. Use `lean_verify` (the
   MCP tool), NOT `#print axioms` against a fresh `lake env lean
   --stdin` snippet — the latter pattern hits the stale-`.olean`
   trap.

### What NOT to try (failed in prior cycles)

* **Do NOT** attempt the full def:381E `reducedMethod` construction
  this cycle. It requires a well-foundedness instance plus
  `Classical.choose` destructors on `IsPReducible`/`IsZeroReducible`
  exposing the partition witnesses, which is multi-cycle scope per
  `.prover-state/issues/reduced_method_deferred.md`. The Priority 1
  deliverables (`size_le` + the two strict-descent lemmas) are
  *prerequisites* for that work but stop short of the construction
  itself.
* **Do NOT** state `PReducesTo` well-foundedness as a single
  `WellFoundedRelation` instance. The relation is heterogeneous in
  the stage-count type, so a `WellFoundedRelation` instance requires
  packaging into `Σ s, RKTableau s` first — that packaging is itself
  multi-cycle Lean-engineering work.
* **Do NOT** reuse the cycle 193/194 templates for
  `eq_of_isIrreducible_of_pReducesTo` composition — that's a
  different lemma family (irreducibility, not stage-count descent).
* **Do NOT** raise `maxHeartbeats`. The three theorems should each
  close in ≤ 200000 with simple induction.
* **Do NOT** edit `scripts/autonomous_loop.py` even if the
  supervisor flags this cycle's commit as "not reaching repo".
  Follow `.prover-state/issues/phantom_commit_verdict_pattern.md` —
  verify with `git show --stat <sha> -- OpenMath/Chapter3/Section381.lean`
  and log a confirmation row in `attempts.md` if a false positive
  fires.

## Priority 2 (stretch, only if Priority 1 closes early) — promote cycle 194 examples

`OpenMath/Chapter3/Section381.lean:1368` is currently an `example`
recovering `paddedEuler.PReducesTo (paddedEuler.pReduced pairPartition)`
via cycle 194's `pReducesTo_of_right_isIrreducible`. Promote to:

```lean
theorem paddedEuler_pReducesTo_pReduced_via_isIrreducible :
    paddedEuler.PReducesTo (paddedEuler.pReduced pairPartition) :=
  paddedEuler_pEquivalent_pReduced.pReducesTo_of_right_isIrreducible
    paddedEuler_pReduced_pairPartition_isIrreducible
```

so downstream test files can reference it. Keep the existing
docstring (it already explains the cycle 194 context). Verify
axiom-clean.

Optionally also promote the `example` at line 1379 (the homogeneous
HEq → Eq trivial case via reflexivity) and line 1351 (the
heterogeneous-stage trivial case) under similar names
(e.g. `paddedEuler_pReduced_pairPartition_eq_self_via_isIrreducible`).

Skip Priority 2 entirely if Priority 1 consumed the cycle budget —
it is cosmetic, not load-bearing.

## Post-cycle bookkeeping

1. Update `OpenMath/Chapter3/Section381.lean` namespace block.
2. Update `extraction/formalization_data/lean_status.json` — the
   `def:381F` row's `last_cycle` to 195 (this is the only row
   carrying that field; do not retrofit others).
3. Update `plan.md` Chapter 3 `def:381F` row's narrative paragraph
   with a "Cycle 195: shipped …" sentence following the existing
   cycle-by-cycle bullet format.
4. Write `.prover-state/task_results/cycle_195.md` per CLAUDE.md
   template.
5. Commit + push. Verify with `git log -1 --format='%H %s'` +
   `git rev-parse origin/butcher-experiments`.

## Why this is the right cycle target

The §441 line is paralyzed by GPFS (14-cycle pathology, loop-
maintainer territory). The §380 P-reducibility line continues to
ship 2-3 axiom-clean theorems per cycle. The descent-on-stage-count
lemmas are exactly the structural infrastructure required before the
def:381E `reducedMethod` construction can land, and they are
single-cycle scoped (3 lemmas, ≤ 60 LOC, no new imports, no new
definitions, no faithfulness divergence).

Compare to the multi-cycle alternative (the full `reducedMethod` via
`WellFoundedRelation` on a Σ-typed wrapper) which would require:
(a) defining the Σ-wrapper structure, (b) lifting `PReducesTo` to
the wrapper, (c) discharging the `WellFoundedRelation` instance,
(d) using `Classical.choose` destructors on the existential
predicates to extract partition witnesses, (e) proving the
fixed-point equation. That sequence is at minimum 3-4 cycles of
work, suitable only as a long-form plan once §441 unblocks.

The cycle 195 deliverable is the smallest forward step that
genuinely advances the def:381E roadmap; it ships in one cycle and
opens the door to all subsequent reducedMethod work.
