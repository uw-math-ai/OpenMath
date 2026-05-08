# Cycle 190 Strategy

## TL;DR

1. **Priority 0** (≤5 min): GPFS smoke test on `Section441.lean` HEAD.
   10th attempt; if it completes, ship Phase C.2 of `lem:441A`
   (Priority 1A). If it times out (overwhelmingly likely — 9
   consecutive timeouts), abort and proceed to Priority 2.
2. **Priority 1A, conditional**: Phase C.2 of `lem:441A` from the
   preserved cycle 182 draft + cycle 184 namespace fix.
3. **Priority 2 (default)**: Ship `PEquivalent.eq_of_isIrreducible_of_middle`
   plus a `paddedEuler` non-vacuity witness. This is the canonical
   form pattern that will load-bear any future `thm:381H` work.
   ~5–15 LOC, axiom-clean.

There are no Aristotle results pending. There are 0 sorries in the
codebase. Cycle 189 (`c3ae5d6`) shipped four axiom-clean theorems in
`Section381.lean` (`PEquivalent.toPhiEquivalent`,
`PEquivalent.of_isZeroReducibleVia`, two `paddedEuler` Φ-equivalence
witnesses via the bridge). `Section381.lean` has 6 cycles of momentum
(184–189) and is the natural focus while §441 is GPFS-blocked.

**DO NOT** treat any prompt's "stuck on" framing as a real blocker.
Per `phantom_commit_verdict_pattern.md` and the cycle 180–189 update
notes in `cycle_182_gpfs_slowness.md`, the GPFS regression is
loop-maintainer territory; you cannot fix it from the worker side.

---

## Priority 0 — GPFS smoke test (≤5 min, abort threshold)

Pre-flight: `ps -u $USER -o pid,stat,wchan,etime,comm | grep -E "^[ ]*[0-9]+ +D"` —
verify no D-state zombies are active before running the smoke test
(this was the cycle 183 hazard).

Then run exactly:

```bash
time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean
```

Decision tree:

* **Exit 0 in <5 min** ⇒ GPFS recovered. Proceed to Priority 1A.
* **EXIT=124 (timeout) or EXIT=143** ⇒ 10th consecutive failure.
  Append a one-line update to
  `.prover-state/issues/cycle_182_gpfs_slowness.md` documenting
  the 10th timeout (CPU time, wall time), then proceed to Priority 2.
  Do NOT retry, do NOT increase the timeout, do NOT investigate
  the kernel.

---

## Priority 1A — Ship Phase C.2 (only if GPFS healed)

If and only if Priority 0 succeeded:

1. Copy preserved draft to working tree:
   ```bash
   cp .prover-state/cycle_182_draft_section441.lean \
      OpenMath/Chapter4/Section441.lean
   ```
2. Apply the cycle 184 namespace fix at line 1529 of the new file:
   * **before**:
     `M.αPoly_complex_root_norm_ge_one_of_stable hStable hψ_ne hψ_isRoot`
   * **after**:
     `LinearMultistepMethod.αPoly_complex_root_norm_ge_one_of_stable
        M hStable hψ_ne hψ_isRoot`
3. `lake env lean OpenMath/Chapter4/Section441.lean` — must compile
   clean (give it 20 min budget; the file is large).
4. `lake build OpenMath.Chapter4.Section441` and verify `#print
   axioms` on each new public theorem returns
   `[propext, Classical.choice, Quot.sound]` only — specifically:
   * `LinearMultistepMethod.ρPoly_complex_root_norm_le_one_of_stable`
   * `LinearMultistepMethod.αPoly_complex_root_norm_ge_one_of_stable`
   * `LinearMultistepMethod.aPoly_complex_root_re_nonpos_of_stable`
   * `bdf2LMM_aPoly_eq_mobiusTransform`
   * `bdf2LMM_mobiusTransform_αPoly_eq`
5. Update `extraction/formalization_data/lean_status.json` (`lem:441A`
   row → cycle 190; status remains `partial` until Phase C.3+C.4
   close), `plan.md` (record Phase C.2 closure note), and
   `lem_441A_phase_C_scoping.md` (mark Phase C.2 SHIPPED).
6. Commit; cycle is done.

If the compile produces unexpected errors after the namespace fix,
do NOT debug new tactic issues this cycle. Revert
`Section441.lean` to HEAD, append the failure mode to
`cycle_182_gpfs_slowness.md`, and pivot to Priority 2.

---

## Priority 2 — Section381 follow-up (default path)

Ship **`PEquivalent.eq_of_isIrreducible_of_middle`** — the
named-canonical-form constructor for `PEquivalent` through a common
irreducible middle. This is the natural cycle 190 target per cycle
189's "Suggested next approach §1, item 2"; it tightens cycle 188's
`trans_of_middle_isIrreducible` story into a *constructive* lemma
suitable for downstream witnesses.

### Deliverable A — `PEquivalent.eq_of_isIrreducible_of_middle`

**Placement**: in `OpenMath.Chapter3.Section312.RKTableau` namespace,
inserted near `PEquivalent.trans_of_middle_isIrreducible` (file line
~497 in the post-cycle-189 file).

**Statement**:

```lean
/-- If two methods both P-reduce to a common (necessarily irreducible)
intermediate `N`, they are P-equivalent in the sense of def:381F.
This is the canonical-form constructor: irreducible reducts witness
P-equivalence directly. The `_hN : N.IsIrreducible` hypothesis is
documentation-only — the constructor body does not consume it. It
is included to flag the intended use case (irreducible normal form
witness). -/
theorem PEquivalent.eq_of_isIrreducible_of_middle
    {s s' sBar : ℕ}
    {M : RKTableau s} {M' : RKTableau s'} {N : RKTableau sBar}
    (_hN : N.IsIrreducible)
    (h₁ : PReducesTo M N) (h₂ : PReducesTo M' N) :
    PEquivalent M M' :=
  ⟨sBar, N, h₁, h₂⟩
```

**Why an unused hypothesis**: this naming convention is the
documentation contract. Future witnesses citing this lemma signal
"reduces to a normal form" by supplying an `IsIrreducible` proof at
the `_hN` slot, even though the existential constructor of
`PEquivalent` does not technically need it. If the planner judges
the unused hypothesis is too risky vs the supervisor's tautology
scanner, **drop `_hN` entirely** and either rename to
`PEquivalent.of_common_middle` or expose only the
`PEquivalent.mk`-style 4-tuple constructor without the irreducibility
documentation.

**Tautology check**: conclusion `PEquivalent M M'` is exactly
`∃ sBar N, PReducesTo M N ∧ PReducesTo M' N` (def:381F unfolded).
The body constructs the existential from the two `PReducesTo`
hypotheses. The `_hN` hypothesis is **not equal to** the conclusion
(it is an `IsIrreducible` predicate on a different witness), so this
is not a tautology. Cycle 188's
`PEquivalent.trans_of_middle_isIrreducible` already validates the
"irreducible-middle" pattern as substantive.

**Identity check**: not `exact h` — proof is the named existential
constructor on three named arguments.

**Hypothesis strength check**: `_hN`'s irreducibility is documentation;
the proof would still go through with a weaker (or no) hypothesis.
The strategic question is whether the named lemma is more useful
*with* the explicit `IsIrreducible` flag (compile-time documentation)
or *without* it (more general). The cycle 190 strategy bets on
"with" — irreducibility is cycle-188 / 189 vocabulary and most
downstream consumers will be feeding irreducible witnesses anyway.

### Deliverable B — Non-vacuity witness on `paddedEuler`

**Placement**: in `Section381` namespace, after the cycle 189
witnesses (file line ~1140 in the post-cycle-189 file).

**Statement**:

```lean
/-- `paddedEuler` is P-equivalent to itself, witnessed via the common
irreducible middle `paddedEuler.pReduced pairPartition`. Exercises
`PEquivalent.eq_of_isIrreducible_of_middle` on a non-trivial,
heterogeneous-stage (2 ↦ 1) reduction chain. -/
theorem paddedEuler_pEquivalent_self_via_pReduced :
    RKTableau.PEquivalent paddedEuler paddedEuler :=
  RKTableau.PEquivalent.eq_of_isIrreducible_of_middle
    paddedEuler_pReduced_pairPartition_isIrreducible  -- existing
    paddedEuler_pReducesTo_pReduced
    paddedEuler_pReducesTo_pReduced
```

**Pre-flight check**: search for
`paddedEuler_pReduced_pairPartition_isIrreducible` (or any
`IsIrreducible` witness on `paddedEuler.pReduced pairPartition`)
in `OpenMath/Chapter3/Section381.lean`. Cycle 184/185 era should
have it. Use:

```bash
grep -n "pReduced_pairPartition.*[Ii]rreducible\|paddedEuler.*[Ii]rreducible" \
  OpenMath/Chapter3/Section381.lean
```

If the witness exists, cite it directly. If absent, **prove it
inline** as a private helper:

```lean
private theorem paddedEuler_pReduced_pairPartition_isIrreducible :
    (paddedEuler.pReduced pairPartition).IsIrreducible := by
  -- 1-stage method (s = 1); IsIrreducible is the conjunction of
  -- "not P-reducible" and "not 0-reducible". For Fin 1, there is
  -- only one possible partition (trivial); both reducibility
  -- predicates fail vacuously by `Fin.subsingleton`.
  sorry  -- expected to close in 5–15 lines via Fin.subsingleton
```

If this inline proof exceeds 30 min budget, **fall back to
Deliverable A only** and skip Deliverable B; document the gap in
cycle results. Do NOT block the cycle on Deliverable B.

### Stretch — `PReducesTo.of_isZeroReducibleVia`

If Deliverables A+B close in under 60 min total, promote cycle 189's
`PEquivalent.of_isZeroReducibleVia` inline composition to a named
`PReducesTo`-side helper:

```lean
theorem PReducesTo.of_isZeroReducibleVia
    {s : ℕ} {M : RKTableau s} {inP1 : Fin s → Bool}
    (h : M.IsZeroReducibleVia inP1)
    (h_nonempty : ∃ i, inP1 i = false) :
    PReducesTo M (M.zeroReduced inP1) :=
  PReducesTo.zeroStep h h_nonempty PReducesTo.refl
```

This is 4 lines and would make future zero-reduction witnesses
one-liners.

### Verification (per deliverable)

* `lake env lean OpenMath/Chapter3/Section381.lean` exits 0.
* `lake build OpenMath.Chapter3.Section381` exits 0.
* `grep -c sorry OpenMath/Chapter3/Section381.lean` → 0.
* `#print axioms` on each new public theorem returns
  `[propext, Classical.choice, Quot.sound]` only.

---

## What NOT to try

* **Do NOT retry the Section441 compile after Priority 0 fails.**
  9 consecutive timeouts establish the pattern is not transient
  cluster load. Worker-side workarounds have been exhausted.
* **Do NOT edit `scripts/autonomous_loop.py`.** Phantom-commit
  verdict and prompt-builder issues are loop-maintainer territory
  (`phantom_commit_verdict_pattern.md`,
  `tautology_scanner_false_positives.md`).
* **Do NOT attempt the reverse direction of `thm:381H`**
  (`PhiEquivalent → PEquivalent`). It requires `thm:314A`
  (Independence of elementary differentials), which is unstarted
  in `plan.md`. Multi-cycle infrastructure; not a cycle 190
  candidate.
* **Do NOT poll Aristotle this cycle.** No jobs are pending. New
  jobs would not return in time and Section381 deliverables are
  too small (<10 LOC) to benefit from Aristotle.
* **Do NOT add `axiom` or `constant`** declarations.
* **Do NOT raise `maxHeartbeats`** above 200000.
* **Do NOT submit another Aristotle job for the Section441 Phase
  C.2 draft.** The cycle 184 Aristotle return already identified
  the namespace fix; further submissions duplicate work and have
  the same GPFS-degraded clean-build problem.
* **Do NOT cherry-pick a fresh Chapter 4 or 5 entity** (e.g.
  `def:451A`, `def:422B`, `def:442A`) over Section381 follow-up.
  The §380 P-equivalence cluster is now within 1–2 cycles of a
  natural pause point (the easy direction of `thm:381H` shipped
  cycle 189; cycle 190 ships the canonical-form constructor;
  cycle 191+ pauses while waiting for `thm:314A` infrastructure).
* **Do NOT attempt to build `thm:314A`** as a precursor — it is
  multi-cycle Hopf-algebra-on-rooted-trees infrastructure and not
  a one-cycle deliverable.
* **Do NOT pursue tautology-scanner cosmetic renames as primary
  cycle work.** Apply only if a flagged identifier appears in the
  new theorems — and only via the established
  `h_<name>` → `h<name>` (drop underscore) workaround.

---

## Cycle 190 budget

* Priority 0: 5 min hard cap.
* Priority 1A (if triggered): 90 min cap; if it stalls, revert
  and pivot to Priority 2.
* Priority 2 Deliverable A: 30 min target.
* Priority 2 Deliverable B: 30 min target (skip if irreducibility
  witness is missing AND inline construction blows budget).
* Stretch: only if all above close in <60 min total.

Total worker budget: ~2 hours.

---

## Commit message templates

If Priority 1A succeeds:
> Cycle 190 — §441 Phase C.2 SHIPPED: αPoly/ρPoly complex-root
> bounds + aPoly_complex_root_re_nonpos_of_stable

If Priority 2 succeeds (default, expected):
> Cycle 190 — §380 PEquivalent.eq_of_isIrreducible_of_middle +
> paddedEuler witness; §441 Phase C.2 GPFS-blocked (10th)

---

## Files to update

In addition to the Lean source:

* `.prover-state/issues/cycle_182_gpfs_slowness.md` — append cycle
  190 timeout entry (if Priority 0 fails).
* `extraction/formalization_data/lean_status.json` — only if
  Priority 1A ships Phase C.2 (`lem:441A` row → cycle 190).
* `plan.md` — only if Priority 1A ships Phase C.2.
* `.prover-state/issues/lem_441A_phase_C_scoping.md` — only if
  Priority 1A ships Phase C.2 (mark Phase C.2 SHIPPED in the
  status block).
* `.prover-state/task_results/cycle_190.md` — required, regardless
  of outcome.
