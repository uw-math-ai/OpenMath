# Cycle 193 Strategy

## Context

* **Sorry count: 0.** All committed files compile axiom-clean.
* **Section441 GPFS pathology**: 12 consecutive timeouts (cycles
  182–192). Phase C.2 of `lem:441A` is verification-blocked. Cycle
  182 draft + cycle 184 namespace fix preserved at
  `.prover-state/cycle_182_draft_section441.lean`; will ship if GPFS
  recovers but worker MUST NOT spin on it.
* **Active cluster**: `def:381F` (P-equivalent) in
  `OpenMath/Chapter3/Section381.lean`. Last 8 cycles (185–192)
  have shipped one or two axiom-clean theorems each on this cluster
  while Section441 has been blocked. File compiles cleanly in ~4s
  warm, ~70s cold.
* **No pending Aristotle results.**

## Cycle 193 deliverables — in execution order

### Priority 0 (mandatory smoke test, 5 min budget — likely 13th timeout)

Run **once**:
```
time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean
```
Pre-flight: confirm no D-state zombies via
`ps -u $USER -o pid,stat,wchan,etime,comm | grep -E "^[ ]*[0-9]+ +D"`.

* **If completes in < 5 min (UNEXPECTED — GPFS recovered)**: STOP all
  other priorities. Replace HEAD `Section441.lean` with the cycle 182
  draft, apply the cycle 184 one-line namespace fix at line 1529
  (`M.αPoly_complex_root_norm_ge_one_of_stable` →
  `LinearMultistepMethod.αPoly_complex_root_norm_ge_one_of_stable M`),
  re-compile, verify axiom-clean, ship Phase C.2. The exact diff is
  documented in
  `.prover-state/issues/cycle_182_gpfs_slowness.md` cycle 184
  update. Update `lean_status.json`, `plan.md`, and the
  `lem_441A_phase_C_scoping.md` cycle 184 update with the close.
* **If times out (EXPECTED)**: log the 13th consecutive timeout in
  `cycle_182_gpfs_slowness.md` (append a one-paragraph "Cycle 193
  update" entry with EXIT code, wall time, CPU% — same shape as
  cycles 185–192). Then proceed to Priority 2.

**DO NOT attempt multiple smoke tests this cycle.** One try, log, move
on. Loop-maintainer escalation is already in flight via
`phantom_commit_verdict_pattern.md` and `cycle_182_gpfs_slowness.md`.

### Priority 2 (substantive deliverable — Option 3B, def:381F follow-up)

**Target**: ship `RKTableau.PEquivalent.eq_of_both_isIrreducible` in
`OpenMath/Chapter3/Section381.lean`.

**Statement** (in the `OpenMath.Chapter3.Section312.RKTableau`
namespace, placed AFTER cycle 190's
`PEquivalent.eq_of_isIrreducible_of_middle`):

```lean
/-- If two P-equivalent methods are both `IsIrreducible`, they are
    equal up to heterogeneous-stage `HEq`. This is the canonical-form
    half of def:381E ("the reduced method"): irreducible
    P-equivalent methods coincide.

    Dual to `PEquivalent.eq_of_isIrreducible_of_middle` (cycle 190),
    which handles the case where the existential middle is irreducible.
    Here both endpoints are irreducible; the common reduct collapses to
    each endpoint via `eq_of_isIrreducible_of_pReducesTo` (cycle 188). -/
theorem PEquivalent.eq_of_both_isIrreducible
    {s s' : ℕ} {M : RKTableau s} {M' : RKTableau s'}
    (hM : M.IsIrreducible) (hM' : M'.IsIrreducible)
    (h : PEquivalent M M') :
    ∃ heq : s' = s, HEq M' M := by
  obtain ⟨sMid, Mmid, h₁, h₂⟩ := h
  -- h₁ : PReducesTo M Mmid
  -- h₂ : PReducesTo M' Mmid
  -- Apply cycle 188's eq_of_isIrreducible_of_pReducesTo to each side.
  obtain ⟨h₁eq, h₁heq⟩ := eq_of_isIrreducible_of_pReducesTo hM h₁
  obtain ⟨h₂eq, h₂heq⟩ := eq_of_isIrreducible_of_pReducesTo hM' h₂
  -- h₁eq : sMid = s,   h₁heq : HEq Mmid M
  -- h₂eq : sMid = s',  h₂heq : HEq Mmid M'
  -- Chain HEq's: M' ≅ Mmid ≅ M.
  subst h₁eq
  subst h₂eq
  exact ⟨rfl, h₂heq.symm.trans h₁heq⟩
```

**Notes on the proof**:
* Verify the exact name and signature of cycle 188's
  `eq_of_isIrreducible_of_pReducesTo` via `lean_hover_info` first —
  the strategy assumes its conclusion shape is
  `∃ heq : sMid = s, HEq Mmid M`. If the conclusion has the equality
  the other way (`s = sMid`) or the `HEq` reversed, adjust the
  `subst`/`HEq.symm` accordingly.
* `subst` on indexed inductive HEq goals can require `cases` instead
  if the variable is locally constrained. Try the direct path first;
  if `subst h₂eq` fails (because `s'` already disappeared after
  `subst h₁eq` left `s = sMid`), use a single `subst h₁eq` and then
  manipulate `h₂eq : sMid = s'` directly via `h₂eq ▸ ...` or `cases
  h₂eq`.
* If both `subst`s fail, fall back to the manual HEq-chain pattern
  used in cycle 190's `eq_of_isIrreducible_of_middle` — verify via
  `lean_goal` after `obtain` to confirm the goal shape, then write
  the chain step-by-step.
* Use `lean_verify` (NOT `#print axioms` from a `/tmp/*.lean`
  external file — per cycle 192's discovery, the latter hits stale
  `.olean` cache and reports `unknownIdentifier` for fresh symbols).

**Non-vacuity witness**: add a one-line `example` immediately after
the theorem, exercising it on the existing `paddedEuler` data:

```lean
example : ∃ heq : 2 = 2, HEq paddedEuler paddedEuler :=
  PEquivalent.eq_of_both_isIrreducible
    paddedEuler_isIrreducible paddedEuler_isIrreducible
    (PEquivalent.refl paddedEuler)
```

This is technically a reflexive instance — the heterogeneous-stage
aspect is exercised at the type level (the conclusion type
`∃ heq : 2 = 2, HEq paddedEuler paddedEuler` is well-formed
*precisely because* the theorem accepts heterogeneous indices). A
non-reflexive irreducible witness pair would require constructing a
second concrete irreducible method, which is genuinely new content;
defer that unless Priority 3 closes early.

**Expected size**: ~25 LOC including docstring + example. **Compile
time**: should remain at ~4s warm rebuild for Section381.lean.

### Priority 3 (stretch — only if Priority 2 ships in < 60 min)

Ship `RKTableau.PReducesTo.toPhiEquivalent` (collapsing the two-hop
`PEquivalent.of_pReducesTo` + `PEquivalent.toPhiEquivalent` path
into a one-hop direct corollary). Placement: immediately after
cycle 187's `PhiEquivalent.of_pReducesTo` (it's a direct alias).

```lean
/-- One-step bridge: any P-reduction induces Φ-equivalence between
    its endpoints. Direct corollary of `PhiEquivalent.of_pReducesTo`,
    provided for caller ergonomics so downstream code can write
    `h.toPhiEquivalent` on a `PReducesTo` hypothesis without going
    through `PEquivalent`. -/
theorem PReducesTo.toPhiEquivalent {s s' : ℕ} {M : RKTableau s}
    {M' : RKTableau s'} (h : PReducesTo M M') : PhiEquivalent M M' :=
  PhiEquivalent.of_pReducesTo h
```

Verify the actual name of cycle 187's `PhiEquivalent.of_pReducesTo`
before writing — if it lives at the bare `PhiEquivalent` namespace,
the proof body is exactly as shown; if it's
`RKTableau.PhiEquivalent.of_pReducesTo` or similar, adjust the
qualifier. ~10 LOC. Trivial proof.

## What NOT to do

* **Do NOT re-attempt Section441.lean compile** after Priority 0's
  one shot. Cycles 182–192 establish the pattern beyond doubt.
* **Do NOT attempt Phase C.3 of `lem:441A`** (real factorisation /
  conjugate pairs). Per `lem_441A_phase_C_scoping.md` §"Risk
  assessment", Phase C.3 is the highest-risk multi-cycle phase and
  requires Phase C.2 to be shipped first.
* **Do NOT modify `scripts/autonomous_loop.py`** — loop-maintainer
  territory per CLAUDE.md.
* **Do NOT raise `maxHeartbeats`** above 200000.
* **Do NOT pivot to a fresh entity** (e.g. `def:451A`, `def:422B`,
  `def:442A`) while the def:381F cluster has natural follow-ups in
  scope. Pivot only after Option 3B + Option 3A-stretch ship and
  the cluster reaches a documented pause point.
* **Do NOT introduce new `axiom`/`constant` declarations.**
* **Do NOT use `#print axioms` against a standalone `/tmp/*.lean`
  import for fresh symbols** — it reads the stale `.olean` cache and
  reports `unknownIdentifier`. Use `lean_verify` against the file
  under test (per cycle 192 discovery).
* **Do NOT poll Aristotle** — no pending jobs.
* **Do NOT cherry-pick a smaller def:381F follow-up** (e.g. trivial
  reflexivity lemma renames or one-line corollaries already implicit
  in existing infrastructure). Option 3B is the next substantive
  theorem in the canonical-form story; the file budget permits it.
* **Do NOT spend cycle time auditing whether cycle 190's
  `eq_of_isIrreducible_of_middle` and the new
  `eq_of_both_isIrreducible` are redundant** — they handle different
  configurations (existential middle vs. both endpoints) and both
  are textbook-relevant. Ship the new theorem; the duality is the
  point.

## Verification protocol

After each new theorem:
1. `lake env lean OpenMath/Chapter3/Section381.lean` exits 0 (warm
   rebuild target ~4s).
2. `grep -c sorry OpenMath/Chapter3/Section381.lean` → 0.
3. `lean_verify
   OpenMath.Chapter3.Section312.RKTableau.PEquivalent.eq_of_both_isIrreducible`
   returns `[propext, Classical.choice, Quot.sound]` only.
4. If Priority 3 ships, also `lean_verify
   OpenMath.Chapter3.Section312.RKTableau.PReducesTo.toPhiEquivalent`.
5. Regression spot-check: `lean_verify` on at least one downstream
   theorem (e.g. `paddedEuler_pEquivalent_pReduced`) to confirm no
   regression to existing axiom-clean witnesses.

## Pre-commit faithfulness checklist (per CLAUDE.md)

For `PEquivalent.eq_of_both_isIrreducible`:
* **Tautology check**: conclusion `∃ heq : s' = s, HEq M' M` does
  NOT appear as any hypothesis. The three hypotheses are
  `M.IsIrreducible`, `M'.IsIrreducible`, and `PEquivalent M M'` —
  all structurally distinct from the conclusion. **Pass.**
* **Identity check**: proof composes two `obtain`s + `subst`/`cases`
  + an `HEq.symm.trans`. Not `exact h`. **Pass.**
* **Hypothesis strength check**: all three hypotheses are consumed
  (both `IsIrreducible`s gate the `eq_of_isIrreducible_of_pReducesTo`
  applications; `PEquivalent` provides the existential middle).
  Cannot weaken. **Pass.**
* **Definition smuggling check**: not a `def` or `structure`. N/A.

For `PReducesTo.toPhiEquivalent` (if shipped):
* Trivial direct corollary. Documents itself in the docstring as a
  caller-ergonomics shim, not a new mathematical claim. **Pass.**

## Task results / plan updates on close

* `extraction/formalization_data/lean_status.json` `def:381F` row:
  bump cycle reference to 193 (status remains `partial` — full
  canonical-form story still needs the `reducedMethod` construction
  per `reduced_method_deferred.md`).
* `plan.md` `def:381F` row: append a `Cycle 193: ...` clause
  mirroring the cycle 188/189/191/192 entries. Cite the new theorem
  name + axiom-clean status.
* If Priority 3 ships, no separate `lean_status.json` row — it's
  caller-ergonomics infrastructure, not a textbook entity. Just
  mention in `plan.md` row's cycle entry.

## End-of-cycle commit message template

If Priority 2 only:
```
Cycle 193 — §380 PEquivalent.eq_of_both_isIrreducible (canonical-form
half of def:381E); §441 Phase C.2 GPFS-blocked (13th)
```

If Priorities 2 + 3:
```
Cycle 193 — §380 PEquivalent.eq_of_both_isIrreducible +
PReducesTo.toPhiEquivalent direct corollary; §441 Phase C.2
GPFS-blocked (13th)
```

If Priority 1 unexpectedly fires (GPFS recovery):
```
Cycle 193 — §441 lem:441A Phase C.2 shipped (Re(ζ) ≤ 0 for aPoly
complex roots under stability); GPFS recovery
```
