# Cycle 187 Strategy

## Context summary

* **Sorry count**: 0 across the project (verified at HEAD `e64f0a1`).
* **Phase B of `lem:441A`**: closed cycle 179, axiom-clean, headline at
  `OpenMath/Chapter4/Section441.lean:913`.
* **Phase C.2 of `lem:441A`**: drafted cycle 182, namespace fix
  identified cycle 184, **GPFS-blocked for 6 consecutive cycles**
  (182/183/184/185/186). Draft preserved at
  `.prover-state/cycle_182_draft_section441.lean`; the one-line
  namespace fix is on draft line 1529 (`M.αPoly_…` →
  `LinearMultistepMethod.αPoly_…`).
* **Section381 (`def:381F` P-equivalent)**: cycles 184–186 shipped
  the `PEquivalent` predicate, restricted transitivity, soundness fix
  to `PReducesTo.step`, and four public heterogeneous-stage witnesses.
  Compiles healthily (~70s clean / ~4s warm — Section441's
  `Mathlib.Analysis.*`-heavy import set is the GPFS pathology, not a
  cluster-wide outage).
* **Loop-maintainer escalation**: `phantom_commit_verdict_pattern.md`
  (cycle 180) and `cycle_182_gpfs_slowness.md` (escalated cycle 186)
  document supervisor and GPFS issues respectively. **Worker MUST NOT
  edit `scripts/autonomous_loop.py`.**

No Aristotle results pending. Prior project
`7c4d0ffb-e6c1-4ef4-b8f5-688d256bac44` was processed in cycle 184; its
useful output (the namespace fix) is already preserved.

## Priority 0 — GPFS health probe (MANDATORY first action, ≤5 min)

Run **once** at the start of the cycle:

```bash
ps -u $USER -o pid,stat,wchan,etime,comm | grep -E "^[ ]*[0-9]+ +D"
time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean
```

Pre-flight: if `ps` shows D-state processes owned by the user that
have been idle >30 min (typically abandoned `find /` queries from
prior tooling), kill them before the smoke test. Cycle 183 found
exactly this pattern.

* **If completes in <5 min cleanly**: GPFS recovered. Proceed to
  Priority 1.
* **If times out (EXIT=124) with near-zero CPU**: 7th consecutive
  GPFS timeout. Append a one-line update to
  `cycle_182_gpfs_slowness.md` recording the 7th timeout. Proceed to
  Priority 2. **Do NOT submit a fresh Aristotle batch for Phase C.2** —
  cycle 184's batch already extracted the only actionable output.

## Priority 1 — Ship Phase C.2 (only if Priority 0 succeeds)

**Recipe**:

1. Copy the preserved draft over HEAD:
   ```bash
   cp .prover-state/cycle_182_draft_section441.lean OpenMath/Chapter4/Section441.lean
   ```
2. Apply the cycle 184 namespace fix at line 1529:
   ```
   -      M.αPoly_complex_root_norm_ge_one_of_stable hStable hψ_ne hψ_isRoot
   +      LinearMultistepMethod.αPoly_complex_root_norm_ge_one_of_stable M
   +        hStable hψ_ne hψ_isRoot
   ```
3. Compile via `time lake env lean OpenMath/Chapter4/Section441.lean`.
   Time-box at **15 minutes** of wall clock per attempt.
4. If errors surface beyond the namespace fix: triage the first 1–2
   surfaced errors. Likely remediation patterns from the cycle 184
   Aristotle audit:
   * Dot notation on `M : LinearMultistepMethod k` for theorems
     defined in `Section441` namespace fails — qualify explicitly
     with `LinearMultistepMethod.<name>`.
   * Simp-set ordering issues: try `simp only [...]` instead of
     `simp [...]` to make the rewrite chain deterministic.
5. Once clean: run `lean_verify` on each new public theorem:
   * `LinearMultistepMethod.ρPoly_complex_root_norm_le_one_of_stable`
   * `LinearMultistepMethod.αPoly_complex_root_norm_ge_one_of_stable`
   * `LinearMultistepMethod.aPoly_complex_root_re_nonpos_of_stable`

   Each must return `[propext, Classical.choice, Quot.sound]` only.
6. Update `lean_status.json` row for `lem:441A` (still `partial` —
   Phase C.3 + C.4 remain), and update the cycle reference to 187.
7. Update `plan.md` row for `lem:441A` to record Phase C.2 closure.
8. Update `lem_441A_phase_C_scoping.md` Phase C.2 section: mark as
   shipped, link to the new theorems by line number.
9. **Time-box the entire Priority 1 attempt at 45 minutes** of wall
   clock. If not closed by then (e.g. an unanticipated mathlib
   API mismatch), revert via
   `git checkout HEAD -- OpenMath/Chapter4/Section441.lean` and pivot
   to Priority 2. Do NOT leave the file with sorries or compile errors.

## Priority 2 — Section381 follow-up (if GPFS still blocked)

Two productive deliverables. **Pick Deliverable A** as the primary
target; if it closes early, ship Deliverable B as a bonus.

### Deliverable A — `PReducesTo` ⇒ `PhiEquivalent` implication

Ship in `OpenMath/Chapter3/Section381.lean`:

```lean
theorem RKTableau.PhiEquivalent.of_pReducesTo {s s' : ℕ}
    {M : RKTableau s} {M' : RKTableau s'}
    (h : M.PReducesTo M') : M.PhiEquivalent M'
```

(or whichever name matches the existing `PhiEquivalent`/`PReducesTo`
conventions in the file — verify with `lean_file_outline`).

**Pre-work** (do this BEFORE writing the proof):
* Run `lean_file_outline OpenMath/Chapter3/Section381.lean` to
  locate the existing `PhiEquivalent` definition (`def:381B`) and
  any already-shipped lemmas about it.
* Run `lean_local_search "PhiEquivalent"` and
  `lean_local_search "elementary"` to find existing infrastructure
  for elementary weights / rooted-tree machinery, since the proof
  requires them.

**Proof recipe**:
* Induction on the `PReducesTo` constructor (cycle 184's
  refl-trans-closure inductive type).
* `refl` case: should reduce to `PhiEquivalent.refl`. If
  `PhiEquivalent.refl` doesn't yet exist, ship it as a one-liner
  helper first.
* `step` case: a single P-reduction preserves elementary weights
  stage-by-stage. The argument: if partition `P` makes
  `Σ_{j ∈ P_J} a_{ij}` constant on each block `P_I`, then for every
  rooted tree `t`, the elementary weight `Φ(t)` computed via `M`
  agrees with the elementary weight via `M.pReduced P`. Inductive
  on `t`'s structure (sum over children's elementary differentials).
* `trans` case (if the `PReducesTo` inductive has one): trivial via
  the IH.

**Estimated LOC**: 30–80 LOC. Axiom-clean expected.

**Fallback**: if the inductive `step` argument turns out to need
substantial rooted-tree machinery (`RootedTree.elementaryWeight`,
`Φ_t`, etc.) that hasn't been ported into Section381's import set,
do NOT add new imports speculatively. Instead:
* File a brief gap note in `.prover-state/issues/` scoping the
  required infrastructure.
* Pivot to Deliverable B and report partial progress.

### Deliverable B — Refactor `paddedEuler.PEquivalent paddedEuler` example

Pure cleanup. Use `lean_file_outline OpenMath/Chapter3/Section381.lean`
to locate the inline `paddedEuler.PEquivalent paddedEuler` example
(cycle 185 introduced it; approximately lines 680–693 — verify before
editing). The example currently constructs its inner reduction
witness inline; replace with one-line invocations of cycle 186's
named theorems:
* `paddedEuler_pReducesTo_pReduced` (single-step witness)
* `paddedEuler_pEquivalent_pReduced` (existential closure)

**Estimated LOC delta**: −10 to −20 LOC (net reduction). Axiom-clean
expected (cosmetic refactor; types are identical).

### Constraints for Priority 2

* **Do NOT touch `Section441.lean`** — preserve cycle 181 HEAD state
  for when GPFS recovers.
* **Do NOT submit Aristotle jobs** for Section381 follow-ups; manual
  proof scope.
* **Do NOT add new top-level definitions or predicates** in
  Section381 (the `def:381F` definitional shape is settled across
  cycles 184–186; work against it, don't redefine it).
* If Deliverable A closes in <30 min: also ship Deliverable B.
* If Deliverable A stalls past 60 min: revert any uncommitted
  Section381 changes via
  `git checkout HEAD -- OpenMath/Chapter3/Section381.lean`, then
  ship Deliverable B + the gap-scoping issue file as the cycle's
  output.

## What NOT to try

These approaches have failed or are explicitly out-of-scope:

1. **Re-attempting Phase C.2 verification with patient long
   compiles**: 6 consecutive cycles confirm GPFS is the bottleneck.
   Time-box at 5 min per `lake env lean` invocation; do NOT try
   30+ minute compiles.
2. **Re-deriving the cycle 174 factor-of-2 bridge**: it is correct;
   Butcher §441 p. 376 has a typo. Independently verified by cycle
   174 + cycle 180 consultants. Do not audit
   `aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent`.
3. **Editing `scripts/autonomous_loop.py`**: loop-maintainer
   territory per CLAUDE.md.
4. **Submitting a fresh Aristotle job for Phase C.2**: cycle 184's
   batch returned the only actionable output. Re-submission consumes
   a job slot without new value.
5. **`Polynomial.ext + simp + ring` on `bdf2LMM`-style closed forms**:
   cycles 172/173 stalled here. Cycle 180's
   `Polynomial.funext + ring` recipe is the canonical pattern.
6. **Attempting Phase C.3 (real factorisation)**: explicitly out of
   scope per `lem_441A_phase_C_scoping.md`. The high-risk phase;
   benefits from Phase C.2 being shipped first.
7. **Inline `Polynomial.ext + ring`-on-the-recursive-`det_succ_row_zero`
   without a helper split**: cycles 148/150's `thm:550A` n=6/n=7
   stepping stones blew past 200000 heartbeats when the matrix
   expansion + polynomial residue were combined in one tactic; the
   working pattern factors the matrix expansion into a
   `private lemma matrixN_oneMinusZSmul_det` first.
8. **Trusting `attempts.md` "stuck on" rows over git state**: per
   `phantom_commit_verdict_pattern.md` and the cycle 180 / cycle 186
   precedent, verify HEAD directly.

## Pre-commit checklist (CLAUDE.md mandatory)

For each new `def`/`structure`/`theorem` introduced this cycle:

* Quote the textbook statement from
  `extraction/formalization_data/entities/<id>.json` (or for
  internal helpers, point to the textbook step in Butcher §380/§441
  that motivates the lemma).
* Confirm the Lean type matches the textbook content; document any
  divergence inline.
* Run the tautology scanner:
  ```bash
  rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/
  ```
  Should return no hits. If it does, apply the cosmetic rename
  workaround (`h_<name>` → `h<name>`) per
  `tautology_scanner_false_positives.md`.
* `#print axioms` (via `lean_verify`) on each new public theorem
  returns `[propext, Classical.choice, Quot.sound]` only.

For Priority 1 specifically: the three Phase C.2 theorems trace to
Butcher §441 p. 376's chain
(stability ⇒ closed-disc ρ-roots ⇒ Möbius lift to closed-left-half-plane
a-roots). The cycle 182 draft's proof structure mirrors the textbook
step-by-step.

For Priority 2 Deliverable A: the implication is implicit in
Butcher's §380 narrative ("P-reducible methods agree on elementary
weights"); document the proof outline in the docstring.

For Priority 2 Deliverable B: pure rename/refactor; no faithfulness
question.

## Task results — write `.prover-state/task_results/cycle_187.md`

Standard sections per CLAUDE.md template. Specifically include:
* Which priority fired and why (record the GPFS probe outcome).
* Per new theorem: faithfulness check + axiom verification result.
* If Priority 1 succeeded: the recipe steps that landed cleanly vs
  any deviations from the cycle 182 draft.
* If Priority 2: which deliverable shipped, LOC delta, and whether
  Deliverable A's induction needed any new helper lemmas (those
  are themselves cycle 187 deliverables, document them).
* Suggested next approach (decision tree for cycle 188):
  * If Priority 1 succeeded → cycle 188 scopes Phase C.3 per
    `lem_441A_phase_C_scoping.md` §3 (multi-cycle high-risk phase).
  * If Priority 0 timed out (7th time) and Priority 2 shipped
    Deliverable A → cycle 188 should re-probe GPFS first, then
    either ship Phase C.2 (if recovered) or ship a §380 follow-up
    such as `def:381E`'s reduced-method construction (per
    `reduced_method_deferred.md`) or a Φ-equivalence companion to
    `paddedEuler_pEquivalent_pReduced`.
  * If both Priority 0 and Priority 2 stalled → diagnose and
    recommend a planner re-scoping cycle.
