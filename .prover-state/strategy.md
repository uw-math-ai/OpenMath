# Cycle 234 — strategy

## A. §441 Phase C.2 status — SKIP (47th consecutive)

GPFS pathology blocks `lake env lean OpenMath/Chapter4/Section441.lean`
on every smoke test since cycle 182 (47 consecutive 5-min timeouts,
~0.2% CPU). This is **loop-maintainer territory**, not worker territory.
Per `cycle_182_gpfs_slowness.md` and `CLAUDE.md`:

* Do NOT re-attempt the §441 Phase C.2 smoke test.
* Do NOT modify `scripts/autonomous_loop.py`.
* Do NOT submit the cycle 182 draft to Aristotle (already tried,
  COMPLETE_WITH_ERRORS verdict captured, blocker is local compile).

The cycle 182 Phase C.2 draft + cycle 184 namespace fix remain
preserved at `.prover-state/cycle_182_draft_section441.lean` for
post-GPFS-recovery resumption.

## B. No Aristotle results to incorporate

No pending Aristotle submissions. Cycle 232's Aristotle-driven
right-action proof is fully integrated. No polling required this cycle.

## C. Priority 1 (P1) — §383 group-hom path Phase 4.2: identity axioms

Cycle 233 shipped associativity (`compose_assoc_phiEquivalent` +
`composeQ_phi_assoc`). Cycle 234 ships the **identity element** axioms
for the `Group` instance on `Quotient PhiEquivalent.setoidSigma`.

### What to ship

Two new theorems in `OpenMath/Chapter3/Section381.lean`, inside
`namespace OpenMath.Chapter3.Section312.RKTableau`, placed immediately
after cycle 233's `composeQ_phi_assoc`:

**P1.1** `composeQ_phi_id_left`:

```lean
theorem composeQ_phi_id_left
    (q : Quotient PhiEquivalent.setoidSigma) :
    composeQ_phi (Quotient.mk PhiEquivalent.setoidSigma ⟨0, RKTableau.id⟩) q
      = q
```

**P1.2** `composeQ_phi_id_right`:

```lean
theorem composeQ_phi_id_right
    (q : Quotient PhiEquivalent.setoidSigma) :
    composeQ_phi q (Quotient.mk PhiEquivalent.setoidSigma ⟨0, RKTableau.id⟩)
      = q
```

### Proof recipe (verbatim port of cycle 219's `composeQ_id_{left,right}` template)

For **P1.1**:

```lean
  refine Quotient.inductionOn q ?_
  rintro ⟨s, M⟩
  show Quotient.mk _ _ = Quotient.mk _ _
  exact Quotient.sound (id_compose_phiEquivalent M)
```

For **P1.2**:

```lean
  refine Quotient.inductionOn q ?_
  rintro ⟨s, M⟩
  show Quotient.mk _ _ = Quotient.mk _ _
  exact Quotient.sound (compose_id_phiEquivalent M)
```

### Ingredients (already shipped, axiom-clean)

* Cycle 228: `id_compose_phiEquivalent (M : RKTableau s) :
  @PhiEquivalent (0 + s) s (RKTableau.id.compose M) M`.
* Cycle 229: `compose_id_phiEquivalent (M : RKTableau s) :
  @PhiEquivalent (s + 0) s (M.compose RKTableau.id) M`.
* Cycle 232: `composeQ_phi` (the full binary
  `Quotient.lift₂` operation).
* Cycle 232: `composeQ_phi_mk` (`@[simp]` definitional unfold, `rfl`).

Both ingredient lemmas were verified axiom-clean in cycles 228/229.
Use them directly — do NOT re-prove or re-derive them.

### Estimated LOC

~10 LOC per theorem + ~10 LOC docstrings = ~40 LOC total. Compare to
cycle 219's `composeQ_id_left`/`composeQ_id_right` at the §382
Equivalent-quotient level, which were also ~10 LOC each.

## D. Priority 2 (P2) — Non-vacuity examples

Add two `example`s in `namespace OpenMath.Chapter3.Section381`, just
before the trailing `end OpenMath.Chapter3.Section381`, alongside
cycle 233's non-vacuity examples:

**P2.1** Homogeneous identity-left:

```lean
example :
    composeQ_phi
      (Quotient.mk PhiEquivalent.setoidSigma ⟨0, RKTableau.id⟩)
      (Quotient.mk PhiEquivalent.setoidSigma ⟨2, paddedEuler⟩)
    = Quotient.mk PhiEquivalent.setoidSigma ⟨2, paddedEuler⟩ :=
  composeQ_phi_id_left _
```

**P2.2** Homogeneous identity-right:

```lean
example :
    composeQ_phi
      (Quotient.mk PhiEquivalent.setoidSigma ⟨2, paddedEuler⟩)
      (Quotient.mk PhiEquivalent.setoidSigma ⟨0, RKTableau.id⟩)
    = Quotient.mk PhiEquivalent.setoidSigma ⟨2, paddedEuler⟩ :=
  composeQ_phi_id_right _
```

These mirror cycle 219's r=2 paddedEuler non-vacuity examples for the
§382 identity laws.

## E. What NOT to try

1. **Do NOT** attempt to ship `inverse_phiEquivalent_inverse` (cycle
   235's target) this cycle. That theorem requires a tree-induction
   argument on the elementary weight of the inverse method and is
   non-trivial; bundling it with the identity laws risks blowing the
   cycle budget.

2. **Do NOT** attempt to ship the `Group` instance on
   `Quotient PhiEquivalent.setoidSigma` this cycle. That requires
   all three axioms (associativity ✓ from cycle 233, identity from
   cycle 234, inverse from cycle 235+) and is at minimum a cycle 237
   deliverable.

3. **Do NOT** introduce a heterogeneous-stage variant of
   `composeQ_phi_id_{left,right}` keyed off raw representatives
   (i.e. with explicit `s : ℕ`). The textbook content is the
   quotient-level axiom; the underlying PhiEquivalent-level
   `id_compose_phiEquivalent` / `compose_id_phiEquivalent` are
   already heterogeneous-stage (`0 + s` vs `s + 0`) and discharge
   that complexity inside the `Quotient.sound` application.

4. **Do NOT** use `composeQ_phi_left_act_id_{left,right}` (cycle
   228/229 partial-action versions) as proof ingredients. Those are
   structurally weaker because their second argument is a raw
   representative `Σ s, RKTableau s`, not a quotient class. They
   were one-sided lifts shipped while cycle 232's full binary
   `composeQ_phi` was still blocked on the right-action. With the
   full binary `composeQ_phi` now available (cycle 232), the
   identity laws lift cleanly via `Quotient.inductionOn` directly
   from the underlying PhiEquivalent lemmas — do NOT route through
   the partial-action layer.

5. **Do NOT** attempt P3 / P4 stretch goals (e.g. `inverseQ_phi` or
   the homomorphism `Φ`). Cycle 233 scored +2 with a focused 2-theorem
   deliverable; cycle 234 should match that scope.

6. **Do NOT** invoke `Quotient.lift₂_mk` or other `simp` lemmas
   inside the proof bodies — the `show Quotient.mk _ _ = Quotient.mk _ _`
   reframing handles the unfolding by definitional reduction (per
   cycle 219's template, which the cycle 233 worker followed verbatim
   for `composeQ_phi_assoc`).

7. **Do NOT** annotate either theorem with `.{u}` universe parameters.
   `PhiEquivalent` is universe-monomorphic (confirmed by cycle 223
   when shipping `PhiEquivalent.setoid` / `setoidSigma`); cycle 233
   shipped `composeQ_phi_assoc` without `.{u}` and it compiled
   cleanly. Cycle 234 follows the same pattern.

## F. Pre-flight checks (run before edits)

* `lake env lean OpenMath/Chapter3/Section381.lean` warm rebuild
  baseline. Cycle 233 measured ~6.5s warm; if today's warm rebuild
  exceeds 60s on the baseline (no edits yet), flag as a §F.3 red flag
  and pause before proceeding.

* Verify the four ingredient symbols exist at HEAD via `lean_verify`:
  - `OpenMath.Chapter3.Section312.RKTableau.id_compose_phiEquivalent`
  - `OpenMath.Chapter3.Section312.RKTableau.compose_id_phiEquivalent`
  - `OpenMath.Chapter3.Section312.RKTableau.composeQ_phi`
  - `OpenMath.Chapter3.Section312.RKTableau.composeQ_phi_mk`

  All four should return axiom set
  `[propext, Classical.choice, Quot.sound]`. If any does NOT exist
  under that exact name, search for the actual name with
  `lean_local_search` before adapting the proof; do NOT guess at a
  renamed symbol.

## G. Post-flight checks (run after edits)

1. `lake env lean OpenMath/Chapter3/Section381.lean` exits 0.
2. `grep -c sorry OpenMath/Chapter3/Section381.lean` returns 0.
3. `lean_verify` on both new theorems
   (`composeQ_phi_id_left`, `composeQ_phi_id_right`) returns
   `[propext, Classical.choice, Quot.sound]` only.
4. Regression spot-checks via `lean_verify` on:
   - `composeQ_phi` (cycle 232)
   - `compose_assoc_phiEquivalent` (cycle 233)
   - `composeQ_phi_assoc` (cycle 233)
   All should remain axiom-clean.
5. Warm rebuild time after edits should remain under 60s
   (cycle 233's baseline was 6.5s; ~40 LOC addition should add <1s).

## H. Faithfulness check

For `composeQ_phi_id_left` and `composeQ_phi_id_right`:

* **Textbook reference**: `thm:384A` (Butcher §384, p. 311) —
  Φ is a group homomorphism between two groups. The `Group` instance
  on the codomain `Quotient PhiEquivalent.setoidSigma` is the multi-cycle
  deliverable; cycle 234 ships piece (b) identity (cycle 233 shipped
  piece (a) associativity; cycle 235+ ships piece (c) inverse).

* **Faithfulness divergence**: same as cycle 233. The full `thm:384A`
  is the homomorphism Φ as a `MonoidHom`; cycle 234 ships only one of
  the three group axioms on the codomain. Status remains `partial` in
  `lean_status.json`; do NOT mark `thm:384A` as `formalized`.

* **Tautology check**: P1.1 / P1.2 conclusions are equalities of
  quotient classes; hypotheses are bare quotient classes with no
  identity assumption. No tautology.

* **Identity-only proof check**: bodies are `Quotient.inductionOn`
  + `Quotient.sound` — these are doing real definitional work
  (extracting a representative, applying the underlying PhiEquivalent
  lemma at that representative, lifting back via `Quotient.sound`).
  Not a single `exact h` re-export.

* **Hypothesis strength**: minimal — just a quotient class. No
  Lipschitz, smallness, or other auxiliary constraints.

## I. Bookkeeping updates

* `plan.md` `thm:384A` row: append a cycle 234 note recording the
  identity-axiom landing (alongside cycle 233's associativity note).
  Keep status `[~]` (partial).

* `lean_status.json` `thm:384A` row: bump `cycle` to 234, update
  `notes` to record cycle 234's deliverables. Keep `status` as
  `partial`.

* `.prover-state/task_results/cycle_234.md`: standard template per
  `CLAUDE.md`. Document the closing recipe, faithfulness divergence
  (same shape as cycle 233), and the cycle 235+ outlook
  (inverse_phiEquivalent_inverse via tree induction on inverse method,
  Aristotle-batch candidate).

## J. Cycle 235+ outlook (informational, not for cycle 234)

* **Cycle 235**: `inverse_phiEquivalent_inverse` — the §383 analog
  of cycle 222's `inverse_equivalent_inverse`. Non-trivial:
  `PhiEquivalent M M' → PhiEquivalent M.inverse M'.inverse` likely
  requires showing equality of elementary weights of the inverse
  tableau under the PhiEquivalent hypothesis. Strong Aristotle
  candidate.

* **Cycle 236**: inverse absorption laws on `composeQ_phi`
  (analog of cycle 220's `composeQ_inverse_{left,right}`). Requires
  cycle 235 + a `MonoidHom`-style closed-form on `inverse`'s
  elementary weight.

* **Cycle 237**: `Group` instance on `Quotient PhiEquivalent.setoidSigma`
  via `Group.ofLeftAxioms` (analog of cycle 222's `instGroup`).

* **Cycle 238+**: the homomorphism Φ as a `MonoidHom`, closing
  `thm:384A` proper.

Aristotle queue: nothing pending. Cycle 234's identity lift is too
small to batch; cycle 235's inverse-PhiEquivalent is the next
candidate for submission.
