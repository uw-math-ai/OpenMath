# Cycle 227 strategy

## TL;DR

§383 group-homomorphism path **Phase 3 follow-up**. The cycle 226 left-action
`compose_phiEquivalent_compose_left` is axiom-clean; the right-action half
(varying `M₂`) is blocked and was submitted to Aristotle at end of
cycle 226. **Priority 0**: a single poll on that Aristotle project.
**Priority 1**: branches on the Aristotle result —
- If COMPLETE with a clean proof, **incorporate the full
  `compose_phiEquivalent_compose`** and ship the downstream
  `composeQ_phi` (`Quotient.lift₂`) + bracketed-form corollary.
- If NOT solved, ship `composeQ_phi_left_act` — a one-sided
  `Quotient.lift` consuming **only** cycle 226's left-action. This
  is genuine, axiom-clean infrastructure that the §383 group-hom
  path needs regardless of when the full binary operation lands.

Sorry count stays at **0** (target: 41st consecutive clean cycle since
the cycle 201 rollback). Skip §441 Phase C.2 (43rd consecutive GPFS
block).

---

## A. §441 Phase C.2 — SKIP (43rd consecutive GPFS block)

`OpenMath/Chapter4/Section441.lean` has timed out on every smoke test
since cycle 182. **Do NOT attempt a smoke test or compile** of
Section441.lean. The cycle 182 draft + cycle 184 namespace fix at
`.prover-state/cycle_182_draft_section441.lean` remain frozen until
GPFS recovers; the loop-maintainer escalation
(`.prover-state/issues/phantom_commit_verdict_pattern.md` and the
GPFS-pathology note in `.prover-state/issues/cycle_182_gpfs_slowness.md`)
is in force.

---

## B. Priority 0 — Aristotle single poll (5 min, hard cap)

The cycle 226 worker submitted the M₂-side sum equality (the
right-action of `compose_phiEquivalent_compose`) to Aristotle at
`2026-05-14T15:50:23 UTC`:

- **project_id**: `176aa964-db7b-40f8-a01c-05247c186ec5`
- Submission time ≈ 20 h before cycle 227 starts.

Run **exactly one** poll at the start of the cycle:

```
mcp__aristotle__get_status (or refresh_status if needed) with
project_id "176aa964-db7b-40f8-a01c-05247c186ec5"
```

Then immediately branch:

### B.1 — Aristotle status = COMPLETE (or COMPLETE_WITH_ERRORS but
the right-action proof verifies)

- Download the result with `mcp__aristotle__download_result` and
  `mcp__aristotle__extract_result`.
- Identify the Lean proof of either:
  (a) the **M₂-side sum equality** `∑ i, M₂.b i *
      M₂.derivativeWeightWithSrc M₁ i t = ∑ i', M₂'.b i' *
      M₂'.derivativeWeightWithSrc M₁ i' t` under `PhiEquivalent M₂ M₂'`,
      OR
  (b) the **full right-action** `PhiEquivalent M₂ M₂' →
      PhiEquivalent (M₁.compose M₂) (M₁.compose M₂')`, OR
  (c) the **full theorem** `compose_phiEquivalent_compose`.
- **Verify locally** by adding the symbol(s) to
  `OpenMath/Chapter3/Section381.lean` after cycle 226's
  `compose_phiEquivalent_compose_left` (`Section381.lean:2858`),
  recompile (`lake env lean OpenMath/Chapter3/Section381.lean`,
  EXIT must be 0), and run `lean_verify` to confirm axiom-clean.
- Then go to **§D** below to ship the downstream `composeQ_phi`
  infrastructure.

### B.2 — Aristotle status = IN_PROGRESS / FAILED / NOT_FOUND

- **Do NOT re-poll.** Per CLAUDE.md, one check per cycle.
- Proceed to **§E** (left-action-only `Quotient.lift` infrastructure).

### B.3 — Aristotle status = COMPLETE but the proof does NOT verify

- The most likely failure modes are namespace drift (cycle 184
  precedent) or `derivativeWeightWithSrc` being unavailable in
  Aristotle's stub Section381. Spend at most 15 minutes on
  mechanical fixes (namespace prefixes, `open` directives).
- If still not verifying after 15 minutes, **abandon** and
  proceed to **§E**.

---

## C. (intentionally skipped — branching already in §B)

---

## D. Priority 1A — full right-action available, ship `composeQ_phi`

Reachable only if §B.1 succeeds. Deliverables:

### D.1 — `compose_phiEquivalent_compose` (full)

If Aristotle returned only the M₂-side sum equality (case (a) in §B.1),
package it into:

```lean
theorem compose_phiEquivalent_compose_right
    {s₁ s₂ s₂' : ℕ}
    (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) (M₂' : RKTableau s₂')
    (hPhi₂ : PhiEquivalent M₂ M₂') :
    PhiEquivalent (M₁.compose M₂) (M₁.compose M₂') := by
  intro t
  rw [compose_elementaryWeight_decomp M₁ M₂ t,
      compose_elementaryWeight_decomp M₁ M₂' t]
  congr 1
  exact <the_M2_side_equality_from_aristotle> M₁ hPhi₂ t
```

Then combine left + right actions via `PhiEquivalent.trans`:

```lean
theorem compose_phiEquivalent_compose
    {s₁ s₁' s₂ s₂' : ℕ}
    (M₁ : RKTableau s₁) (M₁' : RKTableau s₁')
    (M₂ : RKTableau s₂) (M₂' : RKTableau s₂')
    (hPhi₁ : PhiEquivalent M₁ M₁') (hPhi₂ : PhiEquivalent M₂ M₂') :
    PhiEquivalent (M₁.compose M₂) (M₁'.compose M₂') :=
  (compose_phiEquivalent_compose_left M₂ hPhi₁).trans
    (compose_phiEquivalent_compose_right M₁' hPhi₂)
```

**Faithfulness note**: `PhiEquivalent.trans` exists per cycle 030's
`PhiEquivalent` setoid construction (line ~135 in Section381.lean).
Verify the exact name with `lean_local_search "PhiEquivalent.trans"`
before writing the proof.

### D.2 — `composeQ_phi` via `Quotient.lift₂`

Mirror cycle 218's `composeQ`:

```lean
noncomputable def composeQ_phi :
    Quotient PhiEquivalent.setoidSigma →
    Quotient PhiEquivalent.setoidSigma →
    Quotient PhiEquivalent.setoidSigma := by
  refine Quotient.lift₂
    (fun p q => Quotient.mk' ⟨p.1 + q.1, p.2.compose q.2⟩) ?_
  rintro ⟨s₁, M₁⟩ ⟨s₂, M₂⟩ ⟨s₁', M₁'⟩ ⟨s₂', M₂'⟩ hPhi₁ hPhi₂
  apply Quotient.sound
  show @PhiEquivalent (s₁ + s₂) (s₁' + s₂')
        (M₁.compose M₂) (M₁'.compose M₂')
  exact compose_phiEquivalent_compose M₁ M₁' M₂ M₂' hPhi₁ hPhi₂
```

### D.3 — Bracketed-form corollary

```lean
theorem composeQ_phi_eq_of_phiEquivalent
    {s₁ s₁' s₂ s₂' : ℕ}
    {M₁ : RKTableau s₁} {M₁' : RKTableau s₁'}
    {M₂ : RKTableau s₂} {M₂' : RKTableau s₂'}
    (hPhi₁ : PhiEquivalent M₁ M₁') (hPhi₂ : PhiEquivalent M₂ M₂') :
    composeQ_phi ⟦⟨s₁, M₁⟩⟧ ⟦⟨s₂, M₂⟩⟧ =
      composeQ_phi ⟦⟨s₁', M₁'⟩⟧ ⟦⟨s₂', M₂'⟩⟧ := by
  show Quotient.mk _ _ = Quotient.mk _ _
  exact Quotient.sound
    (compose_phiEquivalent_compose M₁ M₁' M₂ M₂' hPhi₁ hPhi₂)
```

### D.4 — Non-vacuity (P2)

Two examples in `namespace OpenMath.Chapter3.Section381` at the end of
the file:

(i) Homogeneous:
```lean
example : composeQ_phi ⟦⟨2, paddedEuler⟩⟧ ⟦⟨2, paddedEuler⟩⟧ =
    ⟦⟨4, paddedEuler.compose paddedEuler⟩⟧ := rfl
```

(ii) Heterogeneous via `paddedEuler_phiEquivalent_pReduced`
(promoted by cycle 187):
```lean
example : composeQ_phi ⟦⟨2, paddedEuler⟩⟧ ⟦⟨2, paddedEuler⟩⟧ =
    composeQ_phi ⟦⟨1, paddedEuler.pReduced pairPartition⟩⟧
                 ⟦⟨1, paddedEuler.pReduced pairPartition⟩⟧ :=
  composeQ_phi_eq_of_phiEquivalent
    paddedEuler_phiEquivalent_pReduced
    paddedEuler_phiEquivalent_pReduced
```

### D.5 — Budget

~80 LOC across D.1–D.4 (D.1 is ~15 LOC if Aristotle's sum equality
is concise; D.2 is ~12 LOC; D.3 is ~10 LOC; D.4 is ~20 LOC; the rest
is docstrings).

---

## E. Priority 1B — Aristotle did NOT solve, ship `composeQ_phi_left_act`

Reachable from §B.2 or §B.3. The full binary `composeQ_phi` requires
both actions; with only the left action, we can still ship a
**one-sided** lift that is genuine, useful infrastructure:

`composeQ_phi_left_act : Quotient PhiEquivalent.setoidSigma →
                         (Σ s, RKTableau s) → Quotient PhiEquivalent.setoidSigma`

This treats the right argument as a **raw representative** (not a
quotient class). Well-definedness needs only that the LEFT argument
respects `PhiEquivalent`, which is exactly cycle 226's
`compose_phiEquivalent_compose_left`.

### E.1 — Definition

```lean
noncomputable def composeQ_phi_left_act :
    Quotient PhiEquivalent.setoidSigma →
    (Σ s, RKTableau s) → Quotient PhiEquivalent.setoidSigma := by
  refine fun p q => Quotient.lift
    (fun (r : Σ s, RKTableau s) =>
      Quotient.mk' ⟨r.1 + q.1, r.2.compose q.2⟩) ?_ p
  rintro ⟨s₁, M₁⟩ ⟨s₁', M₁'⟩ hPhi₁
  apply Quotient.sound
  show @PhiEquivalent (s₁ + q.1) (s₁' + q.1)
        (M₁.compose q.2) (M₁'.compose q.2)
  exact compose_phiEquivalent_compose_left q.2 hPhi₁
```

Place it in `namespace OpenMath.Chapter3.Section312.RKTableau`
immediately after cycle 226's
`compose_phiEquivalent_compose_left` (`Section381.lean:2858`).

### E.2 — `@[simp]` unfold lemma

```lean
@[simp] theorem composeQ_phi_left_act_mk
    {s₁ s₂ : ℕ} (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) :
    composeQ_phi_left_act ⟦⟨s₁, M₁⟩⟧ ⟨s₂, M₂⟩ =
      ⟦⟨s₁ + s₂, M₁.compose M₂⟩⟧ := rfl
```

### E.3 — Well-definedness theorem (the left-action lift theorem)

```lean
theorem composeQ_phi_left_act_eq_of_phiEquivalent
    {s₁ s₁' s₂ : ℕ}
    {M₁ : RKTableau s₁} {M₁' : RKTableau s₁'}
    (M₂ : RKTableau s₂)
    (hPhi₁ : PhiEquivalent M₁ M₁') :
    composeQ_phi_left_act ⟦⟨s₁, M₁⟩⟧ ⟨s₂, M₂⟩ =
      composeQ_phi_left_act ⟦⟨s₁', M₁'⟩⟧ ⟨s₂, M₂⟩ := by
  show Quotient.mk _ _ = Quotient.mk _ _
  exact Quotient.sound (compose_phiEquivalent_compose_left M₂ hPhi₁)
```

### E.4 — Non-vacuity (P2)

In `namespace OpenMath.Chapter3.Section381`:

```lean
example : composeQ_phi_left_act ⟦⟨2, paddedEuler⟩⟧ ⟨2, paddedEuler⟩ =
    ⟦⟨4, paddedEuler.compose paddedEuler⟩⟧ := rfl

example : composeQ_phi_left_act ⟦⟨2, paddedEuler⟩⟧ ⟨2, paddedEuler⟩ =
    composeQ_phi_left_act
      ⟦⟨1, paddedEuler.pReduced pairPartition⟩⟧ ⟨2, paddedEuler⟩ :=
  composeQ_phi_left_act_eq_of_phiEquivalent paddedEuler
    paddedEuler_phiEquivalent_pReduced
```

Confirm `paddedEuler_phiEquivalent_pReduced` is the cycle 187 promoted
theorem (`Section381.lean:1016`-ish). If the symbol name is slightly
different (e.g. `paddedEuler_pEquivalent_pReduced.toPhiEquivalent`),
use the closest available analog.

### E.5 — Budget

~50 LOC across E.1–E.4. The `Quotient.lift` plumbing in E.1 is the
main work; the rest is mechanical.

### E.6 — Document the partial-ship status

After landing E.1–E.4, append a short comment block right above E.1
in `Section381.lean`:

```
/-! ### Partial `composeQ_phi` — left action only

The full binary `composeQ_phi : Quot → Quot → Quot` requires both
`compose_phiEquivalent_compose_left` (cycle 226) and
`compose_phiEquivalent_compose_right` (deferred — see
`.prover-state/issues/cycle_226_compose_phi_right_action.md`).

`composeQ_phi_left_act` is the *one-sided* lift: the left argument
is a quotient class, the right is a raw representative. Useful for
formalising the left-multiplication action of the §383 group on
its underlying set; the full binary operation is a future cycle.
-/
```

---

## F. Verification (mandatory, all paths)

After §D or §E lands:

1. `lake env lean OpenMath/Chapter3/Section381.lean` — EXIT must be 0.
2. `grep -c "^[[:space:]]*sorry[[:space:]]*$\|:= sorry$" OpenMath/Chapter3/Section381.lean`
   — must be 0 (the cycle 216 docstring `sorry` mention does not
   count; the tactic-level sorry count must be 0).
3. **`lean_verify` axiom check** on the new public symbols:
   - §D path: `composeQ_phi`, `composeQ_phi_eq_of_phiEquivalent`,
     `compose_phiEquivalent_compose` — each must return
     `[propext, Classical.choice, Quot.sound]`.
   - §E path: `composeQ_phi_left_act`,
     `composeQ_phi_left_act_eq_of_phiEquivalent` — same axiom check.
4. **Regression spot-checks** (must remain axiom-clean):
   - `OpenMath.Chapter3.Section312.RKTableau.compose_phiEquivalent_compose_left` (cycle 226).
   - `OpenMath.Chapter3.Section312.RKTableau.composeQ_eq_of_equivalent` (cycle 218).
   - `OpenMath.Chapter3.Section312.RKTableau.instGroup` (cycle 222).
5. Warm rebuild time of `Section381.lean` should be ≤ 15 s. Anything
   higher than 30 s is a red flag — bisect by commenting out the new
   additions to identify the offending declaration.

---

## G. What NOT to do (explicit ban list)

- **DO NOT re-poll Aristotle.** One check per cycle (CLAUDE.md).
- **DO NOT attempt direct tree induction on the M₂-side sum
  equality.** Cycle 226 confirmed this does not close: the `t :: ts`
  expansion produces cross-terms
  `∑ i, j, M₂.b i * M₂.A i j * derivativeWeightWithSrc M₁ j t' *
  derivativeWeightWithSrcProd M₁ i ts` mixing outer `b`-weighting
  with inner `A`-recursion; per-summand reasoning fails.
- **DO NOT try to reduce to cycle 217's `compose_equivalent_compose`
  via a `PhiEquivalent → Equivalent` lemma.** That implication is
  Butcher's converse direction (requires Taylor expansion / B-series
  machinery), not formalized in this project.
- **DO NOT re-apply `compose_elementaryWeight_decomp` on the
  right-action goal.** Cycle 226 confirmed this is circular: the
  decomposition restates the same M₂-side sum equality.
- **DO NOT modify `compose_phiEquivalent_compose_left`** (cycle 226's
  shipped left-action). It is axiom-clean and load-bearing.
- **DO NOT attempt §441 Phase C.2.** 43rd consecutive GPFS block.
- **DO NOT modify `scripts/autonomous_loop.py`** (loop-maintainer
  territory; see `.prover-state/issues/phantom_commit_verdict_pattern.md`).
- **DO NOT introduce `axiom` or `constant` declarations.**
- **DO NOT raise `maxHeartbeats` above 200000.** If something stalls,
  decompose into smaller helpers.
- **DO NOT scaffold a `compose_phiEquivalent_compose_right` with
  `sorry` body.** Sorry count must remain 0 — see the cycle 200 →
  201 rollback precedent. If the right-action is not closeable in
  this cycle (i.e. Aristotle path §B.2/§B.3 was taken), ship §E
  (left-action-only `Quotient.lift`) cleanly and document the gap
  in prose (no `sorry`-d declaration).

---

## H. Pre-flagged risks

1. **R1 — `PhiEquivalent.trans` symbol name drift**: if §D.1 needs
   to compose left-action with right-action, verify the cycle 030
   transitivity lemma's exact name with `lean_local_search` /
   `lean_hover_info` before writing the proof. Candidates:
   `PhiEquivalent.trans` (most likely), `Setoid.iseqv.trans` (via
   the cycle 223 setoid), or unqualified `.trans` on
   `Setoid.r`-elements.

2. **R2 — Aristotle's stub Section381 may use different `private`
   names.** Cycle 184's namespace fix was a one-line patch
   (`M.αPoly_...` → `LinearMultistepMethod.αPoly_...`). The cycle
   226 submission includes `derivativeWeightWithSrc` (a cycle 225
   addition), which may or may not be in Aristotle's stub. If
   Aristotle's proof references symbols by stub names, port to
   the real `Section381.lean` namespace.

3. **R3 — `Quotient.lift` may need explicit setoid arguments** in
   §E.1. Mathlib's curried `Quotient.lift` should infer the source
   setoid from the function's domain type
   (`Quotient PhiEquivalent.setoidSigma`), but if Lean complains
   about ambiguity, supply the setoid explicitly. Defensive `show`
   after `rintro` (matching cycle 218's pattern) recommended.

4. **R4 — `paddedEuler_phiEquivalent_pReduced` may not be a direct
   theorem.** Cycle 187 promoted `paddedEuler_pEquivalent_pReduced`;
   the PhiEquivalent variant may need
   `paddedEuler_pEquivalent_pReduced.toPhiEquivalent` (via cycle 187's
   bridge). If §D.4 or §E.4 fails on the witness lookup, try the
   `.toPhiEquivalent` form; if that also fails, use
   `PhiEquivalent.refl paddedEuler` for the homogeneous case only
   and document the heterogeneous case as a known gap.

5. **R5 — `composeQ_phi_left_act` second-argument curry order**:
   Lean 4's `Quotient.lift` takes the function-to-lift first, then
   the respect proof, then the quotient class. Make sure the lambda
   in §E.1 binds `r` (the destructured first argument, the one being
   lifted) correctly. If Lean complains about implicit argument
   inference, swap to the explicit `Quotient.lift _ _` form with
   placeholders.

---

## I. Cycle pacing

- **0–10 min**: Read this strategy. Poll Aristotle (§B).
- **10–30 min**: Branch based on result.
  - §D path: incorporate proof, build D.1–D.4.
  - §E path: build E.1–E.4 + §E.6 doc comment.
- **30–50 min**: Verification (§F) and axiom checks. Fix any
  drift (namespace prefixes, symbol names, simp set).
- **50–60 min**: Update `.prover-state/task_results/cycle_227.md`,
  `extraction/formalization_data/lean_status.json`, `plan.md` row
  for `thm:384A`, and (if §D path was taken) close the
  `.prover-state/issues/cycle_226_compose_phi_right_action.md` issue
  file with a "Resolved cycle 227" note.

---

## J. Update `lean_status.json` and `plan.md`

### Path §D (full theorem shipped)

- `thm:384A` row: status remains `partial` but with cycle 227 note
  recording `composeQ_phi` shipped. Full `formalized` status awaits
  the actual §384 thm:384A "Φ is a group homomorphism" claim, which
  needs both quotient groups' multiplications to commute under Φ.
  Cycle 227 ships the *prerequisite* `composeQ_phi`; cycle 228+ will
  ship the homomorphism theorem itself.

### Path §E (left-action lift only)

- `thm:384A` row: status remains `partial`. Update the note to record
  cycle 227's `composeQ_phi_left_act` deliverable; note that the full
  binary `composeQ_phi` remains blocked on the M₂-side right-action.

In both paths, add a sentence in the `plan.md` `thm:384A` row noting
the cycle 227 outcome (full binary vs left-action-only).

---

## K. Cycle 228+ outlook

### If §D shipped (full `composeQ_phi`)

Next deliverables for the §383+ chain:
1. **`composeQ_phi_assoc`** — quotient-level associativity for
   `composeQ_phi`, via `Quotient.inductionOn₃` + cycle 187's
   `PReducesTo.toPhiEquivalent` applied to the underlying
   `Equivalent`-level associativity (cycle 221).
2. **`composeQ_phi_id_left` / `composeQ_phi_id_right`** —
   identity-element absorption laws on `Quotient PhiEquivalent.setoidSigma`.
3. **`instance : Group (Quotient PhiEquivalent.setoidSigma)`** —
   the §383 group structure on the Φ-quotient.
4. **`thm:384A` proper** — the formal group homomorphism
   `Φ : Quotient Equivalent.setoidSigma →* Quotient PhiEquivalent.setoidSigma`.

Estimated 3–4 cycles after cycle 227.

### If §E shipped (left-action only)

Next priorities:
1. **Cycle 228**: re-poll Aristotle on
   `176aa964-db7b-40f8-a01c-05247c186ec5` once more (single poll
   discipline applies — at most once per cycle, even on follow-up).
   If still IN_PROGRESS, consider canceling and submitting a
   tighter, more focused job specifically on the M₂-side sum
   equality with cycle 225's `derivativeWeightWithSrc` machinery
   as in-context templates.
2. **Cycle 228 alternative**: build the §383 group structure on
   `Equivalent`-quotient consumers of `composeQ_phi_left_act` (e.g.
   the action of an `Equivalent`-class on a `PhiEquivalent`-raw
   representative).
3. **Cycle 229+**: pursue the Connes-Kreimer Hopf-coproduct
   formalization (multi-cycle, ~5–10 cycles), or wait for an
   alternative proof of the right-action to surface.
