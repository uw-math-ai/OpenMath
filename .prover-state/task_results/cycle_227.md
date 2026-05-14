# Cycle 227 Results

## Worked on
§383 group-homomorphism path **Phase 3 follow-up** — shipped the
one-sided `Quotient.lift` `composeQ_phi_left_act` consuming cycle
226's `compose_phiEquivalent_compose_left`. Strategy §E path
(Aristotle's right-action job remains IN_PROGRESS).

## Approach

### Priority 0 — single Aristotle poll
Polled project `176aa964-db7b-40f8-a01c-05247c186ec5` (the M₂-side
sum equality / right-action half of `compose_phiEquivalent_compose`):

- **Status**: IN_PROGRESS at 9 % complete
- Created: 2026-05-14T15:50:23 UTC
- Last updated: 2026-05-14T16:10:00 UTC (~20 minutes after submission)

Per strategy §B.2, **did not re-poll**. Branched to §E
(left-action-only `Quotient.lift` infrastructure).

### Priority 1B — `composeQ_phi_left_act` (§E)

Three new symbols at `OpenMath/Chapter3/Section381.lean`, all placed
in `namespace OpenMath.Chapter3.Section312.RKTableau` immediately
after cycle 226's `compose_phiEquivalent_compose_left` (closing
`end` of the cycle 226 `section ... open OpenMath.Chapter3.Section310 ... end`
at line 2860):

1. **E.1 — `composeQ_phi_left_act`** (`noncomputable def`,
   `Section381.lean:2880`-ish):
   ```
   noncomputable def composeQ_phi_left_act :
       Quotient PhiEquivalent.setoidSigma →
       (Σ s : ℕ, RKTableau s) → Quotient PhiEquivalent.setoidSigma :=
     fun p q => Quotient.lift
       (fun r : Σ s : ℕ, RKTableau s =>
         Quotient.mk PhiEquivalent.setoidSigma
           ⟨r.1 + q.1, r.2.compose q.2⟩)
       (by
         rintro ⟨s₁, M₁⟩ ⟨s₁', M₁'⟩ hPhi₁
         apply Quotient.sound
         show @PhiEquivalent (s₁ + q.1) (s₁' + q.1)
           (M₁.compose q.2) (M₁'.compose q.2)
         exact compose_phiEquivalent_compose_left q.2 hPhi₁)
       p
   ```
   Left argument is a `PhiEquivalent.setoidSigma`-quotient class;
   right argument is a raw `(Σ s, RKTableau s)` representative
   (NOT a quotient — the right-action half is still open).

2. **E.2 — `composeQ_phi_left_act_mk`** (`@[simp]`-tagged
   concrete-representative unfold lemma):
   ```
   @[simp] theorem composeQ_phi_left_act_mk
       {s₁ s₂ : ℕ} (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) :
       composeQ_phi_left_act
           (Quotient.mk PhiEquivalent.setoidSigma ⟨s₁, M₁⟩)
           ⟨s₂, M₂⟩ =
         Quotient.mk PhiEquivalent.setoidSigma
           ⟨s₁ + s₂, M₁.compose M₂⟩ :=
     rfl
   ```
   `Quotient.lift f h ⟦x⟧ = f x` reduces definitionally, so `rfl` closes.

3. **E.3 — `composeQ_phi_left_act_eq_of_phiEquivalent`** (the
   well-definedness theorem — the actual content of the left-action
   lift):
   ```
   theorem composeQ_phi_left_act_eq_of_phiEquivalent
       {s₁ s₁' s₂ : ℕ}
       {M₁ : RKTableau s₁} {M₁' : RKTableau s₁'}
       (M₂ : RKTableau s₂)
       (hPhi₁ : PhiEquivalent M₁ M₁') :
       composeQ_phi_left_act
           (Quotient.mk PhiEquivalent.setoidSigma ⟨s₁, M₁⟩) ⟨s₂, M₂⟩ =
         composeQ_phi_left_act
           (Quotient.mk PhiEquivalent.setoidSigma ⟨s₁', M₁'⟩)
           ⟨s₂, M₂⟩ := by
     show Quotient.mk _ _ = Quotient.mk _ _
     exact Quotient.sound (compose_phiEquivalent_compose_left M₂ hPhi₁)
   ```

### E.4 — Non-vacuity (two P2 examples)

Placed in `namespace OpenMath.Chapter3.Section381` at the file's
bottom, immediately after cycle 226's `compose_phiEquivalent_compose_left`
non-vacuity examples:

(i) **Homogeneous** — `rfl` via E.2:
```
example :
    RKTableau.composeQ_phi_left_act
        (Quotient.mk RKTableau.PhiEquivalent.setoidSigma ⟨2, paddedEuler⟩)
        ⟨2, paddedEuler⟩ =
      Quotient.mk RKTableau.PhiEquivalent.setoidSigma
        ⟨4, paddedEuler.compose paddedEuler⟩ :=
  rfl
```

(ii) **Heterogeneous-stage** — uses cycle 187's `pReduced_phiEquivalent`
on the cycle 186 P-reducibility witness:
```
example :
    RKTableau.composeQ_phi_left_act
        (Quotient.mk RKTableau.PhiEquivalent.setoidSigma ⟨2, paddedEuler⟩)
        ⟨2, paddedEuler⟩ =
      RKTableau.composeQ_phi_left_act
        (Quotient.mk RKTableau.PhiEquivalent.setoidSigma
          ⟨1, paddedEuler.pReduced pairPartition⟩)
        ⟨2, paddedEuler⟩ :=
  RKTableau.composeQ_phi_left_act_eq_of_phiEquivalent paddedEuler
    (pReduced_phiEquivalent paddedEuler
      paddedEuler_isPReducibleVia_pairPartition)
```

This exercises the asymmetry — the *left* argument's class is
heterogeneous (2 stages vs 1 stage), the *right* argument is fixed
(2 stages) — exactly the structure that `composeQ_phi_left_act` is
designed to express.

### E.6 — Documentation comment block
A docstring block above E.1 (`/-! ### Partial composeQ_phi — left
action only (cycle 227) ... -/`) records:
- that the full binary `composeQ_phi` requires both actions;
- the cycle 226 issue file reference for the right-action;
- the intended use case (§383 left-multiplication action).

## Result

**SUCCESS** — all five §E deliverables shipped, all axiom-clean.

### Verification (§F)
1. `lake env lean OpenMath/Chapter3/Section381.lean` — EXIT 0,
   **13.889s** (well under §F.5's 30s red-flag threshold; comparable
   to cycle 226's 13.6s baseline).
2. Tactic-level sorry count: **0** (41st consecutive clean cycle
   since cycle 201 rollback).
3. `lean_verify` axiom checks on the three new public symbols:
   - `OpenMath.Chapter3.Section312.RKTableau.composeQ_phi_left_act` →
     `[propext, Classical.choice, Quot.sound]` ✓
   - `OpenMath.Chapter3.Section312.RKTableau.composeQ_phi_left_act_mk` →
     `[propext, Classical.choice, Quot.sound]` ✓
   - `OpenMath.Chapter3.Section312.RKTableau.composeQ_phi_left_act_eq_of_phiEquivalent` →
     `[propext, Classical.choice, Quot.sound]` ✓
4. Regression spot-checks (all axiom-clean, no regressions):
   - `OpenMath.Chapter3.Section312.RKTableau.compose_phiEquivalent_compose_left`
     (cycle 226) ✓
   - `OpenMath.Chapter3.Section312.RKTableau.composeQ_eq_of_equivalent`
     (cycle 218) ✓
   - `OpenMath.Chapter3.Section312.RKTableau.instGroup` (cycle 222) ✓

## Faithfulness check

This cycle introduces *infrastructure* (a `Quotient.lift` of an
already-formalized operation), not a new mathematical theorem. The
underlying mathematical content (the left-action of compose under
PhiEquivalent) is cycle 226's `compose_phiEquivalent_compose_left`.

For each new `def`/`theorem`:

### `composeQ_phi_left_act` (def)
- Entity ID: prerequisite infrastructure for `thm:384A` (no
  dedicated entity in `formalization_data/entities/`)
- Textbook concept being captured:
  > "Equivalence classes of Runge–Kutta methods form a group under
  > composition" (Butcher §382), with the §383 group-homomorphism
  > sending `Equivalent`-class to `PhiEquivalent`-class.
- Lean statement captures: *partial* — only the left-multiplication
  action on a raw representative is shipped. The full binary
  operation requires the right-action half (deferred).
- Justification for partial ship: prevents stalling the §383 chain
  while Aristotle's right-action job runs; sorry count must remain
  0 per cycle 200→201 rollback precedent.

### `composeQ_phi_left_act_mk` (theorem, `@[simp]`)
- Textbook content: none — pure computational unfold lemma.
- Lean statement captures: definitional unfolding of E.1 on
  concrete representatives (the analog of cycle 218's
  `composeQ`-unfold pattern at line 3067).
- Tautology check: no — concludes `composeQ_phi_left_act ⟦x⟧ y = ⟦x.compose y⟧`;
  this is *not* a hypothesis but a consequence of `Quotient.lift`
  beta-reduction.
- Identity check: not `exact h`; uses `rfl` on a definitional
  equality, which is genuine computational work (Lean must reduce
  `Quotient.lift f h ⟦x⟧` to `f x`).

### `composeQ_phi_left_act_eq_of_phiEquivalent` (theorem)
- Textbook concept: the *underlying* mathematical content is
  "Φ-equivalent left factors produce Φ-equivalent composites"
  — formalized by cycle 226's `compose_phiEquivalent_compose_left`.
  This theorem is the *quotient-level corollary* of that.
- Lean statement captures: same content as cycle 226 in the more
  consumer-friendly quotient form (cf. cycle 218's
  `composeQ_eq_of_equivalent` for the analogous `Equivalent`-side
  pattern).
- Tautology check: no — concludes equality of quotient classes
  under the `PhiEquivalent` left-argument hypothesis.
- Identity check: proof is `show … ; exact Quotient.sound (…)` —
  delegates to the cycle 226 mathematical content via
  `Quotient.sound`. Non-trivial because `Quotient.sound`'s axiom
  (`Quot.sound`) is doing the work.
- Hypothesis strength check: only `PhiEquivalent M₁ M₁'` — exactly
  the textbook hypothesis. Matches cycle 226's hypothesis.

### Two `example`s (P2 non-vacuity)
- Both `example`s witness `composeQ_phi_left_act` on concrete inputs
  (`paddedEuler` and its P-reduction). No abstractions remain
  un-witnessed. Both anchor to existing cycle 186/187 P-reducibility
  witnesses.

## Dead ends
None this cycle — the §E path was the strategy's pre-committed
fallback for Aristotle IN_PROGRESS, and all five sub-deliverables
landed first try.

A minor wrinkle: the strategy E.4 used `⟦⟨2, paddedEuler⟩⟧` syntax,
but `Σ s, RKTableau s` has *two* `Setoid` instances in scope
(`Equivalent.setoidSigma` and `PhiEquivalent.setoidSigma`), which
would create typeclass-resolution ambiguity. Adopted the existing
file convention (cf. lines 1983–1987's PhiEquivalent.setoidSigma
non-vacuity example) of using explicit
`Quotient.mk RKTableau.PhiEquivalent.setoidSigma ⟨...⟩` throughout
the new non-vacuity examples. No correctness impact.

## Discovery

### D1 — `Quotient.lift` curry order for binary partial lifts
The cleanest curry order for a one-sided lift (left arg is a
quotient, right arg is raw) is:
```
fun p q => Quotient.lift
  (fun r => ... ⟨r.1 + q.1, r.2.compose q.2⟩)
  (by ...)
  p
```
The lambda binds `q` (the raw arg) *outside* the `Quotient.lift`, so
`q.1` and `q.2` appear inside both the function-being-lifted and the
respect proof. This pattern generalizes to any "lift one arg, keep
the other raw" definition.

### D2 — `⟦...⟧` and dual Setoid instances on `Σ s, RKTableau s`
With both `Equivalent.setoidSigma` and `PhiEquivalent.setoidSigma`
registered as instances, `⟦x⟧` syntax becomes ambiguous (typeclass
resolution picks one but the choice depends on resolution order).
File convention (lines 1983–1987): always use
`Quotient.mk PhiEquivalent.setoidSigma ⟨...⟩` or
`Quotient.mk Equivalent.setoidSigma.{u} ⟨...⟩` to disambiguate.
This convention propagated cleanly into cycle 227's non-vacuity.

### D3 — Aristotle 9 % progress at +20 min suggests ETA ≥ several hours
The right-action sum equality is structurally hard (mixes outer
`b`-weighting with inner `A`-recursion on `derivativeWeightWithSrc`).
9 % at +20 min hints either at a slow exploration phase or a high
search cost. Strategy §K cycle 228 outlook suggests a single re-poll
next cycle, followed by either incorporation or refocused submission.

## Suggested next approach

Cycle 228 (preferred, in priority order):

1. **Single Aristotle re-poll** on `176aa964-db7b-40f8-a01c-05247c186ec5`
   (strategy §K). If COMPLETE with a verifying proof, promote to
   full `composeQ_phi` per strategy §D (full binary `Quotient.lift₂`,
   bracketed-form corollary, homogeneous + heterogeneous non-vacuity).

2. **If still IN_PROGRESS**, consider canceling and submitting a
   *tighter* Aristotle job: bundle cycle 225's
   `derivativeWeightWithSrc` machinery and cycle 226's
   `derivativeWeightWithSrc_subst_M₁` as in-context templates, and
   ask for *just* the M₂-side sum equality (not the full
   `compose_phiEquivalent_compose_right` packaging — Aristotle's
   prior submission was already at this granularity).

3. **If §1 and §2 both blocked**, build *downstream consumers* of
   `composeQ_phi_left_act`. Two candidates:
   - **Cycle 228A**: `composeQ_phi_left_act_compose_left_id` —
     `composeQ_phi_left_act ⟦⟨0, id⟩⟧ ⟨s, M⟩ = ⟦⟨s, M⟩⟧` (the
     identity-element absorption on the *left* side of the action).
     Proof should mirror cycle 219's `id_compose_equivalent`
     pattern but at the PhiEquivalent level.
   - **Cycle 228B**: `composeQ_phi_left_act_id_left_act` — the
     0-stage class's left-action is the identity map. Both are
     ~30-40 LOC ports of cycle 219.

4. **§441 Phase C.2** remains GPFS-blocked (44th consecutive cycle).

Cycle 229+ if the right-action lands:
- Ship full `composeQ_phi` (binary `Quotient.lift₂`) and bracketed-form corollary.
- `composeQ_phi_assoc` via `Quotient.inductionOn₃` (port cycle 221).
- `composeQ_phi_id_left` / `_id_right` (port cycle 219).
- `instance : Group (Quotient PhiEquivalent.setoidSigma)` (port cycle 222).
- `thm:384A` proper — the group homomorphism Φ from
  `Quotient Equivalent.setoidSigma` to
  `Quotient PhiEquivalent.setoidSigma`.

Pre-flagged risks for cycle 228:
- **R1**: Aristotle's right-action proof, if returned, may reference
  Aristotle's stub `Section381.lean` namespace. Port mechanically
  (cycle 184 precedent: `M.αPoly_...` → `LinearMultistepMethod.αPoly_...`).
- **R2**: Re-poll vs re-submission decision should default to
  re-poll first (single check per cycle per CLAUDE.md). Cancellation
  + resubmission is a separate decision.
- **R3**: The §F.5 warm-rebuild budget (15s target / 30s red flag)
  is comfortable at 13.9s; cycle 228 should preserve this margin
  even with new symbols.
