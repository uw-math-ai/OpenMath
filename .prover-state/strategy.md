# Cycle 236 Strategy

## TL;DR

**Ship the `Group` instance on `Quotient PhiEquivalent.setoidSigma`** —
the §383 codomain group whose four axioms cycles 233/234/235 have all
been closing at the `PhiEquivalent` level. Template is verbatim cycle
222's §382 `Group` instance work; with cycle 235's
`inverse_phiEquivalent_inverse` + `compose_inverse_phiEquivalent` +
`inverse_compose_phiEquivalent` now in hand, the lift is mechanical.

Expected ~80–100 LOC for four new symbols + four `instance` declarations
+ P2 typeclass-level non-vacuity. **Single-cycle deliverable; no
multi-cycle work, no Aristotle batches.**

§441 Phase C.2 — **skip again** (41st consecutive GPFS-timeout cycle).

---

## §A — §441 Phase C.2 status (skip)

GPFS pathology on `OpenMath/Chapter4/Section441.lean` has now reproduced
across cycles 182–235 (40+ consecutive smoke-test timeouts, 50+ calendar
days). Loop-maintainer escalation in
`.prover-state/issues/cycle_182_gpfs_slowness.md` is in force.

**Do NOT smoke-test Section441.lean.** Do NOT submit the cycle 182
draft. Continue Section381-focused work. If GPFS ever recovers, the
cycle 182 draft + cycle 184 namespace fix are preserved at
`.prover-state/cycle_182_draft_section441.lean`.

---

## §B — Priority 1: §383 `Group` instance on `Quotient PhiEquivalent.setoidSigma`

### Context (what's already shipped)

Cycle 232 shipped:
* `noncomputable def composeQ_phi : Quotient PhiEquivalent.setoidSigma →
  Quotient PhiEquivalent.setoidSigma → Quotient PhiEquivalent.setoidSigma`
  via `Quotient.lift₂` (the `Mul` operation).
* `@[simp] composeQ_phi_mk` rfl unfold.

Cycle 233 shipped:
* `composeQ_phi_assoc` (associativity at the quotient level).

Cycle 234 shipped:
* `composeQ_phi_id_left`, `composeQ_phi_id_right` (the identity element
  is `⟦⟨0, RKTableau.id⟩⟧`).

Cycle 235 shipped:
* `inverse_phiEquivalent_inverse` (well-definedness of `M.inverse` on
  PhiEquivalent classes).
* `compose_inverse_phiEquivalent` (right absorption at PhiEquivalent
  level).
* `inverse_compose_phiEquivalent` (left absorption at PhiEquivalent
  level).

### Cycle 236 deliverables (the four `instance` package)

**Place all new symbols at `OpenMath/Chapter3/Section381.lean` inside
`namespace OpenMath.Chapter3.Section312.RKTableau`, immediately after
cycle 235's `inverse_phiEquivalent_inverse` block (around line 4240).**
The §382 analog sits at lines 4513–4579; mirror that structure with
`_phi`-suffixed names.

**Deliverable 1: `inverseQ_phi` (~10 LOC).**
The `Inv` operation, lifting `RKTableau.inverse` through
`Quotient.lift` with cycle 235's `inverse_phiEquivalent_inverse` as the
respect witness. Verbatim port of cycle 222's `inverseQ` (line 4513),
swap `Equivalent` → `PhiEquivalent` everywhere.

```lean
/-- *Lift of `RKTableau.inverse` to `Quotient PhiEquivalent.setoidSigma`.*
The `Inv` operation for the §383 `Group` instance. Well-defined by
cycle 235's `inverse_phiEquivalent_inverse`: Φ-equivalent methods
map to Φ-equivalent inverses. -/
noncomputable def inverseQ_phi :
    Quotient PhiEquivalent.setoidSigma →
    Quotient PhiEquivalent.setoidSigma :=
  Quotient.lift
    (fun (p : Σ s : ℕ, RKTableau s) =>
      Quotient.mk PhiEquivalent.setoidSigma ⟨p.1, p.2.inverse⟩)
    (by
      rintro ⟨s, M⟩ ⟨s', M'⟩ hPhi
      apply Quotient.sound
      show PhiEquivalent M.inverse M'.inverse
      exact inverse_phiEquivalent_inverse hPhi)
```

**Deliverable 2: `@[simp] inverseQ_phi_mk` (~5 LOC).** Definitional
unfold, proved by `rfl` (since `Quotient.lift` reduces definitionally
on `Quotient.mk`). Mirror of cycle 222's `inverseQ_mk` at line 4528.

```lean
@[simp] theorem inverseQ_phi_mk {s : ℕ} (M : RKTableau s) :
    inverseQ_phi (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩)
      = Quotient.mk PhiEquivalent.setoidSigma ⟨s, M.inverse⟩ := rfl
```

**Deliverable 3: `composeQ_phi_inverseQ_phi_left` (~7 LOC).**
Pointwise lift of cycle 235's `inverse_compose_phiEquivalent` to all
quotient classes via `Quotient.inductionOn`. Mirror of cycle 222's
`composeQ_inverseQ_left` at line 4536.

```lean
/-- *Left inverse absorption for `inverseQ_phi` against `composeQ_phi`
at every quotient class.* Pointwise form of cycle 235's
`inverse_compose_phiEquivalent`, used in the `Group` typeclass
instance's `inv_mul_cancel` field. -/
theorem composeQ_phi_inverseQ_phi_left
    (q : Quotient PhiEquivalent.setoidSigma) :
    composeQ_phi (inverseQ_phi q) q
      = Quotient.mk PhiEquivalent.setoidSigma ⟨0, RKTableau.id⟩ := by
  refine Quotient.inductionOn q ?_
  rintro ⟨s, M⟩
  show composeQ_phi _ _ = _
  exact Quotient.sound (inverse_compose_phiEquivalent M)
```

**Risk on the `show` line.** Cycle 222's analog uses
`show composeQ _ _ = _`. The `composeQ_phi` constructor on a single
`Quotient.mk` representative reduces by `composeQ_phi_mk` (simp lemma);
if Lean has trouble matching the LHS pattern, replace with explicit
`change Quotient.mk PhiEquivalent.setoidSigma ⟨s + 0, _⟩ = _` or
unfold via `rw [inverseQ_phi_mk, composeQ_phi_mk]` then
`exact Quotient.sound …`.

**Deliverable 4: `instGroup_phi` typeclass package (~25 LOC).**
The four-instance bundle assembled via `Group.ofLeftAxioms`. Verbatim
port of cycle 222's package at lines 4553–4579. The instances live
inside `namespace OpenMath.Chapter3.Section312.RKTableau` (so they
attach to the `Quotient PhiEquivalent.setoidSigma` type without name
clash with the §382 instances under `Equivalent.setoidSigma`).

```lean
/-! ### §383 `Group` instance on `Quotient PhiEquivalent.setoidSigma`

Assembles the four §383 group axioms (associativity from cycle 233,
identity from cycle 234, inverse from cycle 235's
`inverse_compose_phiEquivalent`, and `inverseQ_phi` lift from this
cycle) into the `Group` typeclass on `Quotient PhiEquivalent.setoidSigma`.
Uses `Group.ofLeftAxioms`; the right-side analogues
(`mul_one`, `mul_inv_cancel`) follow automatically. -/

noncomputable instance instOne_phi :
    One (Quotient PhiEquivalent.setoidSigma) :=
  ⟨Quotient.mk PhiEquivalent.setoidSigma ⟨0, RKTableau.id⟩⟩

noncomputable instance instMul_phi :
    Mul (Quotient PhiEquivalent.setoidSigma) :=
  ⟨composeQ_phi⟩

noncomputable instance instInv_phi :
    Inv (Quotient PhiEquivalent.setoidSigma) :=
  ⟨inverseQ_phi⟩

/-- *§383 `Group` instance on `Quotient PhiEquivalent.setoidSigma`.*
The fourth and final §383 group structure axiom shipping: with cycle
232's `composeQ_phi` (`Mul`), cycle 234's `⟦⟨0, RKTableau.id⟩⟧` as
`One`, cycle 235's inverse-absorption laws, cycle 233's associativity,
and this cycle's `inverseQ_phi` (`Inv`), the four-axiom `Group`
typeclass assembles via `Group.ofLeftAxioms`. The §383 codomain of
the homomorphism Φ : §382 group → §383 group (still TODO; see
`thm:384A`). -/
noncomputable instance instGroup_phi :
    Group (Quotient PhiEquivalent.setoidSigma) :=
  Group.ofLeftAxioms
    composeQ_phi_assoc
    composeQ_phi_id_left
    composeQ_phi_inverseQ_phi_left
```

**Required import.** Cycle 222 needed `import Mathlib.Algebra.Group.MinimalAxioms`
for `Group.ofLeftAxioms`. Verify it's already in the file (it should
be from cycle 222's work). Run `grep -n "MinimalAxioms"
OpenMath/Chapter3/Section381.lean`; if absent, add the import at the
top of the file.

### Deliverable 5: P2 non-vacuity at the typeclass level (~25 LOC)

Place in `namespace OpenMath.Chapter3.Section381` near the end of the
file (after cycle 235's three `paddedEuler` PhiEquivalent witnesses
at lines ~5165–5190). Mirror cycle 222's typeclass witnesses (which
live around lines 4910–4930 of Section381.lean — search for
`mul_inv_cancel` / `inv_mul_cancel` within the
`namespace OpenMath.Chapter3.Section381` block).

```lean
/-- *Cycle 236 non-vacuity for `inverseQ_phi_mk`.* Definitional unfold
on `⟦⟨2, paddedEuler⟩⟧`. -/
example :
    RKTableau.inverseQ_phi
        (Quotient.mk RKTableau.PhiEquivalent.setoidSigma
          ⟨2, paddedEuler⟩)
      = Quotient.mk RKTableau.PhiEquivalent.setoidSigma
          ⟨2, paddedEuler.inverse⟩ :=
  rfl

/-- *Cycle 236 non-vacuity for `instGroup_phi.mul_inv_cancel`.*
Exercises the typeclass-derived right inverse law on the
`⟦⟨2, paddedEuler⟩⟧` class via the §383 `Group` instance. -/
example :
    (Quotient.mk RKTableau.PhiEquivalent.setoidSigma
        ⟨2, paddedEuler⟩)
      * (Quotient.mk RKTableau.PhiEquivalent.setoidSigma
            ⟨2, paddedEuler⟩)⁻¹
      = (1 : Quotient RKTableau.PhiEquivalent.setoidSigma) :=
  mul_inv_cancel _

/-- *Cycle 236 non-vacuity for `instGroup_phi.inv_mul_cancel`.*
Exercises the typeclass-derived left inverse law on the
`⟦⟨2, paddedEuler⟩⟧` class via the §383 `Group` instance. -/
example :
    (Quotient.mk RKTableau.PhiEquivalent.setoidSigma
        ⟨2, paddedEuler⟩)⁻¹
      * (Quotient.mk RKTableau.PhiEquivalent.setoidSigma
            ⟨2, paddedEuler⟩)
      = (1 : Quotient RKTableau.PhiEquivalent.setoidSigma) :=
  inv_mul_cancel _
```

**Risk on the typeclass `*` / `⁻¹` / `1` notation in §381 namespace.**
The §382 `Group` instance lives on `Quotient Equivalent.setoidSigma`;
the §383 instance lives on `Quotient PhiEquivalent.setoidSigma`. Lean
elaborator must pick the right instance from the explicit
`Quotient.mk` annotation. If it gets confused, annotate explicitly:
`(... : Quotient RKTableau.PhiEquivalent.setoidSigma) * ...`.

---

## §C — Step-by-step execution plan

1. **(2 min) Verify §441 GPFS state.** One smoke test:
   `time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean`
   on HEAD. Expected: timeout (41st consecutive). Log to
   `cycle_182_gpfs_slowness.md` cycle 236 row + `attempts.md`. Do NOT
   continue to Section441 work; skip to step 2.

2. **(2 min) Pre-flight verification.**
   * `grep -n "import Mathlib.Algebra.Group.MinimalAxioms"
     OpenMath/Chapter3/Section381.lean` — confirm presence (cycle 222
     added it). If missing, add at top.
   * `grep -n "inverse_phiEquivalent_inverse\|compose_inverse_phiEquivalent\|inverse_compose_phiEquivalent"
     OpenMath/Chapter3/Section381.lean` — confirm all three at HEAD.
   * `grep -n "composeQ_phi_assoc\|composeQ_phi_id_left" OpenMath/Chapter3/Section381.lean`
     — confirm cycle 233/234 landmarks at HEAD.

3. **(20 min) Insert Deliverables 1–4** in
   `namespace OpenMath.Chapter3.Section312.RKTableau`, immediately
   after cycle 235's `inverse_phiEquivalent_inverse` (line ~4240). The
   §383 instance package mirrors cycle 222's §382 package at lines
   4513–4579 — copy-paste-edit, swap `Equivalent` → `PhiEquivalent`,
   `composeQ` → `composeQ_phi`, `inverseQ` → `inverseQ_phi`,
   `composeQ_assoc` → `composeQ_phi_assoc`, etc.

4. **(10 min) Insert Deliverable 5 (P2 examples)** in
   `namespace OpenMath.Chapter3.Section381` at the end of the file
   after cycle 235's witnesses (~line 5190).

5. **(5 min) Compile + axiom-check.** Run:
   ```
   time lake env lean OpenMath/Chapter3/Section381.lean
   ```
   Expected: clean exit. Warm rebuild ≤ 15 s (file is large; warm
   times have been ~6–10 s).

6. **(3 min) Axiom verification.** Use `lean_verify` on each of the
   four new public symbols (`inverseQ_phi`, `inverseQ_phi_mk`,
   `composeQ_phi_inverseQ_phi_left`, `instGroup_phi`). Expected:
   `[propext, Classical.choice, Quot.sound]` only.

7. **(5 min) Regression spot-check.** Use `lean_verify` on cycle 232's
   `composeQ_phi`, cycle 233's `composeQ_phi_assoc`, cycle 234's
   `composeQ_phi_id_left`, cycle 235's `inverse_phiEquivalent_inverse`.
   Expected: all axiom-clean (no changes from cycle 235's state).

8. **(3 min) Sorry-count + tautology-scanner verification.**
   * `grep -cn "^[^-]*sorry[^_]" OpenMath/Chapter3/Section381.lean`
     should return 0 (the only "sorry" hit is in a docstring at line
     3589; the regex `[^-]*sorry[^_]` excludes "sorry-scaffold").
   * `grep -E '\bexact\s+h_\w+\s*$|^[^-]*:= h_\w+\s*$|:=\s*id\s*$'
     OpenMath/Chapter3/Section381.lean` should return nothing.

9. **(10 min) Documentation updates.**
   * `extraction/formalization_data/lean_status.json` — update
     `thm:384A` row: bump cycle to 236; note `instGroup_phi` shipped.
   * `plan.md` — update `thm:384A` row with cycle 236 outcome
     (still `[~]` because Φ itself is the cycle 237+ deliverable;
     cycle 236 closes only the codomain group).
   * `.prover-state/task_results/cycle_236.md` — full deliverable
     record per CLAUDE.md format.
   * `.prover-state/issues/cycle_182_gpfs_slowness.md` — append cycle
     236 row to the timeout log.

10. **(2 min) Commit.** Single commit message
    `Cycle 236 — §383 group-hom path Phase 5: Group instance on
    Quotient PhiEquivalent.setoidSigma SHIPPED.` Body documents the
    four new symbols + P2 non-vacuity + faithfulness note (the
    instance is the §384 codomain group, not Φ itself).

**Total target: ~60 min of active work.**

---

## §D — What NOT to try

* **Do NOT smoke-test or modify `Section441.lean`.** GPFS pathology is
  41st-consecutive. Skip entirely.
* **Do NOT ship Φ : §382 group → §383 group `MonoidHom`.** That's
  cycle 237+ work. Cycle 236 ships only the codomain group; the
  homomorphism requires a separate `Quotient.lift` plus a
  `Equivalent → PhiEquivalent` direction (the easy direction of
  `thm:381H`, since `Equivalent ⊆ PhiEquivalent` follows from cycle
  217's `compose_equivalent_compose` plus the existence of an
  `Equivalent → PhiEquivalent` lemma which is NOT currently shipped
  — cycle 237 must check carefully whether this is single-cycle
  closeable or whether it's the deferred direction in
  `thm_381H_deferred.md`).
* **Do NOT batch-submit to Aristotle.** Cycle 222 was a clean
  single-cycle ship without Aristotle; cycle 236 is the verbatim
  PhiEquivalent analog. Manual close in <60 min.
* **Do NOT touch `compose_assoc` (cycle 210's deferred HEq blocker).**
  Cycle 233's `compose_assoc_phiEquivalent` already finesses it at
  the `PhiEquivalent` level. Cycle 236 consumes that, not the raw
  HEq form.
* **Do NOT introduce `axiom` or `constant` for any of the four
  axioms.** All four were closed in cycles 232–235; cycle 236 is
  pure plumbing.
* **Do NOT raise `maxHeartbeats`.** The proofs are short (≤10 LOC
  each); default heartbeats are sufficient.
* **Do NOT attempt to retire cycle 222's `inverseQ`/`instGroup` on
  the §382 side.** They coexist with the new §383 `_phi`-suffixed
  instances. Both groups live; cycle 237+'s Φ : G_§382 → G_§383
  homomorphism *needs* both.
* **Do NOT rename cycle 235's `inverse_phiEquivalent_inverse`.** It's
  the load-bearing well-definedness theorem; the cycle 236 work
  consumes it verbatim through `Quotient.lift`'s respect obligation.
* **Do NOT spend cycle time on `def:381E`'s `reducedMethod`
  construction** (`.prover-state/issues/reduced_method_deferred.md`).
  Multi-cycle work; cycle 236 doesn't need it.
* **Do NOT spend cycle time on confluence-of-PReducesTo work**
  (`.prover-state/issues/p_reduction_confluence_gap.md`). Multi-cycle.
* **Do NOT touch `scripts/autonomous_loop.py`.** Loop-maintainer
  territory; phantom-verdict pattern (cf.
  `phantom_commit_verdict_pattern.md`) is still in force but not for
  workers to patch.

---

## §E — Backup plan (Plan B)

If `Quotient.lift`'s respect obligation fails to discharge cleanly
(e.g., `show PhiEquivalent _ _` mismatch on the Σ-typed
`PhiEquivalent.setoidSigma.Setoid.r` unfold), the fallback is
**`Quotient.map` instead of `Quotient.lift`**:

```lean
noncomputable def inverseQ_phi :
    Quotient PhiEquivalent.setoidSigma →
    Quotient PhiEquivalent.setoidSigma :=
  Quotient.map
    (fun (p : Σ s : ℕ, RKTableau s) => ⟨p.1, p.2.inverse⟩)
    (fun ⟨s, M⟩ ⟨s', M'⟩ hPhi => inverse_phiEquivalent_inverse hPhi)
```

This is the option cycle 222 strategy §B.P2 floated but did not
ultimately use. If `Quotient.lift` is finicky, switch to
`Quotient.map`; both are valid.

---

## §F — Risk register

* **R1 (Σ-typed Setoid.r unfolding)**: Cycle 222 verified by ad-hoc
  `show` rewrite; cycle 236 likely needs the same. Pre-typed
  `show PhiEquivalent M.inverse M'.inverse` mirrors cycle 222 line
  4522. Should fire cleanly.
* **R2 (typeclass elaboration in P2 examples)**: Lean must pick
  `instGroup_phi` over `instGroup` (cycle 222's §382 instance). If
  ambiguity arises, annotate explicitly with
  `(... : Quotient RKTableau.PhiEquivalent.setoidSigma)`.
* **R3 (warm rebuild time after edits)**: §381 is ~5200 LOC. Adding
  ~150 LOC of new content should not cross the 30 s red-flag
  threshold; cycle 235's warm rebuild was 6.4 s. If a rebuild
  exceeds 30 s, investigate whether the new `instance` blocks are
  triggering universe-instance search loops.
* **R4 (cycle 222 `inverseQ` name shadowing)**: Both instances are in
  the same namespace block (`Section312.RKTableau`). Use `_phi`
  suffix consistently. No shadowing.
* **R5 (`Group.ofLeftAxioms` argument order)**: Mathlib's signature
  is `(mul_assoc, one_mul, inv_mul_cancel)`. Verify by `lean_hover_info`
  if Lean complains.

---

## §G — Cycle 237+ outlook (do not work on this in cycle 236)

With the §383 `Group` instance shipped, the natural cycle 237+
trajectory is:

* **Cycle 237**: ship Φ : `Quotient Equivalent.setoidSigma →
  Quotient PhiEquivalent.setoidSigma` as a `MonoidHom` or `GroupHom`,
  via `Quotient.lift` consuming an `Equivalent → PhiEquivalent`
  inclusion lemma. Cycle 237 planner must check whether this lemma
  is single-cycle closeable or whether it's the deferred direction
  in `.prover-state/issues/thm_381H_deferred.md`. If deferred, pivot.

* **Cycle 238+**: If Φ ships, the §384 textbook theorem is
  axiom-clean.

* **Alternative cycle 237**: pivot to `thm:381G` (Irreducible RK
  Stage Distinguishability) per cycle 199's recon — multi-cycle
  but no GPFS dependency.

* **Alternative cycle 237**: pivot to a fresh entity entirely (e.g.,
  `def:422B` underlying one-step LMM, or §535 GLM underlying one-step
  method). The §380 cluster has been the focus for many consecutive
  cycles (227–236); a planner pivot may be appropriate after the
  cycle 236 ship lands.

---

## §H — Done criteria

Cycle 236 is **done** when:

1. `lake env lean OpenMath/Chapter3/Section381.lean` exits 0.
2. Four new public symbols (`inverseQ_phi`, `inverseQ_phi_mk`,
   `composeQ_phi_inverseQ_phi_left`, `instGroup_phi`) plus three
   instance declarations (`instOne_phi`, `instMul_phi`,
   `instInv_phi`) all verified axiom-clean via `lean_verify`.
3. Three P2 `example` blocks (definitional unfold + `mul_inv_cancel`
   + `inv_mul_cancel` on `⟦⟨2, paddedEuler⟩⟧`) compile clean.
4. Sorry count on `Section381.lean` remains 0.
5. Tautology-scanner regex returns no hits.
6. Regression spot-check confirms cycles 232/233/234/235 landmarks
   remain axiom-clean.
7. `.prover-state/task_results/cycle_236.md` written per CLAUDE.md
   format.
8. `extraction/formalization_data/lean_status.json` + `plan.md`
   updated.
9. `cycle_182_gpfs_slowness.md` cycle 236 row appended (timeout
   log).
10. Single commit landed with the deliverable summary.

If any of (1)–(6) fail, do NOT commit; investigate first.

**Single-cycle deliverable.** No multi-cycle scoping. No Aristotle.
Cycle 222's §382 work establishes the exact template; cycle 236
ports it.
