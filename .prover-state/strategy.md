# Cycle 229 Strategy

## TL;DR

Three-priority cycle, all in `OpenMath/Chapter3/Section381.lean`:

1. **P0 — single Aristotle poll** on the right-action job
   `176aa964-db7b-40f8-a01c-05247c186ec5`. ONE poll only (CLAUDE.md
   discipline). Branch on the result.
2. **P1 (path A — Aristotle COMPLETE / COMPLETE_WITH_ERRORS / mechanical
   fix only)**: incorporate the right-action proof, ship full bilateral
   `compose_phiEquivalent_compose`, ship the full binary `composeQ_phi`,
   ship the bracketed-form corollary `composeQ_phi_eq_of_phiEquivalent`,
   plus homogeneous and heterogeneous-stage non-vacuity. Estimated ~100
   LOC.
3. **P1 (path B — Aristotle IN_PROGRESS / FAILED / substantive errors)**:
   ship the **right-identity counterpart** of cycle 228 —
   `compose_id_phiEquivalent` (`PhiEquivalent (M.compose id) M`) and the
   quotient-level `composeQ_phi_left_act_id_right`. Mirror of cycle 228
   on the other side; ~30 LOC. The two together give the full §382-style
   "identity element acts trivially" story modulo the right-action
   blocker.

Sorry count stays at **0** (target: 43rd consecutive clean cycle since
cycle 201 rollback). §441 Phase C.2 remains GPFS-blocked (44th
consecutive cycle); skip per the standing pattern.

---

## §A — §441 Phase C.2 — SKIP (44th consecutive GPFS block)

`OpenMath/Chapter4/Section441.lean` has timed out on every smoke test
since cycle 182 (cycles 182–228 = 47 attempts, all hitting the same
near-zero-CPU 5-minute timeout). **Do NOT attempt a smoke test or
compile** of Section441.lean. The cycle 182 draft + cycle 184 namespace
fix at `.prover-state/cycle_182_draft_section441.lean` remain frozen
until GPFS recovers; the loop-maintainer escalations
(`.prover-state/issues/phantom_commit_verdict_pattern.md` and
`.prover-state/issues/cycle_182_gpfs_slowness.md`) remain in force.

DO NOT spot-check Section441.lean this cycle. The chance of GPFS
recovery is empirically zero across 47 attempts; spending budget on the
49th attempt is wasted compute. The §383 group-hom path in
Section381.lean is healthy (warm rebuild ~13s) and is the cycle's
focus.

---

## §B — Priority 0: single Aristotle poll (5-min hard cap)

The cycle 226 worker submitted the M₂-side sum equality (the
right-action half of `compose_phiEquivalent_compose`) to Aristotle:

- **project_id**: `176aa964-db7b-40f8-a01c-05247c186ec5`
- Submitted: 2026-05-14T15:50:23 UTC
- Last observed (cycle 228): IN_PROGRESS at 11 %

Run **exactly one** poll:

```
mcp__aristotle__get_status with project_id="176aa964-db7b-40f8-a01c-05247c186ec5"
```

Branch on the returned `status`:

- **`COMPLETE`** → if there's a usable proof in the result, execute §C
  (path A).
- **`COMPLETE_WITH_ERRORS`** → inspect the returned proof. If errors are
  mechanical (namespace fixes only, cf. cycle 184's `M.αPoly_...` →
  `LinearMultistepMethod.αPoly_...` precedent), apply fixes and execute
  §C. If errors are substantive (logic gaps, missing lemmas, malformed
  proof tree), document briefly and execute §D (path B).
- **`IN_PROGRESS`** at any progress percentage → execute §D (path B).
  Do NOT re-poll. Do NOT cancel. Aristotle has been running ~24 hours
  by now; if it hasn't finished, leave it running for the next cycle.
- **`FAILED` / `CANCELLED`** → execute §D (path B).
- **Any other status** → execute §D (path B).

**Hard rule**: ONE poll per cycle. If you find yourself wanting to
"just check if 11% advanced", DO NOT. The next worker will poll in
cycle 230.

---

## §C — Priority 1, Path A: Aristotle right-action incorporation

Only execute if §B's poll returned a usable proof.

### C.1 — Locate insertion point

The new symbols belong inside
`namespace OpenMath.Chapter3.Section312.RKTableau`, immediately after
cycle 227's `composeQ_phi_left_act_eq_of_phiEquivalent` (around line
~3290 of `Section381.lean`) and BEFORE cycle 228's
`id_compose_phiEquivalent` block at line ~3308. Or, more cleanly,
place them after cycle 228's `composeQ_phi_left_act_id_left` at line
~3402 (immediately before the `Inverse method` section block at line
~3404).

### C.2 — Adapt the right-action proof

Aristotle's proof will likely be a `compose_phiEquivalent_compose_right`
theorem with signature

```lean
theorem compose_phiEquivalent_compose_right
    {s₁ s₂ s₂' : ℕ}
    (M₁ : RKTableau s₁) {M₂ : RKTableau s₂} {M₂' : RKTableau s₂'}
    (hPhi₂ : PhiEquivalent M₂ M₂') :
    PhiEquivalent (M₁.compose M₂) (M₁.compose M₂')
```

(or possibly the full bilateral `compose_phiEquivalent_compose` — chain
it with cycle 226's `compose_phiEquivalent_compose_left` via
`PhiEquivalent.trans` if so).

Inspection / port checklist:

- **Namespace**: Aristotle's stub may use `Section381.` qualifiers while
  our codebase uses `OpenMath.Chapter3.Section312.RKTableau.`. Apply
  mechanical renames if needed.
- **Imports**: do NOT add new imports unless absolutely necessary. All
  required infrastructure (cycles 224/225/226) is already in scope.
- **`open` blocks**: cycle 224's mutual block uses
  `section ... open OpenMath.Chapter3.Section310 ... end` to resolve the
  `RootedTree` namespace clash. If Aristotle's proof references
  `RootedTree`, wrap it in the same idiom.
- **Helper lemmas**: if Aristotle introduces auxiliary mutual blocks (à
  la cycle 226's `derivativeWeightWithSrc_subst_M₁`), keep them
  `private` and place them immediately before the public theorem.

### C.3 — Ship `compose_phiEquivalent_compose` (full bilateral)

Once the right-action half is in, the bilateral form follows by
chaining cycle 226's `compose_phiEquivalent_compose_left` with the new
right-action via `PhiEquivalent.trans`:

```lean
theorem compose_phiEquivalent_compose
    {s₁ s₁' s₂ s₂' : ℕ}
    {M₁ : RKTableau s₁} {M₁' : RKTableau s₁'}
    {M₂ : RKTableau s₂} {M₂' : RKTableau s₂'}
    (hPhi₁ : PhiEquivalent M₁ M₁')
    (hPhi₂ : PhiEquivalent M₂ M₂') :
    PhiEquivalent (M₁.compose M₂) (M₁'.compose M₂') :=
  PhiEquivalent.trans
    (compose_phiEquivalent_compose_left M₂ hPhi₁)
    (compose_phiEquivalent_compose_right M₁' hPhi₂)
```

(If `PhiEquivalent.trans` is not exposed as dot notation, qualify as
`PhiEquivalent.trans` — check `Section381.lean` around line 139 for the
cycle 030 namespace.)

### C.4 — Ship `composeQ_phi` (full binary `Quotient.lift₂`)

Following cycle 218's `composeQ` pattern at line ~3067:

```lean
noncomputable def composeQ_phi :
    Quotient PhiEquivalent.setoidSigma →
    Quotient PhiEquivalent.setoidSigma →
    Quotient PhiEquivalent.setoidSigma := by
  refine Quotient.lift₂ (fun p q =>
    Quotient.mk PhiEquivalent.setoidSigma
      ⟨p.1 + q.1, p.2.compose q.2⟩) ?_
  rintro ⟨s₁, M₁⟩ ⟨s₂, M₂⟩ ⟨s₁', M₁'⟩ ⟨s₂', M₂'⟩ hPhi₁ hPhi₂
  apply Quotient.sound
  show @PhiEquivalent (s₁ + s₂) (s₁' + s₂')
    (M₁.compose M₂) (M₁'.compose M₂')
  exact compose_phiEquivalent_compose hPhi₁ hPhi₂
```

`noncomputable` is **required** (matches cycle 218's `composeQ`).

**Universe annotation**: do NOT add `.{u}` to
`PhiEquivalent.setoidSigma` (cycle 223 confirmed it is NOT
universe-polymorphic, unlike `Equivalent.setoidSigma.{u}`).

### C.5 — Ship `@[simp] composeQ_phi_mk` and the bracketed corollary

```lean
@[simp] theorem composeQ_phi_mk
    {s₁ s₂ : ℕ} (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) :
    composeQ_phi
        (Quotient.mk PhiEquivalent.setoidSigma ⟨s₁, M₁⟩)
        (Quotient.mk PhiEquivalent.setoidSigma ⟨s₂, M₂⟩) =
      Quotient.mk PhiEquivalent.setoidSigma
        ⟨s₁ + s₂, M₁.compose M₂⟩ :=
  rfl

theorem composeQ_phi_eq_of_phiEquivalent
    {s₁ s₁' s₂ s₂' : ℕ}
    {M₁ : RKTableau s₁} {M₁' : RKTableau s₁'}
    {M₂ : RKTableau s₂} {M₂' : RKTableau s₂'}
    (hPhi₁ : PhiEquivalent M₁ M₁') (hPhi₂ : PhiEquivalent M₂ M₂') :
    composeQ_phi
        (Quotient.mk PhiEquivalent.setoidSigma ⟨s₁, M₁⟩)
        (Quotient.mk PhiEquivalent.setoidSigma ⟨s₂, M₂⟩) =
      composeQ_phi
        (Quotient.mk PhiEquivalent.setoidSigma ⟨s₁', M₁'⟩)
        (Quotient.mk PhiEquivalent.setoidSigma ⟨s₂', M₂'⟩) := by
  show Quotient.mk _ _ = Quotient.mk _ _
  exact Quotient.sound (compose_phiEquivalent_compose hPhi₁ hPhi₂)
```

### C.6 — P2 non-vacuity (two examples)

In `namespace OpenMath.Chapter3.Section381` at the file's bottom,
immediately after cycle 228's
`composeQ_phi_left_act_id_left_paddedEuler` example (line ~4173+):

(i) Homogeneous (closes by `rfl`):
```lean
example :
    RKTableau.composeQ_phi
        (Quotient.mk RKTableau.PhiEquivalent.setoidSigma
          ⟨2, paddedEuler⟩)
        (Quotient.mk RKTableau.PhiEquivalent.setoidSigma
          ⟨2, paddedEuler⟩) =
      Quotient.mk RKTableau.PhiEquivalent.setoidSigma
        ⟨4, paddedEuler.compose paddedEuler⟩ := rfl
```

(ii) Heterogeneous (uses cycle 187's `pReduced_phiEquivalent` on BOTH
sides — exercises stage shrinkage 4 → 2 across both arguments):
```lean
example :
    RKTableau.composeQ_phi
        (Quotient.mk RKTableau.PhiEquivalent.setoidSigma
          ⟨2, paddedEuler⟩)
        (Quotient.mk RKTableau.PhiEquivalent.setoidSigma
          ⟨2, paddedEuler⟩) =
      RKTableau.composeQ_phi
        (Quotient.mk RKTableau.PhiEquivalent.setoidSigma
          ⟨1, paddedEuler.pReduced pairPartition⟩)
        (Quotient.mk RKTableau.PhiEquivalent.setoidSigma
          ⟨1, paddedEuler.pReduced pairPartition⟩) :=
  RKTableau.composeQ_phi_eq_of_phiEquivalent
    (pReduced_phiEquivalent paddedEuler
      paddedEuler_isPReducibleVia_pairPartition)
    (pReduced_phiEquivalent paddedEuler
      paddedEuler_isPReducibleVia_pairPartition)
```

### C.7 — Update bookkeeping (path A only)

- `extraction/formalization_data/lean_status.json`:
  - `thm:384A` row: status remains `partial` (the homomorphism Φ itself
    is still pending — `composeQ_phi` is the multiplication operation,
    not the `MonoidHom`). Update the cycle 229 note to record full
    `composeQ_phi` ship; the `lean_symbol` should become
    `composeQ_phi_eq_of_phiEquivalent` (the headline form).
- `plan.md`:
  - `thm:384A` row: append cycle 229 entry recording the full
    `composeQ_phi` lift.

DO NOT promote `thm:384A` to `formalized` yet — the actual homomorphism
theorem (Φ is a `MonoidHom`/`GroupHom` between the two `Group`s)
requires identity preservation (`composeQ_phi 1 1 = 1`) and inverse
preservation (`composeQ_phi q⁻¹ q⁻¹ = (composeQ_phi q q)⁻¹`), which need
`inverseQ_phi` infrastructure not built this cycle.

---

## §D — Priority 1, Path B: right-identity counterpart of cycle 228

Only execute if §B's poll did NOT return a usable proof.

Two short, safe deliverables completing cycle 228's identity-element
story on the other side. Total ~30 LOC.

### D.1 — Insertion point

Place new symbols inside
`namespace OpenMath.Chapter3.Section312.RKTableau`, immediately after
cycle 228's `composeQ_phi_left_act_id_left` (currently line ~3402),
before the `Inverse method` section block (currently line ~3404).

### D.2 — `compose_id_phiEquivalent` (auxiliary lemma, ~15 LOC)

This is the right-symmetric counterpart of cycle 228's
`id_compose_phiEquivalent`. **Significantly simpler** than cycle 228
because the bottom-block sum `∑ i : Fin 0, ...` vanishes by `Fin 0`
emptiness, so the mutual-induction infrastructure that cycle 228
needed (`derivativeWeightWithSrc_id` / `derivativeWeightWithSrcProd_id`)
is NOT required here.

Goal:
```lean
theorem compose_id_phiEquivalent
    {s : ℕ} (M : RKTableau s) :
    @PhiEquivalent (s + 0) s (M.compose RKTableau.id) M
```

Stage-arithmetic note: `s + 0 = s` is definitionally true in Lean 4
(`Nat.add` recurses on the second argument), so this is effectively a
homogeneous-stage claim. The `@` qualifier exposes the implicit stage
counts for the type elaborator.

Proof recipe:
```lean
theorem compose_id_phiEquivalent
    {s : ℕ} (M : RKTableau s) :
    @PhiEquivalent (s + 0) s (M.compose RKTableau.id) M := by
  intro t
  rw [compose_elementaryWeight_decomp M RKTableau.id t]
  -- Goal: M.elementaryWeight t +
  --   ∑ i : Fin 0, RKTableau.id.b i * RKTableau.id.derivativeWeightWithSrc M i t
  -- = M.elementaryWeight t
  simp
```

If `simp` does not collapse the empty `Fin 0` sum cleanly, replace
the last line with:

```lean
  rw [Finset.sum_empty]  -- or Fin.sum_univ_zero
  -- Goal: M.elementaryWeight t + 0 = M.elementaryWeight t
  exact add_zero _
```

The empty-Finset lemma name to try first is `Finset.sum_empty` (the
standard form is `∑ x ∈ (∅ : Finset α), f x = 0`); the alternative
`Fin.sum_univ_zero` may need explicit argument fixes. If both fail,
the longhand recipe is:

```lean
  have h_empty : (∑ i : Fin 0, RKTableau.id.b i *
      RKTableau.id.derivativeWeightWithSrc M i t) = 0 := by
    apply Finset.sum_empty.trans rfl
    -- or: exact Finset.sum_of_isEmpty _
  rw [h_empty, add_zero]
```

**DOCSTRING**: include a brief docstring matching cycle 228's style,
referencing `compose_elementaryWeight_decomp` (cycle 225) and noting
that this is the right-symmetric counterpart of cycle 228's
`id_compose_phiEquivalent`. Mention that the proof is simpler than
cycle 228's because the `Fin 0` sum vanishes, eliminating the need for
the mutual induction `derivativeWeightWithSrc_id`.

### D.3 — `composeQ_phi_left_act_id_right` (~10 LOC)

The quotient-level right-identity law on cycle 227's
`composeQ_phi_left_act` (the one-sided partial-action lift). Mirrors
cycle 228's `composeQ_phi_left_act_id_left`.

Goal: for any `q : Quotient PhiEquivalent.setoidSigma`,
```
composeQ_phi_left_act q ⟨0, RKTableau.id⟩ = q
```

Proof recipe via `Quotient.inductionOn`:
```lean
theorem composeQ_phi_left_act_id_right
    (q : Quotient PhiEquivalent.setoidSigma) :
    composeQ_phi_left_act q ⟨0, RKTableau.id⟩ = q := by
  refine Quotient.inductionOn q ?_
  rintro ⟨s, M⟩
  show Quotient.mk _ _ = Quotient.mk _ _
  exact Quotient.sound (compose_id_phiEquivalent M)
```

Note the type-signature asymmetry: `composeQ_phi_left_act` takes a
`Quotient` on the LEFT but a raw representative `Σ s, RKTableau s` on
the RIGHT (because cycle 227 only lifted the left argument; the right
argument is a raw representative pending the right-action half of the
homomorphism). So the right-identity statement uses
`⟨0, RKTableau.id⟩` as the raw representative, not
`Quotient.mk _ ⟨0, RKTableau.id⟩`.

After `Quotient.inductionOn q` + `rintro ⟨s, M⟩`, the LHS unfolds
definitionally:
```
composeQ_phi_left_act (Quotient.mk _ ⟨s, M⟩) ⟨0, RKTableau.id⟩
  = Quotient.mk _ ⟨s + 0, M.compose RKTableau.id⟩
```
by `Quotient.lift_mk` (cycle 227's `@[simp]` unfold).

Then `show Quotient.mk _ _ = Quotient.mk _ _` stabilises the goal to
the two-quotient form, and `Quotient.sound (compose_id_phiEquivalent M)`
discharges (using `s + 0 = s` definitional equality so the LHS's
`s + 0` aligns with the RHS's `s`).

### D.4 — P2 non-vacuity (~10 LOC)

In `namespace OpenMath.Chapter3.Section381` at the file's bottom,
immediately after cycle 228's
`composeQ_phi_left_act_id_left_paddedEuler` example (line ~4173+):

```lean
/-- *Cycle 229 non-vacuity for `composeQ_phi_left_act_id_right`.*
Right-identity action on the `paddedEuler` class; symmetric counterpart
of cycle 228's left-identity example. -/
example :
    RKTableau.composeQ_phi_left_act
        (Quotient.mk RKTableau.PhiEquivalent.setoidSigma
          ⟨2, paddedEuler⟩)
        ⟨0, RKTableau.id⟩ =
      Quotient.mk RKTableau.PhiEquivalent.setoidSigma ⟨2, paddedEuler⟩ :=
  RKTableau.composeQ_phi_left_act_id_right
    (Quotient.mk RKTableau.PhiEquivalent.setoidSigma ⟨2, paddedEuler⟩)
```

### D.5 — Update bookkeeping (path B only)

- `extraction/formalization_data/lean_status.json`:
  - `thm:384A` row: extend the cycle 228 note with cycle 229's
    right-identity addition. Status remains `partial`. `lean_symbol`
    stays at `composeQ_phi_left_act` (still the partial-action pointer
    — full `composeQ_phi` is gated on the Aristotle right-action).
- `plan.md`:
  - `thm:384A` row: append cycle 229 entry recording the right-identity
    `composeQ_phi_left_act_id_right` + `compose_id_phiEquivalent`.

---

## §E — Risks and pitfalls

### E.1 — Risk: `Fin 0` sum simp behavior (Path B D.2)

`simp` *should* recognize `∑ i : Fin 0, f i = 0` automatically because
`Finset.univ : Finset (Fin 0)` reduces to `∅` and `Finset.sum_empty`
is a default simp lemma. If it doesn't fire, the longhand fallback in
D.2 always works. Worst case: ~2 extra LOC.

### E.2 — Risk: `compose_elementaryWeight_decomp` namespace (Path B D.2)

`compose_elementaryWeight_decomp` is declared `private` at line 2819.
Cycle 228 used it at line 3377 inside the same `namespace
OpenMath.Chapter3.Section312.RKTableau` block, so it's in scope. If
the cycle 229 insertion at line ~3403 falls outside this namespace
(check by reading the file's `namespace`/`end` structure near the
insertion point), wrap the new theorem in the namespace or use full
qualification. Cycle 228's `composeQ_phi_left_act_id_left` at line
3396 is also in this namespace, so placement immediately after it
guarantees correct scoping.

### E.3 — Risk: stage-count definitional equality on `s + 0 = s` (Path B D.3)

`Quotient.mk _ ⟨s + 0, ...⟩ = Quotient.mk _ ⟨s, ...⟩` should hold
definitionally because `s + 0 = s` reduces by `Nat.add_zero` (which is
the `_match_` case of `Nat.add` recursion on the second argument). If
Lean elaborates this incorrectly, add an intermediate `have h : s + 0
= s := rfl` and use `cast`/`heq` to bridge. Cycle 219's
`compose_id_equivalent` (line ~2640) shows this works in practice for
the cycle 222 `instGroup`.

### E.4 — Risk: Aristotle returns a different shape (Path A)

Aristotle may return the FULL bilateral `compose_phiEquivalent_compose`
instead of just the right-action half. If so, skip §C.3 (the
`PhiEquivalent.trans` chaining) and use the returned theorem
directly. The §C.4 `composeQ_phi` proof requires only the bilateral
form, so the path remains the same.

### E.5 — Risk: Section381.lean warm rebuild time

Cycle 228's warm rebuild was ~14s, cycle 227's ~14s, cycle 226's
~13s. **Acceptable threshold**: ≤30s warm rebuild. **Red flag**: >30s
suggests Lean is re-elaborating a deeply nested mutual block or
hitting `decreasing_by` complexity.

If warm rebuild exceeds 30s after the cycle 229 deliverables, suspect:
- A new mutual block was introduced (path A only — `compose_phiEquivalent_compose_right` may use one)
- A `decreasing_by` proof obligation was introduced
- Aristotle's proof contains a `decide` or expensive `simp` call

Mitigation: factor large proofs into smaller private helpers (the
established §381 idiom).

---

## §F — Execution discipline

### F.1 — Iteration plan

1. **(5 min)** Run §B's Aristotle poll exactly once. Record the result
   verbatim in your scratch notes; do NOT re-poll.
2. **(0 min)** Decide path: A if usable proof returned, B otherwise.
3. **(60–90 min path A / 30 min path B)** Execute the chosen path's
   §C / §D deliverables in order. After each Lean theorem lands,
   compile-check with `lean_verify` (NOT full file recompile — use
   the LSP MCP for fast targeted checks).
4. **(10 min)** Update `lean_status.json` and `plan.md` per §C.7 or
   §D.5.
5. **(15 min)** Commit and push. Commit message should follow the
   established cycle pattern: cycle number, headline deliverable,
   axiom-clean status, sorry count, regression spot-checks.

### F.2 — Verification cadence

After each new theorem:
- `lean_verify OpenMath.Chapter3.Section312.RKTableau.<theorem_name>`
  → confirm axiom set is `[propext, Classical.choice, Quot.sound]`
  (no `sorryAx`, no new `WellFounded.fix` axioms).

After all deliverables land:
- One warm rebuild of `OpenMath/Chapter3/Section381.lean` to confirm
  the file compiles end-to-end (target ≤30s — see §E.5).
- `grep -c sorry OpenMath/Chapter3/Section381.lean` → confirm 0.

### F.3 — Regression spot-checks

After all deliverables land, axiom-clean spot-check (via
`lean_verify`):
- `compose_phiEquivalent_compose_left` (cycle 226)
- `composeQ_phi_left_act` (cycle 227)
- `composeQ_phi_left_act_id_left` (cycle 228)
- `id_compose_phiEquivalent` (cycle 228)
- `composeQ_eq_of_equivalent` (cycle 218 §382 landmark)
- `instGroup` (cycle 222 §382 group instance)

Any regression to `sorryAx` is a stop-the-line event; revert and
investigate.

### F.4 — Commit message template (path A)

```
Cycle 229 — §383 group-hom path Phase 4: full binary `composeQ_phi` SHIPPED.

Aristotle returned the right-action proof (project
`176aa964-...`). Full bilateral `compose_phiEquivalent_compose` +
`composeQ_phi` (Quotient.lift₂) + `composeQ_phi_eq_of_phiEquivalent`
(the bracketed-form thm:384A multiplication operation) + 2 P2
non-vacuity witnesses.

[insertion locations, axiom-clean confirmations, etc.]

Sorry count: 0 (43rd consecutive clean cycle).
§441 Phase C.2: GPFS-blocked, 44th consecutive skip.
```

### F.5 — Commit message template (path B)

```
Cycle 229 — §383 group-hom path Phase 3 follow-up: right-identity for
`composeQ_phi_left_act` SHIPPED.

Aristotle right-action job IN_PROGRESS at 11% (no advancement from
cycle 228 poll). Strategy §D path taken. Two new symbols:
`compose_id_phiEquivalent` + `composeQ_phi_left_act_id_right`,
symmetric counterparts of cycle 228's left-identity. Plus one P2
non-vacuity witness.

[insertion locations, axiom-clean confirmations, etc.]

Sorry count: 0 (43rd consecutive clean cycle).
§441 Phase C.2: GPFS-blocked, 44th consecutive skip.
```

---

## §G — What NOT to try

### G.1 — Do NOT attempt the right-action half manually

The cycle 226 worker flagged the M₂-side sum equality
`∑ i, M₂.b i * M₂.derivativeWeightWithSrc M₁ i t = ∑ i', M₂'.b i' *
M₂'.derivativeWeightWithSrc M₁ i' t` as resistant to:
- Direct tree induction (cross-terms with outer `M₂.b` coupling don't
  factor).
- Reduction via cycle 217's operational `compose_equivalent_compose`
  (PhiEquivalent vs Equivalent live at different levels — see
  `cycle_226_compose_phi_right_action.md`).

The Connes-Kreimer Hopf algebra coproduct gives the closed form
(`(M₁ ∘ M₂)(t) = ∑ over admissible cuts`), but formalizing this is a
5–10 cycle endeavor. **Do not attempt manually this cycle**; wait for
Aristotle.

### G.2 — Do NOT re-poll Aristotle within this cycle

CLAUDE.md: "Sleep 30 minutes, check results, incorporate proofs, fix
partials. Only manually prove what Aristotle failed on." Re-polling
within the cycle adds zero information (Aristotle's progress is
monotonic) and burns budget.

### G.3 — Do NOT pivot to §441 Phase C.2

47 consecutive GPFS failures. The 48th attempt is wasted compute.

### G.4 — Do NOT attempt the full §383 `Group (Quotient PhiEquivalent.setoidSigma)` instance

Even after `composeQ_phi` is shipped, the §383 group instance requires:
- `composeQ_phi_id_left` / `_id_right` (identity laws on
  `composeQ_phi`, not just `composeQ_phi_left_act`)
- `composeQ_phi_assoc` (PhiEquivalent-level associativity)
- `inverseQ_phi` (PhiEquivalent-respecting inverse)

These are cycles 230–232+ work. Cycle 229's deliverable is the binary
multiplication operation `composeQ_phi` (path A) OR the identity-laws
on the partial-action `composeQ_phi_left_act` (path B), period.

### G.5 — Do NOT modify cycles 224/225/226/227/228 helpers

The `derivativeWeight_compose_castAdd` / `_natAdd` / `derivativeWeightWithSrc` /
`derivativeWeightWithSrcProd_subst_M₁` / `derivativeWeightWithSrc_id`
infrastructure is load-bearing for both paths. Do not refactor or
rename; only consume.

### G.6 — Do NOT introduce `decreasing_by` or `termination_by` annotations

The §381 mutual block style relies on Lean's structural recursion
checker (cycle 187 template). If your new theorem or helper requires
explicit termination annotations, you have likely structured it wrong;
refactor to match the cycle 224/225 mutual-block templates.

### G.7 — Do NOT increase `maxHeartbeats` above 200000

Per CLAUDE.md. If a proof exceeds default heartbeats, decompose.

---

## §H — Score expectations

- **Path A**: full `composeQ_phi` ship is a substantial deliverable
  (thm:384A multiplication operation). Score ≥1, possibly 2.
- **Path B**: right-identity addition is a clean +30 LOC delta with
  axiom-clean ship. Score 1 (matches cycle 228's score).
- **Neither path**: cycle should NOT exit empty. If both §C and §D
  encounter unforeseen blockers, document specifically and ship at
  minimum the §B Aristotle poll result + a focused issue file entry.
  A zero-change cycle is unacceptable per CLAUDE.md.
