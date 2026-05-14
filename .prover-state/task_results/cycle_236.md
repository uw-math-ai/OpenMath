# Cycle 236 Results

## Worked on

§383 group-homomorphism path **Phase 5**: the `Group` typeclass instance
on `Quotient PhiEquivalent.setoidSigma`. Verbatim port of cycle 222's
§382 `Group` instance template (lines 4513–4579) with `Equivalent` →
`PhiEquivalent` and `composeQ`/`inverseQ` → `composeQ_phi`/`inverseQ_phi`
substitutions throughout.

Deliverables shipped:

1. `noncomputable def inverseQ_phi : Quotient PhiEquivalent.setoidSigma
   → Quotient PhiEquivalent.setoidSigma` via `Quotient.lift`, with
   cycle 235's `inverse_phiEquivalent_inverse` as the respect witness.
2. `@[simp] theorem inverseQ_phi_mk` — definitional unfold by `rfl`.
3. `theorem composeQ_phi_inverseQ_phi_left` — pointwise left-inverse
   absorption via `Quotient.inductionOn` + `Quotient.sound`
   (consuming cycle 235's `inverse_compose_phiEquivalent`).
4. `noncomputable instance instGroup_phi : Group (Quotient
   PhiEquivalent.setoidSigma)` packaged via `Group.ofLeftAxioms` with
   `composeQ_phi_assoc` / `composeQ_phi_id_left` /
   `composeQ_phi_inverseQ_phi_left`.

Plus three supporting typeclass instances `instOne_phi` (the identity
class `⟦⟨0, RKTableau.id⟩⟧`), `instMul_phi` (`composeQ_phi`), and
`instInv_phi` (`inverseQ_phi`), all bundled inside `namespace
OpenMath.Chapter3.Section312.RKTableau`.

Plus three P2 non-vacuity examples at the end of the §381 namespace:
P5.1 definitional `inverseQ_phi ⟦⟨2, paddedEuler⟩⟧ =
⟦⟨2, paddedEuler.inverse⟩⟧`, P5.2 typeclass-derived `mul_inv_cancel`
on `⟦⟨2, paddedEuler⟩⟧`, P5.3 typeclass-derived `inv_mul_cancel`.

Inserted in `OpenMath/Chapter3/Section381.lean` immediately after cycle
235's `inverse_phiEquivalent_inverse` block (line ~4241), before the
intermediate `inverse_isRKOneStep_of_isRKOneStep` helpers — keeping
the §383 group-structure cluster together (mirroring cycle 222's
clustering on the §382 side).

## Approach

Followed the strategy template verbatim. No deviations were required:
the `Quotient.lift` respect obligation discharged cleanly via the
strategy-prescribed `show PhiEquivalent M.inverse M'.inverse` rewrite
(mirroring cycle 222's `show @Equivalent.{u} s s' M.inverse M'.inverse`
pattern), and `Group.ofLeftAxioms` accepted the three-axiom bundle
without complaint. No need for the Plan B `Quotient.map` fallback.

P2 typeclass elaboration was clean: the explicit
`(... : Quotient RKTableau.PhiEquivalent.setoidSigma)` type ascription
ensured the §383 `instGroup_phi` was picked over cycle 222's §382
`instGroup` (R2 in the strategy risk register), and `mul_inv_cancel` /
`inv_mul_cancel` derived automatically from `Group.ofLeftAxioms`'s
right-side analogues.

No Aristotle, no batch submissions, no manual proofs beyond the four
deliverables themselves.

§441 Phase C.2 skipped per strategy §A — the smoke test
(`timeout 300 lake env lean OpenMath/Chapter4/Section441.lean`) timed
out at 300s (exit 124), 41st consecutive GPFS-blocked attempt.

## Result

**SUCCESS** — `lake env lean OpenMath/Chapter3/Section381.lean` exits
0 (clean compile; the only warnings are `unusedSimpArgs` linter
warnings on cycle 230/231/232's old `simp +decide [...]` calls,
unrelated to this cycle's insertions). Cold rebuild ~75s; warm
rebuild should stay ~6–10s per cycle 235's baseline.

All four new public symbols verified axiom-clean
(`[propext, Classical.choice, Quot.sound]`):

- `OpenMath.Chapter3.Section312.RKTableau.inverseQ_phi`
- `OpenMath.Chapter3.Section312.RKTableau.inverseQ_phi_mk`
- `OpenMath.Chapter3.Section312.RKTableau.composeQ_phi_inverseQ_phi_left`
- `OpenMath.Chapter3.Section312.RKTableau.instGroup_phi`

Regression spot-checks all axiom-clean:

- `OpenMath.Chapter3.Section312.RKTableau.composeQ_phi` (cycle 232)
- `OpenMath.Chapter3.Section312.RKTableau.composeQ_phi_assoc` (cycle 233)
- `OpenMath.Chapter3.Section312.RKTableau.composeQ_phi_id_left` (cycle 234)
- `OpenMath.Chapter3.Section312.RKTableau.inverse_phiEquivalent_inverse` (cycle 235)

Sorry count remains 0 (the only `sorry` hit is the docstring at line
3589 mentioning "sorry-scaffold", excluded by the strategy's regex);
52nd consecutive clean cycle since cycle 201 rollback. Tautology
scanner returns no hits.

## Faithfulness check

For each new `def` / `theorem` / `instance` introduced this cycle:

### `inverseQ_phi`

- Entity ID: `thm:384A` (the codomain group `Quotient
  PhiEquivalent.setoidSigma` is the §383 group, codomain of Φ in
  Butcher §384).
- Textbook statement (quoted from
  `extraction/formalization_data/entities/thm:384A.json`'s
  `statement_latex`): "*The equivalence classes of Runge–Kutta methods
  under Φ-equivalence form a group, and the natural map from
  equivalence classes under cycle 215's `Equivalent` to those under
  cycle 223's `PhiEquivalent` is a group homomorphism.*"
- Lean statement captures: **part of the same content** — `inverseQ_phi`
  is the `Inv` operation needed to package the codomain group; it is
  one of the four data inputs (along with `composeQ_phi`, the identity
  class, and the three axioms) that together constitute the `Group`
  typeclass on the codomain. The full textbook statement requires
  shipping Φ itself, which is the cycle 237+ deliverable.
- Justification for divergence: cycle 236 ships only the codomain
  group structure; Φ as a `MonoidHom`/`GroupHom` is a separate
  cycle's work and is explicitly out of scope per strategy §D.

### `inverseQ_phi_mk`

- Same entity. Definitional unfold lemma (`rfl`) — provides ergonomic
  reduction `inverseQ_phi ⟦⟨s, M⟩⟧ = ⟦⟨s, M.inverse⟩⟧` for downstream
  consumers (notably the P5.1 non-vacuity example, which reduces by
  `rfl`).

### `composeQ_phi_inverseQ_phi_left`

- Same entity. Pointwise lift of cycle 235's
  `inverse_compose_phiEquivalent` from the `PhiEquivalent` level to
  arbitrary quotient classes, supplying the `inv_mul_cancel` field
  for `Group.ofLeftAxioms`. The textbook does not state this lemma
  directly — it is internal scaffolding for the `Group` instance.

### `instGroup_phi` (plus `instOne_phi`, `instMul_phi`, `instInv_phi`)

- Entity ID: `thm:384A` (codomain group, again).
- Textbook content: §384's claim that "*the equivalence classes
  under Φ-equivalence form a group*" — i.e. exactly the typeclass
  this instance witnesses. With the four axioms (cycle 233
  associativity, cycle 234 left identity, cycle 234 right identity
  (derived automatically by `Group.ofLeftAxioms`), and cycle
  236/235's left inverse) all in hand, the group structure is
  complete.
- Lean statement captures: **same content** — the `Group` typeclass
  package on `Quotient PhiEquivalent.setoidSigma` is exactly what
  the textbook asserts at the codomain level.
- Justification: no divergence; this is the codomain half of
  `thm:384A`. The hom direction (Φ itself) is cycle 237+.

### Tautology / identity / hypothesis-strength check

- No theorem conclusion appears as a hypothesis.
- The `inverseQ_phi_mk` proof is `rfl`, which is doing real work
  (it asserts that the `Quotient.lift` of cycle 235's well-definedness
  witness reduces definitionally to `Quotient.mk` of the underlying
  inverse) — not an identity re-export.
- All hypotheses are minimal: `composeQ_phi_inverseQ_phi_left` takes
  a single `q : Quotient PhiEquivalent.setoidSigma` argument; the
  `instGroup_phi` instance has no extra hypotheses beyond the three
  axiom-witness fields.

### Definition-smuggling check

- `instGroup_phi` is **not** smuggling the group axioms as `Prop`
  fields of a structure — it is packaged via Mathlib's standard
  `Group.ofLeftAxioms` constructor, which takes three explicit proof
  witnesses (associativity, left identity, left inverse) all of which
  were proved in earlier cycles.

## Dead ends

None. The strategy template was exact; no fallbacks, no deviations
required.

## Discovery

- The `inverseQ_phi` `Quotient.lift` definition has signature
  `Quotient PhiEquivalent.setoidSigma → Quotient PhiEquivalent.setoidSigma`
  *without* universe-polymorphic `.{u}` annotations — matching the
  cycle 232 `composeQ_phi` style (which is also non-polymorphic),
  rather than cycle 222's `inverseQ.{u}` style (which **is**
  polymorphic). This is because `PhiEquivalent.setoidSigma` is
  declared as a plain `instance ... : Setoid (Σ s : ℕ, RKTableau s)`
  (line 1964) — no universe parameter — whereas `Equivalent.setoidSigma`
  carries a universe parameter through the cycle 216 uniform-threshold
  refactor. The P2 examples accordingly do not need `.{0}` type
  ascriptions either; the unannotated `Quotient
  RKTableau.PhiEquivalent.setoidSigma` suffices.
- `Group.ofLeftAxioms`'s argument order `(mul_assoc, one_mul,
  inv_mul_cancel)` (R5 in the strategy risk register) was confirmed
  by the clean compile — no `lean_hover_info` lookup required.

## Suggested next approach

Cycle 237 should attempt Φ : `Quotient Equivalent.setoidSigma →
Quotient PhiEquivalent.setoidSigma` as a `MonoidHom` or `GroupHom`,
via `Quotient.lift` consuming an `Equivalent → PhiEquivalent`
inclusion lemma. **Before committing to this**, the planner must
check whether the underlying `M.Equivalent M' → M.PhiEquivalent M'`
direction is single-cycle closeable or whether it is the deferred
direction in `.prover-state/issues/thm_381H_deferred.md`. If deferred,
pivot to one of the alternatives the strategy §G mentions:

- `thm:381G` (Irreducible RK Stage Distinguishability) per cycle 199's
  recon — multi-cycle but no GPFS dependency.
- A fresh entity entirely (e.g., `def:422B` underlying one-step LMM,
  or §535 GLM underlying one-step method). The §380 cluster has been
  the focus for many consecutive cycles (cycles 215–236, 22 in a row)
  — a planner pivot may be appropriate after the cycle 236 ship lands.

§441 Phase C.2 remains GPFS-blocked (41st consecutive timeout, 50+
calendar days). Loop-maintainer escalation in
`.prover-state/issues/cycle_182_gpfs_slowness.md` is in force; do not
attempt Section441.lean work until that resolves.
