# Cycle 223 Results

## Worked on
PhiEquivalent setoid infrastructure for the §383 group-homomorphism path
(strategy §C):

- **P1** — `PhiEquivalent.setoid (s : ℕ) : Setoid (RKTableau s)` (fixed-stage
  setoid) + non-vacuity witness P1.E1.
- **P2** — `PhiEquivalent.setoidSigma : Setoid (Σ s : ℕ, RKTableau s)`
  (heterogeneous Σ-typed setoid) + three non-vacuity witnesses P2.E1
  (homogeneous), P2.E2 (heterogeneous via `pReduced_phiEquivalent`), P2.E3
  (`Quotient.mk` well-formedness via `Quotient.sound`).
- **P3** — `compose_phiEquivalent_compose` — DEFERRED to cycle 224 per
  strategy §D point 1 (sorry-increase avoidance) and §C P3 abort criterion.

Five new symbols, ~55 LOC added between lines 1937–1987 of
`OpenMath/Chapter3/Section381.lean` (immediately after cycle 212's
`Equivalent.setoidSigma`).

## Approach

Direct port of cycles 211 (`Equivalent.setoid`) and 212
(`Equivalent.setoidSigma`) templates, swapping
`Equivalent`/`equivalent_self`/`Equivalent.symm`/`Equivalent.trans` for
`PhiEquivalent`/`PhiEquivalent.refl`/`PhiEquivalent.symm`/`PhiEquivalent.trans`.
Dropped the cosmetic `.{u}` universe annotation (R1 in §G) because
`PhiEquivalent` is not universe-polymorphic — it iterates over
`RootedTree`, not an external `N` type as `Equivalent` does. No
universe-related Lean complaints.

Examples P2.E2 and P2.E3 directly consume cycle 187's
`pReduced_phiEquivalent` (verified at line 1322) together with cycle
186's `paddedEuler_isPReducibleVia_pairPartition` (line 1016), giving a
genuine heterogeneous-stage witness `⟨2, paddedEuler⟩ ≈ ⟨1,
paddedEuler.pReduced pairPartition⟩` mediated by `Quotient.sound`.

## Result

**SUCCESS** — axiom-clean, sorry count remains 0.

Warm rebuild of `OpenMath/Chapter3/Section381.lean`: 8.276s (cold:
4m18s — cluster I/O slowness, not a code-side issue; warm matches
recent cycles 219–222 health).

`lean_verify` results (`scan_source: false`):

- `OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoid` →
  `[propext, Classical.choice, Quot.sound]`
- `OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoidSigma` →
  `[propext, Classical.choice, Quot.sound]`

Regression spot-checks (axiom-clean, unchanged):

- `OpenMath.Chapter3.Section312.RKTableau.composeQ_eq_of_equivalent` →
  `[propext, Classical.choice, Quot.sound]`
- `OpenMath.Chapter3.Section312.RKTableau.instGroup` →
  `[propext, Classical.choice, Quot.sound]`

## Faithfulness check

### `PhiEquivalent.setoid (s : ℕ)`

- **Entity ID**: def:381B (Butcher §380 page 302, Φ-equivalent
  Runge–Kutta methods).
- **Textbook statement (quoted from `def_381B.json`)**:
  > Two Runge–Kutta methods are 'Φ-equivalent' if, for any t ∈ T, the
  > elementary weight Φ(t) corresponding to the first method is equal
  > to Φ(t) corresponding to the second method.
- **Lean statement captures**: pure typeclass packaging. No new
  mathematical content vs. the existing `def PhiEquivalent` (cycle
  030 era, line 124) and its `refl`/`symm`/`trans` lemmas (lines
  129/133/139). The setoid wraps these into Mathlib's `Setoid`
  typeclass with no algebraic content of its own. **No definition
  smuggling.**

### `PhiEquivalent.setoidSigma`

- **No directly-corresponding textbook entity**: this is supplementary
  infrastructure for the §383 quotient path, mirroring cycle 212's
  `Equivalent.setoidSigma` (which is also supplementary to def:381A's
  `Equivalent`). The Σ-typed form is required because thm:384A's
  "group homomorphism" Φ has heterogeneous-stage domain and codomain.
- **Lean statement captures**: typeclass packaging of `PhiEquivalent`
  on Σ-typed pairs. No new mathematical content.

### Examples (P1.E1, P2.E1, P2.E2, P2.E3)

- Non-vacuity witnesses only — no theorem content. P2.E2 and P2.E3
  exercise the heterogeneous-stage case via the already-proved
  `pReduced_phiEquivalent` (cycle 187) and `Quotient.sound`.

### Tautology / identity / definition smuggling checks

- No theorem conclusion equals a hypothesis.
- No proof is `exact h` re-exporting a hypothesis.
- No structure field encodes what should be a theorem conclusion (the
  setoids package three independently-proved lemmas `refl`/`symm`/`trans`
  into a typeclass — exactly the standard Mathlib pattern; no smuggling).

## Dead ends

None. The cycle 211/212 templates ported cleanly. The only non-trivial
investigation was the namespace-resolution surprise (see Discovery #1
below); it did not block any deliverable.

## Discovery

1. **Namespace resolution surprise in Lean 4 dot-notation declarations.**
   The new `instance PhiEquivalent.setoid` was declared inside namespace
   `OpenMath.Chapter3.Section381` (lines 997–1601 after my insertion),
   yet `lean_verify` only resolves the symbol under
   `OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoid`. This
   is consistent with the existing cycle 211/212 `Equivalent.setoid` /
   `Equivalent.setoidSigma`, both of which similarly land under
   `OpenMath.Chapter3.Section312.RKTableau` despite being declared in
   the `Section381` namespace. The mechanism: Lean 4 dot-notation
   resolution promotes `Foo.bar` declarations into `Foo`'s existing
   namespace when `Foo` is reachable via `open` (line 116/999
   `open OpenMath.Chapter3.Section312`). Note `PhiEquivalent` itself
   lives at `OpenMath.Chapter3.Section381.PhiEquivalent`, but `setoid`
   lands at `OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoid`
   — apparently Lean's resolution finds `RKTableau.PhiEquivalent` via
   the `open` chain (since `RKTableau` is opened and `PhiEquivalent` is
   *accessible* through `Section381` being opened back at line 190 in
   the file's first `Section312.RKTableau` block). Future cycles
   targeting these symbols with `lean_verify` should use the
   `OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.*` prefix.

2. **`.{u}` annotation is genuinely cosmetic for `PhiEquivalent`.**
   Unlike `Equivalent` (which has `∀ {N : Type*}` in its body), the
   `PhiEquivalent` body has no external universe variable. Dropping
   `.{u}` from both new setoid declarations compiled with no warnings.
   This matches strategy §G R1's prediction.

3. **R3/R4 risks did NOT fire.** Both `pairPartition` (line 1009) and
   `paddedEuler_isPReducibleVia_pairPartition` (line 1016) exist under
   their expected names, allowing P2.E2 and P2.E3 to be the genuine
   heterogeneous-stage witnesses planned by the strategy. The fallback
   to homogeneous-only `P2.E1` was not needed.

4. **`pReduced_phiEquivalent` is the load-bearing heterogeneous-stage
   witness for the Φ-quotient.** Its (cycle 187) proof gives a single-
   step `PhiEquivalent M (M.pReduced P)` that, combined with
   `Quotient.sound`, immediately yields equal quotient classes — no
   `Equivalent`-level routing needed. This pre-existing leverage
   compresses P2's heterogeneous demonstration into a few lines.

## Suggested next approach

**Cycle 224 — `compose_phiEquivalent_compose` + `composeQ_phi` + identity
laws (PhiEquivalent analogs of cycles 217–219).** The cycle 223 setoid
foundation is now in place; the natural cycle 224 deliverables (in
priority order):

1. **`compose_phiEquivalent_compose`** (~50–80 LOC, the genuinely
   nontrivial one): heterogeneous-stage well-definedness of
   `RKTableau.compose` w.r.t. `PhiEquivalent`. As strategy §C P3 and §D
   point 2 warn, this proof does NOT cleanly port cycle 217's recipe —
   PhiEquivalent operates at the `derivativeWeight` / rooted-tree level
   via `elementaryWeight`, not the `IsRKOneStep` / normed-space level.
   The likely proof path: induct on `RootedTree t`, then prove
   `(M₁.compose M₂).elementaryWeight t = (M₁'.compose M₂').elementaryWeight t`
   by unfolding `elementaryWeight` over the block decomposition of
   `compose`'s `A`/`b`/`c` fields. Inspect cycle 187's
   `derivativeWeight_pReduced` (line 1251) and any
   `derivativeWeightProd_pReduced` helper for the unfolding pattern.

2. **`composeQ_phi : Quotient PhiEquivalent.setoidSigma → ... → ...`**
   (~15 LOC noncomputable def via `Quotient.lift₂`), respect obligation
   = `compose_phiEquivalent_compose`. Direct port of cycle 218's
   `composeQ` recipe.

3. **`composeQ_phi_id_left` / `composeQ_phi_id_right`** (~20 LOC each):
   identity-element absorption laws for the future Φ-quotient group.
   Cycle 219's recipe ports cleanly if `compose_id_left_phiEquivalent`
   / `compose_id_right_phiEquivalent` exist at the `Equivalent` level
   already; otherwise need analogous PhiEquivalent versions.

4. **Optional stretch — `inverse_phiEquivalent_inverse`** (well-
   definedness of `RKTableau.inverse` w.r.t. `PhiEquivalent`,
   PhiEquivalent analog of cycle 220's `inverse_equivalent_inverse`).
   If `RKTableau.inverse` from cycle 220 commutes with `derivativeWeight`
   in a tractable way, this is a short cycle 225 deliverable; if not,
   defer.

After cycle 224's composeQ_phi + identity laws + (cycle 225's)
associativity + inverse, **cycle 226 should assemble**
`instance : Group (Quotient PhiEquivalent.setoidSigma)` via
`Group.ofLeftAxioms` (port of cycle 222's `instGroup`).

**Cycle 227 then ships the group homomorphism** `Φ : Quotient
Equivalent.setoidSigma →* Quotient PhiEquivalent.setoidSigma`, the
formal `thm:384A` ("A homomorphism between two groups"), via
`MonoidHom.mk` with `Quotient.lift` of the identity-on-tableaux map
(well-definedness = "Equivalent ⇒ PhiEquivalent", which is exactly
`Equivalent.toPhiEquivalent` if it already exists, or
`thm:381H`'s "modulo reduction" — needs cross-checking).

A possible cycle 224 risk: if `compose_phiEquivalent_compose` proves
genuinely multi-cycle (R6 in cycle 223 §G), the safer plan is to defer
that single theorem to cycle 224 and ship cycle 225 with just the
elementaryWeight unfolding lemmas as a prep step. The clean state
remains paramount.
