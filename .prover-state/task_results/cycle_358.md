# Cycle 358 Results

## Worked on
Phase D.3.a of `def:422B` — per-tree elementary-weight expansion
lemmas generalising cycle 341 P1/P2/P3
(`elementaryWeightQ_phi_{mul,inv,zpow}_vertex`) from
`RootedTree.vertex` to arbitrary trees `t`.

## Approach
Per strategy §C.3, ran pre-flight on three load-bearing hooks:

1. **`elementaryWeightQ_phi_composeQ_phi_mk`** at
   `OpenMath/Chapter3/Section381.lean:4730–4742` — output shape
   matches the strawman exactly:
   `(M₁.compose M₂).elementaryWeight t = M₁.elementaryWeight t + Σᵢ M₂.b i · M₂.derivativeWeightWithSrc M₁ i t`.
   Confirms D.3.a.1's proof is a one-line `exact`.

2. **Cycle 341 P1's proof body** at
   `OpenMath/Chapter4/Section422.lean:395–409` — recipe is
   `Quotient.inductionOn × 2`, `obtain ⟨s, M⟩ := p`, `show … =
   composeQ_phi …`, `rw [elementaryWeightQ_phi_composeQ_phi_mk]`,
   `congr 1`. D.3.a.1 drops the `Quotient.inductionOn` (takes
   representatives directly) and the `congr 1` (we want the
   asymmetric form).

3. **Cycle 236's `inverseQ_phi_mk`** at
   `OpenMath/Chapter3/Section381.lean:4276–4278` — confirmed to be
   `@[simp]` and `:= rfl`. So `⟦⟨s, M⟩⟧⁻¹ = ⟦⟨s, M.inverse⟩⟧`
   reduces definitionally. D.3.a.2 ships in the clean form.

Then wrote and verified:

* **D.3.a.1 `elementaryWeightQ_phi_mul_mk`**: one-line `exact` via
  the `show`-unfolding recipe.
* **D.3.a.2 `elementaryWeightQ_phi_inv_mk`**: applied
  `inv_mul_cancel` at the quotient level (after a `show`-rewrite of
  `⟦M.inverse⟧ * ⟦M⟧` as `⟦M⟧⁻¹ * ⟦M⟧`), then expanded the LHS via
  D.3.a.1 with `M₁ := M.inverse`, `M₂ := M`, collapsed `Φ_1(t) = 0`
  via cycle 239's `elementaryWeightQ_phi_id`, finished with
  `linarith`.
* **Two non-vacuity `example`s on `explicitEuler` at
  `RootedTree.cherry`** — one per shipped theorem.

For D.3.a.3, made a strategic decision to defer to cycle 359 per
the §C.4 graceful-degradation route. Reason: at arbitrary `t`, the
bottom-block contribution at each `pow_succ` step depends on the
specific representative of the previous power, with no clean closed
form. A proper D.3.a.3 needs a `RKTableau.powRep` recursive
construction + quotient-equality lemma, which is ~80 LOC of
substantive additional work. Per CLAUDE.md and the cycle 200/201
rollback precedents, sorry-bearing scaffolds for multi-cycle
sub-phases get rolled back, so partial ship is preferred.

Compile-checked the file via `lake build OpenMath.Chapter4.Section422`
(414s rebuild, clean). Axiom-checked both new theorems via
`#print axioms`; both depend only on the standard
`[propext, Classical.choice, Quot.sound]`.

Documentation updates:

* `extraction/formalization_data/lean_status.json` — `def:422B` row
  `cycle_completed_at: 351 → 358`, note appended with cycle 358's
  ship details.
* `plan.md` — `def:422B` paragraph appended with cycle 358 update
  documenting both shipped theorems and the deferred D.3.a.3
  rationale.
* `.prover-state/issues/def_422B_phase_D_3_scoping.md` §5 — phase
  table split D.3.a into D.3.a.{1,2} (✅ cycle 358) and D.3.a.3
  (cycle 359 deferred); appended a "Cycle 358 update" subsection
  documenting the shipped theorems, the (corrected) D.3.a.2 formula
  vs the strategy's strawman, the D.3.a.3 deferral reason, and the
  proposed cycle 359 strategy.

## Result
SUCCESS (partial per §C.4) — Success criterion #2: D.3.a.1 +
D.3.a.2 shipped axiom-clean, D.3.a.3 deferred to cycle 359 with
scoping doc updated. Sorry count remains 0. Cycle should score 2
with graceful-degradation note per §G.

Section422.lean: 1597 → 1742 LOC (+145).

## Faithfulness check

### `elementaryWeightQ_phi_mul_mk` (new theorem)

* **Entity ID**: This is a helper lemma for `def:422B` Phase D.3,
  not a textbook-named entity. It lifts cycle 239's
  `elementaryWeightQ_phi_composeQ_phi_mk` (also a helper, not
  textbook-named) from `composeQ_phi`-notation to `*`-notation.
  The underlying mathematical content is the §383 `composeQ_phi`
  decomposition of cycle 225's
  `compose_elementaryWeight_decomp` (Butcher §383 indirectly).
* **Lean statement captures**: same content as cycle 239's hook,
  just notation-translated. The bottom-block sum involves
  source-method-threaded `derivativeWeightWithSrc` exactly as
  cycle 239 ships, with no hypothesis strengthening/weakening.
* **Faithfulness**: at `t = RootedTree.vertex` this collapses to
  cycle 341 P1's symmetric form
  `Φ_{η·η'}(τ) = Φ_η(τ) + Φ_{η'}(τ)` via
  `derivativeWeightWithSrc_vertex` (each bottom-block factor is
  `1`), matching textbook §387's additivity at `τ` exactly.

### `elementaryWeightQ_phi_inv_mk` (new theorem)

* **Entity ID**: Again a Phase D.3 helper, not textbook-named.
  Lifts cycle 341 P2's `_vertex` to arbitrary trees.
* **Lean statement**:
  `Φ_{⟦M⟩⁻¹}(t) = - Σᵢ M.b i · M.derivativeWeightWithSrc M.inverse i t`.
  Notably **differs** from the strategy's strawman `-Φ_M(t) - Σ…`
  in that the strawman included an erroneous extra `-Φ_M(t)` term.
  The cleaner formula above falls directly out of `inv_mul_cancel`
  + D.3.a.1: writing `M.inverse * M = 1`, applying D.3.a.1 with
  `M₁ := M.inverse, M₂ := M` gives
  `0 = Φ_{⟦M.inverse⟧}(t) + Σᵢ M.b i · M.derivativeWeightWithSrc M.inverse i t`,
  hence
  `Φ_{⟦M.inverse⟩}(t) = -Σᵢ M.b i · M.derivativeWeightWithSrc M.inverse i t`,
  and since `⟦M⟩⁻¹ = ⟦M.inverse⟧` definitionally
  (`inverseQ_phi_mk` is `@[simp]` and `:= rfl`), this gives the
  shipped form.
* **Faithfulness check at `t = vertex`**: by
  `derivativeWeightWithSrc_vertex`, each
  `M.derivativeWeightWithSrc M.inverse i vertex = 1`, so
  `Σᵢ M.b i · 1 = M.elementaryWeight vertex = Φ_M(vertex)`,
  giving `Φ_{M⁻¹}(vertex) = -Φ_M(vertex)` — exactly cycle 341 P2.
  ✓
* **Lean statement captures**: same content as cycle 341 P2
  generalised to arbitrary `t`. The strategy's strawman is
  corrected during write-up (consistent with §D.1's recommendation
  to "use the asymmetric form" but with the correct algebra).

### Tautology / identity / definition-smuggling checks

* No theorem conclusion appears verbatim as one of its hypotheses.
* No proof is `exact h` for an unmodified hypothesis. D.3.a.1's
  proof is `exact elementaryWeightQ_phi_composeQ_phi_mk M₁ M₂ t`,
  which IS a one-line application — but it routes through a
  non-trivial `show`-step that unfolds `*` to `composeQ_phi` via
  cycle 236's `instMul_phi`. The new theorem genuinely re-exports
  the cycle 239 hook in a notation more usable by `Eq422a`
  consumers (which write `η_q^(-i) * D_element`, not
  `composeQ_phi (η_q^(-i)) D_element`). Not vacuous.
* No `structure`/`class` definitions introduced.
* No `Prop` fields with implicit conclusion-status.
* No hypothesis strengthening: both new theorems take only
  `(M : RKTableau s)` (or two such) and `(t : RT)` — no auxiliary
  Prop hypotheses introduced.

## Dead ends
None significant. The strategy's strawman D.3.a.2 signature
included an extra `-Φ_M(t)` term that doesn't fall out of the
derivation; the corrected formula was used. This is documented in
the scoping doc cycle-358 update.

The D.3.a.3 deferral is not a "dead end" but a strategic graceful
degradation per §C.4 — the structural obstacle (no canonical
`η_q^m` representative) is well-understood and cycle 359 has a
focused strategy.

## Discovery

### D.3.a.3 needs `RKTableau.powRep`

Lifting cycle 341 P3's `elementaryWeightQ_phi_zpow_vertex` to
arbitrary `t` fails to telescope because the bottom-block at each
`pow_succ` step in D.3.a.1 introduces a fresh
`derivativeWeightWithSrc <rep>` term where `<rep>` is the specific
representative chosen for `η_q ^ m`. At `t = vertex` this collapsed
to `1` independently of the representative, but at arbitrary `t`,
the bottom-block genuinely depends on the representative's
A-matrix structure (which grows with `m`).

Cycle 359 needs to:

1. Define `RKTableau.powRep : (m : ℕ) → RKTableau s → Σ s', RKTableau s'`
   recursively: `powRep 0 M := ⟨0, RKTableau.id⟩`,
   `powRep (m+1) M := let ⟨s', M'⟩ := powRep m M; ⟨s' + s, M'.compose M⟩`.
2. Prove `⟦powRep m M⟧ = ⟦M⟧ ^ m` at the §383 quotient level by
   induction on `m`.
3. State D.3.a.3 as a recursive identity using `powRep` for the
   bottom-block representative.
4. Extend to `n : ℤ` via case split on `Int.ofNat`/`Int.negSucc`,
   composing D.3.a.2 (inverse) with the natural-number version.

### Strategy's D.3.a.2 strawman had an extra spurious term

The strategy §C.1 D.3.a.2 strawman wrote
`= -Φ_M(t) - Σᵢ M.b i · M.derivativeWeightWithSrc <inv-rep> i t`,
but the correct formula via `inv_mul_cancel` + D.3.a.1 is just
`= -Σᵢ M.b i · M.derivativeWeightWithSrc M.inverse i t`.

The `-Φ_M(t)` term is spurious: the `inv_mul_cancel` route applies
D.3.a.1 to `M.inverse * M = 1` (giving
`0 = Φ_{⟦M.inverse⟧}(t) + Σᵢ …`), which after rearrangement
contains only the single Σ term on the RHS, not a `Φ_M(t)` term.
At `t = vertex`, the Σ term collapses to `Φ_M(vertex)` via
`derivativeWeightWithSrc_vertex`, so the formula correctly reduces
to cycle 341 P2's `Φ_{M⁻¹}(vertex) = -Φ_M(vertex)`.

This is documented in the scoping doc §5 cycle-358 update so
cycle 359+ workers don't re-introduce the spurious term.

### `RT` private abbrev needed for `(t : RootedTree)` parameters

Section422.lean has a `private abbrev RT :=
OpenMath.Chapter3.Section310.RootedTree` to disambiguate from
Mathlib's `_root_.RootedTree` (lattice-theoretic). Initial draft
used `(t : RootedTree)` and hit the same ambiguity error cycle
338 hit (per `plan.md:171` cycle 338 note). Used `(t : RT)` to
match cycle 338's pattern.

## Suggested next approach

### Cycle 359 — D.3.a.3 (proposed)

Ship `RKTableau.powRep` + `powRep_quotient_eq` + recursive D.3.a.3
identity per the strategy in this doc's Discovery section above.
Estimated ~80 LOC and 1 cycle. After D.3.a.3 lands, the §422
ladder horizon resumes its single-deliverable-per-cycle cadence:

* Cycle 360: D.3.b — `coeff_eta_t_in_eta_zpow_neg` (linear
  coefficient extraction)
* Cycle 361: D.3.c — `sum_i_alpha_ne_zero_of_stable` (ρ'(1) ≠ 0)
* Cycle 362: D.3.d — `underlyingOneStepMethod_aux` + spec lemma
* Cycle 363: Phase E (lift + seal `def:422B`)

### Cycle 359+ alternative (if D.3.a.3 turns out harder than expected)

If `powRep_quotient_eq` requires substantial Mathlib power-monoid
infrastructure, fall back to:

* (a) Prove D.3.b directly from D.3.a.{1,2} via a custom
  strong-induction argument that bypasses the explicit
  `Φ_{η^n}(t)` closed form, OR
* (b) Ship D.3.a.3 in a `Quotient.inductionOn`-based existential
  form (`∃ M', ⟦M'⟧ = η_q ^ m ∧ <recursive identity holds>`) — uglier
  but easier to discharge.

Both fallbacks add ~1 cycle of buffer to the §422 horizon.
