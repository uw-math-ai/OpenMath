# Cycle 217 Results

## Worked on
- §382 `RKTableau.compose_equivalent_compose` — generalised from the cycle 216
  fixed-stage signature `{s₁ s₂ : ℕ}` to the heterogeneous-stage signature
  `{s₁ s₁' s₂ s₂' : ℕ}`. (P1 from the cycle 217 strategy §B.)
- P2 heterogeneous-stage non-vacuity example: `2+2 = 4` vs `1+1 = 2`
  composite equivalence routed through cycle 208's
  `paddedEuler_equivalent_pReduced` applied twice.
- P3 stretch: appended a "Cycle 217 update — heterogeneous form closed"
  section to `.prover-state/issues/thm_382A_path.md` documenting the cycle
  218 entry point for the `composeQ` lift on cycle 212's
  `Equivalent.setoidSigma`.

## Approach
**P1 (~10 LOC churn)**: at `OpenMath/Chapter3/Section381.lean` lines
2708–2729, replaced the cycle 216 theorem head:

```lean
theorem compose_equivalent_compose.{u}
    {s₁ s₂ : ℕ}
    (M₁ M₁' : RKTableau s₁) (M₂ M₂' : RKTableau s₂)
    (hEq₁ : @Equivalent.{u} s₁ s₁ M₁ M₁')
    (hEq₂ : @Equivalent.{u} s₂ s₂ M₂ M₂') :
    @Equivalent.{u} (s₁ + s₂) (s₁ + s₂) (M₁.compose M₂) (M₁'.compose M₂')
```

with the cycle 217 head:

```lean
theorem compose_equivalent_compose.{u}
    {s₁ s₁' s₂ s₂' : ℕ}
    (M₁ : RKTableau s₁) (M₁' : RKTableau s₁')
    (M₂ : RKTableau s₂) (M₂' : RKTableau s₂')
    (hEq₁ : @Equivalent.{u} s₁ s₁' M₁ M₁')
    (hEq₂ : @Equivalent.{u} s₂ s₂' M₂ M₂') :
    @Equivalent.{u} (s₁ + s₂) (s₁' + s₂') (M₁.compose M₂) (M₁'.compose M₂')
```

Body byte-for-byte identical to cycle 216. Docstring rewritten: replaced
"fixed-stage (382g) form" with "heterogeneous-stage (382g) form",
removed the obsolete "Faithfulness note (fixed-stage restriction)"
paragraph, added a one-line note recording the cycle 217 generalization
and the reason it works (abstract-`N`-level proof + per-side
`compose_isRKOneStep_iff`).

**P2 (~22 LOC)**: added a new `example` immediately after the cycle 216
homogeneous example at `OpenMath/Chapter3/Section381.lean` near line
2840, asserting:

```lean
@RKTableau.Equivalent (2 + 2) (1 + 1)
  (paddedEuler.compose paddedEuler)
  ((paddedEuler.pReduced pairPartition).compose
    (paddedEuler.pReduced pairPartition))
```

via `compose_equivalent_compose paddedEuler (paddedEuler.pReduced
pairPartition) paddedEuler (paddedEuler.pReduced pairPartition)
paddedEuler_equivalent_pReduced paddedEuler_equivalent_pReduced`.

**P3 (~60 lines markdown)**: appended a section to
`.prover-state/issues/thm_382A_path.md` scoping cycle 218's `composeQ`
via `Quotient.lift₂`. Draft signature:

```lean
def composeQ :
    Quotient RKTableau.Equivalent.setoidSigma →
    Quotient RKTableau.Equivalent.setoidSigma →
    Quotient RKTableau.Equivalent.setoidSigma
```

with the respect obligation discharged by cycle 217's
`compose_equivalent_compose` applied directly to the destructured Σ-pair
relation. Notes that plain `Quotient.lift₂` (not `Quotient.hrecOn₂`)
suffices because the output type `Quotient setoidSigma` does not depend
on the inputs (the stage-count dependence is *inside* the Σ-packed
element, not the output type).

## Result
**SUCCESS** — exactly as the strategy predicted, the cycle 216 body
ported verbatim under the heterogeneous-stage signature. Compilation
results:

- Section381.lean warm rebuild after P1 alone: **8.5s** (slightly
  elevated vs. the 5–7s baseline; cold-ish caches on first port).
- Section381.lean warm rebuild after P1+P2: **6.2s**, back to the
  baseline range (32 consecutive cycles of stable health since cycle
  184 GPFS recovery).
- `lean_verify OpenMath.Chapter3.Section312.RKTableau.compose_equivalent_compose`
  → `[propext, Classical.choice, Quot.sound]` (clean — sorryAx absent).
- `lean_verify OpenMath.Chapter3.Section312.RKTableau.compose_isRKOneStep_iff`
  → `[propext, Classical.choice, Quot.sound]` (no regression).
- `lean_verify OpenMath.Chapter3.Section312.RKTableau.compose_of_isRKOneStep`
  → `[propext, Classical.choice, Quot.sound]` (no regression).
- Sorry count: 0 → 0 (unchanged).

Risk 1 from the cycle 217 strategy §E (implicit-parameter unification
failing on the cycle 216 example call site) did NOT fire — Lean inferred
all four implicit `s` parameters as `2` from the `paddedEuler : RKTableau
2` annotations without complaint. No explicit `(s₁ := 2)` annotation
needed.

Risk 2 (sum-type mismatches between the two `compose_isRKOneStep_iff`
applications) did NOT fire — as predicted, `compose_isRKOneStep_iff` is
shape-polymorphic in its two `RKTableau` arguments, so the two `.mp`
results landed in their respective composite types
`RKTableau (s₁ + s₂)` and `RKTableau (s₁' + s₂')` without HEq plumbing.

Risk 3 (stale cross-references in the docstring) was caught and
mitigated — the "Faithfulness note (fixed-stage restriction)" paragraph
was removed, and the "Faithfulness note (textbook (382f) bracketed
form)" paragraph remains valid as-is.

Risk 4 (GPFS pathology re-emerging) did NOT fire — Section381.lean
compiled in baseline time.

## Faithfulness check
**`RKTableau.compose_equivalent_compose` (thm:382A 382g form)**:
- Entity ID and textbook statement (quoted from `extraction/formalization_data/entities/thm_382A.json`):
  > "Let $m_1$, $m_2$, $\widehat{m}_1$, $\widehat{m}_2$ denote
  > Runge–Kutta methods, such that
  > $\widehat{m}_1 \equiv m_1 \quad \text{and} \quad \widehat{m}_2
  > \equiv m_2.$ Then $[m_1 \cdot m_2] = [\widehat{m}_1 \cdot
  > \widehat{m}_2].$"
  > Proof remarks: "an equivalent statement is $m_1 \cdot m_2 \equiv
  > \widehat{m}_1 \cdot \widehat{m}_2.$"
- Lean statement captures: **same content** for the (382g) form, with
  the heterogeneous-stage interpretation. Cycle 217 closes the
  faithfulness gap flagged by cycle 216's fixed-stage restriction —
  the textbook says nothing about $m_1$, $\widehat{m}_1$ sharing a stage
  count, and our signature now reflects that.
- The bracketed (382f) form `[m_1 \cdot m_2] = [\widehat{m}_1 \cdot
  \widehat{m}_2]` still awaits cycle 218's `composeQ` lift; this is a
  packaging-only gap (it follows from cycle 217's theorem via
  `Quotient.sound`), not a mathematical one.

No new `def`s or new theorem names introduced this cycle — only the
existing `compose_equivalent_compose` signature generalised in place.

## Dead ends
None this cycle. The mechanical-port hypothesis from cycle 216's task
results validated cleanly; no risks fired.

## Discovery
- **The cycle 216 body is genuinely shape-polymorphic in stage counts**.
  The proof reads `intro N _ _ _ f L hL` → destructure `hEq₁`/`hEq₂` →
  refine with `min H₁ H₂` → apply `compose_isRKOneStep_iff` on each side
  → equate `y_mid` and `y_mid'` via `hEq₁` → rewrite → apply `hEq₂`.
  At no point does the proof inspect the stage counts; every appeal is
  abstract over `N`. This pattern should generalise to other "binary
  operations on RK tableaux that descend to the equivalence quotient"
  if/when they appear (e.g. tensor-product-style constructions).
- **Implicit unification on `paddedEuler : RKTableau 2` is robust under
  signature changes**. The cycle 216 example call site
  `compose_equivalent_compose paddedEuler paddedEuler paddedEuler
  paddedEuler …` required zero source edit when all four `s` parameters
  separated. Future generalizations of fixed-stage theorems to
  heterogeneous-stage forms can be done without disturbing concrete-
  tableau call sites.

## Suggested next approach
**Cycle 218 — `composeQ` lift via `Quotient.lift₂`**:

The natural continuation. The cycle 217 strategy's §D sketched the
target; the appended section to `.prover-state/issues/thm_382A_path.md`
gives a draft signature and discharge plan. Concretely:

1. Define `composeQ : Quotient setoidSigma → Quotient setoidSigma →
   Quotient setoidSigma` via `Quotient.lift₂`. The lifted operation on
   representatives is `fun ⟨s₁, M₁⟩ ⟨s₂, M₂⟩ => ⟨s₁ + s₂, M₁.compose M₂⟩`.
2. The `Quotient.lift₂` respect obligation has signature `∀ p p' q q',
   p ≈ p' → q ≈ q' → mk' (op p q) = mk' (op p' q')`. Destructure the
   Σ-pairs and apply `Quotient.sound` followed by cycle 217's
   `compose_equivalent_compose`.
3. P2 non-vacuity: `composeQ ⟦⟨2, paddedEuler⟩⟧ ⟦⟨2, paddedEuler⟩⟧ =
   ⟦⟨4, paddedEuler.compose paddedEuler⟩⟧` (definitional unfolding) and
   the heterogeneous variant via the cycle 217 P2 witness.
4. P3 (optional): the bracketed (382f) form `[m₁·m₂] = [m̂₁·m̂₂]` as a
   single-line corollary `Quotient.sound (compose_equivalent_compose
   hEq₁ hEq₂)`.

Risks for cycle 218:
- **R1**: `Quotient.lift₂` may not directly accept a function whose
  body uses `Quotient.mk'` on a different setoid. May need explicit
  `@Quotient.lift₂` with the source/target setoid arguments named.
- **R2**: cycle 212's `Equivalent.setoidSigma` defines `Setoid.r` via
  the bundled `iseqv` field, which may need a `show paddedEuler.Equivalent
  ...` reframing to destructure (cycle 211/212 precedent).
- **R3**: Mathlib API for `Quotient.lift₂` may have evolved; check
  `Quotient.lift₂` vs. `Quotient.lift₂'` (curried) vs. `Quotient.lift_on₂`
  flavor. Use `lean_loogle` or `lean_local_search` to confirm the
  current Mathlib name before coding.

Estimated cycle 218 LOC: ~10 for `composeQ`, ~10 for examples, ~5 for
the (382f) corollary. ~30-minute cycle if R1–R3 don't fire.

**Beyond cycle 218 (cycles 219+)**: §382 group structure (identity
element = trivial 0-stage tableau; inverse element + associativity
= deeper §383/§384 work). Cycle 218's `composeQ` is the foundation; the
group axioms become operations on `Quotient setoidSigma`.
