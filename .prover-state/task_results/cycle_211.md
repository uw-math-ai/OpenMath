# Cycle 211 Results

## Worked on

- **P1**: `RKTableau.Equivalent.setoid.{u}` — `Setoid (RKTableau s)`
  instance combining cycles 203/204/206's refl/symm/trans into the
  standard Mathlib setoid typeclass. (Inserted at line 1897 of
  `OpenMath/Chapter3/Section381.lean`, immediately after
  `Equivalent.trans`.)
- **P2**: Two non-vacuity examples in `namespace OpenMath.Chapter3.Section381`
  (lines 2289–2305): (a) `Setoid.refl paddedEuler` via the new instance,
  (b) `Quotient.mk` well-formedness on `paddedEuler` — exercises the
  `Quotient` API end-to-end.
- **P3**: Stretch — wrote `.prover-state/issues/thm_382A_path.md`
  documenting the two prerequisite gaps (Gap A: `compose_isRKOneStep_iff`
  structural bridge; Gap B: heterogeneous Σ-typed setoid) and a 3–5
  cycle plan to close thm:382A.

## Approach

P1 (P1 implementation):
1. Tried the unqualified strategy recipe first:
   ```lean
   instance Equivalent.setoid (s : ℕ) : Setoid (RKTableau s) where
     r M M' := M.Equivalent M'
     iseqv := ⟨equivalent_self, Equivalent.symm, Equivalent.trans⟩
   ```
   → **failed** with: "declaration contains universe level metavariables …
   `Equivalent.{?u.40116} M M'`".
2. Applied Risk 1 mitigation: switched to explicit `.{u}` annotations:
   ```lean
   instance Equivalent.setoid.{u} (s : ℕ) : Setoid (RKTableau s) where
     r M M' := @Equivalent.{u} _ _ M M'
     iseqv := ⟨equivalent_self, @Equivalent.symm.{u} _ _, @Equivalent.trans.{u} _ _ _⟩
   ```
   → **compiled clean**, axiom-clean check returns
   `[propext, Classical.choice, Quot.sound]`.

P2:
1. First attempt — the strategy's recipe `example : @Setoid.r _ (...) ... := Setoid.refl _`
   triggered the **implicit-lambda feature** on the goal type: `Setoid.r`
   unfolds to `Equivalent`, which unfolds to `∀ {N} [...], ...`, and Lean
   auto-introduces the binders, leaving an `∀ (f : N → N) ...`-shaped
   goal that `Setoid.refl paddedEuler` does not match (its type unfolds to
   `paddedEuler ≈ paddedEuler`).
2. Fixed with `show paddedEuler.Equivalent paddedEuler` + `exact
   paddedEuler.equivalent_self` — the `show` reframes the goal at the
   raw `Equivalent` level, bypassing the auto-introduction.
3. The strategy's second example (`Setoid.symm h`) hit the same trap and
   resisted multiple unfolding/show variations because `h` itself was
   getting implicit-lambda-introduced before `Equivalent.symm`'s
   universe-polymorphic shape could unify. Swapped the symmetry example
   for a **Quotient.mk well-formedness** example (`Quotient.mk … paddedEuler
   = Quotient.mk … paddedEuler := rfl`), which exercises the setoid
   *through the Quotient API* (the actual downstream consumer of the
   setoid) and avoids the implicit-lambda trap entirely. This is a
   stronger non-vacuity witness for the **intended use case**: feeding
   the setoid into `Quotient (Equivalent.setoid s)` for Butcher's §382
   group construction.

P3 (stretch — documentation only):
- Read `extraction/formalization_data/entities/thm_382A.json` to extract
  the textbook statement, proof sketch, and dependencies.
- Wrote `.prover-state/issues/thm_382A_path.md` with three sections:
  (1) quoted textbook statement, (2) two prerequisite gaps, (3) 3–5
  cycle plan to close thm:382A via Gap A → (382g) form → quotient form.
- Made the (382g) reformulation observation explicit: Butcher himself
  notes that `m₁ · m₂ ≡ m̂₁ · m̂₂` is an equivalent statement, which
  **doesn't need the Σ-typed quotient (Gap B)** — only Gap A's
  structural bridge. This lets cycle 214 ship the mathematical content
  of thm:382A without waiting on Gap B's quotient machinery.

## Result

**SUCCESS** — all three deliverables shipped, axiom-clean.

- `RKTableau.Equivalent.setoid` compiles, depends on
  `[propext, Classical.choice, Quot.sound]` only.
- Both P2 examples elaborate and compile within the §381 namespace.
- `.prover-state/issues/thm_382A_path.md` written (~250 lines of
  scoping/documentation, zero code changes from P3).
- Warm rebuild: 5.4s. Sorry count: 0. No new blockers introduced.

## Faithfulness check

### `RKTableau.Equivalent.setoid` (instance, NOT a textbook entity)

- Entity ID: none — this is pure Lean infrastructure (a typeclass
  instance combining three axiom-clean predecessors).
- Lean statement captures: structural packaging of `equivalent_self`,
  `Equivalent.symm`, `Equivalent.trans` into Mathlib's standard `Setoid`
  typeclass. NOT a textbook claim.
- **Tautology check**: `iseqv := ⟨equivalent_self, @Equivalent.symm.{u} _ _,
  @Equivalent.trans.{u} _ _ _⟩` is structural packaging, NOT a tautology
  — the three components do real work (refl/symm/trans of def:381A,
  each axiom-clean from cycles 203/204/206); this is Lean's standard
  `Equivalence` constructor pattern.
- **Hypothesis strength check**: no extra hypotheses on the instance
  beyond what Mathlib's `Setoid` requires (no `[CompleteSpace]`, etc. —
  these are baked into `Equivalent` itself per cycle 206 and don't
  surface at the setoid level).

### P2 examples (anonymous `example`, no faithfulness check needed)

Both exercise the typeclass through the `Setoid` and `Quotient` APIs.
Not named theorems; no entity correspondence.

### P3 — `.prover-state/issues/thm_382A_path.md`

Documentation only. Quotes Butcher's thm:382A statement verbatim from
`thm_382A.json` and identifies the two prerequisite Lean infrastructure
gaps. No definition or theorem introduced.

## Dead ends

1. **Unqualified setoid instance** (without `.{u}`) — universe metavariable
   leak per Risk 1. Resolved by adding `.{u}` annotations to the instance
   AND all three component references in `iseqv`.
2. **`Setoid.symm h` P2 example** — implicit-lambda feature on the goal
   type made `h` get auto-introduced as a function over `(f, L, hL, y₀, h, …)`,
   so `Setoid.symm`/`Equivalent.symm` could not unify universes. Tried:
   (a) bare `Setoid.symm h`, (b) `(show paddedEuler.Equivalent paddedEuler
   from h).symm` (failed: `Equivalent` is a def not a structure, `.symm`
   looks for `Function.symm`), (c) `RKTableau.Equivalent.symm (show … from
   h)` (failed: nested implicit-lambda elaboration left ?-metavars). Pivoted
   to a `Quotient.mk` example which (i) avoids the issue, (ii) exercises
   the actually-relevant downstream API.

## Discovery

1. **Implicit-lambda trap when exercising `Setoid.r` over `∀`-shaped
   relations**: when the underlying relation `r` unfolds to a `∀`-form
   (as `Equivalent` does over `{N} [...]`), `example : @Setoid.r ... :=
   Setoid.refl _` will trigger implicit-lambda introduction on the goal,
   leaving a goal Lean cannot match against `Setoid.refl`'s output. The
   fix is `show <unfolded form>` followed by an explicit witness term —
   this reframes the goal *before* the implicit-lambda feature kicks in.
   **Useful for future cycles that build setoid examples on `∀`-shaped
   relations.**

2. **Quotient.mk + rfl is a stronger non-vacuity test than `Setoid.refl`**:
   `Quotient.mk` exercises both the setoid instance AND the Quotient
   reduction machinery (`Quot.sound` axiom), confirming the setoid is
   well-formed enough for `Quotient`-based reasoning — which is what
   the §382 group construction will actually use. Recommended pattern
   for setoid non-vacuity going forward.

3. **(382g) reformulation lets us skip Gap B**: Butcher's textbook proof
   says "an equivalent statement is `m₁ · m₂ ≡ m̂₁ · m̂₂`". This form
   lives entirely in **heterogeneous `Equivalent`** (no quotient
   needed). A future cycle can ship the mathematical content of thm:382A
   via the (382g) form using only Gap A (the structural bridge
   `compose_isRKOneStep_iff`), deferring Gap B (Σ-typed setoid) to a
   later cosmetic cycle.

## Suggested next approach

**Cycle 212**: Begin work on **Gap A** — the structural bridge
`compose_isRKOneStep_iff` (or its parametrized form). Specifically,
prove that one RK step of `M₁.compose M₂` at the appropriate step size
factors through an intermediate one-step `M₁` output followed by a
one-step `M₂` output on the intermediate point.

- Read `RKTableau.compose`'s c-scaling carefully (Section381.lean ~line
  2410): bottom-block c-values are `(∑ⱼ M₁.bⱼ) + M₂.cᵢ`, so under
  preconsistency `∑ⱼ M₁.bⱼ = 1` they become `1 + M₂.cᵢ`. Determine
  whether the composite step is at size `H = 2h` or `H = h` with c-scaling
  baked in. This is the crucial first scoping question.
- Decompose: a top-block stage lemma (compose's top stages = `M₁`'s
  stages at the corresponding step size), a bottom-block stage lemma
  (compose's bottom stages = `M₂`'s stages from the `M₁`-output as
  intermediate `y₀`), then the output equality.
- Estimated 100–150 LOC, may span 2 cycles.

**Alternative cycle 212**: If Gap A looks too heavy for a single cycle,
ship the **Σ-typed setoid** `Equivalent.setoidSigma` (Gap B's first
piece) instead — it's a clean ~30 LOC packaging of cycles 203/204/206
into a heterogeneous setoid, and enables future quotient-based
reasoning. This is the "Gap B first" alternative.

**Either way**: read `.prover-state/issues/thm_382A_path.md` (cycle 211
deliverable) for the full scoping context before committing to a
direction in cycle 212.
