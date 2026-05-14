# Issue: Path to thm:382A (well-definedness of compose on equivalence classes)

## Textbook statement (from `extraction/formalization_data/entities/thm_382A.json`)

> Let $m_1$, $m_2$, $\widehat{m}_1$, $\widehat{m}_2$ denote Runge–Kutta methods, such that
> $$\widehat{m}_1 \equiv m_1 \quad \text{and} \quad \widehat{m}_2 \equiv m_2. \tag{382f}$$
> Then
> $$[m_1 \cdot m_2] = [\widehat{m}_1 \cdot \widehat{m}_2].$$
> Equivalent form (382g): $m_1 \cdot m_2 \equiv \widehat{m}_1 \cdot \widehat{m}_2$.

Textbook proof: for Lipschitz $f$ and sufficiently small $h$, output values
after the two-step sequence $m_1 \cdot m_2$ and $\widehat{m}_1 \cdot \widehat{m}_2$
agree pointwise because $m_1 \equiv \widehat{m}_1$ on the first step and
$m_2 \equiv \widehat{m}_2$ on the second.

So **thm:382A is well-definedness of `RKTableau.compose` on equivalence
classes**, NOT raw associativity. This frames the proof obligation: given
two equivalences (one per factor), output equality of the composite holds
on every Lipschitz field at every small enough step size.

## Current state (after cycle 211)

- **Cycle 203**: `RKTableau.equivalent_self` — reflexivity of def:381A (axiom-clean).
- **Cycle 204**: `RKTableau.Equivalent.symm.{u}` — symmetry (axiom-clean).
- **Cycle 205**: `IsRKOneStep_exists` (Banach existence for the stage map under contraction).
- **Cycle 206**: `RKTableau.Equivalent.trans.{u}` — transitivity, with `[CompleteSpace N]` baked into def:381A (axiom-clean).
- **Cycle 207**: `RKTableau.PReducesTo.toEquivalent.{u}` (axiom-clean).
- **Cycle 208**: `RKTableau.PEquivalent.toEquivalent.{u}` (axiom-clean).
- **Cycle 209**: `RKTableau.compose` + `compose_A_topLeft` / `compose_A_topRight` / `compose_A_botRight` simp lemmas.
- **Cycle 210**: `RKTableau.IsExplicit` predicate + `compose_isExplicit_iff`, plus `paddedEuler_isExplicit` non-vacuity. `compose_assoc` correctly deferred — see `.prover-state/issues/compose_assoc_HEq_plumbing.md`.
- **Cycle 211 (this cycle)**: `RKTableau.Equivalent.setoid.{u} (s : ℕ) : Setoid (RKTableau s)` — fixed-stage setoid instance composing the three axiom-clean predecessors (refl/symm/trans). Non-vacuity examples: setoid-reflexivity at `paddedEuler` + Quotient.mk well-formedness.

## Two prerequisite gaps before a direct thm:382A proof

### Gap A — Structural bridge: `compose_isRKOneStep_iff`

**Statement (target)**: For sufficiently small step size `H` and Lipschitz `f`,
a single RK step of `M₁.compose M₂` at step size `H` from `y₀` to `y_final`
factors as: there exists an intermediate `y_mid` such that `M₁.IsRKOneStep f y₀ H y_mid`
and `M₂.IsRKOneStep f y_mid H y_final`. (Or with an `H = 2h` scaling factor —
needs scrutiny against compose's c-values.)

Current `RKTableau.compose` (cycle 209, line ~2410 of `Section381.lean`):
```
c := Fin.append M₁.c (fun i : Fin s₂ => (∑ j : Fin s₁, M₁.b j) + M₂.c i)
b := Fin.append M₁.b M₂.b
A := Fin.append (Fin.append M₁.A (fun _ _ => 0))
                (Fin.append (fun i j => M₂.b j) M₂.A)  -- shape-roughly; verify in file
```
The `c`-values for the bottom block are `(∑ⱼ M₁.bⱼ) + M₂.cᵢ`. Under
preconsistency `∑ⱼ M₁.bⱼ = 1`, this becomes `1 + M₂.cᵢ`. Comparing
against two consecutive steps of `M₁` then `M₂` at step size `h`:
- The first step covers `[t, t+h]`; if the composite step at size `H`
  covers `[t, t+H]`, then `H = 2h` makes the second step `[t+h, t+2h] = [t+H/2, t+H]`.
- The top-block stages of compose are the stages of `M₁` at step size
  `H/2 = h` (need careful check), shifted to `c₁ᵢ · H = c₁ᵢ · 2h`.
  Wait — but compose's top-block `c` is exactly `M₁.c i`, NOT `2 · M₁.c i`.
  So either compose's step is size `h` covering `M₁`'s stages exactly,
  and then `M₂`'s stages are at offsets `c = 1 + M₂.c i` which corresponds
  to step `M₂` covering `[t+h, t+2h]` with offset `(c - 1) · h = M₂.c i · h`
  AND the composite step lives on `[t, t+2h]`, in which case
  `H = 2h` and the c-values are `c · H/2`. Hmm.
- This needs careful normalization. Estimated **100–150 LOC** of mostly
  Fin-shape and norm/abs arithmetic.

Even with the right scaling, the bridge lemma has to show:
1. The composite's bottom-block stages, parameterized by Banach
   uniqueness on the `(s₁ + s₂)`-stage system, agree with `M₂`'s stages
   on the **right** input (which is `y₀ + h • Σⱼ M₁.bⱼ • f(Yᵢ)` — i.e.
   the `M₁`-output of the first step).
2. The composite output `y₀ + H • Σ M₂.b · f(stage)` equals
   `M₁(y₀) → M₂` composite output.

This is the genuinely hard prerequisite. Estimated **multi-cycle**.

### Gap B — Heterogeneous quotient

Butcher's §382 group lives on `Σ s : ℕ, RKTableau s` quotiented by
heterogeneous `Equivalent` (i.e. methods with different stage counts can
be equivalent). The cycle 211 `Equivalent.setoid` only quotients
*fixed-stage* methods.

For the group structure on **equivalence classes of all RK methods**,
we need:
1. `setoidSigma : Setoid (Σ s : ℕ, RKTableau s)` with
   `r ⟨s₁, M₁⟩ ⟨s₂, M₂⟩ := @Equivalent.{u} s₁ s₂ M₁ M₂` and `iseqv`
   built from cycle 203's `equivalent_self`, cycle 204's `Equivalent.symm.{u}`,
   cycle 206's `Equivalent.trans.{u}`. (Quick to write; ~20–30 LOC.)
2. `compose` lifts: define
   `composeQ : Quotient setoidSigma → Quotient setoidSigma → Quotient setoidSigma`
   via `Quotient.lift₂`, using Gap A + thm:382A's well-definedness
   conclusion to discharge the proof obligation.
3. The group axioms (identity, inverse, associativity) become
   theorems on `Quotient setoidSigma`; associativity in particular can
   be proved on representatives once `compose_assoc` (cycle 210
   deferred) or its replacement via thm:382A is available.

Gap B is mostly mechanical *once* Gap A is established, since the
heterogeneous `Equivalent.{u}` machinery is already axiom-clean from
cycles 203/204/206.

## Recommended cycle plan (3–5 cycles to close thm:382A)

- **Cycle 212**: Ship Gap A — the structural bridge `compose_isRKOneStep_iff`
  (or its parametrized variant `compose_oneStep_factors_through_M₁_then_M₂`).
  This is the genuine "give compose its meaning" lemma. ~100–150 LOC,
  may itself span 2 cycles depending on Fin-shape complexity.
- **Cycle 213**: Ship the Σ-typed setoid `setoidSigma` + the
  `composeQ` lift on quotients. ~50 LOC, mostly structural.
- **Cycle 214**: Prove **thm:382A directly** by composing Gap A on both
  the `m₁·m₂` and `m̂₁·m̂₂` sides, then closing the output-equality goal
  via the two hypotheses `m₁ ≡ m̂₁`, `m₂ ≡ m̂₂` instantiated at the
  intermediate point produced by Gap A.
- **Cycle 215 (optional)**: Group structure on `Quotient setoidSigma`
  with identity = `[explicitEuler]` (cycle 030's `equivalent_explicitEuler_self`
  reincarnated as `Quotient.mk` of the explicitEuler witness), inverse
  via §382 textbook construction (negate `b` and `A`?), associativity
  via cycle 210's deferred `compose_assoc` or via Gap A on three-fold
  composites.

Total: **3–5 cycles** of disciplined work, all axiom-clean expected.

## Cross-references

- `RKTableau.compose` (cycle 209, Section381.lean ~line 2410).
- `compose_A_topLeft`/`compose_A_topRight`/`compose_A_botRight` simp lemmas
  (cycle 209).
- `compose_isExplicit_iff` (cycle 210).
- `compose_assoc` deferred — see `.prover-state/issues/compose_assoc_HEq_plumbing.md`.
- `Equivalent.setoid.{u}` (cycle 211) — the fixed-stage piece of Gap B.
- Cycle 203/204/206's refl/symm/trans of def:381A — the building blocks
  for both Gap B and the thm:382A output-equality argument.
- Cycle 205's `IsRKOneStep_exists` (Banach existence) — essential for
  threading through the intermediate `y_mid` in Gap A.
- Cycle 207's `PReducesTo.toEquivalent` and cycle 208's
  `PEquivalent.toEquivalent` for §381H ↔ machinery (orthogonal but useful
  for promoting reduction witnesses to `≡`).

## Why this path is right (and why direct attempts won't work)

1. **Gap A is unavoidable.** thm:382A's textbook proof says "let `y₁` and
   `y₂` denote the output values over the two steps for the sequence of
   steps constituting `m₁ · m₂`". This sentence is **a claim about the
   stage values of compose**, which is currently only a syntactic
   definition (cycle 209). Without Gap A, there is no way to invoke the
   hypotheses `m₁ ≡ m̂₁` and `m₂ ≡ m̂₂` because we don't yet have a
   theorem that compose's one-step output factors through `m₁`'s and
   `m₂`'s one-step outputs.

2. **Gap B is needed for `[·]` notation.** The textbook writes
   `[m₁ · m₂] = [m̂₁ · m̂₂]`, where `[·]` denotes equivalence class. In
   Lean, this requires a `Quotient` — and for `m₁ · m₂` to live in the
   same `Quotient` as `m̂₁ · m̂₂` (which may have different stage
   counts, since `m₁` and `m̂₁` may have different stage counts), the
   `Quotient` must be over the **heterogeneous-stage** Σ-typed setoid.
   The fixed-stage setoid from cycle 211 is insufficient for the bare
   `[m₁ · m₂] = [m̂₁ · m̂₂]` form (though the "equivalent form (382g)
   `m₁ · m₂ ≡ m̂₁ · m̂₂`" doesn't need the quotient — it's a direct
   heterogeneous `Equivalent` claim).

3. **The (382g) reformulation lets us skip Gap B in cycle 214.** Butcher
   himself notes "an equivalent statement is `m₁ · m₂ ≡ m̂₁ · m̂₂`". This
   form lives entirely in heterogeneous `Equivalent` and avoids the
   quotient infrastructure. A practical plan:
   - **Cycle 214a**: prove the (382g) form `m₁.compose m₂ ≡ m̂₁.compose m̂₂`
     directly via Gap A + the two hypothesis equivalences. **Axiom-clean
     output, ships the mathematical content of thm:382A.**
   - **Cycle 214b (cosmetic)**: ship the `[m₁ · m₂] = [m̂₁ · m̂₂]` form
     once Gap B (Σ-typed setoid + `composeQ`) is available, as a one-line
     `Quotient.sound`-style corollary.

   This split saves a cycle and front-loads the math (Gap A + (382g)) ahead
   of the bookkeeping (Gap B + bracketed form).

## DO NOT attempt this cycle (cycle 211)

This file is **scoping/documentation only**. Cycle 211 ships the
fixed-stage setoid + non-vacuity, period. Gap A and Gap B are multi-cycle
work and must be planned by the next Planner cycle, not freelanced now.
