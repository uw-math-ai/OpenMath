# Issue: Path to thm:382A (well-definedness of compose on equivalence classes)

## Cycle 216 update — (382g) form CLOSED

Cycle 216 closed `compose_equivalent_compose` (the (382g) form) per the
recipe pre-positioned in the Cycle 215 update below:

1. **Equivalent definition refactored** (Option A): `∀ y₀, ∃ h₀, ...`
   → `∃ h₀, ∀ y₀, ...` (one-line binder reorder).
2. **All downstream consumers ported** by mechanical binder reorder:
   `equivalent_self`, `equivalent_explicitEuler_self`, `Equivalent.symm`,
   `Equivalent.trans`, `pReduced_equivalent`, `zeroReduced_equivalent`.
   The `setoid`/`setoidSigma`/`PReducesTo.toEquivalent`/
   `PEquivalent.toEquivalent`/paddedEuler witnesses needed no body change.
3. **`compose_equivalent_compose` body** replaced the cycle 215 sorry-scaffold
   with the route B.1 recipe (~20 LOC) verbatim — `hEq₂_app` applied at
   `y_mid'` is now admissible because y₀ is universally quantified inside
   the existential.
4. **Status**: `thm:382A` fixed-stage (382g) form formalized, axiom-clean
   (`[propext, Classical.choice, Quot.sound]`). Sorry count 1 → 0.

Cycles 217+ outlook unchanged: heterogeneous-stage (382g) form +
`composeQ` lift via `Quotient.lift₂` + (382f) bracketed form + §382
group structure.

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

---

## Cycle 215 update — (382g) form sorry-scaffolded; new uniform-threshold gap surfaced

**Cycle 213** shipped Gap A reverse direction `RKTableau.compose_of_isRKOneStep`
(axiom-clean, no smallness, no Lipschitz; algebraic block-by-block
assembly via `Fin.append Y₁ Y₂` + cycle 209's compose-simp set + the
3-step regroup `rw [smul_add, ← add_assoc, ← hY₁_out]`).

**Cycle 214** shipped Gap A in full as an iff via
`RKTableau.compose_isRKOneStep_iff` (axiom-clean). The forward
direction turned out to be **purely algebraic** — no Lipschitz, no
smallness threshold, no `[CompleteSpace N]`, no invocation of cycle
205's `IsRKOneStep_exists`. Given a composite stage tuple `Y_compose`,
M₁ and M₂'s stage tuples are *already* `Y_compose ∘ Fin.castAdd s₂` and
`Y_compose ∘ Fin.natAdd s₁` (no existential construction), and `y_mid`
is defined algebraically by projection. This overrode the cycle 212
scoping doc's anticipation of Banach/Lipschitz machinery.

**Cycle 215** attempted to ship the (382g) form
`RKTableau.compose_equivalent_compose`. The cycle 215 strategy's recipe
(route B.1, ~20 LOC) routes through cycle 214's iff to extract `y_mid`
and `y_mid'`, then applies `Equivalent`'s output-uniqueness twice:
`hEq₁` on `y_mid = y_mid'` (both step from y₀ — clean), then `hEq₂` on
`y_final = y_final'` (after rewrite, both step from `y_mid'`).

**The recipe FAILS.** The current `Equivalent` definition (cycle 206)
has the quantifier order `∀ y₀, ∃ h₀, ∀ h ≤ h₀, ...` — non-uniform in
`y₀`. When `hEq₂` is destructured at the outer `y₀`, the resulting
output-uniqueness statement requires both `M₂` and `M₂'` steps to fire
from `y₀`, but the M₂ step in the composite fires from `y_mid'` (not
`y₀`). Destructuring `hEq₂` at `y_mid'` instead works syntactically
but produces a threshold `H₂(y_mid')` that depends on `y_mid'`, which
depends on `H` — circular.

Butcher's textbook proof reads "if h is sufficiently small, then
y₁ = ŷ₁ because m₁ ≡ m̂₁, and y₂ = ŷ₂ because m₂ ≡ m̂₂", implicitly
assuming **uniform** smallness across initial values. Every concrete
`Equivalent` instance in our codebase has a y₀-uniform threshold (e.g.
`equivalent_self`'s `1/(2*(L*C+1))` is y₀-independent), but the
abstract type doesn't expose this.

**Cycle 215 deliverable per the abort threshold (§H)**:

1. `RKTableau.compose_equivalent_compose` shipped as a **sorry-scaffolded
   signature** (fixed-stage form) in `OpenMath/Chapter3/Section381.lean`
   immediately after cycle 214's `compose_isRKOneStep_iff`. Docstring
   documents the quantifier-order gap.
2. P2 paddedEuler reflexive-on-both-factors `example` exercising the
   scaffolded signature in `namespace OpenMath.Chapter3.Section381`.
3. New issue file
   `.prover-state/issues/compose_equivalent_compose_uniform_threshold.md`
   with full gap analysis, four ruled-out workaround attempts, and the
   recommended **Option A** (refactor `Equivalent` to uniform form
   `∃ h₀, ∀ y₀, ...`).
4. `lean_status.json` thm:382A row updated: `unformalized` → `partial`,
   with cycle 215 note + link to the new issue file.
5. `plan.md` thm:382A row: `[ ]` → `[~]` with cycle 215 line.

Sorry count: 0 → 1. Cycle 214's `compose_isRKOneStep_iff` and cycle 213's
`compose_of_isRKOneStep` remain axiom-clean.

### Cycle 216 entry point (recommended): refactor `Equivalent` to uniform form

Change the `Equivalent` definition at
`OpenMath/Chapter3/Section381.lean` line ~980 from:

```lean
def Equivalent {s s' : ℕ} (M : RKTableau s) (M' : RKTableau s') : Prop :=
  ∀ {N} [...] (f : N → N) (L : ℝ≥0) (_hL : LipschitzWith L f) (y₀ : N),
    ∃ h₀ > (0 : ℝ), ∀ h, 0 < h → h ≤ h₀ →
      ∀ y₁ y₁', M.IsRKOneStep f y₀ h y₁ → M'.IsRKOneStep f y₀ h y₁' →
        y₁ = y₁'
```

to:

```lean
def Equivalent {s s' : ℕ} (M : RKTableau s) (M' : RKTableau s') : Prop :=
  ∀ {N} [...] (f : N → N) (L : ℝ≥0) (_hL : LipschitzWith L f),
    ∃ h₀ > (0 : ℝ), ∀ (y₀ : N), ∀ h, 0 < h → h ≤ h₀ →
      ∀ y₁ y₁', M.IsRKOneStep f y₀ h y₁ → M'.IsRKOneStep f y₀ h y₁' →
        y₁ = y₁'
```

Then update existing proofs:
- `equivalent_self`: threshold `1/(2*(L*C+1))` is already y₀-independent;
  port by moving the `intro y₀` after `refine ⟨..., ?_⟩`.
- `Equivalent.symm`: re-uses input threshold; port by moving the `y₀`
  binder.
- `Equivalent.trans`: takes min of three thresholds (all y₀-independent);
  port similarly. The Banach existence at the middle method M' uses
  `IsRKOneStep_exists` at y₀ — instantiate at the universally-quantified
  `y₀` from the inner binder.
- `PReducesTo.toEquivalent` and downstream: mechanical updates.

After the refactor, retry cycle 215's recipe verbatim — it should close
cleanly. The body becomes:

```lean
intro N _ _ _ f L hL
obtain ⟨H₁, hH₁_pos, hEq₁_app⟩ := hEq₁ f L hL
obtain ⟨H₂, hH₂_pos, hEq₂_app⟩ := hEq₂ f L hL
refine ⟨min H₁ H₂, lt_min hH₁_pos hH₂_pos, ?_⟩
intro y₀ H hH_pos hH_le y_final y_final' h_M₁M₂ h_M₁'M₂'
have hH_le_H₁ : H ≤ H₁ := le_trans hH_le (min_le_left _ _)
have hH_le_H₂ : H ≤ H₂ := le_trans hH_le (min_le_right _ _)
obtain ⟨y_mid, h_M₁_step, h_M₂_step⟩ :=
  (compose_isRKOneStep_iff M₁ M₂ f y₀ H y_final).mp h_M₁M₂
obtain ⟨y_mid', h_M₁'_step, h_M₂'_step⟩ :=
  (compose_isRKOneStep_iff M₁' M₂' f y₀ H y_final').mp h_M₁'M₂'
have hmid_eq : y_mid = y_mid' :=
  hEq₁_app y₀ H hH_pos hH_le_H₁ y_mid y_mid' h_M₁_step h_M₁'_step
rw [hmid_eq] at h_M₂_step
exact hEq₂_app y_mid' H hH_pos hH_le_H₂ y_final y_final' h_M₂_step h_M₂'_step
```

The key change: `hEq₂_app` is applied at `y_mid'` (a specific value
inside the inner forall), which the refactored definition allows because
`hEq₂_app` quantifies universally over `y₀` inside the existential.

Estimated cycle 216 LOC: ~30 LOC refactor churn + ~20 LOC compose proof
+ ~5 LOC P2 update = ~55 LOC total.

### Cycles 217+ outlook

- **Cycle 217**: heterogeneous-stage form of `compose_equivalent_compose`
  — replace `s₁ s₂ : ℕ` with `s₁ s₁' s₂ s₂' : ℕ` where M₁ : RKTableau s₁,
  M₁' : RKTableau s₁', etc. The body should largely port (the proof
  works at the abstract space N, not the stage count). ~30–50 LOC.
- **Cycle 218**: `composeQ` lift via `Quotient.lift₂` on cycle 212's
  `Equivalent.setoidSigma`, consuming cycle 217's heterogeneous form.
  Closes the bracketed (382f) form `[m₁·m₂] = [m̂₁·m̂₂]`. ~50 LOC.
- **Cycle 219+**: §382 group structure (identity element + inverse +
  associativity), §383 lemmas, §384 thm:384A, etc.

## Cycle 217 update — heterogeneous form closed

Cycle 217 shipped the heterogeneous-stage form of
`compose_equivalent_compose` (§B of the cycle 217 strategy), confirming
the mechanical-port hypothesis from cycle 216's task results.
`OpenMath/Chapter3/Section381.lean` lines 2708–2729: signature
generalised from fixed-stage `{s₁ s₂ : ℕ}` to heterogeneous
`{s₁ s₁' s₂ s₂' : ℕ}`; body byte-for-byte identical to cycle 216.
Compiled cleanly on first attempt (warm rebuild 6.2s); call site of
cycle 215's `paddedEuler_equivalent_self`-driven non-vacuity example
required no edit (Lean unifies all four implicit stage counts to `2`
from the `paddedEuler : RKTableau 2` annotations).

Cycle 217 P2 (heterogeneous non-vacuity) shipped: a `2+2` vs `1+1`
composite-`Equivalent` witness threading `paddedEuler_equivalent_pReduced`
through both sides — the *actually relevant* heterogeneous test case
that the homogeneous P2 (cycle 216) couldn't exercise.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`) on
`compose_equivalent_compose`; no regressions on cycle 213's
`compose_of_isRKOneStep` or cycle 214's `compose_isRKOneStep_iff`.

### Cycle 218 entry point — `composeQ` via `Quotient.lift₂`

The heterogeneous-stage `compose_equivalent_compose` (cycle 217) is
precisely the respect obligation for a binary `composeQ` operation
on the Σ-typed quotient `Quotient (RKTableau.Equivalent.setoidSigma)`.

Target signature (cycle 218):

```lean
def composeQ :
    Quotient RKTableau.Equivalent.setoidSigma →
    Quotient RKTableau.Equivalent.setoidSigma →
    Quotient RKTableau.Equivalent.setoidSigma := by
  refine Quotient.lift₂ (fun p q =>
    Quotient.mk' ⟨p.1 + q.1, p.2.compose q.2⟩) ?_
  rintro ⟨s₁, M₁⟩ ⟨s₂, M₂⟩ ⟨s₁', M₁'⟩ ⟨s₂', M₂'⟩ hEq₁ hEq₂
  apply Quotient.sound
  show (M₁.compose M₂).Equivalent (M₁'.compose M₂')
  exact RKTableau.compose_equivalent_compose M₁ M₁' M₂ M₂' hEq₁ hEq₂
```

The respect obligation unpacks `Setoid.r` on Σ-typed inputs to
heterogeneous `Equivalent` (cycle 212's `setoidSigma.iseqv` definition
forwards the second projection's `Equivalent`), and the conclusion is
cycle 217's theorem applied directly.

**Risk for cycle 218's planner**: `Quotient.lift₂` accepts a binary
operation `α → α → β` where `β` does not depend on the inputs. In
our case `composeQ`'s output type `Quotient setoidSigma` is independent
of the inputs (the dependence on `s₁ + s₂` is *inside* the Σ-packed
element, not the output type), so plain `Quotient.lift₂` suffices —
no `Quotient.hrecOn₂` needed.

**Risk on Σ-relation unfolding**: cycle 212 defines
`Equivalent.setoidSigma` with `Setoid.r ⟨s₁, M₁⟩ ⟨s₁', M₁'⟩` unfolding
to `Equivalent M₁ M₁'` (heterogeneous form). Cycle 218 should
double-check via `show` reframing (cycle 211/212 precedent) that the
respect obligation destructures cleanly.

LOC estimate: ~10 LOC for `composeQ` + ~10 LOC for non-vacuity examples
(`composeQ ⟦⟨2, paddedEuler⟩⟧ ⟦⟨2, paddedEuler⟩⟧ = ⟦⟨4, paddedEuler.compose paddedEuler⟩⟧`
plus the heterogeneous reduction equivalent via cycle 217 P2 witness).
The (382f) bracketed form `[m₁·m₂] = [m̂₁·m̂₂]` then follows from
`Quotient.sound` on cycle 217's theorem.

## Cycle 218 update — `composeQ` shipped, (382f) bracketed form CLOSED

Cycle 218 shipped both deliverables clean, no surprises:

1. **`RKTableau.composeQ.{u} : Quotient Equivalent.setoidSigma.{u} →
   Quotient Equivalent.setoidSigma.{u} → Quotient Equivalent.setoidSigma.{u}`**
   — `noncomputable def` via `Quotient.lift₂` with the respect
   obligation discharged by cycle 217's `compose_equivalent_compose`
   applied directly after `rintro` + `apply Quotient.sound`. A single
   `show @Equivalent.{u} (s₁ + s₂) (s₁' + s₂') (M₁.compose M₂)
   (M₁'.compose M₂')` after the rintro stabilises the goal for the
   final `exact`. Axiom-clean ([propext, Classical.choice, Quot.sound]).

2. **`RKTableau.composeQ_eq_of_equivalent.{u}`** (the (382f) bracketed
   form of `thm:382A` directly): if `M₁ ≡ M̂₁` and `M₂ ≡ M̂₂`
   heterogeneous-stage, then `[M₁ · M₂] = [M̂₁ · M̂₂]` in
   `Quotient Equivalent.setoidSigma`. Body is `show Quotient.mk _ _
   = Quotient.mk _ _; exact Quotient.sound (compose_equivalent_compose
   ...)`. Axiom-clean.

3. **P2 non-vacuity (W1 homogeneous)**: `composeQ ⟦⟨2, paddedEuler⟩⟧²
   = ⟦⟨2+2, paddedEuler.compose paddedEuler⟩⟧` closed by plain `rfl`
   through `Quotient.lift₂_mk` definitional reduction — no `rw` or
   `simp` needed.

4. **P2 non-vacuity (W2 heterogeneous)**: `composeQ` on `⟦⟨2,
   paddedEuler⟩⟧²` and `composeQ` on `⟦⟨1, paddedEuler.pReduced
   pairPartition⟩⟧²` coincide via `composeQ_eq_of_equivalent` with
   `paddedEuler_equivalent_pReduced` × 2. The *actually relevant*
   heterogeneous witness — stage sums `(2+2) ≠ (1+1)` on the two
   sides, mediated by `Quotient.sound`.

**Pre-flagged risks for cycle 218 (R1–R5 from cycle 218 strategy §C)
that fired or did not fire:**

- **R1 (Quotient.lift₂ explicit setoid args)**: did NOT fire — Mathlib's
  curried `Quotient.lift₂` infers both source setoids from the
  Σ-typed function and the output type. Loogle confirmed signature
  `Quotient.lift₂ : (α → β → φ) → (∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ →
  f a₁ b₁ = f a₂ b₂) → Quotient s₁ → Quotient s₂ → φ`. No explicit
  setoid binders needed.
- **R2 (Σ-relation unfolding `Setoid.r` → `Equivalent`)**: did NOT fire
  in practice — but defensive `show @Equivalent.{u} ...` after the
  rintro was added prophylactically and is recommended for future
  consumers of `setoidSigma` (matches cycle 217 idioms).
- **R3 (Mathlib API name drift)**: did NOT fire — `Quotient.lift₂`
  and `Quotient.lift₂_mk` exist at expected names in `Mathlib.Data.Quot`
  and `Init.Core` respectively.
- **R4 (`noncomputable`)**: applied as planned; without it Lean would
  reject the definition because `Quotient.lift₂` uses `Quot.lift`
  which is itself opaque/noncomputable.
- **R5 (implicit arity on `compose_equivalent_compose`)**: did NOT fire
  — passing all four tableaux explicitly (`M₁ M₁' M₂ M₂'`) ahead of
  `hEq₁ hEq₂` works on first compile, no implicit-stage ambiguity.

**Both textbook forms of `thm:382A` are now closed**: the (382g)
un-bracketed heterogeneous form (`m₁ · m₂ ≡ m̂₁ · m̂₂`, cycles 215–217)
and the (382f) bracketed form (`[m₁ · m₂] = [m̂₁ · m̂₂]`, cycle 218).
`thm:382A`'s row in `lean_status.json` is bumped to `formalized`,
`lean_symbol` switched to `composeQ_eq_of_equivalent` (the bracketed
form is the headline statement).

**Cycle 219+ outlook — §382 group structure**: with `composeQ` in
hand, the natural next deliverables are:

1. **Identity element**: pick the textbook identity (likely the
   trivial 0-stage tableau or `explicitEuler` — Butcher §382 names it).
   Prove `composeQ ⟦identity⟧ q = q` and `composeQ q ⟦identity⟧ = q`
   for all `q : Quotient setoidSigma`.
2. **Inverse element**: Butcher §382's textbook inverse construction
   (negate `b`, transpose `A`? — needs careful reading of §382).
3. **Associativity**: cycle 210's deferred `compose_assoc` may now
   become tractable on `Quotient` via `Quotient.sound` on an
   `Equivalent`-level associativity (the HEq plumbing that blocked
   the on-the-nose `compose_assoc` is finessed by the quotient).

These are cycle 219+ work; cycle 218 ships `composeQ` and the
bracketed corollary, period.

---

## Cycle 219 update — §382 group identity element shipped

Cycle 219 closes the **identity element** of the §382 group structure
on `Quotient Equivalent.setoidSigma`, the first of the four deliverables
sketched in the cycle 218 outlook above (identity, inverse,
associativity, and the `Group` instance package).

### Six new symbols (all in `OpenMath/Chapter3/Section381.lean`, inside
`namespace OpenMath.Chapter3.Section312.RKTableau`, immediately after
cycle 218's `composeQ_eq_of_equivalent`):

1. **`RKTableau.id : RKTableau 0`** — the 0-stage no-op tableau.
   Defined as `{A := 0, b := 0, c := 0}` — the `Zero` instances on
   `Matrix (Fin 0) (Fin 0) ℝ` and `Fin 0 → ℝ` (Pi.Zero) infer cleanly;
   no `Fin.elim0` needed in the body. **`explicitEuler` is NOT the
   identity** — it advances by `H • f y₀`, which is exactly what we
   don't want from a no-op tableau. The 0-stage tableau is the unique
   no-op (its `b` sum is empty, so the output update is `y₀ + h • 0 = y₀`).

2. **`@[simp] RKTableau.id_isRKOneStep_iff`** — the load-bearing
   reduction lemma `RKTableau.id.IsRKOneStep f y₀ h y₁ ↔ y₁ = y₀`.
   Both directions close by `simpa` through Lean's empty `Fin 0` sum
   collapse (no explicit `Fin.sum_univ_zero` or `Finset.sum_empty`
   needed — `simp` handles it via the universe-zero sum lemmas already
   in the default simp set). The reverse direction provides
   `Fin.elim0` as the stage tuple witness.

3. **`RKTableau.compose_id_equivalent.{u} {s} (M : RKTableau s) :
   @Equivalent.{u} (s + 0) s (M.compose RKTableau.id) M`** — right
   identity law at the `Equivalent` level. HOMOGENEOUS-stage since
   `s + 0 = s` is definitionally equal in Lean 4 (`Nat.add` recurses
   on the second argument), so no HEq plumbing is needed despite the
   heterogeneous-looking signature. Proof sketch: extract intermediate
   `y_mid` from the composite step via cycle 214's
   `compose_isRKOneStep_iff.mp`, collapse the right-factor
   `RKTableau.id.IsRKOneStep f y_mid H y₁` to `y₁ = y_mid` via the new
   `id_isRKOneStep_iff`, rewrite, and discharge the remaining `y_mid =
   y₁'` against `M.equivalent_self` (cycle 203) applied at `y₀`.

4. **`RKTableau.id_compose_equivalent.{u} {s} (M : RKTableau s) :
   @Equivalent.{u} (0 + s) s (RKTableau.id.compose M) M`** — left
   identity law at the `Equivalent` level. Unlike (3), the stage
   arithmetic `0 + s = s` is NOT definitionally equal (it requires
   `Nat.zero_add`), so this is a genuinely heterogeneous-stage
   `@Equivalent (0 + s) s` claim. However, the proof works at the
   abstract `IsRKOneStep` level which never inspects stage counts —
   identical in shape to cycle 217's heterogeneous
   `compose_equivalent_compose`. Mirror of (3) with sides swapped:
   factor via `compose_isRKOneStep_iff`, collapse the left-factor
   `id.IsRKOneStep f y₀ H y_mid` to `y_mid = y₀` via
   `id_isRKOneStep_iff`, rewrite `h_M_step` to fire from `y₀`, then
   discharge against `M.equivalent_self`.

5. **`RKTableau.composeQ_id_left.{u} (q : Quotient
   Equivalent.setoidSigma.{u}) : composeQ ⟦⟨0, RKTableau.id⟩⟧ q = q`** —
   the quotient-level left identity law. Immediate consequence of (4)
   via `Quotient.inductionOn` on `q`, destructure the underlying
   `⟨s, M⟩`, reduce `composeQ ⟦⟨0, id⟩⟧ ⟦⟨s, M⟩⟧` to `⟦⟨0+s, id.compose
   M⟩⟧` (definitional through `Quotient.lift₂_mk`), and apply
   `Quotient.sound (id_compose_equivalent M)` to identify the two
   classes.

6. **`RKTableau.composeQ_id_right.{u} (q : Quotient
   Equivalent.setoidSigma.{u}) : composeQ q ⟦⟨0, RKTableau.id⟩⟧ = q`** —
   the quotient-level right identity law. Symmetric to (5), uses
   `compose_id_equivalent` from (3).

### Non-vacuity (P6)

Two `example`s in `namespace OpenMath.Chapter3.Section381` (at the end
of the file, after cycle 218's `composeQ` non-vacuity examples)
exercise the quotient-level laws on the cycle 030 backbone:
`composeQ ⟦⟨0, RKTableau.id⟩⟧ ⟦⟨2, paddedEuler⟩⟧ = ⟦⟨2, paddedEuler⟩⟧`
and the right-handed mirror.

### Risk retrospective (cycle 219 strategy §C)

- **R1 (empty-Finset.sum unfolding)**: did NOT fire — `simpa` on both
  directions of `id_isRKOneStep_iff` handles the empty `Fin 0` sum
  collapse, the `h • 0 = 0` simplification, and the `y₀ + 0 = y₀`
  cleanup automatically; no explicit `Fin.sum_univ_zero` or
  `Finset.sum_empty` needed.
- **R2 (`Fin.elim0` vs `0` for `RKTableau.id`'s body)**: did NOT fire
  — `0` worked cleanly for all three RKTableau fields (`A`, `b`, `c`).
  The `Zero` instances are inferred via Matrix's `Pi.Zero` and the
  function-space `Pi.Zero`.
- **R3 (heterogeneous universe annotation in P4)**: did NOT fire —
  explicit `.{u}` on `Equivalent` works on first compile.
- **R4 (`compose_isRKOneStep_iff` arity at `M = id`)**: did NOT fire —
  Lean infers `s₁ = 0` from `RKTableau.id`'s type without explicit
  annotation (no need to pass `s₁ := 0` explicitly).
- **R5 (`Quotient.ind` motive inference)**: did NOT fire — chose
  `Quotient.inductionOn q` over `Quotient.ind` for cleaner syntax (the
  `motive` is inferred from the goal type without explicit
  specification).
- **R6 (spurious `.{u}` on `RKTableau`)**: did NOT fire — universe
  annotations applied only to `Equivalent.{u}` and
  `Equivalent.setoidSigma.{u}`, never to `RKTableau` references
  (mindful of cycle 218's dead end where this fired).

All six new symbols `[propext, Classical.choice, Quot.sound]`
axiom-clean (no `sorryAx`); cycle 218's `composeQ` and
`composeQ_eq_of_equivalent` re-verified axiom-clean — no regressions.

### Cycle 220+ outlook — §382 inverse element

The natural next step is the **inverse element**. Butcher §382 defines
the inverse method by negating the step size: applying `M` with
step `-h` undoes one step of `M` with step `+h`. The Lean construction
needs reading of Butcher §382's inverse-construction formula carefully
— this is a cycle 220 deliverable with its own pre-flight scoping.

Once inverses are in hand, **associativity** is cycle 221+: an
`Equivalent`-level `compose_assoc` claim, lifted to the quotient via
`Quotient.ind₃` + `Quotient.sound`. This finesses cycle 210's
deferred `compose_assoc` HEq plumbing (the on-the-nose `s₁ + (s₂ + s₃)
= (s₁ + s₂) + s₃` HEq dance is replaced by an abstract-`N`-level
`Equivalent` claim). See `.prover-state/issues/compose_assoc_HEq_plumbing.md`
for the cycle 219 update noting this finesse.

After §382 group structure closes (identity + inverse + associativity),
**`instance : Group (Quotient Equivalent.setoidSigma)`** is cycle 222+
bookkeeping. From there, §383 (group homomorphisms via Φ), §384
(homomorphism to the elementary-weight group), and §388 (subgroups
and quotient groups) all consume the `Group` instance directly.

---

## Cycle 221 update — Equivalent-level associativity CLOSED

The cycle 220 outlook is realized. The third §382 group axiom (after
cycles 219/220's identity and inverse) is now shipped:

1. **`RKTableau.compose_equivalent_compose_assoc.{u}`** at the
   `Equivalent` level — heterogeneous-stage
   `@Equivalent ((s₁ + s₂) + s₃) (s₁ + (s₂ + s₃))
     ((M₁.compose M₂).compose M₃) (M₁.compose (M₂.compose M₃))`
   (~35 LOC body + docstring at
   `OpenMath/Chapter3/Section381.lean` line ~3060).

2. **`RKTableau.composeQ_assoc`** at the quotient level — for
   `p q r : Quotient Equivalent.setoidSigma.{u}`,
   `composeQ (composeQ p q) r = composeQ p (composeQ q r)` (~10
   LOC body + docstring, immediately after deliverable 1) via
   `Quotient.inductionOn₃` + `Quotient.sound`.

The proof recipe generalizes cycles 217 / 219 / 220's abstract-
`IsRKOneStep`-level technique to three factors: threshold
`min (min H₁ H₂) H₃` from three `Mᵢ.equivalent_self f L hL`
applications; factor each side into three sequential single-`Mᵢ`-
step witnesses via cycle 214's `compose_isRKOneStep_iff` (the LHS
unfolds as outer `(M₁·M₂)·M₃` then inner `M₁·M₂`; the RHS as outer
`M₁·(M₂·M₃)` then inner `M₂·M₃`); then three uniqueness chains
(one per `Mᵢ`) force the three intermediates to agree. The proof
never inspects stage counts — the heterogeneous-stage signature is
discharged naturally by abstract-`N`-level reasoning, identical in
shape to cycle 217's heterogeneous `compose_equivalent_compose`.

Both new symbols verified `[propext, Classical.choice, Quot.sound]`
axiom-clean. Cycle 218/219/220 landmarks regression-checked
(`composeQ_eq_of_equivalent`, `composeQ_id_left`, `composeQ_id_right`,
`composeQ_inverse_right`, `composeQ_inverse_left`); no axioms changed.
Section381.lean warm rebuild 7.6s. Sorry count: 0.

P3 non-vacuity: triple `paddedEuler` Equivalent witness at
`((2+2)+2, 2+(2+2))` + quotient-level associativity on three copies
of `⟦⟨2, paddedEuler⟩⟧`.

### Cycle 222+ outlook — `Group` instance

With three of the four `Group` axioms (identity, inverse, associativity)
now closed at the quotient level, cycle 222 is positioned for the
final lift:

1. **`inverse_equivalent_inverse`** (~50 LOC): the missing
   "function respects equivalence" lemma for `RKTableau.inverse`,
   `M ≡ M' → M.inverse ≡ M'.inverse`. Proof recipe (similar to
   `compose_equivalent_compose`): factor a single
   `M.inverse.IsRKOneStep f y₀ H y₁` witness via cycle 220's
   `isRKOneStep_of_inverse_isRKOneStep`, leverage `equivalent_self`
   on `M.inverse` paired with the `M ≡ M'` hypothesis to force
   `y₁ = y₁'` for two parallel `inverse` witnesses.

2. **`inverseQ`** (~10 LOC): lift `RKTableau.inverse` to
   `Quotient Equivalent.setoidSigma` via `Quotient.map` with
   `inverse_equivalent_inverse` as the respect proof (analogous to
   `composeQ` via `Quotient.lift₂`).

3. **`instance : Group (Quotient Equivalent.setoidSigma)`**:
   bundle cycle 219's `composeQ_id_left`/`composeQ_id_right`,
   cycle 220's `composeQ_inverse_right`/`composeQ_inverse_left`,
   and cycle 221's `composeQ_assoc` into Mathlib's `Group`
   typeclass. The `mul`/`one`/`inv` are `composeQ` / `⟦⟨0, id⟩⟧`
   / `inverseQ`.

The §383 group homomorphisms via Φ then consume this `Group`
instance directly.
