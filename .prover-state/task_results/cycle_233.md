# Cycle 233 Results

## Worked on

§383 group-homomorphism path Phase 4.1: associativity of `compose` at
the `PhiEquivalent` level + its quotient-level corollary.

Two new public theorems in
`OpenMath/Chapter3/Section381.lean`, both in
`namespace OpenMath.Chapter3.Section312.RKTableau`:

- **P1** `compose_assoc_phiEquivalent {s₁ s₂ s₃ : ℕ}
  (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) (M₃ : RKTableau s₃) :
  @PhiEquivalent ((s₁ + s₂) + s₃) (s₁ + (s₂ + s₃))
    ((M₁.compose M₂).compose M₃)
    (M₁.compose (M₂.compose M₃))`

- **P2** `composeQ_phi_assoc (p q r : Quotient PhiEquivalent.setoidSigma) :
  composeQ_phi (composeQ_phi p q) r = composeQ_phi p (composeQ_phi q r)`

Plus two non-vacuity `example`s exercising both theorems on
`paddedEuler` / `⟦⟨2, paddedEuler⟩⟧`.

## Approach

Followed the planner's strategy §C verbatim (path A, no Aristotle).

P1 proof recipe (28 LOC body):
1. `intro t` to unfold `PhiEquivalent` to elementary-weight equality.
2. Triple `rw [compose_elementaryWeight_decomp ...]` — once on each
   composite. Goal becomes
   `M₁.eW t + ∑_{j} M₂.b j * M₂.dWWS M₁ j t
     + ∑_{k} M₃.b k * M₃.dWWS (M₁·M₂) k t
   = M₁.eW t + ∑_{i : Fin (s₂+s₃)} (M₂·M₃).b i * (M₂·M₃).dWWS M₁ i t`.
3. `rw [show <RHS sum equation> from ?_]` exposes the RHS sum and
   defers the proof obligation to a `?_` hole.
4. First branch: `ring` (the goal is now algebraically transparent
   modulo `+` associativity).
5. Second branch (the deferred `?_`): `rw [Fin.sum_univ_add]` splits
   the RHS sum into `castAdd` + `natAdd` halves; `congr 1` peels off
   the outer `+`; two `Finset.sum_congr rfl` close the halves via
   cycle 230 `derivativeWeightWithSrc_compose_castAdd` + cycle 231
   `_natAdd` + simp lemmas `compose_b_castAdd` / `_natAdd`.

P2 (6 LOC body): verbatim port of cycle 221's `composeQ_assoc`
template at `Section381.lean:4170-4176` (now `:4178`).
`Quotient.inductionOn₃ p q r`, `rintro ⟨s₁, M₁⟩ ⟨s₂, M₂⟩ ⟨s₃, M₃⟩`,
`show Quotient.mk _ _ = Quotient.mk _ _`, then
`exact Quotient.sound (compose_assoc_phiEquivalent M₁ M₂ M₃)`.

Both theorems placed inside `namespace OpenMath.Chapter3.Section312.RKTableau`:
P1 in a fresh `section / open OpenMath.Chapter3.Section310 / end`
wrapper inserted immediately after cycle 232's
`compose_phiEquivalent_compose` (line 3227 closing `end`); P2
immediately after cycle 232's `composeQ_phi_eq_left_act_mk` simp
lemma (line 3432).

Two non-vacuity `example`s placed inside
`namespace OpenMath.Chapter3.Section381` just before the trailing
`end OpenMath.Chapter3.Section381`, paralleling cycle 232's
non-vacuity region.

## Result

**SUCCESS** — both theorems compile axiom-clean on the first attempt.

Axioms (verified via `lean_verify` MCP):
- `OpenMath.Chapter3.Section312.RKTableau.compose_assoc_phiEquivalent`:
  `[propext, Classical.choice, Quot.sound]`
- `OpenMath.Chapter3.Section312.RKTableau.composeQ_phi_assoc`:
  `[propext, Classical.choice, Quot.sound]`

Regression spot-checks (all axiom-clean):
- `compose_phiEquivalent_compose` (cycle 232 landmark)
- `composeQ_phi` (cycle 232 landmark)
- `compose_equivalent_compose_assoc` (cycle 221 — the §382 analog
  template)

Warm-rebuild time for `Section381.lean`: ~6.5 s (well under §F red-flag
threshold of 60 s; matches cycle 230–232's ~6 s baseline). The
~80 LOC addition had no measurable elaboration impact.

Sorry count: 0 (47th consecutive clean cycle since cycle 201 rollback).

## Faithfulness check

For each new theorem introduced this cycle:

### `compose_assoc_phiEquivalent`

- Entity ID and textbook statement (quoted from
  `extraction/formalization_data/entities/thm_384A.json`):
  > Let Φ : T → R be the elementary weight function associated with
  > (A, b, c) and Φ̃ : T → R the elementary weight function associated
  > with (Ã, b̃, c̃). Let Φ̂ : T → R denote the elementary weight
  > function for the product method as represented by (382a). Then
  > Φ̂ = Φ Φ̃.

- Lean statement captures: **weaker** (strict subset of `thm:384A`'s
  full content). `thm:384A` (Butcher §384, p. 311) says the elementary
  weight function of the product method equals the product of the
  factor weight functions — equivalently, Φ is a group homomorphism
  from `(Quotient Equivalent.setoidSigma, ·)` to `(Quotient
  PhiEquivalent.setoidSigma, ·)`. The full `Group` instance on the
  Φ-quotient (which the homomorphism's target requires) decomposes
  into three axioms: (a) associativity of `composeQ_phi`, (b)
  identity laws (`composeQ_phi_id_{left,right}`), (c) inverse
  absorption laws. Cycle 233 ships piece (a) only — the associativity
  axiom + its underlying elementary-weight-level lemma.

- Justification for divergence: This is the same partial-formalization
  strategy already used in §382: cycle 219 shipped identity, cycle 220
  shipped inverse, cycle 221 shipped associativity, cycle 222
  assembled the `Group` instance via `Group.ofLeftAxioms`. The §383
  story mirrors §382 axiom-by-axiom. Cycle 233 is the §383 analog of
  cycle 221's associativity step. The full `thm:384A` (Φ as a group
  homomorphism, packaged as `MonoidHom`) is the cycle 237+ packaging
  step; cycle 233's `compose_assoc_phiEquivalent` is a load-bearing
  prerequisite. Status remains `partial` in `lean_status.json`.

### `composeQ_phi_assoc`

- Entity ID and textbook statement: same as above (`thm:384A`).

- Lean statement captures: **same axiom-level content** as P1, but at
  the Φ-quotient level. Identical to P1 in scope; it is an immediate
  `Quotient.inductionOn₃` + `Quotient.sound` corollary of P1.

- Justification for divergence: see P1.

### Hypothesis strength check

Neither theorem has any hypotheses beyond the structural ones
(`s₁ s₂ s₃ : ℕ`, `M₁ M₂ M₃ : RKTableau s_i`, `p q r : Quotient ...`).
No Lipschitz, smallness, or other auxiliary constraints are required
— this is associativity at the elementary-weight / quotient level,
not at the dynamical IsRKOneStep level (which cycle 221 needed for
the §382 `Equivalent`-level analog). The §383 form is in fact
strictly simpler because `PhiEquivalent` is a function-equality
predicate on elementary weights, not an existentially-quantified
threshold predicate.

### Tautology / identity / definition-smuggling check

- **Tautology**: P1's conclusion is `PhiEquivalent X Y`; the
  hypotheses are bare `RKTableau`s with no `PhiEquivalent`
  assumption. No collision. P2's conclusion is an equality of
  Φ-quotient classes; the hypotheses are bare quotient classes. No
  collision.
- **Identity**: neither proof reduces to a single `exact h` /
  `:= h_something`. P1 is ~25 tactic lines doing real algebraic
  reduction; P2 is a 6-line `inductionOn₃` lift of P1.
- **Definition smuggling**: P1 + P2 do not introduce new `def`s or
  `structure`s. The `Group` instance on the Φ-quotient (which would
  be the definition smuggling concern if shipped naively) is **not**
  introduced this cycle — it remains a multi-cycle deliverable
  (cycle 237+) consuming cycles 233/234/235/236.

## Dead ends

None. The proof closed on the first compilation attempt, with no
intermediate `lake env lean` failures requiring iteration. The
planner's strategy §C.3 recipe was followed verbatim and worked
as written.

## Discovery

- **Triple-`rw` ordering with `compose_elementaryWeight_decomp`** works
  cleanly when the three `compose_elementaryWeight_decomp` invocations
  are passed in a single `rw [..., ..., ...]` list: Lean rewrites
  left-to-right on the current goal at each step, so the outer LHS
  decomp (operating on `((M₁·M₂)·M₃).eW t`) fires first, exposing the
  inner `(M₁·M₂).eW t` which the second decomp then unfolds, and
  finally the RHS decomp (operating on `(M₁·(M₂·M₃)).eW t`) fires. No
  intermediate `try`/`<;>` discipline was needed.

- **`show ... from ?_` as a controlled-rewrite primitive**: the
  pattern `rw [show A = B from ?_]` with `· ring` as the first branch
  and the deferred `?_` as the second branch is a clean way to (1)
  defer a sum-decomposition proof obligation, and (2) close the
  algebraic-collapse goal via `ring` immediately after. This is
  cleaner than an explicit `have h : A = B := by ...` + `rw [h]`
  because the deferred goal can use tactics like `Fin.sum_univ_add`
  that need the goal to have the unmodified form.

- **Cycle 230/231 mutual lemmas' argument order in `rw`** is `(M₁ M₂
  M₃ t j)` — tree FIRST, stage SECOND in the per-tree branch (after
  the three RKTableau arguments). Reaffirms cycle 232's discovery;
  the planner's strategy §E.1 documented this correctly.

- **P1's heterogeneous-stage signature** `@PhiEquivalent ((s₁ + s₂) +
  s₃) (s₁ + (s₂ + s₃))` works **without** `.{u}` universe annotation
  (in contrast to cycle 221's `@Equivalent.{u} ...`), confirming
  cycle 223's discovery that `PhiEquivalent` is NOT
  universe-polymorphic. This was already pre-flagged in §E.4 of the
  strategy.

- **`Quotient.inductionOn₃` for the Φ-quotient does not need `.{u}`
  annotation** because `PhiEquivalent.setoidSigma` itself is universe-
  monomorphic. Cycle 221's `composeQ_assoc.{u}` needed `.{u}` because
  `Equivalent` (the §382 predicate) is universe-polymorphic; cycle
  233's `composeQ_phi_assoc` ships without `.{u}`.

- **Warm-rebuild time impact**: the ~80 LOC cycle 233 addition added
  ~0 s to the warm rebuild (6.5 s before and after). The cold rebuild
  (first compilation after edit) was ~50 s, well under the §F.5 60 s
  red-flag threshold. The triple-decomp + `Fin.sum_univ_add` + `ring`
  pattern is elaboration-cheap because no large universe-polymorphic
  instances are being synthesized — `RKTableau` is universe-mono,
  `PhiEquivalent` is universe-mono.

## Suggested next approach

Per strategy §I outlook:

- **Cycle 234**: full-binary identity laws on `composeQ_phi`. Lift
  cycles 228/229's partial-action identities
  `composeQ_phi_left_act_id_{left,right}` to full-binary
  `composeQ_phi_id_{left,right}`. Each ~10 LOC via
  `Quotient.inductionOn` + `Quotient.sound` of the existing
  `id_compose_phiEquivalent` / `compose_id_phiEquivalent` lemmas
  (cycles 228/229). Should be a one-cycle deliverable.

- **Cycle 235**: `inverse_phiEquivalent_inverse` — the §383 analog of
  cycle 222's `inverse_equivalent_inverse`. Non-trivial: needs to
  show `PhiEquivalent M M' → PhiEquivalent M.inverse M'.inverse`.
  Likely requires a tree-induction argument on the elementary weight
  of the inverse method. May benefit from an Aristotle batch
  submission.

- **Cycle 236+**: inverse absorption laws on `composeQ_phi`
  (`composeQ_phi q (inverseQ_phi q) = ⟦⟨0, id⟩⟧` and symmetric).
  Requires cycle 235's `inverse_phiEquivalent_inverse` plus the
  textbook §383 inverse-construction analysis (Butcher §383 lemma
  383A — Runge–Kutta group inverse formula at the elementary-weight
  level).

- **Cycle 237+**: `instance : Group (Quotient
  PhiEquivalent.setoidSigma)` via `Group.ofLeftAxioms` packaging the
  associativity / identity / inverse axioms shipped over cycles
  233/234/235/236. This is the §383 group structure that `thm:384A`
  references as the codomain of Φ.

- **Cycle 238+**: define the homomorphism Φ : `Quotient
  Equivalent.setoidSigma → Quotient PhiEquivalent.setoidSigma` as a
  `MonoidHom` (the literal `thm:384A` statement) using cycles
  207/208's bridge lemmas. With both group instances available, this
  becomes a packaging exercise.

Aristotle queue: cycle 233 did not submit anything (per strategy §B).
Cycle 234's identity lift is small enough that Aristotle is overkill;
cycle 235's `inverse_phiEquivalent_inverse` is a strong Aristotle
candidate.

§441 Phase C.2 GPFS-blocked (47th consecutive, skipped per strategy
§A). Loop-maintainer territory; do not re-test.
