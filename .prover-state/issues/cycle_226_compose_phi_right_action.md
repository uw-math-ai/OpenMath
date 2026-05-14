# Issue: `compose_phiEquivalent_compose` right-action (M₂-side) is structurally hard

## Blocker

Cycle 226 targeted the full `compose_phiEquivalent_compose`:

```lean
theorem compose_phiEquivalent_compose
    {s₁ s₁' s₂ s₂' : ℕ}
    (M₁ : RKTableau s₁) (M₁' : RKTableau s₁')
    (M₂ : RKTableau s₂) (M₂' : RKTableau s₂')
    (hPhi₁ : PhiEquivalent M₁ M₁')
    (hPhi₂ : PhiEquivalent M₂ M₂') :
    PhiEquivalent (M₁.compose M₂) (M₁'.compose M₂')
```

The plan was to factor as a transitivity through `M₁'.compose M₂`:

- (left action) `PhiEquivalent (M₁.compose M₂) (M₁'.compose M₂)` —
  varying `M₁` only — **SHIPPED in cycle 226** as
  `compose_phiEquivalent_compose_left`.
- (right action) `PhiEquivalent (M₁'.compose M₂) (M₁'.compose M₂')` —
  varying `M₂` only — **BLOCKED**.

The left action was straightforward via cycle 225's
`compose_elementaryWeight_decomp` plus the cycle 226 helper
`derivativeWeightWithSrc_subst_M₁`. The right action is the hard part:
unfolding via the decomposition reduces it to

```
∑ i : Fin s₂,  M₂.b  i * M₂.derivativeWeightWithSrc  M₁ i t
  = ∑ i : Fin s₂', M₂'.b i * M₂'.derivativeWeightWithSrc M₁ i t
```

with `hPhi₂ : PhiEquivalent M₂ M₂'`. This is `compose_phiEquivalent_compose`
with `M₁ = M₁'`, so circular if attempted via the decomposition route.

## Context

The bottom-block sum mixes two `i`-dependent factors:

1. The outer weight `M₂.b i`.
2. `M₂.derivativeWeightWithSrc M₁ i t`, which expands recursively to
   `∏_{t' ∈ children(t)} (M₁.elementaryWeight t' + ∑ j, M₂.A i j *
   M₂.derivativeWeightWithSrc M₁ j t')`.

Per-summand reasoning fails: the index `i` couples the outer `b_i`
with the inner `A_{ij}` recursion, and the natural tree-induction
hypothesis on subtrees `t' ∈ children(t)` does not match the shape of
the recursive call (which is `M₂.derivativeWeightWithSrc M₁ j t'`, not
`∑ M₂.b j * M₂.derivativeWeightWithSrc M₁ j t'`).

The standard tool (the cycle 187 fiberwise-summation trick used for
P-reduction) doesn't apply: there's no partition of `Fin s₂` we can
push through. The standard tool (cycle 217's operational
`compose_equivalent_compose`) doesn't apply: that proof operates at
the dynamical (RKOneStep) level, not the elementary-weight level.

The mathematical content of the right-action claim is the
**Connes-Kreimer Hopf algebra coproduct formula** for B-series
composition: `(M₁ ∘ M₂)(t) = ∑_{admissible splittings (t₁, t₂) of t}
c(t₁, t₂) · M₁.elementaryWeight(t₁) · M₂.elementaryWeight(t₂)`,
with combinatorial coefficients. Given this closed form,
`compose_phiEquivalent_compose` is immediate: replace each
`M₂.elementaryWeight (...)` by `M₂'.elementaryWeight (...)` via
`hPhi₂`. Formalizing the Connes-Kreimer coproduct is a multi-cycle
endeavor (likely cycles 230+).

## What was tried

1. **Direct tree induction on `t`** for the right-action claim. The
   inductive step at `t = mk children` expands
   `M₂.derivativeWeightWithSrcProd M₁ i (c :: cs)` as
   `(M₁.elementaryWeight c + ∑ j M₂.A i j * M₂.derivativeWeightWithSrc M₁ j c)
    * M₂.derivativeWeightWithSrcProd M₁ i cs`. Distributing produces
   a "cross-term" `∑ i,j, M₂.b i * M₂.A i j *
   M₂.derivativeWeightWithSrc M₁ j c * M₂.derivativeWeightWithSrcProd M₁ i cs`
   that does not factor and is not invariant under `M₂ → M₂'` in any
   obvious per-summand way.

2. **Decomposition via cycle 225 followed by re-application**. The
   sum equals `(M₁.compose M₂).elementaryWeight t -
   M₁.elementaryWeight t`, so the right-action claim is equivalent
   to `(M₁.compose M₂).elementaryWeight t = (M₁.compose M₂').elementaryWeight t`
   for the **same** `t`. This is the same claim restated — no smaller
   subproblem.

3. **Reduction to cycle 217's operational `compose_equivalent_compose`**
   via a hypothetical `PhiEquivalent → Equivalent` lemma. This
   implication is Butcher's converse direction (§380), genuinely
   deeper than `PhiEquivalent` itself; not formalized in this
   project.

4. **Aristotle submission** of the M₂-side sum equality with the cycle
   224/225/226 helpers in scope. Submitted at 2026-05-14T15:50
   (project_id `176aa964-db7b-40f8-a01c-05247c186ec5`).

## Possible solutions

### (A) — Connes-Kreimer coproduct formalization

Formalize the closed-form expansion of `(M₁.compose M₂).elementaryWeight t`
as a sum over "admissible cuts" of `t` weighted by
`M₁.elementaryWeight (cut top) * M₂.elementaryWeight (cut bottom)`.
This is a multi-cycle endeavor (~5–10 cycles to set up the cut
infrastructure on `RootedTree`, prove the combinatorial identity,
and derive the corollary).

### (B) — Operational route via `Equivalent`

Prove `PhiEquivalent M M' → Equivalent M M'` (Butcher's converse,
§380). Then `compose_phiEquivalent_compose` follows from cycle
217's `compose_equivalent_compose` plus the obvious direction
`Equivalent → PhiEquivalent` (already implicit via cycle 187's
`pReducesTo.toPhiEquivalent` route). The converse direction
requires Taylor expansion / B-series machinery; comparable
formalization cost to (A).

### (C) — Strong tree induction with auxiliary `derivativeWeight` invariants

Formulate a stronger induction hypothesis at the
`derivativeWeightWithSrcProd` level over lists, with an
appropriately parameterized "outer weighting" function. Potentially
~150–300 LOC; unclear if it closes.

### (D) — Aristotle / oracle delegation

Wait for the cycle 226 Aristotle submission to return. If
successful, incorporate the proof verbatim. If not, this issue
remains open.

## Status

- Cycle 226: shipped `derivativeWeightWithSrc_subst_M₁` (mutual,
  ~30 LOC) + `compose_elementaryWeight_decomp` (~20 LOC) +
  `compose_phiEquivalent_compose_left` (~10 LOC).
- Cycle 227: partial composition lift `composeQ_phi_left_act`
  (one-sided `Quotient.lift`) shipped as a workaround consuming
  only the left-action half.
- Cycles 228 / 229: left- and right-identity laws shipped on the
  one-sided `composeQ_phi_left_act` (`id_compose_phiEquivalent`,
  `compose_id_phiEquivalent`).
- **Cycle 230 update (path B taken)**: Aristotle project
  `176aa964-db7b-40f8-a01c-05247c186ec5` was IN_PROGRESS at 24 %
  on the single permitted poll (growth pattern: 9 % → 11 % →
  17 % → 24 % across cycles 227–230, ≈ 2–7 %/cycle). Cycle 230
  built **infrastructure** for cycle 232's
  `compose_assoc_phiEquivalent` rather than retrying the
  right-action: shipped the top-block mutual block
  `derivativeWeightWithSrc_compose_castAdd` (per-tree) +
  `derivativeWeightWithSrcProd_compose_castAdd` (list-helper),
  both `private` and axiom-clean
  (`[propext, Classical.choice, Quot.sound]`). For
  `M₂.compose M₃`'s top-block stage `castAdd s₃ j`, the
  composite source-method-threaded derivative weight on `M₁`
  reduces to `M₂`'s own source-method-threaded derivative weight
  at stage `j`. ~50 LOC at `Section381.lean` lines ~2862–2920,
  inserted between cycle 226's
  `compose_phiEquivalent_compose_left` `end` and cycle 227's
  `composeQ_phi_left_act` definition. Three-factor `paddedEuler`
  non-vacuity at `s₁ = s₂ = s₃ = 2` verifies the new mutual pair
  on a concrete trio.
- **Cycle 231 update (path B taken)**: Aristotle still IN_PROGRESS
  at 29 % on the single permitted poll (growth 24 % → 29 % since
  cycle 230, ≈ 5 %/cycle, several-day ETA). Cycle 231 shipped the
  bottom-block partner mutual block:
  `derivativeWeightWithSrc_compose_natAdd` (per-tree) +
  `derivativeWeightWithSrcProd_compose_natAdd` (list-helper),
  both `private` and axiom-clean
  (`[propext, Classical.choice, Quot.sound]`). For
  `M₂.compose M₃`'s bottom-block stage `natAdd s₂ k`, the
  composite source-method-threaded derivative weight on `M₁`
  reduces to `M₃`'s own source-method-threaded derivative weight
  at stage `k` *threaded from the combined source `M₁.compose M₂`*
  (because the bottom block of `M₂.compose M₃` corresponds to
  `M₃`'s stages starting from a state already advanced through
  `M₁` and then `M₂`). The proof bridges cycle 225's
  `compose_elementaryWeight_decomp` (exposing `(M₁.compose
  M₂).elementaryWeight t` as `M₁.elementaryWeight t + ∑ M₂.b
  · M₂.derivativeWeightWithSrc M₁`) with cycle 230's top-block
  lemma and the cycle 231 mutual partner itself; the
  `compose_A_botLeft = M₂.b j` / `compose_A_botRight = M₃.A k k'`
  simp set splits the LHS block-sum, cycle 230 collapses the top
  half, the IH collapses the bottom half, and `ring` resolves the
  residual associativity. ~95 LOC at `Section381.lean` lines
  ~2933–3025 (inserted between cycle 230's top-block `end` and
  cycle 227's `composeQ_phi_left_act` doc block). Three-factor
  `paddedEuler` non-vacuity at `s₁ = s₂ = s₃ = 2` verifies the
  new mutual pair on a concrete trio (added at file's bottom-end
  alongside cycle 230's witness). Warm-rebuild 6.35s (well under
  §F.3 30s red-flag threshold; comparable to cycle 230's 6.0s).
- **Cycle 232 outlook**: with cycle 230 + cycle 231 both landed,
  cycle 232 can finally ship `compose_assoc_phiEquivalent`
  (three-factor associativity at the PhiEquivalent level),
  mirroring cycle 221's `compose_equivalent_compose_assoc` at
  the §382 level. The recipe: apply `compose_elementaryWeight_decomp`
  to both sides of the target Φ-equivalence, then route the LHS
  via cycle 230 (top-block) + cycle 231 (bottom-block) and the
  RHS via the same lemmas with shifted source/range — the proof
  is essentially a `Fin.sum_univ_add` rearrangement followed by
  per-summand routing through the four mutual lemmas. Estimated
  ~50–80 LOC.
- **Cycle 233+ outlook**: Aristotle (project
  `176aa964-db7b-40f8-a01c-05247c186ec5`) growth trajectory
  suggests 32–36 % at cycle 232 poll. If still IN_PROGRESS,
  continue path-B infrastructure for the `Group` instance on
  `Quotient PhiEquivalent.setoidSigma` once associativity lands.
- Open: the right-action half (M₂-side sum equality) and the
  full `compose_phiEquivalent_compose`. Cycle 231 did NOT
  attempt this; the Aristotle delegation remains the primary
  path A and the path-B infrastructure builds toward
  associativity rather than the right-action.
- Downstream impact: cycle 227's planned full
  `composeQ_phi` (the `Quotient.lift₂` lift to
  `Quotient PhiEquivalent.setoidSigma`) is still blocked on
  this issue. The respect obligation requires the full
  `compose_phiEquivalent_compose`, not just the left action.

## Cycle 232 update — RESOLVED via Aristotle path A

- **Aristotle status**: project `176aa964-db7b-40f8-a01c-05247c186ec5`
  reached **COMPLETE at 100 %** between cycle 231 (poll at 29 %)
  and cycle 232 start. Single poll at cycle 232 start returned
  successful proof of `derivativeWeightWithSrcSum_M₂_phi_eq`.
- **Proof strategy** (per `ARISTOTLE_SUMMARY.md`): generalized
  weight-compatibility induction. Three new private symbols
  added at `OpenMath/Chapter3/Section381.lean`:
  - `derivativeWeightProd_append` (DP is multiplicative over
    list append) — standard list induction.
  - `private mutual gen_dws_eq` / `gen_dwsp_eq` (tree- and
    list-level generalized claim). The list-level claim
    parameterizes a **trailing factor `f : List RootedTree`**
    that threads through the induction; in the cons-case
    kept-child subterm, the updated-weights compatibility is
    propagated by the list-IH on the *shorter* `cs` with the
    *longer* trailing factor `f ++ [RootedTree.mk g]`. This
    breaks the circularity that defeated direct per-summand
    reasoning (the four ruled-out approaches in this issue).
  - `derivativeWeightWithSrcSum_M₂_phi_eq` (the M₂-side sum
    equality) — proved by specializing `gen_dwsp_eq` with
    `w = M₂.b`, `w' = M₂'.b`, `f = []`, where weight
    compatibility is exactly `hPhi₂` applied at each
    `RootedTree.mk g`.
- **Public theorems shipped**:
  - `compose_phiEquivalent_compose_right` — the right-action
    counterpart of cycle 226's
    `compose_phiEquivalent_compose_left`. Proof: apply cycle
    225's `compose_elementaryWeight_decomp` to both sides;
    the `M₁.elementaryWeight t` summand matches trivially,
    and the bottom-block sums agree by
    `derivativeWeightWithSrcSum_M₂_phi_eq`.
  - `compose_phiEquivalent_compose` — the full bilinear
    result. Proof: combine left (cycle 226) + right (cycle
    232) by `.trans` at the intermediate `M₁'.compose M₂`.
  - `noncomputable def composeQ_phi : Quotient
    PhiEquivalent.setoidSigma → Quotient
    PhiEquivalent.setoidSigma → Quotient
    PhiEquivalent.setoidSigma` via `Quotient.lift₂`. The
    well-definedness witness consumed by `Quotient.lift₂`
    is exactly `compose_phiEquivalent_compose`.
  - `@[simp] composeQ_phi_mk` (rfl) and
    `@[simp] composeQ_phi_eq_left_act_mk` (rfl, bridging to
    cycle 227's partial left-action).
- **Axiom status**: all symbols
  `[propext, Classical.choice, Quot.sound]` only.
- **Sorry count**: 0 (46th consecutive clean cycle).
- **LOC**: ~280 LOC inserted between cycle 231's `end` (line
  3021 in HEAD before edit) and cycle 227's
  `composeQ_phi_left_act` doc block, plus the `composeQ_phi`
  block after `composeQ_phi_left_act_eq_of_phiEquivalent`.
  Five non-vacuity examples at file's end.
- **Connes–Kreimer formalization**: still NOT done — Aristotle's
  proof avoids it entirely via the trailing-factor trick.
  This issue is closed for the *right-action* obligation; the
  Connes–Kreimer machinery may still be useful for future
  developments (e.g., explicit B-series expansion at the
  rooted-tree level).
- **Cycle 233+ outlook**: The `Group` instance on `Quotient
  PhiEquivalent.setoidSigma` is the natural next step.
  Required: associativity (consume cycle 232's full
  `compose_phiEquivalent_compose` to lift cycle 221's
  `compose_equivalent_compose_assoc` to the Φ-quotient via
  a `compose_assoc_phiEquivalent` analog — but at the
  PhiEquivalent level via the new infrastructure rather than
  the path-B route the cycle 232 strategy outlined),
  identity (cycles 228/229's `composeQ_phi_left_act_id_*`
  generalized to `composeQ_phi`), inverse (lift
  `inverse_equivalent_inverse` at the Φ-level).
- **Status**: **CLOSED** for the right-action obligation.
