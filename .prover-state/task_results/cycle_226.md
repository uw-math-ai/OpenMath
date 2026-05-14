# Cycle 226 Results

## Worked on

§383 group-homomorphism path **Phase 3** — the central deliverable
of cycle 226 per strategy §B was the full
`compose_phiEquivalent_compose`. The attempt landed **partial**:

- ✅ **SHIPPED — `derivativeWeightWithSrc_subst_M₁` + helper**
  (mutual block, `Section381.lean:2762–2810`): substitutes `M₁ → M₁'`
  in `derivativeWeightWithSrc` under `PhiEquivalent M₁ M₁'`, the
  cycle 226 Route 1 helper from strategy §B.5.
- ✅ **SHIPPED — `compose_elementaryWeight_decomp`** (private
  theorem, `Section381.lean:2819–2835`): packages cycles 224 + 225
  into the canonical elementary-weight identity
  `(M₁.compose M₂).elementaryWeight t = M₁.elementaryWeight t +
   ∑ i, M₂.b i * M₂.derivativeWeightWithSrc M₁ i t`.
- ✅ **SHIPPED — `compose_phiEquivalent_compose_left`** (the
  *left-action* half of the full theorem,
  `Section381.lean:2849–2858`): `PhiEquivalent M₁ M₁'` ⟹
  `PhiEquivalent (M₁.compose M₂) (M₁'.compose M₂)`, for **any** fixed
  `M₂`. ~10 LOC.
- ✅ **SHIPPED — 2 P2 non-vacuity witnesses**
  (`Section381.lean:3929–3955` in `namespace Section381`):
  homogeneous (paddedEuler-self via `PhiEquivalent.refl`) and
  heterogeneous-stage (paddedEuler vs paddedEuler.pReduced
  pairPartition via cycle 187's `pReduced_phiEquivalent`, exercising
  distinct stage counts 4 vs 3).
- ❌ **NOT SHIPPED — `compose_phiEquivalent_compose_right`** (the
  *right-action* half, varying `M₂`) and hence the full
  `compose_phiEquivalent_compose`. Structurally hard; documented as
  `.prover-state/issues/cycle_226_compose_phi_right_action.md`.

Sorry count remains **0** (40th consecutive clean cycle since the
cycle 201 rollback).

## Approach

Followed strategy §B's Route 1 for the left action. The right action
was attempted but reduced (via the cycle 225 decomposition) to a
sum-level equality whose direct tree induction does not close (see
"Dead ends" below). Submitted the M₂-side equality to Aristotle as a
backstop (project_id `176aa964-db7b-40f8-a01c-05247c186ec5`,
submitted 2026-05-14T15:50:23 UTC); result not incorporated in this
cycle (still IN_PROGRESS at commit time).

### Left action — successful recipe (strategy §B.5 Route 1):

1. **`derivativeWeightWithSrc_subst_M₁`** — mutual induction on
   `(t : RootedTree, children : List RootedTree)` mirroring
   cycles 187/224/225's templates:
   - Tree-level partner unfolds via `show` to the list-level partner
     on `children`.
   - List-level `[]` is `rfl`; list-level `t :: ts` distributes the
     leaf factor, rewrites `M₁.elementaryWeight t` via `hPhi₁ t`,
     and recurses on `ts` and inside the inner sum on `t`.
2. **`compose_elementaryWeight_decomp`** — `Fin.sum_univ_add` on
   `(M₁.compose M₂).elementaryWeight t`, then collapse:
   - top half via `compose_b_castAdd` + cycle 224's
     `derivativeWeight_compose_castAdd` → `M₁.elementaryWeight t`.
   - bottom half via `compose_b_natAdd` + cycle 225's
     `derivativeWeight_compose_natAdd` → the
     `M₂.derivativeWeightWithSrc M₁` sum.
3. **`compose_phiEquivalent_compose_left`** — after the two
   decomposition rewrites and `hPhi₁ t`, reduces to the per-summand
   `derivativeWeightWithSrc_subst_M₁` rewrite.

### Right action — attempted but did not close:

By the decomposition, the right-action claim reduces to
`∑ i, M₂.b i * M₂.derivativeWeightWithSrc M₁ i t
 = ∑ i', M₂'.b i' * M₂'.derivativeWeightWithSrc M₁ i' t`
for any `M₁` (the "M₂-side sum equality"). This is the same
content as `compose_phiEquivalent_compose` with `M₁ = M₁'`, so
**circular** if attempted via the decomposition route again. Direct
tree induction on `t` produces a cross-term
`∑ i, j, M₂.b i * M₂.A i j * M₂.derivativeWeightWithSrc M₁ j t' *
       M₂.derivativeWeightWithSrcProd M₁ i ts`
in the inductive step that mixes the outer `b_i` with the inner
`A_{ij}`-recursion and does not factor for per-summand reasoning.
See the issue file for details.

## Result

**PARTIAL** — three new public/private symbols shipped (~95 LOC total
including the mutual block, the decomposition helper, and the
left-action theorem) plus two non-vacuity witnesses. Cycle 226's
central deliverable (the full `compose_phiEquivalent_compose`) is
not closed; the gap is documented and the path forward (M₂-side
equality, likely requiring Connes-Kreimer Hopf-algebra
formalization in cycles 230+) is laid out in
`.prover-state/issues/cycle_226_compose_phi_right_action.md`.

### Verification outcomes (strategy §C)

1. `lake env lean OpenMath/Chapter3/Section381.lean` — EXIT=0.
   Warm rebuild **6.101s** (well within the strategy §C.1 budget;
   comparable to cycle 224 / 225's 6.088s / 6.310s).
2. `lean_verify` on the public left-action theorem:
   - `OpenMath.Chapter3.Section312.RKTableau.compose_phiEquivalent_compose_left`
     → `[propext, Classical.choice, Quot.sound]`. **Axiom-clean.**
3. Sorry count: `grep -c sorry OpenMath/Chapter3/Section381.lean`
   returns 1 occurrence (line 2995 — the docstring-prose `sorry`
   from cycle 216, unchanged). No tactic-level `sorry`.
4. Regression spot-checks (all axiom-clean
   `[propext, Classical.choice, Quot.sound]`):
   - `OpenMath.Chapter3.Section312.RKTableau.composeQ_eq_of_equivalent`
     (cycle 218).
   - `OpenMath.Chapter3.Section381.pReduced_phiEquivalent`
     (cycle 187).
   - `OpenMath.Chapter3.Section312.RKTableau.instGroup` (cycle 222).

The cycle 224/225 private theorems
(`derivativeWeight_compose_castAdd` / `_natAdd`) are file-private
and not directly verifiable by name; their axiom-cleanliness is
inherited transitively through `compose_phiEquivalent_compose_left`
(which depends on both).

### Aristotle submission (P3 backstop)

Submitted at 2026-05-14T15:50:23 UTC. Status at commit time:
IN_PROGRESS, ~4% complete. Will be checked in cycle 227.

## Faithfulness check

**New `def`s introduced this cycle**: none. (The two new `private
theorem`s `derivativeWeightWithSrc_subst_M₁` /
`derivativeWeightWithSrcProd_subst_M₁` are mutual partners proving
an equality, not new definitions.)

**New `theorem`s introduced this cycle**:

- `derivativeWeightWithSrc_subst_M₁` /
  `derivativeWeightWithSrcProd_subst_M₁` (`private`).
  - Entity ID: none (internal helper for the §383 group-hom path).
  - Captures: the substitution property
    `M₂.derivativeWeightWithSrc M₁ i t = M₂.derivativeWeightWithSrc
    M₁' i t` under `PhiEquivalent M₁ M₁'`. Same content as the
    informal observation in strategy §B.5 Route 1.

- `compose_elementaryWeight_decomp` (`private`).
  - Entity ID: none (internal infrastructure — repackages cycles
    224 + 225).
  - Captures: the canonical decomposition
    `(M₁.compose M₂).elementaryWeight t = M₁.elementaryWeight t +
    ∑ i, M₂.b i * M₂.derivativeWeightWithSrc M₁ i t`. Faithful to
    the textbook intuition: top-block stages match `M₁`'s elementary
    weight; bottom-block stages contribute a `M₁.elementaryWeight`-
    threaded `M₂`-derivative.

- `compose_phiEquivalent_compose_left` (public).
  - Entity ID: there is no direct textbook entity for the left-only
    action; this is an *internal* half of `thm:384A`. The full
    `compose_phiEquivalent_compose` (the relevant external theorem)
    is **NOT** shipped this cycle.
  - Captures: `PhiEquivalent M₁ M₁'` ⟹ `PhiEquivalent (M₁.compose
    M₂) (M₁'.compose M₂)`. Strictly weaker than the textbook claim
    (which also varies M₂); this is the left-action restriction.
    The full theorem is documented as open in the issue file.

**Definition smuggling check**: no new `def`s, no new `structure`s,
no `class`-with-`Prop`-field added. All new symbols are `theorem`s
with explicit hypotheses; the conclusions do not appear verbatim in
the hypotheses; the proofs do real work (mutual induction +
`Fin.sum_univ_add` decomposition).

## Dead ends

1. **Direct tree induction for the right-action M₂-side equality.**
   For `t = mk children`, the bottom-half sum
   `∑ i, M₂.b i * M₂.derivativeWeightWithSrcProd M₁ i (c :: cs)`
   expands to a sum that does not factor and does not match the
   shape of any natural induction hypothesis (on `mk cs` or on
   `c`). The cross-term `∑ i,j, M₂.b i * M₂.A i j *
   M₂.derivativeWeightWithSrc M₁ j c * M₂.derivativeWeightWithSrcProd
   M₁ i cs` couples the outer `b`-weighting with the inner
   `A`-recursion; no clean per-summand reasoning closes.

2. **Reduction to cycle 217's `compose_equivalent_compose`** via a
   `PhiEquivalent → Equivalent` implication. That implication is
   Butcher §380's converse direction (genuinely deeper than the
   forward; relies on Taylor expansion / B-series machinery) and
   is not formalized in this project.

3. **Re-deriving the cycle 225 identity at the elementary-weight
   level for the right-action case.** Going through
   `(M₁.compose M₂).elementaryWeight t` and re-applying cycle 225
   yields the same claim restated (no smaller subproblem) —
   circular.

## Discovery

1. **Cycle 225's decomposition packages cleanly.** The composite
   identity `(M₁.compose M₂).elementaryWeight t = M₁.elementaryWeight
   t + ∑ M₂.b * derivativeWeightWithSrc M₁` (lifting cycles 224 +
   225 from `derivativeWeight` to `elementaryWeight`) is a single
   ~20 LOC lemma (`compose_elementaryWeight_decomp`) — useful
   tooling for any future `compose`-related reasoning at the
   elementary-weight level.

2. **The mutual-induction template extends to "substitution"
   lemmas, not just identity lemmas.** Cycle 187/224/225's
   per-tree mutual-block template (with `RootedTree.mk children`
   unfolding to a list-helper recursion) works just as well for
   substitution claims of the form "`f M₁ t = f M₁' t` under
   `PhiEquivalent M₁ M₁'`", with `hPhi₁ t` providing the
   per-leaf substitution.

3. **The right-action half is genuinely the hard direction.**
   While `compose_phiEquivalent_compose_left` mirrors cycle 217's
   shape (left-vary closes via per-component manipulation), the
   right-action is the Connes-Kreimer Hopf-coproduct direction
   (requires combinatorial expansion of the composite into tree
   "cut" terms). The planner's `derivativeWeightWithSrc`
   "leaf-shape" hint in strategy §B.4 (suggesting Route 1 might
   close the full theorem) under-estimated the gap between
   substituting `M₁` and varying `M₂`: the former affects
   leaf-level constants (`M₁.elementaryWeight t'`), the latter
   affects both the outer `b`-weighting and the inner `A`-recursion
   throughout the tree.

4. **Lean 4 dot notation requires the FIRST argument to be of the
   target type for namespace lookup.**
   `RKTableau.compose_phiEquivalent_compose_left paddedEuler ...`
   resolves only because `paddedEuler : RKTableau 2`. If the
   signature were `(hPhi₁ : ...) (M₂ : RKTableau s₂)`, the dot-
   notation lookup would have to put `M₂` first.

## Suggested next approach

For **cycle 227**, the priority is the M₂-side sum equality. Two
parallel paths:

1. **Check the Aristotle backstop.** Project_id
   `176aa964-db7b-40f8-a01c-05247c186ec5` was submitted at
   2026-05-14T15:50:23 UTC. If complete and the proof type-checks,
   incorporate verbatim and close cycle 227 with the full
   `compose_phiEquivalent_compose`. ~15 LOC for the wrapping.

2. **If Aristotle did not solve it**, decompose the right-action
   into "easier" sub-claims:
   - (A) An auxiliary stage-level identity for
     `derivativeWeightWithSrc` analogous to cycle 224/225's
     `derivativeWeight_compose_*`. Specifically: for any "twin"
     tableau structure that encodes both `M₂` and `M₂'`, is there
     a closed-form relating `derivativeWeightWithSrc M₁` on
     `M₂` to `derivativeWeightWithSrc M₁` on `M₂'`?
   - (B) Reformulate the M₂-side sum as a `Finset.sum_image` over
     a tree-cut combinatorial structure. This is the
     Connes-Kreimer path; cleaner but multi-cycle.

3. **In parallel**: extend the §383 group-hom path's downstream
   plumbing using only `compose_phiEquivalent_compose_left` —
   namely, the "left-action of `Quotient.lift₂`" on the right
   argument. This gives a partial `composeQ_phi` definition (or
   at least a `composeQ_phi.fst_action` lemma) that doesn't need
   the full theorem. ~25 LOC.

The standing 43rd-consecutive §441 Phase C.2 GPFS block remains;
no action needed per strategy §A.
