# Cycle 230 Results

## Worked on

§383 group-homomorphism path Phase 3 follow-up: built the
top-block `derivativeWeightWithSrc_compose_castAdd` mutual block
(path B per cycle 230 strategy §H decision tree). This is
infrastructure for cycle 231's bottom-block partner and cycle
232's `compose_assoc_phiEquivalent`, NOT for the right-action
deferred in `.prover-state/issues/cycle_226_compose_phi_right_action.md`.

## Approach

1. **Aristotle single poll**: project
   `176aa964-db7b-40f8-a01c-05247c186ec5` (right-action M₂-side
   sum equality) returned `IN_PROGRESS` at **24 %** on the single
   permitted poll. Growth pattern: 9 % → 11 % → 17 % → 24 % across
   cycles 227 / 228 / 229 / 230 (≈ 2–7 % per cycle). Several-day
   ETA at this rate. **Path B** taken per §H.
2. **Insertion site**: lines 2862–2920 of `Section381.lean`,
   inserted between cycle 226's `compose_phiEquivalent_compose_left`
   `end` (line 2860) and cycle 227's `composeQ_phi_left_act`
   `noncomputable def` (which moved to ~line 2935).
3. **Mutual block** (per cycle 230 strategy §D.1, ~50 LOC inside
   `section ... open OpenMath.Chapter3.Section310 ... end`
   wrapper, mirroring cycles 224 / 225 / 226):
   - `derivativeWeightWithSrc_compose_castAdd` — per-tree branch.
     For `t = RootedTree.mk children`, `show` rewrites the goal to
     the list-helper form and `exact` delegates to the companion.
   - `derivativeWeightWithSrcProd_compose_castAdd` — list-helper
     branch. For `t :: ts`, `show` unfolds both sides of the cons
     cell, `rw [derivativeWeightWithSrcProd_compose_castAdd … ts j]`
     applies the IH on the tail, then `congr 1 ; congr 1`
     (two-level congruence: outer factor product + inner-sum
     addition) reduces the goal to the per-summand sum equality.
     `Fin.sum_univ_add` block-splits the `Fin (s₂ + s₃)` sum;
     `simp only [compose_A_topLeft, compose_A_topRight, zero_mul,
     Finset.sum_const_zero, add_zero]` kills the bottom-block
     `castAdd s₃` × `natAdd s₂` cross-summands (because
     `compose_A_topRight = 0`); top half collapses via
     `compose_A_topLeft : (M₂.compose M₃).A (castAdd s₃ j)
     (castAdd s₃ j') = M₂.A j j'`; per-summand
     `derivativeWeightWithSrc_compose_castAdd M₁ M₂ M₃ t j'` closes
     via `Finset.sum_congr`.
4. **Departure from strategy §D.1 verbatim template**: the strategy
   used a single `congr 1` before `Fin.sum_univ_add`, but the goal
   produced by `rw [...IH on ts...]` was an equality of products
   `(A) * X = (B) * X` where `A` = `(...elementaryWeight + sum_compose)`
   and `B` = `(elementaryWeight + sum_M₂)`. A single `congr 1`
   reduces to `A = B`, which is an equality of sums; a second
   `congr 1` reduces it to `sum_compose = sum_M₂`. The strategy's
   template would have produced an off-by-one congruence depth.
   Verified by `lake env lean` clean build with no diagnostic
   messages.
5. **Non-vacuity (P2)**: added the three-factor `paddedEuler` witness
   `(paddedEuler.compose paddedEuler).derivativeWeightWithSrc
   paddedEuler (Fin.castAdd 2 j) t = paddedEuler.derivativeWeightWithSrc
   paddedEuler j t` at the file's end (after cycle 225's
   `paddedEuler_derivativeWeight_compose_natAdd` example), exercising
   the new mutual pair on `(M₁, M₂, M₃) = (paddedEuler, paddedEuler,
   paddedEuler)`.

## Result

**SUCCESS**.

- Three new symbols at `OpenMath/Chapter3/Section381.lean`:
  - `derivativeWeightWithSrc_compose_castAdd` (private,
    namespace `OpenMath.Chapter3.Section312.RKTableau`)
  - `derivativeWeightWithSrcProd_compose_castAdd` (private)
  - One `example` non-vacuity witness in
    `namespace OpenMath.Chapter3.Section381` near file end
- Sorry count: **0** (44th consecutive clean cycle since cycle
  201 rollback).
- Both new theorems axiom-clean
  (`[propext, Classical.choice, Quot.sound]`); no new
  well-founded recursion axioms.
- Warm rebuild: **6.099s** on `OpenMath/Chapter3/Section381.lean`
  (well under the §F.3 60s red-flag and consistent with cycle 229's
  6.2s baseline; the cold-cache reading of 29s on the first compile
  after the edit corresponds to the LSP-side first-touch, not the
  steady-state cost).
- Regression spot-checks all axiom-clean:
  - Cycle 224 `derivativeWeight_compose_castAdd` (regression
    against the structurally identical sibling): unchanged.
  - Cycle 226 `compose_phiEquivalent_compose_left`: unchanged.
  - Cycle 227 `composeQ_phi_left_act`: unchanged (insertion was
    immediately before this def's doc block, no source-order
    disruption).
- `plan.md` `thm:384A` row updated with cycle 230 outcome
  (still partial; the right-action is still gated).
- `.prover-state/issues/cycle_226_compose_phi_right_action.md`
  appended with a cycle 230 update + cycle 231 outlook.

## Faithfulness check

### `derivativeWeightWithSrc_compose_castAdd` (private theorem)

- Not a textbook entity — it is a helper lemma in the path toward
  `thm:384A` (`extraction/formalization_data/entities/thm_384A.json`).
- Status: helper / infrastructure. Documented in the docstring
  ("companion to `derivativeWeightProd_compose_castAdd`", "top-block
  half of `derivativeWeightWithSrc_compose`").
- Lean statement: for the top-block `castAdd`-indexed stage of
  `M₂.compose M₃`, the composite source-method-threaded derivative
  weight on `M₁` reduces to `M₂`'s own. Captures: same content as
  the strategy §D.1 specification.
- **Tautology check**: conclusion `(M₂.compose M₃).derivativeWeightWithSrc
  M₁ (Fin.castAdd s₃ j) t = M₂.derivativeWeightWithSrc M₁ j t` does
  NOT appear as a hypothesis. ✓
- **Identity check**: proof is a structural mutual induction, not
  `exact h`. ✓
- **Hypothesis strength check**: takes only `(M₁ : RKTableau s₁)
  (M₂ : RKTableau s₂) (M₃ : RKTableau s₃)` — minimal; matches
  cycle 224's `derivativeWeight_compose_castAdd` signature pattern
  (just adding the `M₁` source-method parameter that flows through
  `derivativeWeightWithSrc`). ✓
- **Absent theorem check**: the mutual companion
  `derivativeWeightWithSrcProd_compose_castAdd` is actually present
  in the file. ✓

### `derivativeWeightWithSrcProd_compose_castAdd` (private theorem)

- Helper / list companion of the above.
- **Tautology check**: conclusion does NOT appear as a hypothesis. ✓
- **Identity check**: proof body is genuinely doing congruence on
  the cons cell, not `exact h`. ✓
- **Hypothesis strength check**: minimal (three tableaux). ✓

### Non-vacuity `example` on `paddedEuler`

- Instantiates the new mutual pair at `s₁ = s₂ = s₃ = 2` with
  `M₁ = M₂ = M₃ = paddedEuler`. Genuinely exercises the three-method
  dependency.
- Not a theorem (anonymous `example`), so no name conflict.

## Dead ends

- **`congr 1` depth**: the strategy §D.1 verbatim template would
  have applied a single `congr 1` before `Fin.sum_univ_add`,
  matching cycle 224's pattern. But because `derivativeWeightWithSrc`'s
  cons-cell expansion uses `(M₁.elementaryWeight t + ∑ ...) * tail`
  instead of cycle 224's `(∑ ...) * tail`, a single `congr 1` lands
  on the sum-equality `elementaryWeight + sum_compose =
  elementaryWeight + sum_M₂`, and a second `congr 1` further reduces
  to the sum equality `sum_compose = sum_M₂` (since the
  `elementaryWeight t` term is syntactically identical on both
  sides). This is a minor adaptation of the cycle 224 template, not
  a true dead end — caught on first compile, no wasted attempts.

## Discovery

1. **`congr 1` twice for `derivativeWeightWithSrc` cons-cell**:
   cycle 224's template applied one `congr 1` (collapse outer
   product to equality of sums) before `Fin.sum_univ_add`; cycle
   230 path B needs **two** because the outer factor is itself
   `(elementaryWeight + ∑ ...)`, not just `∑ ...`. Mechanical
   recipe: count the layers of `_ * _` outside the sum, then the
   `_ + _` layers between the outermost level and the sum, and add
   one `congr 1` per layer until the goal reduces to the sum
   equality. This rule will apply verbatim to cycle 231's bottom-
   block partner (which uses the same `(elementaryWeight + ∑ ...) *
   tail` cons-cell shape on the LHS).
2. **First-compile cost vs warm-rebuild cost gap**: the first
   `lake env lean OpenMath/Chapter3/Section381.lean` after the
   edit took 2m10s (cold-cache) while the immediate second run
   was 29s and the third was 6.099s. The "warm" baseline is
   ~6s; the LSP-side first-touch overhead is several minutes
   even when the file is sole-modified (full transitive olean
   walk). Useful for future cycles' time-budget planning:
   do NOT use the first `lake env lean` reading as the
   warm-rebuild gauge.
3. **Path-B infrastructure scale**: ~50 LOC for one mutual block
   matches cycle 224's footprint exactly. Cycle 231's bottom-block
   partner will likely be ~70–100 LOC because it consumes BOTH
   cycle 230's top-block lemma AND cycle 225's
   `compose_elementaryWeight_decomp` (whereas cycle 230 only
   consumed the cons-cell unfolding).

## Suggested next approach

### Cycle 231 (primary)

Ship the bottom-block partner per cycle 230 strategy §D.4 preview:

```lean
private theorem derivativeWeightWithSrc_compose_natAdd
    {s₁ s₂ s₃ : ℕ}
    (M₁ : RKTableau s₁) (M₂ : RKTableau s₂) (M₃ : RKTableau s₃) :
    ∀ (t : RootedTree) (k : Fin s₃),
      (M₂.compose M₃).derivativeWeightWithSrc M₁ (Fin.natAdd s₂ k) t
        = M₃.derivativeWeightWithSrc (M₁.compose M₂) k t
```

Proof recipe:

1. Mutual induction on `t` (per-tree + list-helper) using the
   same `section ... open Section310 ... end` namespace trick.
2. List-helper cons-cell: `(M₁.elementaryWeight t + ∑ k' :
   Fin (s₂+s₃), (M₂.compose M₃).A (natAdd s₂ k) k' *
   (M₂.compose M₃).derivativeWeightWithSrc M₁ k' t) * tail`.
3. `rw [...IH on ts...]` → `congr 1` (twice, per cycle 230
   discovery #1) → `Fin.sum_univ_add` → simp the A blocks.
4. RHS expansion: `((M₁.compose M₂).elementaryWeight t + ∑ k' :
   Fin s₃, M₃.A k k' * M₃.derivativeWeightWithSrc (M₁.compose M₂)
   k' t)`. Rewrite `(M₁.compose M₂).elementaryWeight t` via cycle
   225's `compose_elementaryWeight_decomp` to expose the explicit
   `M₁.elementaryWeight t + ∑ j, M₂.b j * M₂.derivativeWeightWithSrc
   M₁ j t` form.
5. Match LHS top half (via cycle 230's lemma → ∑ j, M₂.b j *
   M₂.derivativeWeightWithSrc M₁ j t) with RHS's
   `compose_elementaryWeight_decomp` expansion term.
6. Match LHS bottom half (via per-summand
   `derivativeWeightWithSrc_compose_natAdd … t k'` IH) with RHS's
   M₃-sum.

If `(M₁.compose M₂).elementaryWeight t` doesn't unfold cleanly
to the decomposition form via `rw`, may need an auxiliary helper
"push the decomposition inside" (e.g., a substitution lemma
"`derivativeWeightWithSrc (M₁.compose M₂) k t` equals some explicit
combination of `M₁`-source and `M₂`-source threaded-derivatives").
This is a known structural challenge but not a dead end —
cycle 226's `derivativeWeightWithSrc_subst_M₁` is the template.

### Cycle 232 (deferred)

Assemble `compose_assoc_phiEquivalent` from cycles 230 + 231,
mirroring cycle 221's `compose_equivalent_compose_assoc` at the
§382 level. This is the three-factor associativity at the
PhiEquivalent level and is a prerequisite for the §383 `Group`
instance on `Quotient PhiEquivalent.setoidSigma`.

### Aristotle right-action (parallel track)

If Aristotle project `176aa964-...` completes by cycle 231, the
planner should branch to path A (full binary `composeQ_phi` via
the right-action). Growth rate suggests several more days; do NOT
re-poll mid-cycle per CLAUDE.md single-poll discipline.
