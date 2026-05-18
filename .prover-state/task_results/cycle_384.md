# Cycle 384 Results

## Worked on

§422 Phase D.3.b Step 2 — order-5 symmetric-two-cherry-children
closed form for `Φ_{η_q⁻¹}(mk [cherry, cherry])` plus its m=0
Sub-lemma A corollary. Ninth data point in the cycle 366 §G Route B
hypothesis ladder (vertex, cherry, broom₃, mk [cherry], bushy,
mk [broom₃], mk [vertex, cherry], mk [mk [cherry]], **mk [cherry,
cherry]**).

P1 + P2 + P3 ship at `OpenMath/Chapter4/Section422.lean:4655–5128`:

- P1 `elementaryWeightQ_phi_inv_mkCherryCherry` (line 4655).
- Non-vacuity example at `⟦explicitEuler⟧⁻¹` evaluating to −1
  (line 4998).
- P2 `powRep_sum_eq_of_agreement_at_mkCherryCherry_zero` (line 5067).
- Reflexive non-vacuity example at `η_q = η_q' = ⟦explicitEuler⟧`
  (line 5113).

## Approach

Followed cycle 372's `mk [vertex, cherry]` proof template verbatim,
substituting the **symmetric square structure** for the asymmetric
mixed-children product.

**Symbolic derivation** (done on paper before coding):

Let v = Φ_η(vertex), c = Φ_η(cherry), b' = Φ_η(broom₃),
m = Φ_η(mk[cherry]), vc' = Φ_η(mk[vertex,cherry]),
C = Φ_η(mk[cherry,cherry]).

For `mk [cherry, cherry]`, the two-child cons-case unfold of
`derivativeWeightWithSrc M.inverse i` produces a product of two
identical source-tagged cherry factors:

```
M.derivativeWeightWithSrc M.inverse i (mk [cherry, cherry])
  = (inv_c + Σⱼ Aᵢⱼ · (inv_v + Σₖ Aⱼₖ))²
```

Substituting `inv_v = -v` (cycle 367) and `inv_c = v² − c` (cycle 369),
expanding the square, summing against `M.b i`, and back-substituting
the elementary-weight kernels gives the **8-term closed form**:

```
Φ_{η_q⁻¹}(mk [cherry, cherry])
  = −v⁵ + 4v³c − 3vc² − v²b' − 2v²m + 2cm + 2v·vc' − C
```

This is the first Family C witness requiring **6 distinct
elementary weights** on its RHS (vertex, cherry, broom₃, mk[cherry],
mk[vertex,cherry], mk[cherry,cherry]) — degree-5 trees naturally
require more elementary-weight kernels than cycle 372's degree-4
`mk [vertex, cherry]` (5 elementary weights) or cycle 378's
degree-4 `mk [mk [cherry]]` (4 elementary weights).

**Proof structure**: 15 `have` lemmas (12 reused from cycles
367/368/369/372, 3 new for the symmetric structure) + `h_sum`
computation with 6-term `h_subst` per-summand decomposition + 5×
`Finset.sum_add_distrib` + 5× `← Finset.mul_sum` + 6× back-sub via
`← h_X` + `ring`.

**P2 (m=0 corollary)**: standard `h_pow : ζ^(-(0+1)) = ζ⁻¹` bridge,
then `rw` by P1 and the six agreement hypotheses.

**P3 non-vacuity**: at `⟦explicitEuler⟧⁻¹` all higher elementary
weights vanish (A=0) and `Σ b = 1` (so `Φ_η(vertex) = 1`), giving
the closed form value `−1`. The m=0 reflexive witness discharges
six `rfl` hypotheses.

## Result

**SUCCESS.** Both new theorems ship axiom-clean
(`[propext, Classical.choice, Quot.sound]` only — verified via
`#print axioms`). File compiles with the single pre-existing
warning at line 2272 (cycle 365 grandfathered sorry).

Diff stats: +521 LOC added to `Section422.lean` (4655→5176 net new
content, plus header pushdown of `Phase α'.1` section by 521 lines).

## Faithfulness check

For `elementaryWeightQ_phi_inv_mkCherryCherry`:

- **Entity ID**: not a textbook entity. Internal Lean housekeeping
  (9th tree in inverse-polynomial closed-form ladder, analogue of
  cycles 367/368/369/370/371/372/378). The underlying object
  `Φ_{η⁻¹}(mk [cherry, cherry])` is the §383 group-inverse evaluated
  at a specific rooted tree.
- **Textbook statement quote**: Butcher §383 / §387 provides the
  framework (`η ∈ G_2 ⇒ η⁻¹ ∈ G_2` and the inverse formula
  on B-series coefficients); no explicit closed form for individual
  trees printed in the textbook. The closed form derived here is a
  symbolic evaluation of cycle 358's representative-form formula
  `Φ_{⟦M⟧⁻¹}(t) = -Σᵢ bᵢ · M.derivativeWeightWithSrc M.inverse i t`
  at `t = mk [cherry, cherry]`.
- **Lean statement captures**: same content as the symbolic
  derivation. Verified by independent hand-computation:
  - At `explicitEuler` (v=1, all higher zero): expected −1, computed −1 ✓.
  - All 6 elementary-weight dependencies match the cherry-children
    symmetry expected from the cons-case unfold structure.
- **Hypothesis strength check**: no hypotheses beyond `η_q :
  Quotient PhiEquivalent.setoidSigma`. Faithful to cycle 367–372
  pattern.

For `powRep_sum_eq_of_agreement_at_mkCherryCherry_zero`:

- Lists exactly the 6 elementary-weight agreement hypotheses
  matching the RHS of P1's closed form. **No extras** (faithful to
  cycle 378 worker's discovery that the corollary lists only the
  weights actually appearing in the closed-form RHS).

## Dead ends

None this cycle. Cycle 372's proof template ported cleanly. The
symbolic derivation was straightforward once I recognized the
symmetric square structure (both `mk [cherry, cherry]` children are
identical cherry subtrees, so the two source-tagged factors are
identical → product collapses to a square).

The planner's predicted closed forms in the strategy doc
(`-v³ + 2v·c - b' - (something at mk [cherry])` or
`v⁴ − 2v²·c + c² − v·b' + 2v·m − C`, 4–6 terms) were both **wrong**
— the actual closed form is 8 terms because `mk [cherry, cherry]`
is order 5 and requires elementary weights up to order 5
(specifically including `Φ_η(mk [vertex, cherry])` order 4, which
the planner didn't anticipate).

## Discovery

**Order-5 closed forms require more elementary-weight kernels.**
Cycle 372's mk[vertex, cherry] (order 4) had 5 elementary weights
on RHS; cycle 378's mk[mk[cherry]] (order 4) had 4 elementary
weights; this cycle's mk[cherry,cherry] (order 5) has **6
elementary weights** (vertex, cherry, broom₃, mk[cherry],
**mk[vertex,cherry]**, mk[cherry,cherry]). The `mk[vertex,cherry]`
dependency is non-obvious — it arises from the cross-term
`-2v · Σᵢ bᵢ · S₁ · S₂` in the expanded square, where `S₁ = Σⱼ Aᵢⱼ`
(vertex factor) and `S₂ = Σⱼ Aᵢⱼ · Σₖ Aⱼₖ` (cherry factor).

**Cross-dependency between Family C witnesses.** Cycle 384's
`mk [cherry, cherry]` closed form **depends on** cycle 372's
`mk [vertex, cherry]` elementary-weight kernel (not its closed
form — just the M-representative formula). This means Family C is
not strictly hierarchical-by-tree-shape: order-5 symmetric trees
can require order-4 asymmetric tree elementary-weight kernels.

**Implication for cycle 385+ scoping.** The unified
`inversePolyTree` recursion (cycle 386+ deliverable) must be able
to express **mixed cross-tree-shape dependencies**. The naive
"recurse on each child's closed form" approach would not capture
the `S₁ · S₂` cross-term that introduces `mk[vertex,cherry]` as a
witness. The dispatch by children-list pattern needs auxiliary
helper lemmas for **pairwise child-product elementary weights**.

## Suggested next approach

For cycle 385 (Family C scoping doc):

1. **Document the 3-witness Family C pattern**:
   - mk[broom₃] (cycle 371): 5 terms, single non-leaf child of
     order 3.
   - mk[vertex, cherry] (cycle 372): 6 terms, mixed leaf +
     non-leaf children of orders 1+2.
   - mk[cherry, cherry] (cycle 384): 8 terms, symmetric two-cherry
     children of orders 2+2.

2. **Identify the unifying recipe**:
   - The number of terms in the closed form scales with the
     **product of child-orders + 1** (loosely).
   - The cross-product term `S₁ · S₂` between different child
     factors introduces a fresh elementary-weight witness
     (a tree shaped by combining the children's shape signatures).

3. **Phase α'.4 scoping outline**: propose a tree-product helper
   recursion `inversePolyTree : RT → (RT → ℝ) → ℝ` that dispatches
   by children-list pattern via a fresh auxiliary
   `bichildren_weight : RT × RT → (RT → ℝ) → ℝ` capturing the
   pairwise cross-term contributions. This is **distinct** from
   the cycle 380 `inversePolyChain` (Family A) and cycle 382
   `inversePolyBroom` (Family B) recursions, which are
   single-child recursions.

4. **Optional cycle 385 deliverable**: ship a 4th Family C
   witness `mk [broom₃, cherry]` (order 6) to confirm the
   bichildren cross-term pattern at one more data point.
