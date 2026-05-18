# Cycle 368 Strategy — §422 Phase D.3.b Step 2: broom₃ closed form

## A. Current state (verified at HEAD `1d1422f`)

* `OpenMath/Chapter4/Section422.lean` — 2596 LOC.
* Sole code-level sorry: line 2279, Sub-lemma A
  `powRep_sum_eq_of_strict_subtree_agreement`'s general body
  (grandfathered from cycle 365). **DO NOT touch this cycle.**
* §422 axiom-clean streak: **33 consecutive cycles** (336–367).
* Cycle 367 shipped: `elementaryWeightQ_phi_inv_cherry` (line 2376)
  and `powRep_sum_eq_of_agreement_at_cherry_zero` (line 2477), both
  axiom-clean.
* Cycle 366 shipped: `powRep_sum_eq_of_agreement_at_vertex` (line
  2314), axiom-clean.
* Specialised-witness library for Sub-lemma A now covers
  `{vertex, cherry (m=0)}`.

There is **NO blocker**. Cycle 367 was a clean ship; cycle 368
continues the small-tree witness ladder per cycle 367 task
results' "Suggested next approach" §G (Route B at `broom₃`).

## B. Cycle 368 target

**Ship `elementaryWeightQ_phi_inv_broom₃` plus its m=0 corollary
`powRep_sum_eq_of_agreement_at_broom₃_zero` plus two non-vacuity
examples on `explicitEuler`.** Both new theorems must be axiom-clean.

This extends the cycle 367 cherry pattern to the third tree
`broom₃ = mk [vertex, vertex]` (order 3, two children). It is the
next-non-trivial test of whether the cycle 366 §G Route B hypothesis
("closed-form polynomial in Φ at strict subtrees with quotient-
invariant coefficients") generalises beyond order 2.

### B.1 The closed-form identity (paper-derived; verify before
shipping)

For `broom₃ = mk [vertex, vertex]` and any
`η_q : Quotient PhiEquivalent.setoidSigma`, with representative
`⟨s, M⟩`:

```
Φ_{η_q⁻¹}(broom₃) = -(Φ_η(vertex))³
                    + 2 · Φ_η(vertex) · Φ_η(cherry)
                    - Φ_η(broom₃)
```

**Derivation** (paper-only; worker should re-derive in scratch
before writing the Lean):

1. By cycle 358 `_inv_mk`:
   `Φ_{⟦⟨s, M⟩⟧⁻¹}(broom₃) = -∑ᵢ M.b i · M.derivativeWeightWithSrc M.inverse i broom₃`.
2. Unfold `derivativeWeightWithSrc M.inverse i broom₃` via the
   `mk [vertex, vertex] = mk (vertex :: [vertex])` cons-structure
   into:
   `(M.inverse.elementaryWeight vertex + ∑ⱼ M.A i j ·
     M.derivativeWeightWithSrc M.inverse j vertex) ·
    M.derivativeWeightWithSrcProd M.inverse i [vertex]`.
3. The first factor reduces (via cycle 366
   `derivativeWeightWithSrc_vertex = 1`) to
   `(M.inverse.elementaryWeight vertex + ∑ⱼ M.A i j)`.
4. The second factor is **the same expression** (because `[vertex]`
   has the same structure as the front of `[vertex, vertex]`):
   `derivativeWeightWithSrcProd M.inverse i [vertex] =
    (M.inverse.elementaryWeight vertex + ∑ⱼ M.A i j) ·
    derivativeWeightWithSrcProd M.inverse i [] =
    (M.inverse.elementaryWeight vertex + ∑ⱼ M.A i j) · 1 =
    (M.inverse.elementaryWeight vertex + ∑ⱼ M.A i j)`.
5. So `derivativeWeightWithSrc M.inverse i broom₃ =
   (M.inverse.elementaryWeight vertex + ∑ⱼ M.A i j)²`.
6. By cycle 367's `h_inv_v` helper computation:
   `M.inverse.elementaryWeight vertex = -M.elementaryWeight vertex`.
7. Let `v := Φ_η(vertex) = ∑ⱼ M.b j` and `Aᵢ := ∑ⱼ M.A i j` (the
   "row sum"). Then `derivativeWeightWithSrc M.inverse i broom₃ =
   (-v + Aᵢ)² = v² - 2·v·Aᵢ + Aᵢ²`.
8. Sum over i with M.b weight:
   `∑ᵢ M.b i · (v² - 2·v·Aᵢ + Aᵢ²)
    = v² · (∑ᵢ M.b i) - 2·v · (∑ᵢ M.b i · Aᵢ) + ∑ᵢ M.b i · Aᵢ²
    = v² · v - 2·v · Φ_η(cherry) + Φ_η(broom₃)
    = v³ - 2·v·Φ_η(cherry) + Φ_η(broom₃)`.
   (Using `Φ_η(cherry) = ∑ᵢ M.b i · ∑ⱼ M.A i j = ∑ᵢ M.b i · Aᵢ`
   and `Φ_η(broom₃) = ∑ᵢ M.b i · derivativeWeight i broom₃
                    = ∑ᵢ M.b i · Aᵢ²`, since
    `derivativeWeight i broom₃ = (∑ⱼ M.A i j · derivativeWeight j vertex)
                                 · derivativeWeightProd i [vertex]
                               = Aᵢ · (∑ⱼ M.A i j · 1) · 1
                               = Aᵢ · Aᵢ = Aᵢ²`.)
9. Negate per step 1:
   `Φ_{η⁻¹}(broom₃) = -v³ + 2·v·Φ_η(cherry) - Φ_η(broom₃)`.

**Sanity check at `explicitEuler`** (s = 1, A = !![0], b = ![1]):
* `v = Φ_η(vertex) = 1`.
* `Aᵢ = 0` for all i, so `Φ_η(cherry) = 0` and `Φ_η(broom₃) = 0`.
* Expected: `Φ_{η⁻¹}(broom₃) = -(1)³ + 2·1·0 - 0 = -1`.

## C. Concrete proof recipe for `elementaryWeightQ_phi_inv_broom₃`

Mirror cycle 367's `elementaryWeightQ_phi_inv_cherry` proof (lines
2376–2439 of `Section422.lean`) with these extensions:

1. `refine Quotient.inductionOn η_q ?_; rintro ⟨s, M⟩`.

2. **Reuse cycle 367's helpers verbatim** (paste them into the
   broom₃ proof body):
   * `h_inv_v : M.inverse.elementaryWeight vertex = -M.elementaryWeight vertex`
   * `h_vertex : M.elementaryWeight vertex = ∑ⱼ M.b j`
   * `h_dw_cherry : ∀ i, M.derivativeWeight i cherry = ∑ⱼ M.A i j`
   * `h_cherry : M.elementaryWeight cherry = ∑ᵢ M.b i · ∑ⱼ M.A i j`

3. **Add three NEW helpers for broom₃**:
   * `h_dw_broom₃ : ∀ i, M.derivativeWeight i broom₃ = (∑ⱼ M.A i j)²`.
     Proof shape: `show (∑ⱼ M.A i j · derivativeWeight j vertex) ·
     derivativeWeightProd i [vertex] = (∑ⱼ M.A i j)²`. Then:
     - `derivativeWeightProd i [vertex] =
        (∑ⱼ M.A i j · derivativeWeight j vertex) · derivativeWeightProd i []`
       (from the recursive def — show this via `rfl` or
       `show ... = ... from rfl`).
     - `derivativeWeightProd i [] = 1` (`rfl`).
     - Each inner sum collapses by `Finset.sum_congr +
       derivativeWeight_vertex + mul_one` to `∑ⱼ M.A i j`.
     - Final: `(∑ⱼ M.A i j) · (∑ⱼ M.A i j) · 1 = (∑ⱼ M.A i j)^2`
       via `ring` or `sq`.

   * `h_broom₃ : M.elementaryWeight broom₃ =
                ∑ᵢ M.b i · (∑ⱼ M.A i j)²`.
     One-line `Finset.sum_congr rfl (fun i _ => by rw [h_dw_broom₃ i])`
     after `show ... = ...`.

   * `h_dws_broom₃ : ∀ i,
       M.derivativeWeightWithSrc M.inverse i broom₃ =
         (M.inverse.elementaryWeight vertex + ∑ⱼ M.A i j)^2`.
     Proof shape: parallel to cycle 367's `h_dws_cherry`, with one
     additional unfold layer. The `derivativeWeightWithSrcProd
     M.inverse i [vertex]` factor expands the same way as the
     outer factor:
     `show (M.inverse.elementaryWeight vertex + ∑ⱼ M.A i j ·
       M.derivativeWeightWithSrc M.inverse j vertex) ·
      derivativeWeightWithSrcProd M.inverse i [vertex] = ...`.
     Then `derivativeWeightWithSrcProd M.inverse i [vertex] =
     (M.inverse.elementaryWeight vertex + ∑ⱼ M.A i j ·
       M.derivativeWeightWithSrc M.inverse j vertex) · 1` (from
     definitional unfold), and each inner sum collapses via
     `derivativeWeightWithSrc_vertex = 1` to `∑ⱼ M.A i j`.
     Close with `(x + Aᵢ) · ((x + Aᵢ) · 1) = (x + Aᵢ)²` via `ring`
     where `x := M.inverse.elementaryWeight vertex`.

4. **Main computation** (mirror cycle 367's lines 2423–2439):
   ```
   rw [elementaryWeightQ_phi_inv_mk M RootedTree.broom₃,
       elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
       elementaryWeightQ_phi_mk]
   ```
   Need THREE `elementaryWeightQ_phi_mk` rewrites — one each for
   Φ_η at vertex, cherry, broom₃ on the RHS — plus the implicit
   one for Φ_{η⁻¹}(broom₃) on the LHS that `_inv_mk` handles.

5. **Closed-form bridge** via a `have h_sum` block:
   ```
   have h_sum :
       (∑ᵢ M.b i · M.derivativeWeightWithSrc M.inverse i broom₃)
         = M.elementaryWeight vertex ^ 3
           - 2 * M.elementaryWeight vertex * M.elementaryWeight cherry
           + M.elementaryWeight broom₃ := by
     have h_subst :
         (∑ᵢ M.b i · M.derivativeWeightWithSrc M.inverse i broom₃)
           = ∑ᵢ M.b i · (-M.elementaryWeight vertex + ∑ⱼ M.A i j)^2 := by
       refine Finset.sum_congr rfl (fun i _ => ?_)
       rw [h_dws_broom₃ i, h_inv_v]
     rw [h_subst]
     -- Expand the square per-summand:
     -- ∑ᵢ M.b i · (v² - 2·v·Aᵢ + Aᵢ²)
     -- = v² · (∑ᵢ M.b i) - 2·v · (∑ᵢ M.b i · Aᵢ) + ∑ᵢ M.b i · Aᵢ²
     -- = v³ - 2·v·Φ_η(cherry) + Φ_η(broom₃)
     -- WORKER: distribute the square per-summand via Finset.sum_congr +
     -- ring into a ternary-sum form, then collapse via
     -- Finset.sum_sub_distrib + Finset.sum_add_distrib +
     -- ← Finset.mul_sum × 2.
     sorry
   rw [h_sum]; ring
   ```

   The trickiest step is the per-summand square expansion plus the
   sum-distribution. Two paths:
   * **Path A (recommended)**: expand the square via
     `Finset.sum_congr rfl (fun i _ => by ring)` to get
     `∑ᵢ (M.b i · v² - 2·v·M.b i·Aᵢ + M.b i·Aᵢ²)`, then
     `Finset.sum_sub_distrib` + `Finset.sum_add_distrib`, then
     `← Finset.mul_sum` for the constant-`v²` and `-2·v` factors.
     Finally `rw [← h_vertex, ← h_cherry, ← h_broom₃]` and `ring`.
   * **Path B (fallback)**: open the square `(x + y)^2 = x^2 + 2*x*y + y^2`
     via `add_pow_two` first (verify Mathlib name with
     `lean_local_search "add_pow_two"`), then distribute. May
     produce cleaner intermediate goals.

   Don't waste cycle budget — pick Path A. If after 30 minutes
   the per-summand `ring` chain isn't closing, switch to Path B.

6. **Close the main goal** with `rw [h_sum]; ring`.

## D. `powRep_sum_eq_of_agreement_at_broom₃_zero` (m=0 corollary)

Three-rewrite-line proof mirroring cycle 367 (line 2477). Note that
the hypothesis list now has THREE agreement equations (vertex,
cherry, broom₃) because the cycle-368 closed form involves all
three:

```lean
theorem powRep_sum_eq_of_agreement_at_broom₃_zero
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_vertex : elementaryWeightQ_phi η_q RootedTree.vertex
              = elementaryWeightQ_phi η_q' RootedTree.vertex)
    (h_cherry : elementaryWeightQ_phi η_q RootedTree.cherry
              = elementaryWeightQ_phi η_q' RootedTree.cherry)
    (h_broom₃ : elementaryWeightQ_phi η_q RootedTree.broom₃
              = elementaryWeightQ_phi η_q' RootedTree.broom₃) :
    elementaryWeightQ_phi (η_q ^ (-(((0 + 1 : ℕ) : ℤ)))) RootedTree.broom₃
      = elementaryWeightQ_phi (η_q' ^ (-(((0 + 1 : ℕ) : ℤ)))) RootedTree.broom₃ := by
  have h_pow : ∀ ζ : Quotient PhiEquivalent.setoidSigma,
      ζ ^ (-(((0 + 1 : ℕ) : ℤ))) = ζ⁻¹ := by
    intro ζ; rw [zero_add, Nat.cast_one]; exact zpow_neg_one _
  rw [h_pow η_q, h_pow η_q',
      elementaryWeightQ_phi_inv_broom₃, elementaryWeightQ_phi_inv_broom₃,
      h_vertex, h_cherry, h_broom₃]
```

## E. Non-vacuity examples (two of them)

1. **Closed-form witness at explicitEuler**:
   ```lean
   example :
       elementaryWeightQ_phi
         ((Quotient.mk PhiEquivalent.setoidSigma
             ⟨1, RKTableau.explicitEuler⟩))⁻¹ RootedTree.broom₃ = -1 := by
   ```
   Expected: `-(1)³ + 2·1·0 - 0 = -1`. Proof recipe: same as cycle
   367's cherry non-vacuity but with TWO inner-zero helpers
   (`h_cherry_zero` from cycle 367 still valid; add
   `h_broom₃_zero`):
   ```
   have h_broom₃_zero :
       RKTableau.explicitEuler.derivativeWeight 0 RootedTree.broom₃ = 0 := by
     show (∑ j : Fin 1, RKTableau.explicitEuler.A 0 j ·
           RKTableau.explicitEuler.derivativeWeight j RootedTree.vertex) ·
          RKTableau.explicitEuler.derivativeWeightProd 0 [RootedTree.vertex] = 0
     simp [RKTableau.explicitEuler]
   ```
   Then `simp [h_broom₃_zero]` + `norm_num` to close.

2. **m=0 broom₃ witness with reflexive agreement**:
   ```lean
   example :
       elementaryWeightQ_phi
           ((Quotient.mk PhiEquivalent.setoidSigma
              ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
           RootedTree.broom₃
         = elementaryWeightQ_phi
             ((Quotient.mk PhiEquivalent.setoidSigma
                ⟨1, RKTableau.explicitEuler⟩) ^ (-(((0 + 1 : ℕ) : ℤ))))
             RootedTree.broom₃ :=
     powRep_sum_eq_of_agreement_at_broom₃_zero
       (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
       (Quotient.mk PhiEquivalent.setoidSigma ⟨1, RKTableau.explicitEuler⟩)
       rfl rfl rfl
   ```

## F. Insertion location

Insert the four new declarations (theorem + theorem + example +
example) in `OpenMath/Chapter4/Section422.lean` **between line
2507** (end of cycle 367's m=0 cherry non-vacuity example) **and
line 2509** (start of cycle 365's `linearResidualAt_depends_only_on_strict_subtrees`
docstring). Match the cycle 367 docstring style (Phase D.3.b Step 2
labelling, multi-paragraph rationale, proof-recipe summary).

## G. Verification checklist

After writing the four new declarations:

1. `time timeout 600 lake env lean OpenMath/Chapter4/Section422.lean`
   — expect <300s warm rebuild on healthy GPFS. EXIT=0 required.
2. `grep -c sorry OpenMath/Chapter4/Section422.lean` — must remain
   5 (4 documentation references + 1 grandfathered Sub-lemma A).
   **If this increases, REVERT immediately and do not commit.**
3. `#print axioms OpenMath.Chapter4.Section422.elementaryWeightQ_phi_inv_broom₃`
   — must be `[propext, Classical.choice, Quot.sound]` (no
   `sorryAx`). **If `sorryAx` appears, REVERT and diagnose.**
4. `#print axioms OpenMath.Chapter4.Section422.powRep_sum_eq_of_agreement_at_broom₃_zero`
   — same requirement.
5. Spot-check that the cycle 365/366/367 axiom-clean theorems
   (`linearResidualAt_depends_only_on_strict_subtrees`,
   `powRep_sum_eq_of_agreement_at_vertex`,
   `elementaryWeightQ_phi_inv_cherry`,
   `powRep_sum_eq_of_agreement_at_cherry_zero`) still match their
   expected axiom profiles (one `sorryAx` for the headline; clean
   for the others).

If verification passes, §422 axiom-clean streak extends from 33 → 34
(336–368). The Sub-lemma A general-body sorry remains grandfathered.

## H. DO NOT (explicit prohibitions)

* **DO NOT touch Sub-lemma A's body** at line 2279. This is the
  cycle 365 grandfathered sorry; closing it requires the multi-cycle
  inner-tableau substitution lemma (Route A) per cycle 366 task
  results. Cycle 368 is small-tree witness work, not Route A work.
* **DO NOT attempt the general-m broom₃ closed form** in the same
  cycle. Cycle 367 strategy §G explicitly notes the general-m
  cherry form would need a `Φ_{η₁·η₂}(cherry)` decomposition lemma
  that is itself multi-cycle. The m=0 corollary is the only
  cycle 368 stretch.
* **DO NOT attempt `mk [cherry]`** (the fourth order-3 tree) in the
  same cycle. It is a third witness on the order-3 ladder and not
  needed for cycle 368's planner-validation goal.
* **DO NOT attempt the multilinear Phase D.3.a.3 ℤ-form** at
  arbitrary `t` (cycle 360 deferral). That is Route A territory.
* **DO NOT modify `linearResidualAt`'s definition** (cycle 364
  audit fix is final).
* **DO NOT raise `maxHeartbeats`** above 200000. If the per-summand
  ring expansion (Path A) stalls, decompose into smaller named
  `have` blocks; do NOT increase heartbeats.
* **DO NOT submit to Aristotle this cycle.** The proof recipe is
  mechanical (cycle 367 template with one more unfold layer), and
  Aristotle jobs in the §422 cluster have historically been weak
  on convolution-product algebra. Manual closure is faster and
  more reliable.
* **DO NOT introduce new axioms or `noncomputable` definitions.**

## I. Failed approaches NOT to repeat (from cycle 366 / 367 logs)

* **Strong induction on `t.order`** with cycle 362's
  `derivativeWeightWithSrc_eq_of_strict_subtree_agreement` (cycle
  366 attempt): the substitution lemma swaps the SOURCE tableau
  (`M₁` argument), not the INNER tableau (`M₂` argument), so it
  cannot bridge cross-side heterogeneity in Sub-lemma A's general
  body. **This path is documented closed** in
  `.prover-state/issues/def_422B_phase_D_3_scoping.md` cycle 366
  update. Cycle 368 is per-tree witness work; Sub-lemma A general
  body remains deferred.
* **`rw [show ∀ i, ...]` syntax** under a binder (cycle 367 dead
  end): cannot rewrite under a binder with `rw`. Use
  `Finset.sum_congr rfl (fun i _ => by ...)` inside a `calc`
  chain or as a `have h_subst` intermediate instead. **Reapply
  this pattern verbatim** in the broom₃ proof's per-summand
  square expansion.
* **`simp [explicitEuler]` over-eager reduction** (cycle 367 dead
  end at cherry non-vacuity): when `simp` reduces the outer sum
  but leaves the inner `derivativeWeight i cherry` unfolded,
  introduce a separate `h_<tree>_zero` step that manually unfolds
  the inner expression via `show ... = 0` and a targeted simp set
  with `RKTableau.explicitEuler` + `Fin.sum_univ_one`. **Reapply
  this pattern** in the broom₃ non-vacuity example: add a separate
  `h_broom₃_zero : RKTableau.explicitEuler.derivativeWeight 0
  RootedTree.broom₃ = 0` step.
* **`norm_num` for `Int.negSucc` bridging** (cycle 361 dead end):
  `-(((m+1):ℕ):ℤ) = Int.negSucc m` is definitional `rfl`; do NOT
  use `norm_num` (leaves display-ambiguous unsolved goal). Use
  `Nat.cast_one + zpow_neg_one` (cycle 367 m=0 cherry recipe)
  uniformly in the m=0 broom₃ corollary.

## J. Risk and abort criteria

* **MEDIUM risk** that the per-summand square expansion (Path A
  in C.5) takes longer than expected. The cycle 367 cherry proof
  was ~40 LOC; broom₃ may be 60–80 LOC due to the extra unfold
  layer for two-child trees plus the squared-quantity arithmetic.
* **Abort threshold**: if after 60 minutes of focused work the
  per-summand expansion is not closing, ABANDON Path A and try
  **Path B**: open the square via `add_sq` (Mathlib name; verify
  with `lean_local_search "add_sq"` or
  `lean_loogle "(_ + _) ^ 2"`) at the very start of `h_expand`,
  getting an explicit ternary sum, then close via
  `Finset.sum_add_distrib` + `Finset.sum_sub_distrib` +
  `← Finset.mul_sum` × 2.
* **Hard abort**: if neither path closes within 2 hours total,
  REVERT to HEAD and ship only the m=0 corollary alongside a
  cycle 369+ scoping note explaining the obstacle. **Do NOT leave
  a sorry in the broom₃ closed form**. The cycle 365 rollback
  precedent (revert if sorry count would rise) is in force.
* **Sorry count discipline**: this cycle must NOT increase code-
  level sorry count above 1 (the grandfathered Sub-lemma A
  sorry). Any new sorry introduced REVERTS the cycle.

## K. Expected cycle 368 outcome (success criteria)

* Two new public theorems shipped axiom-clean:
  `elementaryWeightQ_phi_inv_broom₃` and
  `powRep_sum_eq_of_agreement_at_broom₃_zero`.
* Two new non-vacuity `example`s on `explicitEuler`.
* `lake env lean OpenMath/Chapter4/Section422.lean` exits 0.
* `grep -c sorry` returns 5 (unchanged).
* §422 axiom-clean streak: 33 → 34.
* Section422.lean grows from 2596 → ~2700 LOC.
* `extraction/formalization_data/lean_status.json` unchanged for
  `def:422B` (it's already `partial`).
* `plan.md` def:422B row may be updated with a cycle 368 line
  noting "third-tree closed form (broom₃) extends the witness
  library; closed-form pattern now validated at 3 trees of orders
  1, 2, 3".

## L. Cycle 369+ outlook (per cycle 367 §G decision rule)

* **If broom₃ closed form ships cleanly in 1 cycle** (this cycle):
  the Route B Hypothesis (cycle 366 §G) is now supported by THREE
  data points (vertex, cherry, broom₃). Cycle 369 should attempt
  the **inductive `t.order` formulation of Sub-lemma A** — i.e.
  start the multi-cycle Route B closure, going through a uniform
  `Φ_{η⁻¹}(t)` closed-form theorem indexed by tree depth.
* **If broom₃ resists in 1 cycle** (e.g. abort at J): pivot to
  Route A (inner-tableau substitution lemma) as a multi-cycle
  effort. File a scoping doc explaining the obstacle.
* **Stretch (skip this cycle)**: general-m cherry closed form
  `powRep_inv_cherry_closed_form` per cycle 367 §C.2. This is
  cycle 370+ work, NOT cycle 368.

## M. Bottom line for the worker

Cycle 368 is a focused **single-tree extension** of the cycle 367
cherry template. Mirror the cherry proof recipe (lines 2376–2439
of `Section422.lean`) with one additional unfold layer for the
two-child `broom₃` structure. The closed form is
`Φ_{η⁻¹}(broom₃) = -(Φ_η(vertex))³ + 2·Φ_η(vertex)·Φ_η(cherry) -
Φ_η(broom₃)`. The m=0 corollary is a 3-line `rw` chain. The
non-vacuity at `explicitEuler` is `-1` and closes with the
`h_broom₃_zero` workaround from cycle 367.

Both theorems must be axiom-clean. Sorry count must remain at 5.
The Sub-lemma A grandfathered sorry stays untouched. Do not pursue
the general-m form, do not pursue `mk [cherry]`, do not pursue
Route A, do not submit to Aristotle.

Total expected cycle effort: ~60–90 minutes of focused work,
~80–100 new LOC across four declarations + their docstrings.
