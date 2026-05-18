# Cycle 384 strategy

## TL;DR

**Ship `elementaryWeightQ_phi_inv_mkCherryCherry`** (the 9th-tree
closed form at the order-5 tree `mk [cherry, cherry]`) plus its
m=0 Sub-lemma A corollary, both axiom-clean. This is a mechanical
extension of the cycle 367–372 single-tree-per-cycle ladder using
the cycle 371/372 template (heterogeneous-children trees).

Hard-rejected alternatives: scoping-doc-only (cycle 379 was scored
**0** for shipping only markdown — the supervisor wants Lean code
per cycle); Family C scoping work in isolation (premature: cycle
372 worker explicitly said 2 Family C data points was insufficient
for unification; need a 3rd disambiguation data point first); any
attempt at the cycle 365 grandfathered sorry (multi-cycle work
gated on a unified `inversePolyTree` recursion that doesn't exist
yet).

This cycle continues the cycle 322-onward §422 axiom-clean streak
**47 substantive + 1 doc → 48 substantive + 1 doc** (cycles 336–384).

## Status at HEAD (commit `091f6f3`)

* `OpenMath/Chapter4/Section422.lean`: ~5999 LOC.
* `grep -c sorry` = 5 lines (4 docstring + 1 actual code sorry at
  line 2279, the cycle 365 grandfathered
  `powRep_sum_eq_of_strict_subtree_agreement` body).
* Witness library: 8 trees with closed-form inverse +
  m=0 corollaries shipped (vertex, cherry, broom₃, mk [cherry],
  bushy, mk [broom₃], mk [vertex, cherry], mk [mk [cherry]]).
* `inversePolynomial` covers 8 ladder trees + `0` fallback; Family
  A `inversePolyChain` (4 cases) and Family B `inversePolyBroom` (4
  cases) closed-form helpers migrated cycles 380/381/382/383.
* The order-5 tree `mk [cherry, cherry]` already has B-series
  infrastructure shipped in cycle 269
  (`bseriesExactTerm_mkCherryCherry_scalar` at
  `OpenMath/Chapter3/Section301.lean:1747`); confirmed `σ = 2`,
  `γ = 20` via `rfl`-reducible structural values.

## P1 (primary, mandatory) — ship `elementaryWeightQ_phi_inv_mkCherryCherry`

**Target file**: `OpenMath/Chapter4/Section422.lean`. Insert the new
theorem **immediately after** cycle 378's
`powRep_sum_eq_of_agreement_at_mkMkCherry_zero` (which ends around
line 4554). Keep the chronological cycle ordering visible in the
file.

**Target statement** (signature to type-check first; worker derives
the precise polynomial during proof):

```lean
/-- **Quotient-level closed form: `Φ_{η_q⁻¹}` at `mk [cherry, cherry]`.**

Order-5 tree with σ=2 (two identical cherry children — `2!·σ(cherry)²`).
Ninth tree in the inverse-polynomial closed-form ladder; first
**symmetric two-non-leaf-children** witness. Disambiguates Family C
recipe alongside cycle 371 `mk [broom₃]` (single non-leaf child) and
cycle 372 `mk [vertex, cherry]` (mixed leaf + non-leaf children). -/
theorem elementaryWeightQ_phi_inv_mkCherryCherry
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi (η_q⁻¹)
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.cherry, RootedTree.cherry])
      = -- closed form, derived below by worker
        sorry
```

**Closed-form derivation steps** (worker MUST derive symbolically
on paper before coding the RHS):

* Let `v := Φ_η(vertex), c := Φ_η(cherry), b' := Φ_η(broom₃),
  m := Φ_η(mk [cherry]), C := Φ_η(mk [cherry, cherry])`.
* Cycle 358 `elementaryWeightQ_phi_inv_mk` gives:
  `Φ_{η⁻¹}(mk [cherry, cherry]) = −Σⱼ M.b j · M.derivativeWeightWithSrc M.inverse j (mk [cherry, cherry])`.
* For `mk [cherry, cherry]`, the `derivativeWeightWithSrc M.inverse i`
  factorizes via cycle 372-style two-child unfold into a product of
  two source-tagged factors *each at `cherry`*. Both factors are
  identical (same child); use cycle 367's `h_dws_cherry`:
  `M.derivativeWeightWithSrc M.inverse i cherry = M.inverse.elementaryWeight vertex + (Σⱼ Aᵢⱼ)`
  `= -v + Aᵢ` (using `h_inv_v`).
* Per-row factor: `(-v + Aᵢ)²` where `Aᵢ := Σⱼ Aᵢⱼ`.
* Distribute: `Σᵢ M.b i · (-v + Aᵢ)² = Σᵢ M.b i · (v² − 2v·Aᵢ + Aᵢ²)`.
  - The `v² · Σᵢ M.b i = v² · v = v³` (using `h_vertex`).
  - The `−2v · Σᵢ M.b i · Aᵢ = −2v · c` (using `h_cherry`).
  - The `Σᵢ M.b i · Aᵢ² = b'` (using `h_broom₃`).
* So `Σᵢ M.b i · derivativeWeightWithSrc M.inverse i (mk [cherry, cherry])
  = v³ − 2v·c + b' + (the part involving C itself from the
  outermost layer of derivativeWeightWithSrc)`.

**WARNING**: the derivation above is incomplete — the worker must
unfold `M.derivativeWeightWithSrc M.inverse i (mk [cherry, cherry])`
carefully via the cycle 372 two-child cons-case pattern. There may
be an additional `+M.elementaryWeight(mk [cherry, cherry])` term
contributing from the outer-layer unfold beyond just the product of
two cherry-child factors. Reference cycle 372's `h_dws_mkVertexCherry`
proof at `Section422.lean:3940–3970` for the precise two-layer recipe.

**Predicted closed form** (likely; worker verifies):

```
Φ_{η⁻¹}(mk [cherry, cherry])
  = -v³ + 2v·c - b' - (something at mk [cherry])  -- speculative;
  - C
```

OR (alternative shape, possibly correct):

```
Φ_{η⁻¹}(mk [cherry, cherry]) = v⁴ − 2v²·c + c² − v·b' + 2v·m − C
```

The cycle 371 `mk [broom₃]` form has 5 terms ending in `−M`; cycle
372 `mk [vertex, cherry]` has 6 terms ending in `−V`. Cycle 384's
`mk [cherry, cherry]` is symmetric like cycle 371 and probably has
4–6 terms ending in `−C`. **Worker must compute, not guess.**

**Proof recipe**: copy-paste the cycle 372
`elementaryWeightQ_phi_inv_mkVertexCherry` skeleton verbatim
(`Section422.lean:3798–4135`) and adapt:

1. **Reused helpers** (verbatim from cycle 372 / 369 / 368 / 367):
   - `h_inv_v`, `h_vertex` (cycle 367).
   - `h_dw_cherry`, `h_cherry`, `h_dws_cherry` (cycle 367).
   - `h_dw_broom₃`, `h_broom₃` (cycle 368).
   - `h_inv_cherry` (cycle 369, representative-lift at `⟦M⟧`).
   - `h_dw_mkCherry`, `h_mkCherry` (cycle 369) — include ONLY if
     the closed form has an `m` term, else drop.

2. **New helpers** for the two-identical-cherry-children structure:
   - `h_dw_mkCherryCherry : ∀ i,
        M.derivativeWeight i (mk [cherry, cherry])
          = (∑ j, M.A i j * ∑ k, M.A j k)²`
     via two-cons unfold using `h_dw_cherry` per slot; the two
     identical cherry factors collapse to a square.
   - `h_mkCherryCherry : M.elementaryWeight (mk [cherry, cherry])
        = ∑ i, M.b i * (∑ j, M.A i j * ∑ k, M.A j k)²`
     via `Finset.sum_congr` + `h_dw_mkCherryCherry`.
   - `h_dws_mkCherryCherry : ∀ i,
        M.derivativeWeightWithSrc M.inverse i (mk [cherry, cherry])
          = (M.inverse.elementaryWeight cherry + ...)²` OR appropriate
     two-cherry product form
     via two-layer cons-case unfold; the *outer* layer strips `mk` and
     produces a product of two source-tagged factors; both factors
     reduce via cycle 367's `h_dws_cherry` (identical children, so
     the same simplification applies twice). **CRITICAL**: this is
     where the two-cherry symmetry differs from cycle 372's
     `mk [vertex, cherry]` — for cycle 372 the first factor was
     `M.derivativeWeightWithSrc M.inverse i vertex = 1` (trivial),
     here it's `M.derivativeWeightWithSrc M.inverse i cherry` (non-trivial,
     squared).

3. **Main `h_sum` computation**:
   - Apply cycle 358 `elementaryWeightQ_phi_inv_mk` to expose the
     `-Σᵢ M.b i · M.derivativeWeightWithSrc M.inverse i (mk
     [cherry, cherry])` form.
   - Substitute `h_dws_mkCherryCherry` per `i`.
   - Distribute `Σᵢ M.b i · (factor)²` via `Finset.sum_congr` +
     `ring` per-term into a sum of named elementary weights via
     `← Finset.mul_sum` + back-substitution
     (`← h_vertex, ← h_cherry, ← h_broom₃, ...` as needed).

4. **Close** with `linarith` or `ring` after all elementary weights
   are re-substituted.

**LOC budget**: 220 LOC (similar to cycle 371's 230 LOC, cycle 372's
220 LOC).

**Axiom target**: `[propext, Classical.choice, Quot.sound]` only.

## P2 (mandatory) — ship `powRep_sum_eq_of_agreement_at_mkCherryCherry_zero`

The m=0 Sub-lemma A corollary. Place immediately after the P1 theorem.
Mirror cycle 371 `_at_mkBroom₃_zero` / cycle 372 `_at_mkVertexCherry_zero`
exactly:

```lean
/-- **m=0 case of Sub-lemma A at `t = mk [cherry, cherry]`.** -/
theorem powRep_sum_eq_of_agreement_at_mkCherryCherry_zero
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_vertex : elementaryWeightQ_phi η_q RootedTree.vertex
                 = elementaryWeightQ_phi η_q' RootedTree.vertex)
    (h_cherry : elementaryWeightQ_phi η_q RootedTree.cherry
                 = elementaryWeightQ_phi η_q' RootedTree.cherry)
    (h_broom₃ : elementaryWeightQ_phi η_q RootedTree.broom₃
                 = elementaryWeightQ_phi η_q' RootedTree.broom₃)
    -- include h_mkCherry only if the closed form mentions it
    -- (h_mkCherry : ...)
    (h_mkCherryCherry : elementaryWeightQ_phi η_q
                    (RootedTree.mk [RootedTree.cherry, RootedTree.cherry])
                   = elementaryWeightQ_phi η_q'
                    (RootedTree.mk [RootedTree.cherry, RootedTree.cherry])) :
    elementaryWeightQ_phi (η_q ^ (-(((0 + 1 : ℕ) : ℤ)))) (RootedTree.mk
        [RootedTree.cherry, RootedTree.cherry])
      = elementaryWeightQ_phi (η_q' ^ (-(((0 + 1 : ℕ) : ℤ)))) (RootedTree.mk
        [RootedTree.cherry, RootedTree.cherry]) := by
  -- 4-line ζ^{-1} bridge + apply P1 + rewrite via agreement hypotheses
  ...
```

Recipe (verbatim from cycle 371/372 corollaries):

1. `have h_neg_one : ∀ ζ : Quotient PhiEquivalent.setoidSigma,
       ζ ^ (-(((0 + 1 : ℕ) : ℤ))) = ζ⁻¹ := by
     intro ζ; rw [zero_add, Nat.cast_one]; exact zpow_neg_one _`.
2. `rw [h_neg_one η_q, h_neg_one η_q']`.
3. `rw [elementaryWeightQ_phi_inv_mkCherryCherry,
       elementaryWeightQ_phi_inv_mkCherryCherry]`.
4. Rewrite by all agreement hypotheses provided.

**LOC budget**: 15 LOC.

**Hypothesis selection**: include exactly the elementary-weight names
that appear on the RHS of P1's closed form. Do NOT add extraneous
hypotheses (cycle 378 worker discovery: faithful corollary lists only
the weights actually appearing in the closed-form RHS — the cycle 371
m=0 corollary did NOT list `h_mkCherry` because `mk [broom₃]`'s
closed form doesn't depend on `m`).

## P3 (mandatory) — non-vacuity examples

Mirror cycles 371/372 exactly. Two anonymous `example`s after the
m=0 corollary:

```lean
/-- Non-vacuity: closed form at `explicitEuler`. -/
example : elementaryWeightQ_phi
            ((Quotient.mk PhiEquivalent.setoidSigma
              ⟨_, RKTableau.explicitEuler⟩)⁻¹)
          (OpenMath.Chapter3.Section310.RootedTree.mk
            [RootedTree.cherry, RootedTree.cherry]) = ?_value := by
  rw [elementaryWeightQ_phi_inv_mkCherryCherry]
  -- All Φ_{explicitEuler}(t) = 1 (cycle 187 witness) → closed form
  -- evaluates to a concrete numeric constant.
  simp [explicitEuler_elementaryWeight]   -- or analogous simp set
  norm_num                                -- if needed

/-- Non-vacuity: reflexive m=0 witness. -/
example : True := by
  have := powRep_sum_eq_of_agreement_at_mkCherryCherry_zero
    (Quotient.mk PhiEquivalent.setoidSigma ⟨_, RKTableau.explicitEuler⟩)
    (Quotient.mk PhiEquivalent.setoidSigma ⟨_, RKTableau.explicitEuler⟩)
    rfl rfl rfl rfl  -- N hypotheses, all by rfl
  trivial
```

(The first example's exact numerical value depends on which closed
form lands — worker fills in by computing each term at v=c=b'=m=C=1
for `explicitEuler`.)

## What NOT to do this cycle

1. **Do NOT extend `inversePolynomial`'s pattern-match** with a 9th
   `else if t = mk [cherry, cherry]` branch. Cycle 372 worker
   explicitly recommended **scoping over extending the pattern-match
   ladder**; this cycle's purpose is closed-form data acquisition
   (P1), not pattern-match extension. The migration of
   `mk [cherry, cherry]` into `inversePolynomial` is deferred to
   cycle 385+ as part of the unified Family C helper definition.

2. **Do NOT touch `inversePolynomial`, `inversePolyChain`,
   `inversePolyBroom`, or their bridge theorems**. These are cycle
   380–383 deliverables; modifying them risks breaking the Phase γ
   `inversePolynomial_eq_of_subtree_agreement` proof.

3. **Do NOT attempt the cycle 365 grandfathered sorry**
   (`powRep_sum_eq_of_strict_subtree_agreement` at line 2279).
   Multi-cycle work, gated on the unified `inversePolyTree` recursion
   that doesn't exist yet.

4. **Do NOT submit Aristotle batches** for P1. Closed-form
   derivation + cycle 372 template port is one-cycle manual work.
   Aristotle adds latency without value.

5. **Do NOT do scoping-doc-only work**. Cycle 379 scored 0 for
   shipping a 903-line markdown doc with no Lean code. The
   supervisor wants Lean per cycle. If P1+P2+P3 ship under budget,
   an optional one-paragraph appendix to
   `def_422B_phase_alpha_prime_scoping.md` §4 (Family C analysis)
   is permitted but NOT a substitute for the Lean ship.

6. **Do NOT use `simp [recursive-def, name-eq-thm, …]`** patterns
   on `derivativeWeightWithSrcProd` or its helpers. Per memory
   `feedback_simp_recursive_def_overunfolds.md`: simp over-unfolds
   recursive defs before name theorems can fold back. Use targeted
   `rw [name-eq-thm-1, name-eq-thm-2, …]` then `simp [arithmetic]; ring`.

7. **Do NOT rename `h_<name>` → `h<name>`** cosmetically to dodge the
   tautology scanner. The cycle 371/372 helpers all use
   `h_inv_v, h_vertex, h_dw_cherry, h_cherry, h_dws_cherry, h_dw_broom₃,
   h_broom₃, h_inv_cherry, h_dw_mkCherry, h_mkCherry, h_dw_mkCherryCherry,
   h_mkCherryCherry, h_dws_mkCherryCherry` etc. without scanner hits
   (these are sub-proof intermediates that the scanner doesn't flag).

## Faithfulness check (worker fills in during proof)

For `elementaryWeightQ_phi_inv_mkCherryCherry`:

* **Entity ID**: not a textbook entity. Internal Lean housekeeping
  (9th tree in inverse-polynomial closed-form ladder, analogue of
  cycles 367/368/369/370/371/372/378).
* **Textbook statement quote**: the underlying object
  `Φ_{η⁻¹}(mk [cherry, cherry])` is the §383 group-inverse evaluated
  at a specific rooted tree — Butcher §383 / §387 provide the
  framework; no explicit closed form printed.
* **Lean statement captures**: same content as the symbolic
  derivation from cycle 358's `elementaryWeightQ_phi_inv_mk` applied
  to the cycle 269 `mk [cherry, cherry]` tree shape (σ=2, γ=20). The
  worker must compute the RHS step-by-step and verify
  symbolically before committing the proof body.
* **Hypothesis strength check**: no hypotheses beyond `η_q :
  Quotient PhiEquivalent.setoidSigma`. Faithful to cycle 367–372
  pattern.
* **Absent theorem check**: P1 + P2 + P3 examples must all land
  axiom-clean in the same cycle (no cross-cycle promises).

For `powRep_sum_eq_of_agreement_at_mkCherryCherry_zero`:

* Lists the elementary-weight agreement hypotheses exactly matching
  the RHS of P1's closed form (NO extras). Faithful to cycle 378
  worker's discovery.

## Pre-flight checklist

Before any code edit, run:

```bash
git log -1 --format='%H %s'                    # confirm HEAD = 091f6f3
wc -l OpenMath/Chapter4/Section422.lean        # confirm ~5999 LOC
grep -c sorry OpenMath/Chapter4/Section422.lean # confirm 5
```

After P1+P2+P3 ship:

```bash
lake env lean OpenMath/Chapter4/Section422.lean
# exit 0 with single warning at line 2279
grep -c sorry OpenMath/Chapter4/Section422.lean
# confirm still 5 (unchanged)
```

Then `#print axioms` on the 2 new public theorems
(`elementaryWeightQ_phi_inv_mkCherryCherry`,
`powRep_sum_eq_of_agreement_at_mkCherryCherry_zero`) — both must
return `[propext, Classical.choice, Quot.sound]` only.

## Graceful degradation (if P1 stalls past 60 min)

If symbolic derivation of the P1 closed form gets stuck:

1. **Step back**: literally copy-paste cycle 372's
   `elementaryWeightQ_phi_inv_mkVertexCherry` proof body
   (`Section422.lean:3798–4135`). Substitute identifiers:
   `mkVertexCherry → mkCherryCherry`; replace the cycle 372
   "vertex factor" helper with a second cycle 367-style cherry
   factor; the per-row factorization becomes
   `(M.derivativeWeightWithSrc M.inverse i cherry)²` (squared,
   symmetric) instead of cycle 372's
   `(M.derivativeWeightWithSrc M.inverse i vertex) ·
   (M.derivativeWeightWithSrc M.inverse i cherry)` (mixed).

2. **If still stuck**: extract just the new `h_dw_mkCherryCherry +
   h_mkCherryCherry + h_dws_mkCherryCherry` helpers (the 3 new
   pieces) and the closed-form polynomial computation (the
   `h_sum` block) as a focused sub-deliverable. Ship the P1 theorem
   with `unfold + rfl`-or-substitution placeholder if the per-term
   substitution arithmetic blows up. **Do NOT introduce a sorry
   without escalating** — file a cycle 385 entry-point issue
   instead.

3. **Last-resort fallback** (acceptable for streak preservation):
   ship a **weaker version** of P1 — instead of the full quotient-
   level closed form, ship `M.inverse.elementaryWeight (mk
   [cherry, cherry]) = (closed form in M.elementaryWeight values)`
   at the representative level only, without the
   `elementaryWeightQ_phi (η_q⁻¹)` quotient lift. This still gives
   a Family C data point but skips one layer of abstraction.

## Cycle 385+ outlook (after cycle 384 lands)

With 9 closed-form witnesses spanning 5 trees of order ≤ 4 and 4
trees of order 5 (after this cycle: vertex, cherry, broom₃, mk
[cherry], bushy, mk [broom₃], mk [vertex, cherry], mk [mk [cherry]],
mk [cherry, cherry]):

* **Cycle 385**: Family C scoping doc. With 3 Family C data points
  (`mk [broom₃]`, `mk [vertex, cherry]`, `mk [cherry, cherry]`),
  the structural rule for heterogeneous-children closed forms should
  be derivable. Write the Phase α'.4 plan (unified
  `inversePolyTree : RT → (RT → ℝ) → ℝ` recursion).

* **Cycle 386+**: ship the unified `inversePolyTree` definition that
  dispatches by children-list pattern matching. Migrate
  `inversePolynomial`'s remaining branches.

* **Cycle 387+**: ship the global bridge
  `elementaryWeightQ_phi_inv_eq_inversePolynomial` over all `t : RT`,
  closing the cycle 365 grandfathered sorry at line 2279.

The 9-witness data set unblocks cycle 385's scoping work. Without
this cycle's P1 ship, cycle 385 would still need this empirical data
point first — so we ship it now.
