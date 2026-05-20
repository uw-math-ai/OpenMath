---
name: Consultant advice — cycle 504 (Phase α'.5.2.5 closed; "still pending" is stale; the heterogeneous obstacle is the long-term Phase β/γ blocker, not single-cycle work)
description: Verified cycle 504 already shipped mk[c,c,c,c] (Section422.lean lines 12626/13882). The "stuck on" framing claiming (c,c,c,c) is pending Phase α'.5.2.5 is stale. The genuine remaining blocker — heterogeneous inner-tableau M₂ vs M₂' obstacle in Sub-lemma A (cycle 365 grandfathered sorry) — is multi-cycle Phase β/γ extension work, not single-cycle closeable. Recommends cycle 505 either pursue one more α'.5.2.k mixed-child witness, or pivot to writing a Phase β/γ scoping doc consuming the now-five-witness empirical surface.

Author: consultant subagent.
Date: 2026-05-20.
Phase at time of writing: cycle 504, post-worker.
Branch tip: `3853cbb Cycle 503 — §422 Phase α'.5.2.4 ship`; cycle 504 work uncommitted but present in working tree.

---

## TL;DR

1. **The "stuck on" framing is stale.** The prompt says "the all-cherry symmetric quadruple (c,c,c,c) still pending Phase α'.5.2.5" — verifiably false. Cycle 504 has already shipped `elementaryWeightQ_phi_inv_mkCherryCherryCherryCherry` (`Section422.lean:12626`) and `powRep_sum_eq_of_agreement_at_mkCherryCherryCherryCherry_zero` (`Section422.lean:13882`). Phase α'.5.2.5 is closed at the working-tree level; only the commit/bookkeeping remains.

2. **The "heterogeneous M₂ vs M₂' obstacle" is the genuine multi-cycle blocker.** This is the cycle 365 grandfathered sorry at `Section422.lean:2279` (`powRep_sum_eq_of_strict_subtree_agreement`). It has been open for 139 cycles (365 → 504) because no single-cycle path closes it. The cycle 495 scoping doc (`def_422B_phase_beta_gamma_scoping.md`) explicitly identifies Phase β.2 (`Φ_{η⁻¹}(t) = inversePolyTree t (Φ_η ·)` lifted to arbitrary `t`) as a load-bearing prerequisite, and cycle 497's task results §"Discovery #3" confirmed that closure requires the k=4 (and eventually k≥5) extension of `inversePolyTree`.

3. **The five-witness Phase α'.5.2 ladder is now sufficient empirical surface.** Cycles 499/501/502/503/504 have closed every k=4 quadruple using ONLY {vertex, cherry} as children. The cycle 504 sympy-validated cancellation pattern (3 cancellations: v, m, cccc — NOT 4 as the strategy predicted) is a meaningful refinement of cycles 502/503's discoveries. **Cycle 505+ has a genuine pivot decision** between: (a) one more mixed-child α'.5.2.k witness, (b) Phase β/γ k=4-extension scoping, (c) fresh-entity pivot.

4. **Do not attempt the cycle 365 sorry closure in cycle 505.** It is not single-cycle work, and the Phase β.2 falsity diagnosed in cycle 497 means even Phase β/γ work requires α'.5.2 to be extended further (to k=5 and beyond) OR a parametric `nchildPolynomial` (multi-cycle infrastructure). Either way, the sorry stays open as the grandfathered blocker; that is correct project state and does not require remediation this cycle.

---

## §A. Verification: cycle 504 already shipped Phase α'.5.2.5

`git status` shows uncommitted work in `OpenMath/Chapter4/Section422.lean` plus a new `.prover-state/task_results/cycle_504.md`. Spot-checking the file:

* Line 12626: `theorem elementaryWeightQ_phi_inv_mkCherryCherryCherryCherry` — quotient-level closed form for the all-cherry order-9 tree.
* Line 13282–13609: matching `_dw`, `_mk`, `_dws` helpers + main computation. Per the file's own §18 update (the `def_422B_phase_alpha_prime_5_2_scoping.md` doc), this is a "31-monomial closed form in 15 named kernels."
* Line 13882: `theorem powRep_sum_eq_of_agreement_at_mkCherryCherryCherryCherry_zero` — Sub-lemma A m=0 specialisation, 14 agreement hypotheses.
* Memory entry `feedback_cherry_child_cancellation.md` documents cycle 504's sympy correction (3 not 4 cancellations).

§422 cluster status: 77 substantive + 6 doc cycles, sorry count 5 (4 docstring + 1 grandfathered cycle 365). LOC ≈ 19159, up from ~17000 pre-cycle-504.

**Net: cycle 504's substantive work is DONE.** The "stuck on" framing in the prompt was constructed before cycle 504 completed and is now stale.

---

## §B. The heterogeneous obstacle — why it's not single-cycle closeable

The cycle 365 sorry's statement:

```lean
theorem powRep_sum_eq_of_strict_subtree_agreement
    (m : ℕ) (t : RT)
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (_h_closed : ∀ s : RT, s.order ≤ t.order →
        elementaryWeightQ_phi η_q s = elementaryWeightQ_phi η_q' s) :
    elementaryWeightQ_phi (η_q ^ (-(((m + 1) : ℕ) : ℤ))) t
      = elementaryWeightQ_phi (η_q' ^ (-(((m + 1) : ℕ) : ℤ))) t := by
  sorry
```

After `Quotient.inductionOn₂ η_q η_q'` and cycle 361's `elementaryWeightQ_phi_zpow_negSucc_mk`, both sides reduce to

```
-Σⱼ N.b j · N.derivativeWeightWithSrc N.inverse j t
```

where `N := (M.powRep (m+1)).2 : RKTableau (M.1·(m+1))` for the LHS and `N' := (M'.powRep (m+1)).2 : RKTableau (M'.1·(m+1))` for the RHS. **When `M.1 ≠ M'.1` these sums range over different `Fin` types** — no direct algebraic identification.

### Why cycle 362's strict-subtree lemma can't bridge it

Cycle 362's `derivativeWeightWithSrc_eq_of_strict_subtree_agreement` substitutes the **source** tableau `M₁` (the argument to `.derivativeWeightWithSrc M₁ i t`), not the **inner** tableau `M₂` (the receiver `.derivativeWeightWithSrc` is called on). Specifically:

```lean
theorem derivativeWeightWithSrc_eq_of_strict_subtree_agreement
    (M₂ : RKTableau s₂) (t : RT)
    (h_strict : ∀ s, s.order < t.order →
        M₁.elementaryWeight s = M₁'.elementaryWeight s)
    (i : Fin s₂) :
    M₂.derivativeWeightWithSrc M₁ i t = M₂.derivativeWeightWithSrc M₁' i t
```

— note `M₂` is FIXED across the equality. Our cycle 365 obstacle needs `M₂ ↔ M₂'` substitution (the powRep representatives differ on the LHS vs RHS), which is structurally different.

### Why "strong induction on t.order via cycle 343" doesn't directly work either

The natural induction tries to reduce to children of `t`, but each induction step's recursive call lands at `derivativeWeightWithSrc M.inverse j t'` for some child `t'` and stage `j : Fin s_M·(m+1)`. The recursion's IH lives at order `< t.order` for the tree but at the **same** stage-count `M.1·(m+1)` for the inner tableau — yet on the RHS, the stage count is `M'.1·(m+1)`, different.

This is the structural mismatch. It is not single-cycle closeable.

---

## §C. The Phase β/γ scoping doc's resolution route (cycle 495) and why it currently doesn't close

Cycle 495 (`def_422B_phase_beta_gamma_scoping.md`) proposed:

* **Phase β.1**: per-tree dispatch `elementaryWeightQ_phi_inv = inversePolyTree …` for the 14-tree calibration ladder. **SHIPPED** cycle 496.
* **Phase β.2**: lift Phase β.1 to ARBITRARY `t : RT` via structural induction. **SHIPPED for k≤3 children** cycle 497.
* **Phase γ**: `inversePolyTree`'s closed-subtree-agreement preservation. **SHIPPED** cycle 497.
* **Phase δ + ε**: lift to general `m+1` powers + close the sorry. Pending.

**However**, cycle 497 worker discovered Phase β.2's R6 assumption is FALSE for k≥4 trees: `inversePolyTree`'s `mk (_::_::_::_::_) → 0` catch-all does NOT match `Φ_{η⁻¹}(mk[c₁..c₅])` — the latter is generically nonzero per cycle 358's `_inv_mk`. So Phase β.2 currently holds only for k≤3 trees; for k=4 it requires `inversePolyTree` extended (which is exactly what Phase α'.5.2 has been doing).

**Now that Phase α'.5.2 has 5 calibration witnesses (cycles 499/501/502/503/504) covering all symmetric vertex/cherry k=4 quadruples**, the situation is:

* `inversePolyTree` is point-wise correct on every tree in the calibration ladder. Phase γ extends agreement at children to agreement at the parent (cycle 497).
* For trees in the ladder, Phase β.2 closes (by combining Phase β.1's per-tree witness + structural induction's child recursion + Phase γ).
* For trees OUTSIDE the ladder — including `mk [v, v, v, mk[c]]`, `mk [c, c, c, mk[c]]`, etc., and any tree with k≥5 children — Phase β.2 is still false.

So **Phase β.2 cannot close at full generality without either**:
* Extending the calibration ladder to cover every k≥4 tree (impossible — there are infinitely many), OR
* A parametric `nchildPolynomial` recursion that handles arbitrary children-list-shape uniformly (Phase α'.7+ infrastructure, multi-cycle).

The cycle 504 fixed-set ladder (5 symmetric witnesses + 0 mixed-child witnesses for k=4) does NOT eliminate Phase β.2's gap; it merely demonstrates that **the empirical surface for the parametric recursion is consolidating**. The eventual cycle 365 closure path is Phase α'.7+ via `nchildPolynomial`, not Phase β.2 alone.

---

## §D. Cycle 505+ strategic options

Three credible directions, in increasing scope:

### Option 1 (LOW risk, single-cycle): one more α'.5.2.k mixed-child witness

Candidates from the Phase α'.5.2 scoping doc §17.6:
* `(v, v, v, mk[c])` — order 7, single non-leaf-final-position. **First mixed-child k=4 witness with a depth-2 ladder tail.**
* `(v, v, c, mk[c])` — order 8, cherry + `mk[c]` blend.
* `(v, mk[c], c, c)` — order 8, mid-position non-leaf.

**Recommendation: `(v, v, v, mk[c])`.** Mechanical extension of cycle 501's (v,v,v,c) recipe with one new `dws_mk[c]` factor per row. Estimated ~250–350 LOC. Aristotle suitability: medium.

**Faithfulness check**: the cycle 504 sympy lesson applies — paper-derive expected cancellations and verify symbolically BEFORE committing to a Lean proof. The cycle 503 (v,c,c,c) "v + m + vccc cancel" pattern does NOT generalize naively to (v,v,v,mk[c]); the `mk[c]` factor has a different inverse-row structure than `cherry` does.

### Option 2 (MEDIUM-HIGH risk, multi-cycle): Phase β/γ k=4-extension scoping doc

Following cycle 495's precedent, write a markdown-only scoping doc for the Phase β.2 k=4 extension. The cycle 495 doc was the model for cycle 504's `def_422B_phase_alpha_prime_5_2_scoping.md`; this would be its k=4 successor.

**Concrete deliverables**:
1. Catalog the 5 closed Phase α'.5.2 calibration witnesses (cycles 499/501/502/503/504).
2. Identify the missing infrastructure for k≥5 (the natural Phase α'.5.3+).
3. Phase-decompose into 4–6 single-cycle deliverables toward eventual cycle 365 closure.
4. Define the cross-over point between Phase α'.5 ladder accumulation and Phase α'.7 parametric `nchildPolynomial`.

**Estimated LOC**: 400–700 markdown only. No Lean changes. This is cycle 505's clean fresh-entity-flavored deliverable while staying on the §422 track.

### Option 3 (LOW–MEDIUM risk, single-cycle): pivot to fresh entity

Per `cycle_336_pivot_options.md`, viable candidates:
* `def:451A` (G-stability) — definition only; ~50 LOC.
* `def:442A` (principal sheet of stability function) — small §442 entry.
* `thm:535A` (GLM analog of `def:422B`) — would consume §382/§383 group structure.
* `thm:541A` (DIMSIM types).

A pivot now breaks the §422 streak (78 substantive cycles post-cycle-504), but the symmetric quadruple ladder being complete provides a natural pause point. Future cycles can return to §422 with fresh perspective.

### Recommendation

**Option 2** (Phase β/γ k=4-extension scoping doc) is the highest-value pivot. It:
* Captures the cycle 504 5-witness empirical surface in a planning document while it's fresh.
* Frees cycle 505's worker from mechanically extending the ladder (Option 1) without strategic justification — the cycle 504 lesson is that each new tree adds ~250–350 LOC and ~12-kernel surface, and the marginal information is dropping.
* Doesn't risk the §422 streak (still markdown-only ship, axiom-clean baseline).

If cycle 505's planner judges Option 2 premature, fall back to Option 1 with `(v, v, v, mk[c])` as the safest target (least new kernel surface).

---

## §E. Mathematical observation: the heterogeneous obstacle has a quotient-theoretic resolution

This is offered as long-term scoping insight, not cycle 505 work.

The fundamental tension is that `derivativeWeightWithSrc M₂ M₁ i t : ℝ` indexes `i : Fin (M₂.1)` over the stage count of the INNER tableau M₂, but the quotient `PhiEquivalent` collapses M₂ and M₂' that may have different stage counts. When we ask "is `Φ_{η⁻¹}(t)` equal for two η, η' that agree on subtrees", we're really asking whether the rational/polynomial expression for `Φ_{η⁻¹}` factors through `Φ_η`-evaluation at subtrees only.

The cycle 358 `_inv_mk` and cycle 362 strict-subtree-agreement results almost suffice — they tell us that `derivativeWeightWithSrc M.inverse i (mk children) = Πℓ (M.inverse.eW cℓ + Σⱼ M.A i j · M.inverse.dW j cℓ)`. The first factor `M.inverse.eW cℓ` is a function of `Φ_η` at children only (by recursion + quotient invariance). The problematic part is `Σⱼ M.A i j · M.inverse.dW j cℓ` — this is M₂-stage-count-indexed and does NOT obviously factor through `Φ_η`.

**The `inversePolyTree` recursion (cycles 387–504) IS the resolution at the polynomial level.** It encodes the per-tree polynomial in `Φ_η`-values that `Φ_{η⁻¹}` must equal, sidestepping the stage-count indexing entirely. The Phase β.2 lift = "this polynomial encoding is correct on every tree". The Phase α'.5 work = "extending the polynomial encoding's correctness to k=4 trees". The eventual Phase α'.7 work = "the polynomial encoding is uniform in k via a parametric `nchildPolynomial`".

**Once Phase β.2 closes at full generality** (Phase α'.7 + extended Phase β.2), the cycle 365 sorry closes in ~5 lines:
1. Quotient.inductionOn₂ η_q η_q'.
2. Phase β.2 (general) rewrites both sides to `inversePolyTree t (Φ_η ·)` evaluated at η_q and η_q' respectively.
3. Phase γ (cycle 497) gives `inversePolyTree t (Φ_η η_q) = inversePolyTree t (Φ_η η_q')` from the closed-subtree agreement hypothesis.
4. The `(m+1)` power lift uses cycle 359's `powRep_quotient_eq` + cycle 358's `_phi_mul_mk` to peel the m factor off; the inner `Φ_{η⁻¹}` instance is then a special case.

The infrastructure for steps 3 and 4 exists. Step 2 is the bottleneck: it requires Phase α'.7 (parametric `nchildPolynomial`).

---

## §F. Mathlib hooks for future Phase α'.7 work (no immediate cycle 505 use)

If/when cycle 506+ attempts a parametric `nchildPolynomial`:

* `Finset.powerset` (already used in `Section383.lean`) — for the `2^k`-block decomposition of `_inv_mk`.
* `Finset.sum_powerset_insert` — for the inductive step on the children list.
* `Multiset.sum_map_mul_left` (used cycle 078) — for the algebraic manipulation of per-block contributions.
* `WellFoundedRelation.onFun` (cycle 343, used) — for `nchildPolynomial`'s termination on `t.order`.

The cycle 402 scoping doc §2.3 already sketched the `nchildPolynomial` shape. Reviewing that section before any cycle 506+ attempt is recommended.

---

## §G. What NOT to do this cycle

* Do **NOT** attempt to close the cycle 365 sorry. Multi-cycle Phase α'.7 / β.2-extension work; not single-cycle.
* Do **NOT** restate the "(c,c,c,c) pending Phase α'.5.2.5" framing. It is verifiably stale per §A.
* Do **NOT** edit `scripts/autonomous_loop.py` to "fix" the stale-prompt issue. Loop-maintainer territory per the standing tautology-scanner / phantom-verdict precedent.
* Do **NOT** ignore the cycle 504 sympy lesson. Future α'.5.2.k extensions MUST sympy-verify cancellations before Lean.
* Do **NOT** raise `maxHeartbeats` above 200000.
* Do **NOT** introduce `axiom`/`constant` declarations.
* Do **NOT** introduce new sorries beyond the grandfathered cycle 365 one.

---

## §H. Cross-references

* `.prover-state/issues/def_422B_phase_alpha_prime_5_2_scoping.md` §18 — cycle 504 worker's own update documenting Phase α'.5.2.5 closure with sympy-corrected cancellation count (3 not 4).
* `.prover-state/issues/def_422B_phase_beta_gamma_scoping.md` (cycle 495) — sibling scoping doc, identifies Phase β.2 R6 falsity and the eventual cycle 365 closure recipe.
* `.prover-state/issues/cycle_336_pivot_options.md` — fresh-entity menu for Option 3.
* `.prover-state/issues/def_422B_phase_alpha_prime_5_scoping.md` (cycle 402) — model for the recommended Option 2 scoping doc.
* Memory `feedback_cherry_child_cancellation.md` — cycle 504's sympy-correction lesson (current).
* Memory `feedback_dws_cherry_factor_includes_v_aᵢ.md` — the structural reason behind cherry-child kernel arithmetic.
* `OpenMath/Chapter4/Section422.lean:2279` — the cycle 365 grandfathered sorry, untouched since cycle 365.
* `OpenMath/Chapter4/Section422.lean:12626` — cycle 504's `elementaryWeightQ_phi_inv_mkCherryCherryCherryCherry`.
* `OpenMath/Chapter4/Section422.lean:13882` — cycle 504's m=0 corollary.

---

## §I. Bottom-line directive for cycle 505

**The cycle 504 ship is real and substantial.** The (c,c,c,c) tree is closed; the symmetric quadruple ladder is complete. The remaining "blocker" (heterogeneous Sub-lemma A obstacle) is correctly grandfathered and will not close without multi-cycle Phase α'.7 infrastructure.

Cycle 505's planner should choose between Option 1 (one more mixed-child α'.5.2.k witness, ~250–350 LOC), Option 2 (Phase β/γ k=4-extension scoping doc, markdown-only, ~500 LOC), or Option 3 (pivot to fresh entity, ~50–100 LOC).

**Strongly recommend Option 2.** The five-witness empirical surface is at the right inflection point for a planning doc; further ladder extension without strategic justification risks the cycle 504 mechanical-routine pattern that the cycle 504 task results' "Suggested next approach" was right to flag as diminishing returns.

If Option 2 is rejected, fall back to Option 1 with `(v, v, v, mk[c])` as the lowest-risk target. Sympy-verify cancellations before Lean per the cycle 504 lesson.

The §422 streak (78 substantive + 6 doc cycles, sorry count 5) is preserved under any of the three options. Cycle 504 is a clean ship.
