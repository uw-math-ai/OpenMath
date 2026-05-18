# Cycle 366 Strategy — §422 Phase D.3.b Step 2 closure (Sub-lemma A body)

## §A. One-sentence goal

Discharge the body of `powRep_sum_eq_of_strict_subtree_agreement`
(Sub-lemma A) in `OpenMath/Chapter4/Section422.lean` so that the
cycle 365 Phase D.3.b Step 2 headline
`linearResidualAt_depends_only_on_strict_subtrees` becomes
unconditionally axiom-clean.

Closing A drives the code-level sorry count from 1 → 0 in §422 and
automatically upgrades the headline's `#print axioms` from
`[propext, sorryAx, Classical.choice, Quot.sound]` to
`[propext, Classical.choice, Quot.sound]` without any headline
restatement (the headline is **locked**; do not touch it).

## §B. Context (do not skip — informs the recipe)

Sub-lemma A signature (`OpenMath/Chapter4/Section422.lean:2266`):

```lean
theorem powRep_sum_eq_of_strict_subtree_agreement
    (m : ℕ) (t : RT)
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_closed : ∀ s : RT, s.order ≤ t.order →
        elementaryWeightQ_phi η_q s = elementaryWeightQ_phi η_q' s) :
    elementaryWeightQ_phi (η_q ^ (-(((m + 1) : ℕ) : ℤ))) t
      = elementaryWeightQ_phi (η_q' ^ (-(((m + 1) : ℕ) : ℤ))) t := by
  sorry
```

Key prior results to consume (verified at HEAD `ec50e8d`):

* **Cycle 358** (`OpenMath/Chapter3/Section381.lean`):
  `elementaryWeightQ_phi_inv_mk` — `Φ_{⟦M⟧⁻¹}(t) = -Σⱼ M.b j ·
  M.derivativeWeightWithSrc M.inverse j t`.
* **Cycle 359** (`OpenMath/Chapter3/Section381.lean`):
  `RKTableau.powRep`, `powRep_quotient_eq` — `⟦M.powRep m⟧ = ⟦M⟧^m`.
* **Cycle 361** (`OpenMath/Chapter4/Section422.lean`):
  `elementaryWeightQ_phi_zpow_negSucc_mk` — closed form for
  `Φ_{⟦M⟧^(Int.negSucc m)}(t)`. Crucially,
  `-(((m+1):ℕ):ℤ) = Int.negSucc m` is **definitional rfl**.
* **Cycle 362** (`OpenMath/Chapter3/Section381.lean`):
  `derivativeWeightWithSrc_eq_of_strict_subtree_agreement` —
  substitution lemma: if `M₁, M₁'` agree on `elementaryWeight` at
  trees of order **strictly less than** `t.order`, then
  `M₂.derivativeWeightWithSrc M₁ i t =
   M₂.derivativeWeightWithSrc M₁' i t` for every inner tableau `M₂`
  and stage `i`.
* **Cycle 343** (`OpenMath/Chapter3/Section301.lean`):
  `instance : WellFoundedRelation RootedTree := measure
  RootedTree.order` — well-founded recursion on `t.order`.
* **Cycle 226** (`OpenMath/Chapter3/Section381.lean`):
  `elementaryWeightQ_phi_mk` — `Φ_{⟦M⟧}(t) = M.elementaryWeight t`
  at representatives (the bridge that lets `h_closed` be used at
  the representative level via `simpa`).

## §C. Priority 1 — manual closure via the cycle-365 task results recipe

**Time-box: 90 minutes of focused work.** If no convergence
(lake build not exit 0 OR proof structure clearly stuck) after
90 min, abort to Priority 2.

### §C.1 Pre-flight reconnaissance (10–15 min, use `lean_multi_attempt`)

Before any file edit, validate the building blocks one at a time at
the sorry-bearing position (line 2266 of `Section422.lean`):

1. **Expansion check** — `Quotient.inductionOn₂` + cycle 361 rewrite.
   Try as a single `lean_multi_attempt` step:
   ```lean
   intro h_closed
   induction η_q, η_q' using Quotient.inductionOn₂
   case _ M M' =>
     rw [show (-(((m + 1) : ℕ) : ℤ)) = Int.negSucc m from rfl]
     rw [elementaryWeightQ_phi_zpow_negSucc_mk M.2 t,
         elementaryWeightQ_phi_zpow_negSucc_mk M'.2 t]
     sorry
   ```
   Confirm: the resulting goal has the heterogeneous powRep-sum form
   `-Σⱼ (M.powRep (m+1)).2.b j · ... = -Σⱼ (M'.powRep (m+1)).2.b j · ...`.
   If the rewrite fails to fire (e.g. due to `Quotient.mk` vs
   `Quotient.mk'` namespace drift), STOP and report — that is a
   prerequisite failure that has to be fixed before any further work.

2. **h_closed → representative bridge**. Confirm:
   ```lean
   have h_rep : ∀ s, s.order ≤ t.order →
       M.2.elementaryWeight s = M'.2.elementaryWeight s := by
     intro s hs; simpa using h_closed s hs
   ```
   succeeds. (Cycle 226's `elementaryWeightQ_phi_mk` is a `@[simp]`
   lemma, so `simpa` should fire automatically. If it doesn't, fall
   back to an explicit `rw [elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk]`.)

3. **Cycle 362 signature check**. Run `lean_local_search` on
   "derivativeWeightWithSrc_eq_of_strict_subtree_agreement" to confirm
   the name and grab the explicit signature. If the name has drifted,
   adjust references throughout the proof.

### §C.2 Recommended proof structure (60 min)

The cycle 365 task results §"Suggested next approach" + cycle 365
strategy §"Cycle 366 entry-point recommendation" both point to the
same decomposition. Implement it as a strong induction on `t.order`
internal to the proof body, where each level of the induction
handles one `Φ_{η^(-(m+1))}(t)` value:

```lean
theorem powRep_sum_eq_of_strict_subtree_agreement
    (m : ℕ) (t : RT)
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_closed : ∀ s : RT, s.order ≤ t.order →
        elementaryWeightQ_phi η_q s = elementaryWeightQ_phi η_q' s) :
    elementaryWeightQ_phi (η_q ^ (-(((m + 1) : ℕ) : ℤ))) t
      = elementaryWeightQ_phi (η_q' ^ (-(((m + 1) : ℕ) : ℤ))) t := by
  -- Quotient.inductionOn₂ on (η_q, η_q'). Now M, M' : Σ s, RKTableau s.
  induction η_q, η_q' using Quotient.inductionOn₂
  case _ M M' =>
    have h_rep : ∀ s, s.order ≤ t.order →
        M.2.elementaryWeight s = M'.2.elementaryWeight s := by
      intro s hs; simpa using h_closed s hs
    rw [show (-(((m + 1) : ℕ) : ℤ)) = Int.negSucc m from rfl]
    rw [elementaryWeightQ_phi_zpow_negSucc_mk M.2 t,
        elementaryWeightQ_phi_zpow_negSucc_mk M'.2 t]
    -- Step 4 (substantive): show the two powRep-sums agree.
    -- The b-coefficients of (M.powRep (m+1)).2 vs (M'.powRep (m+1)).2
    -- depend on M / M' respectively (different Σ-typed bodies). We
    -- can't go elementwise on the sums; the comparison must happen
    -- at the unfolded `Σ-typed Φ_{⟦M⟧^(-(m+1))}` level via a
    -- recursive argument on (m, t).
    sorry
```

**Step 4 — the substantive content.** Two viable sub-approaches:

**Sub-approach 4.a — strong induction on `t.order` with auxiliary
inverse-agreement lemma**:

The natural strategy. Prove an auxiliary private lemma (likely as
the cycle 366 deliverable, alongside Sub-lemma A's body):

```lean
private theorem powRep_inverse_elementaryWeight_eq_of_strict_subtree_agreement
    {sM sM' : ℕ} (M : RKTableau sM) (M' : RKTableau sM') (m : ℕ)
    (t : RT)
    (h_rep : ∀ s, s.order ≤ t.order →
       M.elementaryWeight s = M'.elementaryWeight s) :
    ∀ s, s.order ≤ t.order →
      (M.powRep (m+1)).2.inverse.elementaryWeight s
        = (M'.powRep (m+1)).2.inverse.elementaryWeight s
```

If this lands, cycle 362's
`derivativeWeightWithSrc_eq_of_strict_subtree_agreement` applied to
the inner tableau `(M.powRep (m+1)).2` with source agreement on
`(M.powRep (m+1)).2.inverse` vs `(M'.powRep (m+1)).2.inverse` at
STRICT subtrees of `t` (extract from the closed-subtree witness via
`fun s hs_strict => h_inv s (le_of_lt hs_strict)`) gives the
per-summand equality.

**But this alone doesn't close the sum equality** — the two sums
range over DIFFERENT Fin types when `M.1 ≠ M'.1`. The closure
mechanism must be:

(i) The cycle-358 identity `Φ_{⟦N⟧⁻¹}(t) = -Σⱼ N.b j ·
N.derivativeWeightWithSrc N.inverse j t` (representative-level).

(ii) Apply (i) with `N := (M.powRep (m+1)).2` and `(M'.powRep (m+1)).2`
respectively to fold each side back to a quotient-level expression.

(iii) The resulting quotient-level expression depends only on `⟦M⟧`
(resp. `⟦M'⟧`) and m, not on the specific representative. Use
`powRep_quotient_eq` (cycle 359) to identify
`⟦(M.powRep (m+1)).2⟧⁻¹ = ⟦M⟧^(-(m+1))` (definitionally? or via
`Quotient.sound`?). Then both sides equal `Φ_{⟦M⟧^(-(m+1))}(t)` and
`Φ_{⟦M'⟧^(-(m+1))}(t)` respectively, which is exactly the goal
after `rw` UNDID our `rw` in Step 3.

**Observation: the cycle 365 task results' Step 3 `rw` is reversible.**
The Step 4 closure works by NOT actually opening the `rw` —
applying it forward and then immediately reversing it via the cycle
358 `_inv_mk` identity restated at the powRep level. The substantive
content is in `h_inv` (the auxiliary inverse-agreement lemma) plus
cycle 362's substitution, which together prove that for any
representative-level equality
`Φ_{⟦N⟧⁻¹}(t) = Φ_{⟦N'⟧⁻¹}(t)` provided `N, N'` agree on
`elementaryWeight` at `t` and at strict subtrees of `t`.

**Sub-approach 4.b — direct quotient-level recursion**:

The alternative (cleaner if it works): bypass the representative-level
expansion entirely. The Quotient.lift definition of `^` and the
recursive structure of `powRep_quotient_eq` give:

`⟦M⟧^(-(m+1)) = (⟦M⟧⁻¹)^(m+1)`

So `Φ_{⟦M⟧^(-(m+1))}(t)` is a polynomial expression in
`Φ_{⟦M⟧⁻¹}(t')` for `t'` various. If we can prove the parametricity
of `Φ_{η⁻¹}` (a single lemma:
`Φ_{η^(-1)}_eq_of_closed_subtree_agreement`), then iterating gives
the full claim by induction on `m`.

This requires showing:
* **Base case (induction on m)**: at `m = 0`,
  `Φ_{η_q^(-1)}(t) = Φ_{η_q'^(-1)}(t)` under h_closed.
* **Inductive step**: `Φ_{η_q^(-(m+1))}(t) = Φ_{η_q'^(-(m+1))}(t)`
  given the IH at `m`. Likely via `⟦M⟧^(-(m+2)) = ⟦M⟧^(-1) *
  ⟦M⟧^(-(m+1))` and cycle 226's `compose_elementaryWeight_decomp`
  applied to the quotient-level multiplication.

The base case at `m = 0` reduces to: under h_closed at `t.order ≤ t.order`
(closed-subtree at t itself), is `Φ_{η^(-1)}(t) = Φ_{η'^(-1)}(t)`?

By cycle 358 (representative-level):
* `Φ_{⟦M⟧⁻¹}(t) = -Σⱼ M.b j · M.derivativeWeightWithSrc M.inverse j t`
* `Φ_{⟦M'⟧⁻¹}(t) = -Σⱼ M'.b j · M'.derivativeWeightWithSrc M'.inverse j t`

To prove these are equal under h_closed, we need:
1. `M.inverse` and `M'.inverse` agree on `elementaryWeight` at strict
   subtrees of `t` (consequence of h_closed at strict subtrees + the
   relation `M.inverse.elementaryWeight = -M.elementaryWeight` …
   wait that's only at vertex; for higher trees `M.inverse` is more
   complex per cycle 235's `inverse_phiEquivalent_inverse` working
   recursion).
2. Hence cycle 362 gives per-summand equality of
   `M.derivativeWeightWithSrc M.inverse j t` against
   `M'.derivativeWeightWithSrc M'.inverse j t`.
3. The b-coefficients side: `Σⱼ M.b j · (...)` vs `Σⱼ M'.b j · (...)`
   — different Fin types again.

The b-coefficient side is the recurring obstacle. Cycle 235 may have
infrastructure for this — its mutual block
`inverseDerivativeWeight_eq_derivativeWeightWithSrc_inverse` /
`inverseDerivativeWeightWithSrc_M_eq_derivativeWeight` worked
representative-level for proving `⟦M⟧⁻¹` IS the group inverse on
`Quotient PhiEquivalent.setoidSigma`. Worth a quick scan to see if
that infrastructure has the right shape.

### §C.3 Decomposition if 4.a/4.b stall (15 min)

If neither sub-approach closes within the 60-min Step 4 budget, ship
the auxiliary inverse-agreement lemma alone (~30–50 LOC) and leave
Sub-lemma A's body still `sorry`'d. The inverse-agreement lemma is a
genuine infrastructure deliverable that will be consumed in cycle 367
when Sub-lemma A is re-attempted. Document the partial progress in
`def_422B_phase_D_3_scoping.md` §"Cycle 366" subsection.

In this scenario the §422 streak is preserved (the new auxiliary
lemma is axiom-clean), but the sorry count is unchanged (1 → 1).

## §D. Priority 2 — specialised small-tree witnesses (90-min fallback)

If Priority 1 stalls after 90 minutes, ship per cycle 365 strategy
Option 3A (graceful degradation):

1. **`powRep_sum_eq_of_agreement_at_vertex`** (~30 LOC):
   ```lean
   theorem powRep_sum_eq_of_agreement_at_vertex
       (m : ℕ) (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
       (h : elementaryWeightQ_phi η_q RootedTree.vertex
            = elementaryWeightQ_phi η_q' RootedTree.vertex) :
       elementaryWeightQ_phi (η_q ^ (-(((m + 1) : ℕ) : ℤ))) RootedTree.vertex
         = elementaryWeightQ_phi (η_q' ^ (-(((m + 1) : ℕ) : ℤ))) RootedTree.vertex
   ```
   Proof: apply cycle 341's `elementaryWeightQ_phi_zpow_vertex`
   (`Φ_{η^n}(τ) = (n:ℝ) · Φ_η(τ)`) on both sides. Both reduce to
   `-(m+1:ℝ) · Φ_η(τ)` and `-(m+1:ℝ) · Φ_η'(τ)`, then `h` forces them
   equal via `congr 1`. ~15–25 LOC.

2. **`powRep_sum_eq_of_agreement_at_cherry`** (~50 LOC):
   Use cycle 358's `elementaryWeightQ_phi_inv_mk` to compute
   `Φ_{η^(-1)}(cherry)` explicitly. The cycle 360
   `linearResidualAt_one_mk_eq` proof at `t = cherry` is a near-template.
   Then handle the `m+1` iteration manually for the cherry case.

3. **Update `def_422B_phase_D_3_scoping.md`** with a "Cycle 366
   graceful degradation" subsection documenting the specialised ship
   and deferring general body closure to cycle 367+.

In fallback scenario:
* Code-level sorry count: 1 (unchanged; Sub-lemma A general body
  still deferred).
* New specialised theorems ship axiom-clean.
* §422 streak preserved (axiom-clean infrastructure additions never
  break the streak; the existing single sorry is grandfathered from
  cycle 365 and acknowledged).
* **Do NOT delete or modify Sub-lemma A's signature or the headline.**
  Add specialised witnesses *alongside* (after) Sub-lemma A in the file.

## §E. NOT in scope for cycle 366

* **DO NOT attempt Phase D.3.d (`underlyingOneStepMethod_aux`).**
  Requires Sub-lemma A's body as prerequisite; attempting both in one
  cycle risks both halves rolling back (cycle 200/201 thm:381H
  precedent). Phase D.3.d's recursion + spec lemma is itself a
  ~1-cycle deliverable.

* **DO NOT redefine `linearResidualAt`.** Cycle 364 shipped the
  audit-correct form per the cycle 363 P2 audit; the definition is
  final and downstream consumers (`_vertex_eq_zero`, `_one_mk_eq`,
  `_succ_mk_eq`, the Step 2 headline) all depend on it. Touching
  would cascade.

* **DO NOT change the closed-subtree hypothesis to strict-subtree.**
  The closed-subtree form (`s.order ≤ t.order`, including `t` itself)
  is strictly weaker / more permissive than strict-subtree
  (`s.order < t.order`), matches Phase D.3.d's recursion shape
  exactly, and was the deliberate weakening chosen by cycle 365 to
  give the headline a clean 2-line body. Maintain consumer API
  stability.

* **DO NOT submit to Aristotle.** §422 work has been entirely manual
  since cycle 336 (30 consecutive cycles). Sub-lemma A is
  well-scoped: representative-level expansion (cycle 361),
  source-substitution (cycle 362), closure via induction on either
  `t.order` (4.a) or `m` (4.b). The cycle 232 trailing-factor
  Aristotle precedent doesn't apply — that was for forest
  convolutions over `List RootedTree`; A operates on
  `Σ s, RKTableau s` with iterated composition.

* **DO NOT introduce `axiom`/`constant` declarations.**

* **DO NOT add NEW sorries.** Per CLAUDE.md "absolute rule"
  sorry-first. The sorry on Sub-lemma A's body is grandfathered from
  cycle 365; new sorries are forbidden.

## §F. Approaches explicitly ruled out (from prior attempts)

* **`induction t with | mk children ih =>`** on `RootedTree` —
  fails per `feedback_rootedtree_nested_induction.md` (nested-inductive
  motive failure). Use `WellFoundedRelation` (cycle 343) or
  `Nat.strong_induction_on` applied to `t.order` instead. Preferred
  pattern (per cycle 343 precedent):
  ```lean
  induction t using WellFoundedRelation.fix?
  -- or:
  refine WellFounded.induction (measure_wf RootedTree.order) t ?_
  intro t ih
  ```

* **Per-summand reasoning on the heterogeneous powRep-sums** when
  `M.1 ≠ M'.1` — won't close because the sums have different index
  sets (`Fin (M.1·(m+1))` vs `Fin (M'.1·(m+1))`). The comparison
  must happen at the quotient level (where the sums fold into a
  single scalar via cycle 358's `_inv_mk` + cycle 359's
  `powRep_quotient_eq`), not summand-by-summand.

* **`linear_combination` on the powRep-sum equality** — won't fire
  for the same reason; the sums have different shapes.

* **`Nat.cast_one + zpow_neg_one` bridge** at the general `i = m+1`
  case — only works for the `i = 1` special case (cycle 360
  `_one_mk_eq`). Cycle 361's `_succ_mk_eq` is the right general form
  and is what this cycle should consume.

## §G. Required verification before commit

1. **No new sorries**:
   ```bash
   grep -c sorry OpenMath/Chapter4/Section422.lean
   ```
   * Best case (Priority 1 closes): result is 0 (success — Sub-lemma
     A's body lands).
   * Fallback (Priority 2): result is 1 (unchanged — Sub-lemma A's
     body still sorry'd, but new specialised witnesses are
     axiom-clean).
   * Value MUST NOT exceed 1. Any value > 1 is a hard fail.

2. **Axiom check on the headline** (the critical artifact for Phase
   D.3.b Step 2):
   ```bash
   echo '#print axioms
     OpenMath.Chapter4.Section422.linearResidualAt_depends_only_on_strict_subtrees' \
     | lake env lean --stdin OpenMath/Chapter4/Section422.lean
   ```
   * Best case: `[propext, Classical.choice, Quot.sound]` — the
     `sorryAx` is gone. This is the cycle 366 success criterion.
   * Fallback case: `[propext, sorryAx, Classical.choice, Quot.sound]`
     — sorry still present; specialised witnesses shipped but
     headline not yet upgraded. Documented as expected.

3. **Axiom check on Sub-lemma A** (only if Priority 1 closes):
   ```bash
   echo '#print axioms
     OpenMath.Chapter4.Section422.powRep_sum_eq_of_strict_subtree_agreement' \
     | lake env lean --stdin OpenMath/Chapter4/Section422.lean
   ```
   Expected: `[propext, Classical.choice, Quot.sound]`.

4. **Build**:
   ```bash
   lake build OpenMath.Chapter4.Section422
   ```
   Exit 0. Expect ~5-min rebuild (cycle 365's was 352s).

5. **§422 streak unbroken** — `task_results/cycle_366.md` should
   record the axiom-clean state of all new theorems and the streak
   count (336–366 = 31 cycles plus cycle 366).

## §H. Deliverable shape

**Priority 1 success (target outcome)**:
* Section422.lean: ~2306 → ~2400–2480 LOC.
* New Sub-lemma A body: ~80–150 LOC (replacing the `sorry`).
* Possibly one private auxiliary lemma (e.g.
  `powRep_inverse_elementaryWeight_eq_of_strict_subtree_agreement`
  or the cycle 4.b base case `Φ_{η^(-1)}_eq_at_closed_subtrees`),
  ~30–50 LOC each.
* Code-level sorry count: 1 → 0.
* §422 axiom-clean streak: 31 → 32 (336–366).
* `def_422B_phase_D_3_scoping.md` §"Cycle 366 closure" subsection
  appended documenting the closure path and any auxiliary lemmas.
* `lean_status.json` `def:422B` row cycle trail extended.
* `plan.md` row updated.

**Priority 2 fallback (graceful degradation)**:
* Section422.lean: ~2306 → ~2400 LOC.
* New specialised witnesses (`_at_vertex`, `_at_cherry`, optional
  `_at_broom₃`): ~80–150 LOC total.
* Code-level sorry count: 1 → 1 (unchanged; Sub-lemma A general
  body still deferred).
* §422 axiom-clean streak: 31 → 32 (specialised witnesses are
  axiom-clean; existing sorry grandfathered).
* `def_422B_phase_D_3_scoping.md` §"Cycle 366 graceful degradation"
  subsection appended.
* `lean_status.json` cycle trail extended noting partial closure.

## §I. Cycle 367 outlook (post-366 planning hint, not for execution)

If cycle 366 closes Sub-lemma A (Priority 1 success), cycle 367 ships
Phase D.3.c (`sum_i_alpha_ne_zero_of_stable`) — the non-vanishing
fact `Σᵢ i·αᵢ ≠ 0` for stable LMMs. Per the cycle 362 worker's
analysis, this is now a ~10 LOC corollary of cycle 176's
`ρPoly_deriv_eval_one_ne_zero_of_stable_preconsistent` + cycle 344's
`coef_α_pos_of_stable_preconsistent`. Near-free.

If cycle 366 falls back to specialised witnesses (Priority 2), cycle
367 re-attempts Sub-lemma A general body using cycle 366's
specialised evidence as a guide (and any auxiliary lemma cycle 366
salvaged per §C.3).

After Phase D.3.c lands, Phase D.3.d (`underlyingOneStepMethod_aux` +
spec lemma) is the cycle 368 deliverable, then Phase E sealing of
`def:422B` itself ships in cycle 369.
