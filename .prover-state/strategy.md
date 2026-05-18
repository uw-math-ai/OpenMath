# Cycle 367 Strategy — Ship cherry closed form (Phase D.3.b Step 2 cherry specialisation)

## TL;DR

Ship **`elementaryWeightQ_phi_inv_cherry`** (quotient-level closed
form for `Φ_{η⁻¹}(cherry)`) plus the corollary
**`powRep_sum_eq_of_agreement_at_cherry_zero`** (cherry-case
specialisation of Sub-lemma A at `m = 0`). This is the cycle 366
task results' explicitly-recommended Priority 1 deliverable (~50
LOC core, ~1 cycle, axiom-clean target). It extends cycle 366's
vertex witness (`powRep_sum_eq_of_agreement_at_vertex`) one tree
higher and provides a second non-vacuity witness for the Sub-lemma A
infrastructure introduced cycle 365.

**Do NOT attempt Sub-lemma A's general body** — cycle 366
conclusively established that the heterogeneous-inner-tableau
obstacle blocks both Sub-approaches 4.a (strong induction + cycle
362 substitution) and 4.b (induction on `m` at quotient level).
General body needs new infrastructure (cycle 368+ work) — see §G.

## §A. Aristotle results

**None pending.** No Aristotle submissions active from prior cycles
worth integrating. Cycle 367 is fully manual.

## §B. Primary target — `elementaryWeightQ_phi_inv_cherry`

### B.1 Signature

```lean
/-- Quotient-level closed form for `Φ_{η⁻¹}(cherry)`:
    `Φ_{η⁻¹}(cherry) = (Φ_η(vertex))² − Φ_η(cherry)`.

    Companion to cycle 341's `elementaryWeightQ_phi_zpow_vertex`
    (vertex closed form); this is the cherry analog. Both are
    quotient-level identities — `Φ_{η⁻¹}(cherry)` admits a closed
    expression in `Φ_η` at the subtrees of cherry (= {vertex,
    cherry}), where the inverse-of-cherry coefficient is `−1`
    (matching cycle 364's `linearResidualAt` coefficient) and the
    inverse-of-vertex quadratic coefficient is `+1` (a non-trivial
    structural fact). -/
theorem elementaryWeightQ_phi_inv_cherry
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi (η_q⁻¹) RootedTree.cherry
      = (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
        - elementaryWeightQ_phi η_q RootedTree.cherry
```

### B.2 Proof recipe (per cycle 366 task results §Discovery #2)

```lean
theorem elementaryWeightQ_phi_inv_cherry η_q := by
  induction η_q using Quotient.inductionOn with
  | h p =>
    obtain ⟨s, M⟩ := p
    -- Step 1: LHS expansion via cycle 358's _inv_mk
    --   (Quotient.mk _ ⟨s, M⟩)⁻¹ = Quotient.mk _ ⟨s, M.inverse⟩
    --   reduces by `rfl` through cycle 236's inverseQ_phi_mk simp lemma
    rw [show (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩)⁻¹
          = Quotient.mk PhiEquivalent.setoidSigma ⟨s, M.inverse⟩ from rfl]
    rw [elementaryWeightQ_phi_inv_mk M RootedTree.cherry,
        elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk]
    -- Now goal:
    --   -(Σⱼ M.b j · M.derivativeWeightWithSrc M.inverse j cherry)
    --     = (M.elementaryWeight vertex)² - M.elementaryWeight cherry
    -- Step 2: Expand derivativeWeightWithSrc at cherry = mk [vertex]
    -- Per cycle 358's _inv_mk and the recursive def of
    -- derivativeWeightWithSrcProd (Section381.lean:~2680-2700):
    --   M.derivativeWeightWithSrc M.inverse j cherry
    --     = M.derivativeWeightWithSrcProd M.inverse j [vertex]
    --     = (M.inverse.elementaryWeight vertex
    --        + Σ k, M.A j k · M.derivativeWeightWithSrc M.inverse k vertex)
    --       * M.derivativeWeightWithSrcProd M.inverse j []
    --   M.derivativeWeightWithSrcProd M.inverse j [] = 1   (empty-list base case)
    --   M.derivativeWeightWithSrc M.inverse k vertex = 1   (cycle 341's _vertex)
    --   M.inverse.elementaryWeight vertex
    --     = -M.elementaryWeight vertex  (cycle 358 _inv_mk at vertex,
    --                                    or directly from M.inverse.b = -M.b)
    -- So inner factor at index j = -M.elementaryWeight vertex + (Σₖ M.A j k)
    -- Step 3: Apply sumB_eq_elementaryWeight_vertex (§B.3 helper):
    --   M.elementaryWeight vertex = Σⱼ M.b j
    -- And recall the structural identity:
    --   M.elementaryWeight cherry = Σⱼ M.b j · (Σₖ M.A j k)
    -- (Derive inline from elementaryWeight_eq + derivativeWeight_mk at
    --  cherry = mk [vertex] + derivativeWeight_vertex = 1.)
    -- Step 4: Final algebra
    -- LHS = -Σⱼ M.b j · (-M.elementaryWeight vertex + row-sum at j)
    --     = M.elementaryWeight vertex · (Σⱼ M.b j)
    --       - Σⱼ M.b j · (row-sum at j)
    --     = M.elementaryWeight vertex · M.elementaryWeight vertex
    --       - M.elementaryWeight cherry
    --     = (M.elementaryWeight vertex)² - M.elementaryWeight cherry  ✓
    sorry  -- worker: ~20-30 LOC arithmetic via
           -- Finset.sum_mul, sum_neg_distrib, derivativeWeightWithSrcProd unfold
```

### B.3 Key sub-step: `sumB_eq_elementaryWeight_vertex`

Ship this as a private helper *before* §B.2:

```lean
private lemma sumB_eq_elementaryWeight_vertex {s : ℕ} (M : RKTableau s) :
    (∑ j : Fin s, M.b j) = M.elementaryWeight RootedTree.vertex := by
  rw [elementaryWeight_eq]
  -- now: Σ i, M.b i = Σ i, M.b i · M.derivativeWeight i vertex
  simp [derivativeWeight_vertex]
```

If `derivativeWeight_vertex` is in cycle 187 (it is), this is a
2-line proof. Alternative: just inline this where needed in §B.2's
proof body via `simp [elementaryWeight_eq, derivativeWeight_vertex]`.

### B.4 Non-vacuity example

Add one example on `explicitEuler`. Numeric values:
- `Φ_{explicitEuler}(vertex) = 1` (via cycle 337's
  `D_element_elementaryWeight_vertex` or direct: `Σⱼ M.b j = 1`).
- `Φ_{explicitEuler}(cherry) = Σⱼ M.b j · Σₖ M.A j k = 1 · 0 = 0`
  (explicit Euler has `A = 0`).
- So `Φ_{explicitEuler⁻¹}(cherry) = 1² − 0 = 1`.

```lean
example :
    elementaryWeightQ_phi
      (Quotient.mk PhiEquivalent.setoidSigma ⟨1, explicitEuler⟩)⁻¹
      RootedTree.cherry = 1 := by
  rw [elementaryWeightQ_phi_inv_cherry]
  -- compute Φ_{explicitEuler}(vertex) and Φ_{explicitEuler}(cherry)
  -- via elementaryWeightQ_phi_mk + Fin.sum_univ_one + simp on explicitEuler
  sorry  -- worker: ~5 LOC of arithmetic
```

If the explicit Euler witnesses aren't readily available (this is
Section381 / Section422 boundary territory), use the alternative
witness `D_element` from cycle 337 — that has known closed-form
elementary weights at vertex (= 1) and at higher trees (= 0).

## §C. Secondary target — `powRep_sum_eq_of_agreement_at_cherry_zero`

### C.1 Minimal corollary (Priority 1 mandatory ship)

```lean
/-- Cherry-case specialisation of Sub-lemma A
    (`powRep_sum_eq_of_strict_subtree_agreement`) at `m = 0`.

    At `t = cherry` and `n = -1` (i.e. `m = 0`), the closed-subtree
    hypothesis simplifies to two equations (at `vertex` and at
    `cherry`). Closure via cycle 367's `elementaryWeightQ_phi_inv_cherry`. -/
theorem powRep_sum_eq_of_agreement_at_cherry_zero
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_vertex : elementaryWeightQ_phi η_q RootedTree.vertex
              = elementaryWeightQ_phi η_q' RootedTree.vertex)
    (h_cherry : elementaryWeightQ_phi η_q RootedTree.cherry
              = elementaryWeightQ_phi η_q' RootedTree.cherry) :
    elementaryWeightQ_phi (η_q ^ (-(((0 + 1 : ℕ) : ℤ)))) RootedTree.cherry
      = elementaryWeightQ_phi (η_q' ^ (-(((0 + 1 : ℕ) : ℤ)))) RootedTree.cherry := by
  -- Reduce `η_q ^ (-((1 : ℕ) : ℤ))` to `η_q⁻¹` via
  -- `zpow_neg_one` + `Nat.cast_one` (cycle 360 bridge pattern).
  -- Then apply `elementaryWeightQ_phi_inv_cherry` to both sides and
  -- substitute `h_vertex`, `h_cherry`.
  sorry  -- worker: ~5-8 LOC
```

3-line proof body once §B lands. **This is the mandatory minimum
deliverable**.

### C.2 General-`m` stretch (Priority 2 optional)

Optionally also ship the general-`m` closed form
`powRep_inv_cherry_closed_form`:

```lean
/-- General closed form `Φ_{η^(-(m+1))}(cherry) = (m+1)(m+2)/2 ·
    (Φ_η(vertex))² − (m+1) · Φ_η(cherry)` (per cycle 366 task
    results §Discovery #2). -/
theorem powRep_inv_cherry_closed_form (m : ℕ)
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi (η_q ^ (-(((m + 1) : ℕ) : ℤ))) RootedTree.cherry
      = ((m + 1 : ℝ) * (m + 2) / 2)
          * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
        - (m + 1 : ℝ)
          * elementaryWeightQ_phi η_q RootedTree.cherry
```

**Risk**: the inductive step would need `Φ_{η^(-(m+1)) · η⁻¹}(cherry)`
decomposition, which requires `elementaryWeightQ_phi_mul_mk` (cycle
358) plus a closed form for `Φ_{η₁·η₂}(cherry)` at the quotient
level. Cycle 358 gave `_mul_mk` (full bottom-block sum form), but
the cherry-specific cleanup may itself blow up.

**Recommended**: **defer §C.2 to cycle 368** unless cycle 367 worker
finds the inductive step easy after §B + §C.1 land. The cherry
closed form for general `m` is genuinely useful infrastructure but
NOT cycle 367's mandatory bar.

If attempting §C.2: alternative route via cycle 359's `_pow_succ_mk`
+ cycle 361's `_zpow_negSucc_mk`. The `Φ_{η^(-(m+1))} · η = η^(-m)`
identity may give a cleaner recursion than direct `_mul_mk` use.

## §D. What NOT to attempt

### D.1 Do NOT attempt Sub-lemma A's general body

Cycle 366 pre-flight analysis (documented in cycle 366 task results
§Dead ends and §Discovery #1) conclusively established that the
existing infrastructure cannot bridge the heterogeneous-inner-tableau
gap:

1. **Sub-approach 4.a (strong induction on `t.order` + cycle 362
   substitution)**: cycle 362's lemma substitutes the *source*
   tableau (`M₁`), not the *inner* tableau (`M₂`). Sub-lemma A's
   LHS/RHS difference is precisely in the inner tableau, so cycle
   362 cannot fire across the two sides. **DO NOT retry.**

2. **Sub-approach 4.b (induction on `m` at quotient level)**: base
   case `m = 0` already hits the heterogeneous-sum issue after
   cycle 358 `_inv_mk` expansion. Same obstacle, different shape.
   **DO NOT retry.**

3. **Cross-cancellation via `η^(m+1) · η^(-(m+1)) = 1`**:
   positive-power parametricity is itself open with the same
   heterogeneity. **DO NOT retry.**

These require new infrastructure (cycle 368+ — see §G).

### D.2 Do NOT modify cycle 366's vertex witness

`powRep_sum_eq_of_agreement_at_vertex` (cycle 366, axiom-clean) is
correct and load-bearing for future planning. The cycle 367 cherry
witness is *additional* infrastructure, not a replacement.

### D.3 Do NOT touch Sub-lemma B's headline

`linearResidualAt_depends_only_on_strict_subtrees` (cycle 365) is
shipped axiom-clean modulo Sub-lemma A's body. Once Sub-lemma A
lands in some future cycle, its `#print axioms` will auto-upgrade
from `[propext, sorryAx, Classical.choice, Quot.sound]` to
`[propext, Classical.choice, Quot.sound]` *without any headline
restatement*. Do not preemptively touch the headline.

### D.4 Do NOT attempt to compile `Section441.lean`

43+ consecutive GPFS timeouts since cycle 182 per
`.prover-state/issues/cycle_182_gpfs_slowness.md`. Skip per the
standing protocol.

### D.5 Do NOT introduce sorries beyond the existing one

The existing sorry at `Section422.lean:2279` (Sub-lemma A's body) is
grandfathered from cycle 365. The cycle 367 deliverables must be
axiom-clean. If §C.2's general-`m` form blocks, ship only §C.1's
`m = 0` specialisation — that's strictly axiom-clean and preserves
the streak.

### D.6 Do NOT raise `maxHeartbeats`

If §B.2's Step 4 arithmetic blows past the default 200000, factor
the per-step calculations into private lemmas. Per CLAUDE.md.

### D.7 Do NOT introduce `axiom` or `constant` declarations

Per CLAUDE.md absolute rule. If §B or §C blocks on a Mathlib gap,
file an issue and ship Priority 1 only.

## §E. Faithfulness considerations

Cycle 367's deliverables are Lean-side infrastructure helpers, NOT
textbook entities. The §422 `def:422B` entity remains `partial` in
`lean_status.json` (and `[~]` in `plan.md`). The cherry closed form
and its `m = 0` corollary do not by themselves close any textbook
lemma — they extend the Sub-lemma A specialised-witness library by
one tree.

**For the new `theorem` `elementaryWeightQ_phi_inv_cherry`**: 

- Tautology check: PASS expected — conclusion
  `Φ_{η⁻¹}(cherry) = (Φ_η(vertex))² − Φ_η(cherry)` is a genuine
  closed-form identity, not equal to any hypothesis.
- Identity check: PASS expected — proof composes cycle 358
  `_inv_mk` + cycle 187 `derivativeWeight_vertex` + arithmetic;
  not a one-line `exact h`.
- Definition smuggling check: PASS — no new `def`/`structure`.
- Hypothesis strength: PASS — universally quantified over all
  `η_q : Quotient PhiEquivalent.setoidSigma`, matches the cycle
  341 P3 vertex template's signature pattern.

**For the new `theorem` `powRep_sum_eq_of_agreement_at_cherry_zero`**:

- Tautology check: PASS — conclusion at `cherry, m = 0` is *not*
  reachable from the per-tree hypotheses without the inv-cherry
  closed form.
- Identity check: PASS — 3-line proof using `_inv_cherry` + 2 `rw`s.
- Hypothesis strength: matches the closed-subtree at cherry case
  (just two equations); cannot be weakened further since both
  `h_vertex` and `h_cherry` are individually load-bearing.

Update `.prover-state/issues/def_422B_phase_D_3_scoping.md` with a
"Cycle 367 update" subsection per the cycles 358/359/360/361/362/365/366
precedent — summarise the cherry closed-form ship + where it sits
relative to Phase D.3.d's blocking dependency on Sub-lemma A
general body.

## §F. Verification checklist

After landing §B + §C.1:

1. `lake build OpenMath.Chapter4.Section422` exits 0 (~150–270 s
   warm cache expected).
2. `grep -c sorry OpenMath/Chapter4/Section422.lean` = 5 lines
   (unchanged from cycle 366: 4 doc references + 1 actual code
   sorry — Sub-lemma A's body, grandfathered).
3. `#print axioms` on each new public theorem returns
   `[propext, Classical.choice, Quot.sound]` only:
   - `elementaryWeightQ_phi_inv_cherry`
   - `powRep_sum_eq_of_agreement_at_cherry_zero`
   - (if shipped) `powRep_inv_cherry_closed_form`
4. `#print axioms linearResidualAt_depends_only_on_strict_subtrees`
   still returns `[propext, sorryAx, Classical.choice, Quot.sound]`
   (unchanged — Sub-lemma A body still sorry'd).
5. `grep -n "sorry" OpenMath/Chapter4/Section422.lean` shows only
   the line at `Section422.lean:2279` (Sub-lemma A body) plus the
   4 doc references.

§422 axiom-clean streak target: **32 → 33** (336–367) if §B + §C.1
both land.

## §G. Cycle 368+ outlook — Sub-lemma A general body

The heterogeneity obstacle requires new infrastructure beyond the
cycle 367 cherry ship. Per cycle 366 §Discovery #1, three routes
remain:

* **Route A (cycle 368+, multi-cycle)**: inner-tableau substitution
  lemma. Prove a cycle-362-style substitution where the *inner*
  tableau varies under appropriate hypotheses. Likely 150–300 LOC
  spanning 2–3 cycles. The substantive content is understanding how
  `derivativeWeightWithSrc M₂ M₁ i t` depends on `M₂`'s `A, b, c`
  data.

* **Route B (cycle 368+, exploratory)**: quotient-level
  reformulation. Cycle 367's cherry closed form
  (`Φ_{η^(-(m+1))}(cherry) = (m+1)(m+2)/2 · Φ_η(vertex)² − (m+1) ·
  Φ_η(cherry)`) is the cherry instance of a hoped-for *general*
  closed-form pattern: `Φ_{η^(-(m+1))}(t)` as a polynomial in
  `Φ_η` at strict subtrees of `t` with quotient-invariant
  coefficients. If this pattern generalises (induction on
  `t.order`?), Sub-lemma A reduces to a closed-form lookup.
  **Cycle 367's cherry ship is the first non-trivial data point**
  for this hypothesis — cycle 368 should attempt the pattern at
  `broom₃` (next-simplest tree, order 3) to gauge tractability.

* **Route C (cycle 368+, structural)**: well-founded induction on
  `t.order` with a stronger motive. Same blocker as Sub-approach
  4.a — inner-tableau heterogeneity at `t` itself unresolved.
  **Unlikely to be the right path** without first attempting
  Routes A or B.

**Recommended cycle 368 strategy** (preliminary): ship Route B at
`broom₃` (third tree). If the closed-form pattern is identifiable
across vertex/cherry/broom₃, cycle 369+ can attempt the general
inductive formulation. If broom₃ resists, pivot to Route A
infrastructure (the safer multi-cycle path).

**Phase D.3.d remains blocked** on Sub-lemma A general body. Cycle
367's deliverables are pure infrastructure / non-vacuity ship, not
a Phase D.3.d unblock. Phase E sealing of `def:422B` projected for
cycle 370+ (revised down from earlier projections due to the
multi-cycle Sub-lemma A blocker).

## §H. Cycle 367 LOC budget

| Deliverable                                              | LOC est. | Required? |
|----------------------------------------------------------|----------|-----------|
| `sumB_eq_elementaryWeight_vertex` (helper, or inline)    | ~5–15    | yes       |
| `elementaryWeightQ_phi_inv_cherry`                       | ~40      | yes (§B)  |
| `_inv_cherry` non-vacuity on `explicitEuler`             | ~5–10    | yes       |
| `powRep_sum_eq_of_agreement_at_cherry_zero` (§C.1 minimal) | ~10    | yes       |
| `powRep_inv_cherry_closed_form` (§C.2 general m)         | ~50      | stretch   |
| Scoping doc update (`def_422B_phase_D_3_scoping.md`)     | ~30 doc  | yes       |

Target total: **~85 LOC core + ~30 LOC doc = ~115 LOC**. Stretch:
+50 LOC if §C.2 closes cleanly. Within cycle 367's single-cycle
budget.

## §I. Implementation order

1. **(5 min)** Verify `lake build OpenMath.Chapter4.Section422`
   exits 0 on HEAD (sanity check).
2. **(15 min)** Read cycle 358 `_inv_mk` proof at
   `Section381.lean:~2820` and cycle 226 `elementaryWeight_eq` /
   cycle 187 `derivativeWeight_vertex` for the §B.2 proof body.
   Verify `derivativeWeightWithSrcProd` recursion at
   `Section381.lean:~2680–2700`.
3. **(15 min)** Ship `sumB_eq_elementaryWeight_vertex` helper (or
   plan to inline equivalently).
4. **(45 min)** Ship `elementaryWeightQ_phi_inv_cherry` (§B).
   Follow §B.2 recipe step-by-step. If Step 4 arithmetic blows
   up, factor each algebraic step into a private `have` first.
5. **(10 min)** Add the `explicitEuler` non-vacuity example (§B.4)
   with the correct numeric RHS `1` (verified: `1² − 0 = 1`).
6. **(15 min)** Ship `powRep_sum_eq_of_agreement_at_cherry_zero`
   (§C.1) — 3-line proof via two `rw` calls.
7. **(stretch, 60 min)** Attempt `powRep_inv_cherry_closed_form`
   (§C.2 general-`m`). If the inductive step's `Φ_{·*·}(cherry)`
   decomposition stalls past 30 min, STOP and ship Priority 1 only.
8. **(15 min)** Run verification checklist (§F).
9. **(15 min)** Update `.prover-state/issues/def_422B_phase_D_3_scoping.md`
   with cycle 367 closure subsection per §E.
10. **(10 min)** Write `.prover-state/task_results/cycle_367.md`.

Total: ~2.5 hours core, +1 hour stretch.
