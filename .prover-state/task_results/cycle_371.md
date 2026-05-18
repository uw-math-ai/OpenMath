# Cycle 371 Results

## Worked on
§422 Phase D.3.b Step 2 — `mk [broom₃]` (depth-2 ladder, order-4) closed
form for `Φ_{η_q⁻¹}` and m=0 specialisation of Sub-lemma A. Sixth data
point in the cycle 366 §G Route B hypothesis ladder.

Two new public theorems + two non-vacuity examples appended to
`OpenMath/Chapter4/Section422.lean`:

1. `elementaryWeightQ_phi_inv_mkBroom₃` — closed form
   `Φ_{η_q⁻¹}(mk [broom₃])
     = v⁴ − 3v²·c + v·b' + 2v·m − M`
   where v, c, b', m, M denote `Φ_η` at vertex, cherry, broom₃,
   mk [cherry], mk [broom₃].
2. `powRep_sum_eq_of_agreement_at_mkBroom₃_zero` — Sub-lemma A m=0
   specialisation at `t = mk [broom₃]` under agreement at the five
   subtrees in the closed form.
3. Closed-form witness `example` at `⟦explicitEuler⟧`: pins
   `Φ_{⟦explicitEuler⟧⁻¹}(mk [broom₃]) = 1`.
4. Reflexive m=0 `example`: `... rfl rfl rfl rfl rfl`.

## Approach
Followed cycle 371 planner strategy §B.5 verbatim. The depth-2 ladder
form `mk [broom₃]` has a single child `broom₃` (which is itself
`mk [vertex, vertex]`), so the proof structure is cycle 369's
`mk [cherry]` recipe with the inner cycle 367 `_dws_cherry` unfold
swapped for cycle 368's two-layer `_dws_broom₃` unfold (giving
`(inv_v + ∑ₖ A_{jk})²` instead of `(inv_v + ∑ₖ A_{jk})`).

Concretely:

1. `Quotient.inductionOn η_q` to descend to a representative `⟨s, M⟩`.
2. Reused **eight** helpers verbatim from cycles 367/368/369:
   `h_inv_v`, `h_vertex`, `h_dw_cherry`, `h_cherry`,
   `h_dw_broom₃`, `h_broom₃`, `h_dw_mkCherry`, `h_mkCherry`.
3. **Four new cycle 371 helpers**:
   * `h_inv_broom₃` — representative-lift of cycle 368's quotient
     closed form (one-liner via `elementaryWeightQ_phi_inv_broom₃` at
     `⟦⟨s, M⟩⟩`, descended definitionally via `:= rfl` simp lemmas
     `inverseQ_phi_mk` and `elementaryWeightQ_phi_mk`).
   * `h_dw_mkBroom₃` — one-layer cons-case unfold:
     `M.derivativeWeight i (mk [broom₃]) = ∑ⱼ A_{ij}·(∑ₖ A_{jk})²`,
     by `Finset.sum_congr` on `h_dw_broom₃`.
   * `h_mkBroom₃` — `M.elementaryWeight (mk [broom₃])
       = ∑ᵢ b_i · ∑ⱼ A_{ij} · (∑ₖ A_{jk})²`, by `Finset.sum_congr`
     on `h_dw_mkBroom₃`.
   * `h_dws_mkBroom₃` — outer one-cons unfold strips the `mk` layer
     (`derivativeWeightWithSrcProd M.inverse i [] = 1`), then the
     inner `derivativeWeightWithSrc M.inverse j broom₃` is unfolded
     in-line via a nested cycle 368-style two-layer
     `derivativeWeightWithSrcProd M.inverse j [vertex]` reduction
     (using `derivativeWeightWithSrc_vertex = 1`). Final form:
     `inv_broom₃ + ∑ⱼ A_{ij} · (inv_v + ∑ₖ A_{jk})²`.
4. Main computation: apply `elementaryWeightQ_phi_inv_mk M`,
   `elementaryWeightQ_phi_mk × 5`. Then build `h_sum` (the
   `Σᵢ b_i · derivativeWeightWithSrc M.inverse i (mk [broom₃])` closed
   form):
   * `h_subst` rewrites the per-summand via
     `h_dws_mkBroom₃ i, h_inv_broom₃, h_inv_v`, then **first expands
     the inner square**: `(−v + ∑ₖ A_{jk})² = (∑ₖ A_{jk})² − 2v·∑ₖ A_{jk} + v²`
     via a sub-`Finset.sum_congr` + `ring`, then distributes via
     `Finset.sum_add_distrib`/`Finset.sum_sub_distrib` and factors out
     `2v` and `v²` via `← Finset.mul_sum`, then closes with `ring`.
   * After `h_subst`, distribute the outer sum across the 4 terms via
     `Finset.sum_add_distrib`/`Finset.sum_sub_distrib`/`Finset.sum_add_distrib`.
   * Factor three outer constants via `← Finset.mul_sum × 3` (one each
     for the constant-times-b_i term, the 2v term, and the v² term).
   * Back-substitute via `← h_mkBroom₃`, `← h_mkCherry`, `← h_cherry`,
     `← h_vertex`.
   * Close `h_sum` with `ring`.
5. Final `rw [h_sum]; ring` closes the main theorem.
6. The m=0 corollary follows cycle 369's pattern: `zero_add`,
   `Nat.cast_one`, `zpow_neg_one` to reduce `η_q ^ -(0+1)` to `η_q⁻¹`,
   then `elementaryWeightQ_phi_inv_mkBroom₃` on both sides and the
   five agreement hypotheses.
7. Non-vacuity examples on `⟦explicitEuler⟧` use the
   `RKTableau.derivativeWeight_vertex` + `simp [RKTableau.explicitEuler]`
   pattern (cycle 368's recipe) for each of the five elementary
   weights.

## Result
**SUCCESS** — both new theorems compile axiom-clean
(`[propext, Classical.choice, Quot.sound]`) on second build pass after
fixing two compilation issues (see "Dead ends" below). Both non-vacuity
examples typecheck. `lake env lean OpenMath/Chapter4/Section422.lean`
exits 0 with only the existing cycle 365 grandfathered Sub-lemma A body
sorry warning. Sorry count remains 5 (4 docstring references + 1
grandfathered code sorry). Tautology-scanner grep returns no matches.
§422 streak extends to **37 consecutive axiom-clean cycles** (336–371).

Witness library now has **6 trees**: vertex, cherry, broom₃, mk
[cherry], bushy, mk [broom₃].

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `elementaryWeightQ_phi_inv_mkBroom₃`
- **Entity ID**: not in `extraction/formalization_data/entities/` —
  Phase D.3.b internal milestone, derivable from cycle 358's
  `elementaryWeightQ_phi_inv_mk` representative-form characterization.
- **Textbook statement**: closed-form polynomial identity for the
  inverse §383 quotient's elementary weight at the depth-2 ladder tree
  `mk [broom₃]`. Sixth data point in cycle 366 §G Route B hypothesis
  ladder; no direct textbook entity.
- **Lean statement captures**: derived content — the closed form
  produced is mathematically equivalent (by direct computation, see
  §B.3 sanity check on `explicitEuler` pinning to 1) to the unique
  `Φ_{η_q⁻¹}(mk [broom₃])` for any representative.
- **Tautology check**: conclusion is a 5-term polynomial in 5
  elementary weights at distinct subtrees, none of which appear as
  hypotheses (only `η_q` is). Not a tautology.
- **Identity check**: proof uses 4 new helpers + 8 reused helpers +
  multi-step computation with `Finset` algebra and `ring`. Not
  vacuous.
- **Hypothesis strength check**: only the universal `η_q` is
  quantified. Not overcomplicated.

### `powRep_sum_eq_of_agreement_at_mkBroom₃_zero`
- **Entity ID**: not in `extraction/formalization_data/entities/` —
  m=0 specialisation of Sub-lemma A
  `powRep_sum_eq_of_strict_subtree_agreement` (cycle 365, body still
  sorry) at `t = mk [broom₃]`.
- **Textbook statement**: corollary infrastructure, not in Butcher
  directly.
- **Lean statement captures**: weakening of Sub-lemma A — instead of
  requiring agreement at every strict subtree of `t`, requires only
  agreement at the **five subtrees in the closed form**. This is
  weaker than what Sub-lemma A would deliver if its body were proved,
  and demonstrates that the closed form is the operational content.
- **Tautology check**: conclusion is `Φ_{η_q⁻¹}(mk [broom₃])
  = Φ_{η_q'⁻¹}(mk [broom₃])`, hypotheses are `Φ_{η_q}(t) = Φ_{η_q'}(t)`
  at five distinct trees — different statements. Not a tautology.
- **Identity check**: proof rewrites via
  `elementaryWeightQ_phi_inv_mkBroom₃` on both sides and substitutes
  five `rw [h_*]`. Real work via the closed-form bridge.
- **Hypothesis strength check**: five agreement hypotheses are
  exactly what the closed form requires — minimal.

## Dead ends

1. **`ring` failure inside `h_subst`'s per-summand step (first build
   attempt)**: The naïve `rw [h_dws_mkBroom₃ i, h_inv_broom₃, h_inv_v]; ring`
   left a goal with an inner `∑ⱼ A_{ij}·(−v+∑ₖ A_{jk})²` on the LHS
   and a 4-term distributed form on the RHS. `ring` does **not**
   distribute scalars over `Finset.sum`, so this failed.

   **Fix**: introduce an intermediate `h_inner_expand` that expands
   `∑ⱼ A_{ij}·(−v+∑ₖ A_{jk})²` to its 3-term distributed form
   (`∑ⱼ A_{ij}·(∑ₖ A_{jk})² − 2v·∑ⱼ A_{ij}·∑ₖ A_{jk} + v²·∑ⱼ A_{ij}`)
   via a sub-`Finset.sum_congr` + `ring`, then `Finset.sum_add_distrib`,
   `Finset.sum_sub_distrib`, and `← Finset.mul_sum × 2`.

2. **`← Finset.sum_mul` wrong direction (first build attempt)**: The
   constant `(−v³ + 2vc − b')` is on the **left** of `M.b i`
   (`const * M.b i`), so the matching lemma is `Finset.mul_sum`, not
   `Finset.sum_mul`. The latter expects `f i * c` (constant on right).

   **Fix**: change `← Finset.sum_mul` to `← Finset.mul_sum`. The
   net effect is reducing the 4 reverse-rewrites to 3 since one
   sub-sum (the `M.b i * (∑ⱼ A_{ij} · (∑ₖ A_{jk})²)` term) needs no
   constant factoring — it directly matches `← h_mkBroom₃`.

Both fixes were applied in the second build attempt; the build then
passed cleanly.

## Discovery

1. **`ring` does not distribute scalars over `Finset.sum`**. This
   has come up in cycles 367, 368, 369, 370 as well (each used a
   per-summand `Finset.sum_congr` + `ring` step before invoking
   distribution lemmas). Cycle 371 reaffirms the pattern: when a
   per-summand identity contains a sub-sum, the sub-sum's
   distribution must be done explicitly before `ring`.

2. **`Finset.mul_sum` vs `Finset.sum_mul`**: the choice of direction
   depends on which side the constant is on. `Finset.mul_sum : c * ∑ⱼ f j = ∑ⱼ c * f j`
   (constant on left). `Finset.sum_mul : (∑ⱼ f j) * c = ∑ⱼ f j * c`
   (constant on right). Cycle 371 used 5 instances of `← Finset.mul_sum`
   (3 in the main h_sum block, 2 in the h_inner_expand block) and
   zero of `Finset.sum_mul`. The natural form for these cycles'
   constants seems to be left-multiplication.

3. **Depth-2 ladder closed-form signature**: cycle 369 (`mk [cherry]`)
   gave `−v³ + 2v·c − m`. Cycle 371 (`mk [broom₃]`) gives
   `v⁴ − 3v²·c + v·b' + 2v·m − M`. The `2v·m` cross term in cycle
   371 is the depth-2 ladder signature inherited from cycle 369; the
   `−v² · (signed lift of inv_broom₃ closed form)` produces the
   four `v⁴, v²c, vb', vm, M` terms. Pattern hypothesis: for `mk [t]`
   where `t` is order-3 with closed form `α·v³ + β·v·c + γ·b'`,
   the depth-2 ladder closed form is
   `Φ_{η_q⁻¹}(mk [t]) = −(α·v³ + β·v·c + γ·b')·v + (per-row inv_t
   distribution)`. For `t = cherry` (cycle 369): `Φ_{η_q⁻¹}(cherry)
   = v² − c`, so `α = 1, β = −1` (degenerate cubic); lifting gives
   `−v³ + 2v·c − m`. For `t = broom₃` (cycle 371): `Φ_{η_q⁻¹}(broom₃)
   = −v³ + 2v·c − b'`, so `α = −1, β = 2, γ = −1`; lifting gives the
   5-term form. Generalising this lift to arbitrary order is
   essentially the cycle 370 "binomial conjecture" but at the
   depth-2-ladder level instead of the broomₖ level.

4. **Representative-lift via `:= rfl` simp**: cycle 369 introduced and
   cycle 371 reuses the pattern: any quotient-level closed form
   `elementaryWeightQ_phi_inv_*` can be lifted to a representative-
   level form `M.inverse.elementaryWeight * = ...` with a **one-liner**
   `:= elementaryWeightQ_phi_inv_* (Quotient.mk … ⟨s, M⟩)`, because
   both `inverseQ_phi_mk` and `elementaryWeightQ_phi_mk` are
   `@[simp] := rfl`. This is a cheap way to scale the witness library
   when a depth-2 ladder needs the depth-1 child's closed form at the
   representative level.

## Suggested next approach

Per cycle 371 strategy §G "Cycle 372+ outlook", three viable next
targets for cycle 372's planner:

1. **`mk [vertex, cherry]`** — first asymmetric order-4 tree. Tests
   the heterogeneous-children pattern, the substantive next structural
   step. Closed form (paper-derived in cycle 371 strategy §E.2):
   `v⁴ − 3v²·c + c² + v·b' + v·m − Φ_η(mk [vertex, cherry])`. The
   new elementary weight is `∑ᵢ b·A·B` (the new tree's elementary
   weight). 6-term polynomial in 6 weights including a `c²` quadratic
   self-term that's new to the witness library.

2. **`mk [mk [cherry]]`** — depth-3 ladder. Tests deeper ladders.
   Closed form would extend cycle 369 `_mkCherry` and cycle 371
   `_mkBroom₃` with an extra wrap, structurally like a "depth-1
   inverse of `mk [cherry]`" — applying the cycle 369 closed form
   inside another depth-1 ladder. Mechanistically a smaller step
   than option 1.

3. **Pivot to scoping the inductive Sub-lemma A attack.** After 6
   closed-form data points (vertex, cherry, broom₃, mk [cherry],
   bushy, mk [broom₃]), the witness library is sufficient to inform
   a multi-cycle scoping doc analogous to `lem_310B_plan.md` for
   the strong-induction-on-`t.order` argument toward Sub-lemma A's
   body. This is the path off the witness-accumulation treadmill
   toward Phase D.3.d and Phase E sealing of `def:422B`.

**Recommendation**: option 1 (`mk [vertex, cherry]`). The heterogeneous-
children pattern is the substantive next structural test, and the
introduction of a new elementary-weight name (the first asymmetric
order-4 tree's weight) is the kind of expansion that informs whether
the closed-form approach generalises beyond symmetric/homogeneous
trees. Option 2 is also viable but is a more incremental step. Option
3 is high-value but multi-cycle scope — better left for after one
more data point (cycle 372 ships option 1, cycle 373 planner scopes
the inductive attack).

Cycle 371 worker recommends cycle 372 pick option 1, ship
`elementaryWeightQ_phi_inv_mkVertexCherry` + m=0 corollary, then
cycle 373's planner can decide between option 2 (one more witness)
or option 3 (pivot to inductive scoping).
