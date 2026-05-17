# Cycle 360 Strategy — §422 Phase D.3.b: linear coefficient extraction

## A. Where we are

Cycle 359 shipped Phase D.3.a.3 axiom-clean per the
`def_422B_phase_D_3_scoping.md` plan:

* `RKTableau.powRep` — recursive self-composition Σ-typed value
  (`Section381.lean`, after `instGroup_phi`).
* `RKTableau.powRep_quotient_eq` — `⟦M.powRep m⟧ = ⟦⟨s, M⟩⟧^m`.
* `elementaryWeightQ_phi_pow_succ_mk` — Phase D.3.a.3 ℕ-form
  recursive identity (`Section422.lean`).

Plus three non-vacuity `example`s on `explicitEuler`. All
axiom-clean (`[propext, Classical.choice, Quot.sound]`). Sorry
count remains 0. §422 streak now 25 consecutive axiom-clean cycles
(336–359).

The Phase D.3 ladder per scoping doc §5: **D.3.a.{1,2} (cycle 358)
→ D.3.a.3 (cycle 359) → D.3.b (cycle 360) → D.3.c (cycle 361) →
D.3.d (cycle 362) → Phase E sealing (cycle 363)**.

There are no pending Aristotle jobs and no open sorries.

## B. Target — Phase D.3.b: `coeff_eta_t_in_eta_zpow_neg`

Per `def_422B_phase_D_3_scoping.md` §4.b and §5 phase table, Phase
D.3.b ships **linear coefficient extraction**: the textbook claim
(Butcher §422, p. 359, ch04.txt:1158) that

> the coefficient of `η(t)` in `η⁻ⁱ(t)` is equal to `i·(-1)^r(t)`,
> and there are no other terms in `η⁻ⁱ(t)` with orders greater than
> `r(t) − 1`.

### B.1 Target statement (strawman, refine before committing)

```lean
theorem coeff_eta_t_in_eta_zpow_neg
    (i : ℕ) (hi : 0 < i)
    {s : ℕ} (M : RKTableau s) (t : RootedTree) :
    ∃ C : ℝ,
      elementaryWeightQ_phi
          ((Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩)^(-(i : ℤ))) t
        = (i : ℝ) * (-1)^(t.order)
          * elementaryWeightQ_phi
              (Quotient.mk PhiEquivalent.setoidSigma ⟨s, M⟩) t
          + C
      ∧ -- C depends only on values of M-stages at strict subtrees of t
        True  -- placeholder; cycle 360 worker pins the right form
```

The "depends only on strict subtrees of t" parametricity is the
substantive content — it's what lets Phase D.3.d's well-founded
recursion close at each tree.

**Cycle 360 worker MUST pin the exact signature before writing the
proof body.** Three candidate signatures, ordered by likelihood:

1. **Existential form** (above): `∃ C : ℝ, …`, with the
   parametricity claim packaged inside `C` via a per-subtree
   recursion. Most flexible, hardest to consume in D.3.d.
2. **Closed-form-with-RHS-helper**: split `C` into a named helper
   `linearResidualAt M t : ℝ` that recurses on `RootedTree.order`.
   The theorem becomes `Φ_{⟦M⟧^(-i)}(t) = i·(-1)^(t.order)·Φ_⟦M⟧(t)
   + linearResidualAt M t`, and a companion theorem
   `linearResidualAt_depends_only_on_strict_subtrees` does the
   parametricity argument. Cleaner for D.3.d consumption.
3. **At-vertex closed form only**: skip the general tree formulation
   entirely and prove `Φ_{⟦M⟧^(-i)}(τ) = -(i : ℝ)·Φ_⟦M⟧(τ)` at the
   vertex, which is cycle 341 P3 specialised to negative integers
   via cycle 358's `elementaryWeightQ_phi_inv_mk`. **Insufficient
   for Phase D.3.d** (the strategy is to find `η(t)` for *every*
   `t`, not just `τ`). Don't pursue (3) as the cycle 360
   deliverable.

**Recommend (2)** — it's the cleanest interface for Phase D.3.d's
well-founded recursion. The cycle 360 worker should write the
named helper first (a `noncomputable def` over `RootedTree.order`
using cycle 343's `WellFoundedRelation` instance), then the
theorem.

### B.2 Proof recipe

The textbook argument is short:

> The coefficient of `η(t)` in `η⁻ⁱ(t)` is equal to `i·(-1)^r(t)`,
> and there are no other terms in `η⁻ⁱ(t)` with orders greater than
> `r(t) − 1`.

Lean recipe:

1. **ℤ-power decomposition**: For `i ≥ 1`,
   `η_q ^ (-(i : ℤ)) = (η_q^(-1 : ℤ))^i = (η_q⁻¹)^i`. Then
   `η_q⁻¹ = ⟦⟨s, M.inverse⟩⟧` via cycle 222's `inverseQ_mk`. So at the
   representative level, `η_q ^ (-(i : ℤ))` corresponds to a `powRep
   M.inverse i` representative (cycle 359 infrastructure).

2. **Recursive descent via D.3.a.3**: induct on `i`. Base case
   `i = 1` is cycle 358's `elementaryWeightQ_phi_inv_mk` directly:
   `Φ_{⟦M⟧⁻¹}(t) = -Σⱼ M.b j · M.derivativeWeightWithSrc M.inverse j t`.
   The "coefficient of `η(t)`" claim is read off by inspecting the
   leading term of the bottom-block sum (at `j` such that
   `derivativeWeightWithSrc M.inverse j t` contributes a `Φ_⟦M⟧(t)`
   factor through the `M.inverse.A` entries).

3. **Inductive step**: combine D.3.a.3
   (`elementaryWeightQ_phi_pow_succ_mk`) with D.3.a.2
   (`elementaryWeightQ_phi_inv_mk`) at each step. The bottom-block
   `Σⱼ M.b j · M.derivativeWeightWithSrc (M.powRep m).2 j t` produces
   the `η(t)`-coefficient contribution at each iteration. Sum over
   `i` iterations gives the total `i·(-1)^r(t)`.

4. **Sign cancellation**: the `(-1)^(t.order)` factor comes from the
   parity of the recursive expansion. Specifically: each application
   of `derivativeWeightWithSrc` on a tree of order `k` produces
   factors that include `(M.b · (-1)^(k))`-style contributions
   through the `M.inverse.A` entries (`M.inverse.A i j = M.A i j -
   M.b j`). The cycle 358 worker's Discovery #1 (the cleaner
   formula `Φ_{⟦M⟧⁻¹}(t) = -Σ...`) carries the sign through.

5. **Strict-subtree parametricity**: by the recursive shape of
   `derivativeWeightWithSrc` (cycle 187's `derivativeWeight_mk`),
   the value at `t = mk children` depends only on values at children
   of `t`, which have strictly smaller `order`. This is a
   strong-induction argument on `RootedTree.order`, leveraging
   cycle 343's `WellFoundedRelation RootedTree := measure RootedTree.order`
   instance.

### B.3 LOC budget and concrete sub-deliverables

Per scoping doc §5: **~100 LOC, partial Aristotle suitability for
the sign-cancellation algebra**.

Decompose into:

* **Sub-deliverable 1** (~20 LOC): pin the signature shape (1, 2,
  or 3 above). Write the type, leave proof as one initial `sorry`
  IF unable to close in P1. Per project rules and the cycle 200/201
  rollback precedent, **do NOT commit any `sorry`s** — if the
  signature pinning fails or the proof exceeds budget, ship the
  named helper definition + a base-case witness only, defer the
  general theorem.

* **Sub-deliverable 2** (~30 LOC): base case at `i = 1` (combining
  cycle 358's `_inv_mk` with the linear-coefficient extraction).
  This is the easy first step and should be the minimum cycle 360
  ship if anything goes wrong with the inductive step.

* **Sub-deliverable 3** (~50 LOC): inductive step in `i`, via
  cycle 359's `_pow_succ_mk` + the base case. Closure via
  `RootedTree.order` strong induction (cycle 343 instance).

* **Sub-deliverable 4** (~20 LOC, optional): one non-vacuity
  `example` at `t = vertex` recovering cycle 341 P3
  (`elementaryWeightQ_phi_zpow_vertex`).

## C. What NOT to try

* **Do NOT attempt Phase D.3.c or D.3.d in the same cycle.** Phase
  D.3.b is the cycle 360 ceiling. The scoping doc explicitly
  decomposes Phase D.3 into 4 sub-phases at ~1 cycle each — combining
  them risks the cycle 200/201 rollback pattern. Cycle 358's
  partial-ship precedent (D.3.a.{1,2} only, D.3.a.3 deferred to
  cycle 359) sets the right ladder rhythm.

* **Do NOT ship `sorry`s.** If the proof exceeds budget, ship
  Sub-deliverable 2 only (base case `i = 1`) plus a scoping update
  to the issue file. Per cycle 200/201 and cycle 149/150 rollback
  precedents, sorry-bearing scaffolds get rolled back. The cycle
  358 worker shipped 2/3 D.3.a deliverables clean rather than 3/3
  with a sorry; follow the same discipline.

* **Do NOT use `conv_rhs => rw [← powRep_quotient_eq]` as a follow-up
  to a global `rw [← powRep_quotient_eq]`.** Cycle 359 discovery
  #1: `rw [← powRep_quotient_eq]` fires globally on both the LHS
  factor AND the RHS first summand simultaneously. The cycle 358
  strategy's two-step `rw` + `conv_rhs => rw` is over-specified;
  the second rewrite then fails with "Did not find an occurrence of
  the pattern". Use a single global `rw`.

* **Do NOT skip the `Σ s' : ℕ, RKTableau s'` type ascription in
  `show` goals.** Cycle 359 discovery #2: without the explicit
  `Σ`-vs-`PSigma` disambiguation, the elaborator picks `PSigma` and
  the `show` reframing fails. Whenever Phase D.3.b's proof needs a
  `show Quotient.mk ... ⟨..., ...⟩ = ...` step, add `(⟨..., ...⟩ : Σ
  s' : ℕ, RKTableau s')` ascription.

* **Do NOT try `induction t with | mk children ih =>` directly on
  `RootedTree`.** Per memory `feedback_rootedtree_nested_induction.md`,
  this fails because of the nested-inductive motive issue. Use cycle
  343's `WellFoundedRelation RootedTree := measure RootedTree.order`
  with `WellFoundedRecursion` or a `termination_by t => t.order`
  clause on the helper `def`.

* **Do NOT modify cycle 358's `_mul_mk`/`_inv_mk` or cycle 359's
  `_pow_succ_mk` signatures.** Each is already axiom-clean and
  is the foundation for D.3.b. If D.3.b's recipe needs additional
  variants, ship them as new theorems, not refactors.

* **Do NOT attempt to compile `OpenMath/Chapter4/Section441.lean`.**
  GPFS timeout pathology persists since cycle 182 (43+ consecutive
  timeouts). Skip per `cycle_182_gpfs_slowness.md`. Phase D.3.b
  deliverables live entirely in `Section381.lean` (potentially) and
  `Section422.lean`; Section441 is not on the path.

* **Do NOT introduce `axiom` or `constant` declarations.** Per
  CLAUDE.md and the cycle 149/150 rollback precedent.

* **Do NOT raise `maxHeartbeats` above 200000.** If the sign-
  cancellation `ring` step is slow, decompose into named
  intermediate lemmas (the cycle 358 helper-decomposition pattern
  is the right model).

## D. File placement

* `RKTableau`-level helpers (if any new ones): append to
  `OpenMath/Chapter3/Section381.lean` after cycle 359's
  `powRep_quotient_eq` (~line 4350+).
* `elementaryWeightQ_phi`-level theorems: append to
  `OpenMath/Chapter4/Section422.lean` after cycle 359's
  `elementaryWeightQ_phi_pow_succ_mk` (~line 1800+).
* Non-vacuity `example`s: append at end of `Section422.lean` after
  cycle 359's three `example`s.

## E. Concrete first-15-minute plan

Before writing any Lean code:

1. Re-read `def_422B_phase_D_3_scoping.md` §4.b and §5 phase D.3.b
   row.
2. Re-read cycle 358's `elementaryWeightQ_phi_inv_mk`
   (`Section422.lean:577–600`) and cycle 341 P3
   `elementaryWeightQ_phi_zpow_vertex` (`Section422.lean:433–475`)
   to confirm the existing API shape.
3. Re-read cycle 359's `elementaryWeightQ_phi_pow_succ_mk`
   (`Section422.lean:606+`) — verified at `task_results/cycle_359.md`
   to use a 3-line `rw [pow_succ]; rw [← powRep_quotient_eq]; exact
   _mul_mk` recipe.
4. `lean_local_search "RootedTree.order"` and
   `lean_hover_info` on cycle 343's `WellFoundedRelation` instance
   to confirm the well-founded-recursion plumbing.
5. **Pick the signature shape (1/2/3 from §B.1).** Write the type
   *only*. Verify it parses (`lake env lean OpenMath/Chapter4/Section422.lean`).
6. Sketch the base case `i = 1` proof using
   `elementaryWeightQ_phi_inv_mk`. Aim for ≤30 LOC. If clean, this is
   the cycle 360 minimum ship.
7. Attempt the inductive step using
   `elementaryWeightQ_phi_pow_succ_mk`. Aim for ≤50 LOC.

## F. Graceful degradation

If the cycle 360 worker cannot close the full D.3.b in budget:

* **Ship Sub-deliverables 1 + 2 only** (the type signature + base
  case `i = 1`), append cycle 360 update to
  `def_422B_phase_D_3_scoping.md` documenting what's open, and
  defer D.3.b inductive step to cycle 361. The §422 ladder horizon
  extends one cycle further (D.3.c → 362, D.3.d → 363, Phase E
  sealing → 364).
* If even Sub-deliverable 1 stalls (e.g. signature shape (1/2/3) is
  ambiguous and the worker needs to reframe), ship a
  named helper `noncomputable def linearResidualAt M t` alone with
  a single non-vacuity `example` at `t = vertex` (collapsing to
  `(-1)^1 · Φ_M(τ) · 1 + 0`). This still counts as a non-zero ship
  and threads infrastructure forward.

## G. Strategic context

* **§422 streak preservation**: 25 consecutive axiom-clean cycles
  (336–359). Phase E sealing of `def:422B` is projected ~4 cycles
  away. The compound investment payoff is high; stay on `def:422B`
  through cycle 363 unless a hard blocker surfaces.

* **No pivot temptation this cycle.** Cycle 359 ladder rhythm is
  productive; cycle 360 should continue without distraction. If a
  pivot ever becomes appropriate (after Phase E seals, or earlier
  if D.3.b/c/d hit a multi-cycle gap), the planner picks from the
  `cycle_336_pivot_options.md` menu at that time.

* **σ-faithfulness deferral remains in force** per
  `symmetry_group_equivalence.md`. Phase D.3.b's recursion produces
  `η : RootedTree → ℝ` and does not directly involve σ — so no new
  σ-side obligation surfaces this cycle.

## H. Bottom line

Ship Phase D.3.b: a single named theorem (or theorem + named helper
`linearResidualAt`) extracting the linear coefficient of `η(t)` in
`η⁻ⁱ(t)` as `i·(-1)^(t.order)`, with strict-subtree parametricity
for the residual term. Axiom-clean, ~100 LOC, no sorries. If
budget overruns, ship base case `i = 1` only and defer the
inductive step to cycle 361.
