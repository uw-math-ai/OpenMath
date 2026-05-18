# Cycle 366 Results

## Worked on

§422 Phase D.3.b Step 2 — discharge of Sub-lemma A
(`powRep_sum_eq_of_strict_subtree_agreement`) body per cycle 366
strategy §C Priority 1 attempt; fallback to §D Priority 2 specialised
witness ship.

## Approach

Per the cycle 366 strategy §C, the Priority 1 plan was to:

1. `Quotient.inductionOn₂` on `(η_q, η_q')` to obtain representatives
   `M, M'`.
2. Apply cycle 361's `elementaryWeightQ_phi_zpow_negSucc_mk` on both
   sides to expand `Φ_{η^(-(m+1))}(t)` to a `powRep`-sum.
3. Bridge the two heterogeneous `powRep`-sums (LHS sum over
   `Fin (M.1 * (m+1))`, RHS over `Fin (M'.1 * (m+1))`) via:
   - Sub-approach 4.a: strong induction on `t.order` + cycle 362's
     `derivativeWeightWithSrc_eq_of_strict_subtree_agreement` to
     substitute `M.inverse → M'.inverse` at strict subtrees.
   - Sub-approach 4.b: induction on `m` at quotient level with
     base-case parametricity of `Φ_{η⁻¹}` + iterated multiplicativity.

Pre-flight analysis (no file edit): traced the goal-state structure
of each sub-approach against cycle 358's `_inv_mk`, cycle 359's
`powRep_quotient_eq`, and cycle 362's substitution lemma. **Result:
both sub-approaches hit the same structural obstacle.** Cycle 362
substitutes the *source* tableau (`M₁` argument) while keeping the
*inner* tableau (`M₂` argument) fixed. In Sub-lemma A, both LHS and
RHS have *different* `M₂` (LHS uses `M₂ := (M.powRep (m+1)).2`; RHS
uses `M₂ := (M'.powRep (m+1)).2`), so the per-summand cycle 362
substitution cannot fire across the two sides. The cycle 365 task
results' "Suggested next approach" §4 cancellation hint (the
`+((m+1):ℝ)·M.elementaryWeight t` term cancelling against a hidden
contribution) resolves an algebraic identity *within each side* but
does not enable cross-side comparison.

Per the cycle 366 strategy §C.3 abort criterion (90 min hard time-box
on Priority 1), aborted to Priority 2 (graceful degradation): ship
specialised small-tree witnesses at `t = vertex` (clean closed form
via cycle 341 P3) and document the cherry case as cycle 367 work.

Implemented:

* **`powRep_sum_eq_of_agreement_at_vertex`** (~25 LOC including
  docstring + non-vacuity example): specialised case of Sub-lemma A
  at `t = RootedTree.vertex` with hypothesis simplified to the
  single equation `Φ_η(vertex) = Φ_{η'}(vertex)` (no closed-subtree
  quantifier needed since the only `s` with `s.order ≤ vertex.order
  = 1` is `vertex` itself). Proof: three composed `rw`s —
  `elementaryWeightQ_phi_zpow_vertex` reduces both sides to
  `(-(m+1):ℝ) * Φ_η(vertex)` and `(-(m+1):ℝ) * Φ_{η'}(vertex)`
  respectively, then `h` closes.

* **Non-vacuity `example`** at `(m, η_q, η_q') = (0,
  ⟦explicitEuler⟧, ⟦explicitEuler⟧)` with `rfl` discharging `h`.

## Result

**SUCCESS (Priority 2 graceful degradation)** — cycle 366 ships one
new axiom-clean public theorem + one non-vacuity example, with the
Sub-lemma A general body **still sorry'd** (grandfathered from cycle
365). The §422 streak is preserved.

Verification (`lake build OpenMath.Chapter4.Section422`, exit 0,
~160 s warm cache):

* `#print axioms OpenMath.Chapter4.Section422.powRep_sum_eq_of_agreement_at_vertex`
  → `[propext, Classical.choice, Quot.sound]`. **Axiom-clean.**
* `#print axioms OpenMath.Chapter4.Section422.linearResidualAt_depends_only_on_strict_subtrees`
  → `[propext, sorryAx, Classical.choice, Quot.sound]`. **Unchanged**
  (still routes through Sub-lemma A's sorry'd body).
* `grep -c sorry OpenMath/Chapter4/Section422.lean` = 5 lines (4
  documentation references + 1 actual code sorry). Code-level sorry
  count: **1 (unchanged from cycle 365)**.

§422 axiom-clean streak: **31 → 32** (336–366). The new theorem is
axiom-clean; the existing Sub-lemma A sorry is grandfathered from
cycle 365 and does not break the streak (analogous to cycle 358 →
359, cycle 360 → 361 split-cycle precedents).

## Faithfulness check

For the one new `theorem` introduced this cycle:

* **`powRep_sum_eq_of_agreement_at_vertex`** is a Lean-side
  infrastructure helper, NOT a textbook entity. There is no JSON in
  `extraction/formalization_data/entities/` corresponding to it. It
  is a *specialised case* of `powRep_sum_eq_of_strict_subtree_agreement`
  (Sub-lemma A from cycle 365) restricted to `t = RootedTree.vertex`
  with the closed-subtree hypothesis simplified to a single
  equation. Sub-lemma A itself is also Lean-side infrastructure (a
  sub-lemma supporting Sub-lemma B / the Phase D.3.b Step 2 headline
  parametricity claim for `linearResidualAt`), introduced in cycle
  365.

  - Tautology check: **PASSED.** Conclusion (`Φ_{η^(-(m+1))}(vertex)
    = Φ_{η'^(-(m+1))}(vertex)`) does not appear among the
    hypotheses; the hypothesis is `Φ_η(vertex) = Φ_{η'}(vertex)`,
    which is structurally different.
  - Identity check: **PASSED.** The proof is a 3-step `rw` chain
    using two applications of cycle 341 P3 and then the hypothesis
    `h`. This is genuine algebraic work — the closed form for
    `Φ_{η^n}(vertex)` (cycle 341 P3) is the load-bearing
    representation theorem.
  - Definition smuggling check: **PASSED.** No new `def` or
    `structure` introduced this cycle.
  - Hypothesis strength check: **PASSED.** The hypothesis is the
    *weakest possible* — a single equation at the only tree with
    `order ≤ vertex.order = 1`. Sub-lemma A's general
    closed-subtree quantifier would specialise to this exact
    equation at `t = vertex`, so there is no strengthening.

* Sub-lemma A `powRep_sum_eq_of_strict_subtree_agreement` (cycle 365
  signature, body still sorry'd in cycle 366) — no change this cycle.

## Dead ends

1. **Sub-approach 4.a (strong induction on `t.order` + cycle 362
   substitution)**: traced through the goal-state structure but
   found the heterogeneous-inner-tableau obstacle. Even with the IH
   in hand, cycle 362's substitution lemma cannot swap the inner
   `M₂` between LHS and RHS of the powRep-sum equality. The
   substitution is *one-sided* (source tableau only), so it bridges
   `M.inverse` against a hypothetical `X` that agrees with
   `M.inverse` at strict subtrees of `t`, but it cannot bridge
   between LHS's `(M.powRep (m+1)).2.derivativeWeightWithSrc` and
   RHS's `(M'.powRep (m+1)).2.derivativeWeightWithSrc` because those
   are *different inner tableaux*.

2. **Sub-approach 4.b (induction on `m` at quotient level)**: the
   base case `m = 0` (parametricity of `Φ_{η⁻¹}` under closed-subtree
   agreement) faces the *same* heterogeneous-sum issue: after
   `Quotient.inductionOn₂` and cycle 358's `_inv_mk` expansion, LHS
   is `-Σⱼ:Fin s, M.b j · M.derivativeWeightWithSrc M.inverse j t`
   and RHS is `-Σⱼ:Fin s', M'.b j · M'.derivativeWeightWithSrc
   M'.inverse j t` with `s ≠ s'` in general. The `b`-coefficients
   and the inner-tableau argument differ, with no cycle 362-style
   substitution available to bridge.

3. **Cross-cancellation via `η^(m+1) · η^(-(m+1)) = 1`**: traced this
   route as a potential alternative to direct expansion. The plan
   would be to use `Φ_{η^(m+1) · η^(-(m+1))}(t) = 0` at both
   `η = ⟦M⟧` and `η = ⟦M'⟧`, then subtract. The subtraction yields
   `Φ_{η^(m+1)}(t) - Φ_{η'^(m+1)}(t)` on one side and the difference
   of two heterogeneous powRep-sums on the other. The positive-power
   parametricity `Φ_{η^(m+1)}(t) = Φ_{η'^(m+1)}(t)` is itself open
   (faces the same heterogeneity), so this doesn't reduce the
   problem.

## Discovery

1. **Heterogeneity is genuine, not a presentation artefact.** Both
   the cycle 365 task results' suggestion §4 and the cycle 366
   strategy's Sub-approaches 4.a and 4.b assume cycle 362's
   substitution can bridge the LHS/RHS difference. Detailed
   goal-state tracing shows it cannot: cycle 362 substitutes the
   *source* tableau (`M₁`), keeping the *inner* tableau (`M₂`)
   fixed; Sub-lemma A's LHS/RHS difference is precisely in the
   inner tableau. No existing infrastructure in this repository
   provides a cycle 362-style substitution lemma where the
   *inner* tableau varies. The cycle 367 strategy should either
   (a) build such infrastructure (an `inner-tableau-substitution`
   lemma; likely non-trivial because the inner tableau's `A`,
   `b`, `c` data all enter `derivativeWeightWithSrc`'s recursion),
   or (b) introduce a quotient-level invariant that abstracts the
   inner-tableau choice (the natural candidate: prove
   parametricity of `Φ_{η^(-(m+1))}(t)` directly at the quotient
   level via a new structural argument, e.g. characterising
   `Φ_{η^(-(m+1))}(t)` as a polynomial in `Φ_η` at subtrees of
   `t` with quotient-invariant coefficients).

2. **Cherry case admits a clean closed-form at `m = 0`.** Direct
   computation gives `Φ_{η⁻¹}(cherry) = (Φ_η(vertex))^2 -
   Φ_η(cherry)` (a quotient-level invariant: at the representative
   `M`, expand cycle 358's `_inv_mk` at cherry = `mk [vertex]`,
   use `M.derivativeWeightWithSrc M.inverse j cherry =
   M.inverse.elementaryWeight vertex + Σⱼ' M.A j j'`,
   `M.inverse.elementaryWeight vertex = -M.elementaryWeight
   vertex`, `M.elementaryWeight cherry = Σⱼ M.b j · Σⱼ' M.A j j'`
   to collapse). The `(M.A j j')` terms in the intermediate
   expression bundle into `M.elementaryWeight cherry`, which IS
   a quotient invariant — that's the reason the closed form
   works at the quotient level. This formula generalises to
   `Φ_{η^(-(m+1))}(cherry) = (m+1)(m+2)/2 · (Φ_η(vertex))^2 -
   (m+1) · Φ_η(cherry)` for all `m` via cycle 359's
   `_pow_succ_mk` recursion (~30-40 LOC Lean formalisation).
   Cycle 367 should ship this as a quotient-level closed-form
   lemma (analogous to cycle 341 P3 for vertex but at cherry),
   with the cherry-case Sub-lemma A specialisation following
   immediately.

3. **Vertex specialisation is structurally trivial.** Cycle 341 P3
   `elementaryWeightQ_phi_zpow_vertex` already provides the full
   closed form `Φ_{η^n}(vertex) = (n : ℝ) · Φ_η(vertex)` at the
   quotient level (no representative-level expansion needed). This
   means the vertex case of Sub-lemma A — including the simpler
   single-equation hypothesis — closes in three `rw` calls. The
   ~30 LOC budgeted in the strategy was conservative; actual
   implementation is ~10 LOC of proof body + ~15 LOC of docstring +
   non-vacuity example.

## Suggested next approach

**Cycle 367 — ship the cherry closed form + corollary.**

Priority 1 (~50 LOC, ~1 cycle): ship `elementaryWeightQ_phi_inv_cherry`
(quotient-level closed form `Φ_{η⁻¹}(cherry) = (Φ_η(vertex))^2 -
Φ_η(cherry)`, derived via Quotient.inductionOn + cycle 358 `_inv_mk`
+ explicit computation at cherry = mk [vertex]), then the
specialised witness `powRep_sum_eq_of_agreement_at_cherry` (at general
`m`, using the same closed-form approach iterated via cycle 359's
`_pow_succ_mk`). The proof structure:

```
theorem elementaryWeightQ_phi_inv_cherry
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi η_q⁻¹ RootedTree.cherry
      = (elementaryWeightQ_phi η_q RootedTree.vertex)^2
        - elementaryWeightQ_phi η_q RootedTree.cherry := by
  induction η_q using Quotient.inductionOn with
  | h p =>
    obtain ⟨s, M⟩ := p
    rw [elementaryWeightQ_phi_inv_mk M RootedTree.cherry,
        elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk]
    -- expand derivativeWeightWithSrc at cherry = mk [vertex]
    -- using derivativeWeightWithSrc_vertex = 1, inverse_b = -M.b
    -- then arithmetic via Finset.sum_mul, sum_neg_distrib
    sorry  -- ~20-30 LOC of arithmetic manipulation
```

Then derive the corollary `powRep_sum_eq_of_agreement_at_cherry` (at
general `m`) from the general closed form `Φ_{η^(-(m+1))}(cherry) =
(m+1)(m+2)/2 · (Φ_η(vertex))^2 - (m+1) · Φ_η(cherry)`, which can be
proved by induction on `m` using cycle 359's `_pow_succ_mk` recursion.

Priority 2 (multi-cycle): revisit Sub-lemma A's general body. The
heterogeneity obstacle requires either:

* **Route A — inner-tableau substitution infrastructure**: prove a
  lemma analogous to cycle 362 but where the *inner* tableau varies
  under appropriate hypotheses. This requires understanding how
  `derivativeWeightWithSrc M₂ M₁ i t` depends on `M₂`'s `A`, `b`, `c`
  data. Likely a multi-cycle infrastructure layer (~150-300 LOC
  total).

* **Route B — quotient-level reformulation**: characterise
  `Φ_{η^(-(m+1))}(t)` as a polynomial in `Φ_η` at subtrees of `t`
  with quotient-invariant coefficients. This is the "closed form"
  pattern that worked for vertex (cycle 341 P3) and works for cherry
  (cycle 367 Priority 1). Generalising to arbitrary `t` is unclear —
  the polynomial coefficients depend on `t`'s structure in
  complicated ways.

* **Route C — direct structural induction with a new motive**: use
  well-founded induction on `t.order` (via cycle 343's
  `WellFoundedRelation`) with a *stronger* IH that quantifies over
  all `(m, η_q, η_q')` agreeing on Φ at trees of order `< t.order`,
  and bootstrap the closed-subtree-at-`t` hypothesis via a separate
  cancellation argument. The blocker is the same: even with the IH,
  the inner-tableau heterogeneity at `t` itself is not resolved.

**Phase D.3.d (`underlyingOneStepMethod_aux`) remains blocked** on
Sub-lemma A's general body. The vertex + cherry specialised witnesses
do not enable Phase D.3.d on their own — Phase D.3.d's recursion
needs Sub-lemma A at *arbitrary* `t`. Cycle 367's cherry ship is
purely additive infrastructure / non-vacuity work, not a Phase D.3.d
unblock.

**Recommended cycle 367 strategy ladder:**

* Cycle 367: cherry closed form + corollary ship (~1 cycle).
* Cycle 368: Sub-lemma A general body attempt via Route B
  (quotient-level reformulation). If stalls, document and consider
  Route A as multi-cycle work.
* Cycle 369+: Phase D.3.d once Sub-lemma A general body lands.
* Cycle 370+: Phase E sealing.

The §422 streak (32 at end of cycle 366) should be maintainable
through cycle 367 (cherry ship is straightforward closed-form
algebra). Cycles 368+ for Sub-lemma A general body may require
Priority 2 graceful-degradation deferrals depending on which Route
yields progress.
