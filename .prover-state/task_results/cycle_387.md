# Cycle 387 Results

## Worked on

Phase α'.4.1 of `def:422B` per the cycle 385 scoping doc
`.prover-state/issues/def_422B_phase_alpha_prime_family_C_scoping.md`
§5.2 — shipped the recursive `inversePolyTree` definition (Variant
V4), the `bichildPolynomial` and `bichildCrossTerm` helpers, and the
two P1+P2 calibration witnesses `inversePolyTree_vertex` and
`inversePolyTree_cherry`.

This is the cycle 386-pinned next move: cycle 386 shipped the 10th
Family C ladder witness `mk [broom₃, cherry]`, and the strategy doc
identifies cycle 387 as the entry point for Phase α'.4.1's recursive
infrastructure (no more empirical witnesses without amortising
infrastructure first).

## Approach

1. **Pre-flight study (~30 min).** Read cycle 386's task results, the
   §1/§3.2/§5.2 of the Family C scoping doc, and verified existing
   precedents:
   * Cycle 380's `inversePolyChain` recurrence (sign convention:
     `-(Σ_p …) - f (chainTree (n+1))`).
   * Cycle 382's `inversePolyBroom` binomial closed form.
   * Cycle 384's `elementaryWeightQ_phi_inv_mkCherryCherry` 9-kernel
     RHS (the canonical (cherry, cherry) anchor).
   * Cycle 386's `elementaryWeightQ_phi_inv_mkBroomCherry` 14-term
     polynomial (the asymmetric pair anchor).
   * Mathlib/Section301's `WellFoundedRelation RootedTree :=
     measure RootedTree.order` instance (cycle 336 infrastructure).

2. **Design pivot from strategy strawman.** The strategy §C.1's
   conjectured `bichildPolynomial` shape had a positive-leading
   sign `+ v · inv₁ · inv₂ + inv₁ · f (mk [t₂]) + …`. Empirical
   check against cycle 384's closed form revealed this would require
   a very awkward `bichildCrossTerm cherry cherry f` correction
   roughly `+2v³c - 2vc² - v²·broom₃ + 2v·mkVertexCherry` (a
   4-kernel non-trivial polynomial). Switching to the *negated*
   shape:
   ```
   bichildPolynomial t₁ t₂ inv₁ inv₂ f
     := -(v · inv₁ · inv₂) - inv₁ · f (mk [t₂]) - inv₂ · f (mk [t₁])
        + bichildCrossTerm t₁ t₂ f - f (mk [t₁, t₂])
   ```
   makes the single-child collapse `mk [c]` close the cherry
   calibration P2 witness by simple `rw + ring`. The cross-term
   becomes (eventually, cycle 388+) `+2v³c - 2vc² - v²·broom₃
   + 2v·mkVertexCherry` for the (cherry, cherry) anchor — a clean
   4-kernel adjustment. See scoping doc §11.2 for the full
   justification.

3. **Implementation (~30 min).** Inserted the Phase α'.4.1 block
   after `inversePolyBroom_three` (line 6199, before the §α.1
   `inversePolynomial` pattern-match block) in
   `OpenMath/Chapter4/Section422.lean`:
   ```lean
   noncomputable def bichildCrossTerm (_t₁ _t₂ : RT) (_f : RT → ℝ) : ℝ := 0

   noncomputable def bichildPolynomial
       (t₁ t₂ : RT) (inv₁ inv₂ : ℝ) (f : RT → ℝ) : ℝ :=
     -(f RootedTree.vertex * inv₁ * inv₂)
       - inv₁ * f (mk [t₂])
       - inv₂ * f (mk [t₁])
       + bichildCrossTerm t₁ t₂ f
       - f (mk [t₁, t₂])

   noncomputable def inversePolyTree : RT → (RT → ℝ) → ℝ
     | mk [], f       => -f vertex
     | mk [c], f      => -(f vertex * inversePolyTree c f) - f (mk [c])
     | mk [c₁,c₂], f  => bichildPolynomial c₁ c₂
                            (inversePolyTree c₁ f) (inversePolyTree c₂ f) f
     | mk (_::_::_::_), _ => 0
   ```
   Termination via Lean's default `sizeOf` measure: each recursive
   call descends to a literal child of the `mk` constructor (which
   the elaborator handles automatically, no explicit `decreasing_by`
   block needed).

4. **P2 calibration witnesses (~10 min).**
   * `inversePolyTree_vertex` closes by `rfl` (the empty-children
     branch reduces definitionally to `-f vertex`).
   * `inversePolyTree_cherry` reduces cherry = `mk [vertex]` to the
     single-child branch via a `show … = …` coercion, then
     `rw [inversePolyTree, inversePolyTree_vertex]` and finally
     `ring` to discharge `-(v · -v) - cherry = v² - cherry`.

5. **Verification.** `lake env lean OpenMath/Chapter4/Section422.lean`
   exits 0 with only the cycle 365 grandfathered sorry warning.

## Result

**SUCCESS** — P1+P2 deliverables shipped:

* `bichildCrossTerm`, `bichildPolynomial`, `inversePolyTree`
  (three new `noncomputable def`s) — all axiom-clean.
* `inversePolyTree_vertex`, `inversePolyTree_cherry` (two new
  calibration `theorem`s) — both axiom-clean.
* `grep -c sorry OpenMath/Chapter4/Section422.lean` = 5 (unchanged:
  4 docstring references + 1 grandfathered code sorry at line 2279).
* Section422.lean: 7321 → 7442 LOC (+121 LOC), well within the
  strategy's hard 500 LOC ceiling.
* §422 axiom-clean streak: **50 substantive + 2 doc** cycles
  (336–387).
* `def_422B_phase_alpha_prime_family_C_scoping.md` updated with a
  full §11 cycle 387 closure section (§11.1–§11.6).

P3 (Family C calibration witnesses) and P4 (scoping doc cycle 388
entry point) — P4 *ships* (§11.6 covers Phase α'.4.1's cycle 388
continuation), P3 deferred to cycle 388 as it requires
`bichildCrossTerm` per-pair refinement (out of scope for cycle 387's
infrastructure ship per strategy §C.4 + §E).

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `bichildCrossTerm` (placeholder helper)

* Entity ID: helper supporting `def:422B` Phase α' infrastructure
  (no direct textbook entity).
* Textbook statement (from
  `extraction/formalization_data/entities/def_422B.json`): the
  underlying-one-step-method definition statement is
  > "Corresponding to a linear multistep method [α, β], the member
  > of G1 represents the 'underlying one-step method'."
  This is a high-level Phase E sealing target; the cycle 387 helper
  is Phase α' infrastructure for the eventual Phase E closure.
* Lean statement captures: **placeholder** (returns 0 uniformly).
  This is the strategy-explicit cycle 387 entry shape per §C.1:
  "For Phase α'.4.1's first ship, `bichildCrossTerm` may be left as
  a `noncomputable def` with explicit per-pair cases … a fully
  unified combinatorial recipe is out of scope for cycle 387".
* Definition smuggling: PASS (no `Prop` field; pure computational
  helper).

### `bichildPolynomial` (binary-children helper)

* Entity ID: helper supporting `def:422B` Phase α' infrastructure.
* Lean statement captures: **same content** as the strategy
  strawman §C.1 *modulo* the §11.2 sign revision. The negated shape
  is the version that makes the single-child collapse (and hence
  the cherry calibration witness) close cleanly; this is the
  empirically-justified refinement of the strategy's strawman.
* Definition smuggling: PASS.

### `inversePolyTree` (recursive inverse-polynomial)

* Entity ID: helper supporting `def:422B` Phase α' infrastructure.
* Lean statement captures: **same content** as the strategy
  strawman §C.2's 4-branch dispatch (`mk []`, `mk [c]`, `mk [c₁,c₂]`,
  `mk (_::_::_::_)`), modulo:
  - The single-child branch uses the one-step bichild collapse
    `-(v · inversePolyTree c f) - f (mk [c])` rather than routing
    through `inversePolyChain` (the strategy left this open between
    two options per §C.2; we picked the simpler one-step collapse,
    which suffices for the cherry P2 calibration; later cycles can
    add a bridge theorem `inversePolyTree_eq_inversePolyChain` for
    Family A trees if needed).
  - Termination via default `sizeOf` (Lean's pattern-match elaborator
    handles this automatically for the literal `[c]` and `[c₁,c₂]`
    patterns) rather than explicit `WellFoundedRelation` invocation.
    Equivalent power; lower LOC.
* Definition smuggling: PASS.

### `inversePolyTree_vertex` (calibration theorem)

* Statement: `inversePolyTree vertex f = -f vertex`.
* Captures cycle 341's vertex inverse-polynomial closed form
  `Φ_{η⁻¹}(τ) = -Φ_η(τ)` at the `inversePolyTree` interface.
* Tautology check: PASS (LHS is `inversePolyTree vertex`, RHS is
  `-f vertex` — `f vertex` ≠ `inversePolyTree vertex f` syntactically).
* Identity check: proof is `rfl`. This is a *definitional unfold*,
  not a hypothesis re-export — the closed form falls out of
  `inversePolyTree`'s empty-children branch. This is genuine
  computational content (the branch matched is the 0-arg branch).
* Hypothesis strength: PASS (only `f : RT → ℝ` as input).

### `inversePolyTree_cherry` (calibration theorem)

* Statement: `inversePolyTree cherry f = (f vertex)^2 - f cherry`.
* Captures cycle 367's cherry inverse-polynomial closed form
  `Φ_{η⁻¹}([τ]) = (Φ_η τ)² - Φ_η [τ]` at the `inversePolyTree`
  interface.
* Tautology check: PASS.
* Identity check: proof is `show … = …; rw [inversePolyTree,
  inversePolyTree_vertex]; show … = …; ring`. Non-trivial
  computational content — the single-child branch unfolds, the
  inner `inversePolyTree vertex f` reduces via the prior theorem,
  and `ring` closes the polynomial identity `-(v · -v) - cherry =
  v² - cherry`.
* Hypothesis strength: PASS (only `f : RT → ℝ` as input).

## Dead ends

The first design attempt used the strategy's strawman positive-sign
`bichildPolynomial` shape from §C.1 verbatim. Empirical check against
cycle 384's closed form showed the implied
`bichildCrossTerm cherry cherry f` would be a 4-kernel polynomial
`-2v⁵ + 6v³c - 4vc² - v²·broom₃ - 4v²·mkCherry + 4·cherry·mkCherry
+ 2v·mkVertexCherry` — much more complex than the strategy's
suggested `2v·mkVertexCherry + 2c·mkCherry`. Pivoting to the
negated-leading-sign shape made the cross-term collapse to a clean
4-kernel `+2v³c - 2vc² - v²·broom₃ + 2v·mkVertexCherry` (deferred to
cycle 388's per-pair refinement).

No Aristotle submission this cycle — the new symbols are pure
definitions and one-line / one-step calibration proofs, no `sorry`'s
to mine.

## Discovery

* **The strategy's strawman bichildPolynomial sign convention was
  empirically wrong.** A naive `+v·inv₁·inv₂ + …` leading
  positive-sign shape doesn't fit cycle 384's closed form cleanly;
  the cross-term would need to absorb a leading `-2v⁵` that ought to
  come from the inv-product term. Negating the whole `inv`-product
  block matches both (a) the cycle 380 `inversePolyChain (n+1)`
  recurrence's leading-`-` convention and (b) the uniform `-1`
  self-term coefficient across cycles 371/372/384/386. This is the
  Phase α'.4 design insight — the recursion is fundamentally
  *negative*-leading at every depth, matching the §387 group
  inverse's parity flip.

* **The single-child branch matters even for the cherry case.** The
  vertex calibration (`mk []`) reduces by `rfl` alone, but the
  cherry calibration (`mk [vertex]`) requires the single-child
  branch's `-(v · inversePolyTree c f) - f (mk [c])` formula to
  fire. The choice of formula here directly determines the cherry
  calibration's `ring`-closure. With the negated-leading-sign
  convention, `-(v · -v) - cherry = v² - cherry` ✓.

* **Lean's pattern-match elaborator handles strict-subtree
  termination automatically for literal `[c]` / `[c₁,c₂]` patterns**
  (no explicit `decreasing_by` block needed). This was a pleasant
  surprise — the cycle 387 ship has zero termination-proof LOC.
  The custom `WellFoundedRelation RootedTree := measure
  RootedTree.order` instance from cycle 336 wasn't required.

* **LOC budget.** Cycle 387 came in at +121 LOC, well below the
  strategy's hard 500 LOC ceiling and below even the ~300 LOC P1+P2
  target. This is the amortisation payoff the strategy predicted:
  one infrastructure ship covers all future Family C calibration
  witnesses (vs cycle 386's +801 LOC for *one* witness).

## Suggested next approach

**Cycle 388 — Phase α'.4.1 P3 + bichildCrossTerm refinement.**

Recommended:

* **Refine `bichildCrossTerm` for `(cherry, cherry)`** to make
  `inversePolyTree (mk [cherry, cherry]) f` evaluate to cycle 384's
  closed form. From the cycle 387 §11.2 analysis, the value should
  be `+2v³c - 2vc² - v²·broom₃ + 2v·mkVertexCherry`. Then ship the
  P3 calibration witness `inversePolyTree_mkCherryCherry` closing
  by `rw [inversePolyTree, bichildPolynomial, bichildCrossTerm,
  inversePolyTree_cherry]` + `ring`.

* **Also refine `bichildCrossTerm` for `(broom₃, cherry)`** to
  match cycle 386's 14-term polynomial. The cross-term value can be
  back-computed from cycle 386's closed form minus the
  `bichildPolynomial`-without-cross-term backbone, parallel to the
  cycle 384 derivation. Estimated +200 LOC for both witnesses + the
  per-pair cross-term cases.

* **Stretch (if cycle 388 has slack)**: Define `inversePolyTree`'s
  single-child branch via `inversePolyChain` (Family A) when the
  child is itself in the chain shape, and ship the bridge theorem
  `inversePolyTree_mk_singleton_eq_inversePolyChain` to demonstrate
  this refactor is sound. This positions Phase α'.4.2 (Family C
  branch migration) cleanly.

Phase α'.4.2 (cycle 389+): once cycle 388 lands the cross-term
refinement, migrate the Family C branches of `inversePolynomial`
(`mk [broom₃]`, `mk [vertex, cherry]`, `mk [cherry, cherry]`,
`mk [broom₃, cherry]`) to dispatch to `inversePolyTree`, parallel
to cycles 381 (Family A) and 383 (Family B).

Phase E sealing of `def:422B` (closing the cycle 365 grandfathered
sorry at Section422.lean:2279) remains projected for the 390s —
multi-cycle Phase β/γ extension consuming `inversePolyTree` as the
Family C branch driver for the
`powRep_sum_eq_of_strict_subtree_agreement` general body.
