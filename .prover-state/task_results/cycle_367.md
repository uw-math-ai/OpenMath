# Cycle 367 Results

## Worked on

§422 Phase D.3.b Step 2 — cherry closed form
(`elementaryWeightQ_phi_inv_cherry`) + `m = 0` cherry corollary
(`powRep_sum_eq_of_agreement_at_cherry_zero`) per cycle 367
strategy §B + §C.1 (Priority 1 mandatory deliverables).

## Approach

Per the cycle 367 strategy §B.2 recipe, the cherry closed form
`Φ_{η⁻¹}(cherry) = (Φ_η(vertex))² − Φ_η(cherry)` was assembled by:

1. **`Quotient.inductionOn`** on `η_q` to obtain a representative
   `⟨s, M⟩`.
2. **Cycle 358 `elementaryWeightQ_phi_inv_mk`** to reduce
   `Φ_{⟦⟨s, M⟩⟧⁻¹}(cherry)` to
   `−∑ᵢ M.b i · M.derivativeWeightWithSrc M.inverse i cherry`.
3. **Recursive unfold of `derivativeWeightWithSrc` at cherry**:
   `cherry = mk [vertex]`, so the helper expands to
   `M.derivativeWeightWithSrcProd M.inverse i [vertex]`, then to
   `(M.inverse.elementaryWeight vertex + ∑ⱼ M.A i j ·
     M.derivativeWeightWithSrc M.inverse j vertex)
    · M.derivativeWeightWithSrcProd M.inverse i []`.
   The base cases collapse via cycle 366's
   `derivativeWeightWithSrc_vertex` (each factor `= 1`) and
   `derivativeWeightWithSrcProd M.inverse i [] = 1` (`rfl`).
4. **`M.inverse.elementaryWeight vertex = -M.elementaryWeight vertex`**:
   from `inverse_b` (`M.inverse.b j = -M.b j`) and `derivativeWeight_vertex`
   (`derivativeWeight j vertex = 1`), the inverse-vertex weight
   becomes `∑ⱼ (-M.b j) · 1 = -∑ⱼ M.b j = -M.elementaryWeight vertex`.
5. **`M.elementaryWeight cherry = ∑ᵢ M.b i · ∑ⱼ M.A i j`** and
   **`M.elementaryWeight vertex = ∑ⱼ M.b j`**: by parallel unfolds
   of `derivativeWeight i cherry` and `derivativeWeight j vertex`.
6. **Calc-chain assembly**: substitute Steps 3–5 in the LHS sum
   under `Finset.sum_congr`, then split via
   `← Finset.sum_sub_distrib` and `← Finset.sum_mul` to extract
   `(∑ᵢ M.b i) · M.elementaryWeight vertex` and close by `ring`.

Sub-lemma A's cherry-`m = 0` specialisation
`powRep_sum_eq_of_agreement_at_cherry_zero` then follows in 3 lines:

1. Reduce `η_q ^ (-(((0 + 1 : ℕ) : ℤ)))` to `η_q⁻¹` via
   `zero_add + Nat.cast_one + zpow_neg_one` (a uniform
   `∀ ζ, ζ ^ (-(((0 + 1 : ℕ) : ℤ))) = ζ⁻¹` lemma applied to both
   `η_q` and `η_q'`).
2. Apply `elementaryWeightQ_phi_inv_cherry` on both sides.
3. Substitute `h_vertex` and `h_cherry`.

Two non-vacuity `example`s ship alongside:
- `Φ_{⟦explicitEuler⟧⁻¹}(cherry) = 1` (computed as `1² − 0 = 1`
  since `Σ b = 1` for explicit Euler and `A = 0` makes `Φ(cherry) = 0`).
- Cherry m=0 witness at `η_q = η_q' = ⟦explicitEuler⟧` with
  agreement hypotheses discharged by `rfl, rfl`.

## Result

**SUCCESS** — cycle 367 ships TWO new axiom-clean public theorems
(`elementaryWeightQ_phi_inv_cherry` + `powRep_sum_eq_of_agreement_at_cherry_zero`)
plus two non-vacuity examples, extending the cycle 366 small-tree
witness library from `{vertex}` to `{vertex, cherry (m = 0)}`. The
existing cycle 365 Sub-lemma A body sorry is unchanged
(grandfathered).

Verification (`lake env lean OpenMath/Chapter4/Section422.lean`,
exit 0):

* `#print axioms OpenMath.Chapter4.Section422.elementaryWeightQ_phi_inv_cherry`
  → `[propext, Classical.choice, Quot.sound]`. **Axiom-clean.**
* `#print axioms OpenMath.Chapter4.Section422.powRep_sum_eq_of_agreement_at_cherry_zero`
  → `[propext, Classical.choice, Quot.sound]`. **Axiom-clean.**
* `#print axioms OpenMath.Chapter4.Section422.linearResidualAt_depends_only_on_strict_subtrees`
  → `[propext, sorryAx, Classical.choice, Quot.sound]`. **Unchanged**
  (still routes through Sub-lemma A's sorry'd body).
* `grep -c sorry OpenMath/Chapter4/Section422.lean` = 5 lines (4
  documentation references + 1 actual code sorry). Code-level sorry
  count: **1 (unchanged from cycle 365)**.

§422 axiom-clean streak: **32 → 33** (336–367). Both new theorems
are axiom-clean; the existing Sub-lemma A sorry is grandfathered
from cycle 365 and does not break the streak (analogous to cycles
358 → 359, 360 → 361, 365 → 366 split-cycle precedents).

## Faithfulness check

Both new theorems are Lean-side infrastructure helpers, NOT
textbook entities; there is no JSON file in
`extraction/formalization_data/entities/` corresponding to them.

### `elementaryWeightQ_phi_inv_cherry`

A quotient-level closed-form identity; the cherry analog of cycle
341 P3's vertex closed form `elementaryWeightQ_phi_zpow_vertex`.

- **Tautology check**: PASSED. Conclusion
  `Φ_{η⁻¹}(cherry) = (Φ_η(vertex))² − Φ_η(cherry)` does not appear
  among hypotheses (the theorem has no hypotheses — it is a
  universally-quantified identity).
- **Identity check**: PASSED. Proof composes cycle 358 `_inv_mk`,
  unfold of `derivativeWeightWithSrc` recursion, cycle 187
  `derivativeWeight_vertex`, cycle 358 `inverse_b`, and final
  algebraic assembly via `Finset.sum_congr` + `Finset.sum_sub_distrib`
  + `Finset.sum_mul` + `ring`. ~40 LOC including five `have` blocks
  — not a one-line `exact`.
- **Definition smuggling check**: PASSED — no new `def`/`structure`.
- **Hypothesis strength check**: PASSED — universally quantified
  over all `η_q : Quotient PhiEquivalent.setoidSigma`, matching the
  cycle 341 P3 vertex template's signature pattern.

### `powRep_sum_eq_of_agreement_at_cherry_zero`

The `m = 0` cherry specialisation of Sub-lemma A
`powRep_sum_eq_of_strict_subtree_agreement`. Drops Sub-lemma A's
closed-subtree quantifier `∀ s, s.order ≤ cherry.order = 2 → ...`
in favour of the equivalent finite conjunction of agreement at
`vertex` and `cherry` (the only two trees of order `≤ 2`).

- **Tautology check**: PASSED. Conclusion
  `Φ_{η_q^(-1)}(cherry) = Φ_{η_q'^(-1)}(cherry)` is reachable from
  the two per-tree hypotheses via the cherry closed form (which is
  the *content* of cycle 367), not by hypothesis substitution
  alone.
- **Identity check**: PASSED — 3-line composed `rw` proof, doing
  real work via `elementaryWeightQ_phi_inv_cherry` on each side.
- **Hypothesis strength check**: PASSED — both `h_vertex` and
  `h_cherry` are load-bearing; the closed-form RHS depends on both
  via `(Φ_η(vertex))² − Φ_η(cherry)`. Neither can be dropped.
- **Absent theorem check**: PASSED — the cherry closed form
  invoked (`elementaryWeightQ_phi_inv_cherry`) is shipped earlier
  in the same file in this cycle, not promised-but-missing.

### Non-vacuity examples

Both examples are concrete numeric witnesses on `explicitEuler`,
not new public theorems. They contribute no faithfulness obligations
beyond confirming the new public theorems' signatures and proof
recipes fire on a concrete tableau.

## Dead ends

None encountered this cycle. The proof recipe in cycle 367 strategy
§B.2 was followed step-by-step; the main implementation deviations
were:

1. **Initial `rw [show ∀ i, ...]` syntax failed**: cannot rewrite
   under a binder using `rw` with a universally-quantified
   equation. **Fix**: replaced with `Finset.sum_congr rfl (fun i _
   => by ...)` inside a `calc` chain. Each `calc` step transforms
   one sum into the next via explicit `Finset.sum_congr` or
   `← Finset.sum_sub_distrib` / `← Finset.sum_mul`.

2. **`Finset.sum_sub_distrib` is a universally-quantified equation,
   not a typed rewrite term**: passing it as a term of the goal
   type fails. **Fix**: invoked via `rw [← Finset.sum_sub_distrib]`
   inside a `by` block.

3. **explicitEuler `simp` reduction at cherry over-eager**: the
   initial `simp [explicitEuler, derivativeWeight_vertex,
   Fin.sum_univ_one]` left an unresolved
   `derivativeWeight 0 cherry = 0` subgoal because `simp` reduced
   the outer sum but couldn't unfold `derivativeWeight i cherry`.
   **Fix**: introduced a separate
   `h_cherry_zero : derivativeWeight 0 cherry = 0` step that
   manually unfolds via `show derivativeWeightProd 0 [vertex]
   = (∑ j, A 0 j * derivativeWeight j vertex) * derivativeWeightProd
   0 [] = 0` and `simp [explicitEuler]` (using `A = 0` to make the
   sum vanish), then dispatches the outer `elementaryWeight cherry =
   0` via `simp [h_cherry_zero]`.

## Discovery

1. **Cherry closed form coefficients confirm the cycle 366 §G
   Route B pattern hypothesis**: cycle 366 §G Route B posited that
   `Φ_{η^(-(m+1))}(t)` for arbitrary `t` should be a polynomial in
   `Φ_η` at strict subtrees of `t` with quotient-invariant
   coefficients. Cycle 367's cherry case at `m = 0` produces
   coefficients `(+1, −1)` at subtree weights
   `((Φ_η(vertex))², Φ_η(cherry))`. The generalised cherry form
   strategy-§C.2 conjectured is `(+(m+1)(m+2)/2, −(m+1))` — the
   `m = 0` case matches `(1, -1)`. This data point is consistent
   with the Route B hypothesis, but a single tree of order 2 is
   insufficient to confirm the pattern. Cycle 368 should attempt
   `broom₃` (third tree, order 3) to gauge tractability.

2. **`derivativeWeightWithSrcProd M₁ i [] = 1` and
   `derivativeWeight i vertex = 1` are both definitional `rfl`**:
   these collapse the cherry recursion in two `rw` steps. The
   ambient cycle 366 `RKTableau.derivativeWeightWithSrc_vertex`
   lemma names the second fact for legibility but is *not*
   strictly needed (a plain `show ... = 1; rfl` would suffice).
   Using the named lemma keeps the proof body readable.

3. **`zero_add` in the `n = -1` bridge is necessary**: the
   `0 + 1 : ℕ` literal in `powRep_sum_eq_of_agreement_at_cherry_zero`'s
   signature does not reduce to `1` definitionally inside the
   `Nat.cast_one` rewrite. The proof body has to explicitly
   `rw [zero_add, Nat.cast_one]` before `exact zpow_neg_one _`.
   This pattern will recur in any future `m = 0` specialisations of
   Sub-lemma A; cycle 368 worker should expect to write a uniform
   `∀ ζ, ζ ^ (-(((0 + 1 : ℕ) : ℤ))) = ζ⁻¹` helper.

4. **`Finset.sum_sub_distrib` direction**: the canonical form is
   `∑ i, (f i - g i) = (∑ i, f i) - (∑ i, g i)`, but our goal
   shape has the RHS form; we close via `rw [← Finset.sum_sub_distrib]`.
   The "reverse" rewrite is the canonical way to consume the lemma
   in this direction.

## Suggested next approach

Per the cycle 367 strategy §G, cycle 368 should attempt
**Route B at `broom₃`** (third tree, order 3) to gauge whether the
quotient-level closed-form pattern generalises:

- **Target**: ship `elementaryWeightQ_phi_inv_broom₃` (closed form
  for `Φ_{η⁻¹}(broom₃)`) and the corresponding `m = 0` cherry-style
  witness. Conjectured form: a quadratic polynomial in
  `Φ_η(vertex), Φ_η(cherry), Φ_η(broom₃)` with coefficients
  involving small rationals.

- **Why broom₃ first**: at order 3, broom₃ = `mk [vertex, vertex]`
  is the simplest "branched" tree; its `derivativeWeight` recursion
  involves *two* `internalWeight` factors at vertex, making it the
  next-non-trivial test of whether the closed-form pattern
  generalises beyond order 2.

- **Outcome criteria for cycle 369+ decision**:
  - If broom₃ closed form ships cleanly in 1 cycle: probable that
    Route B generalises; cycle 369 attempts the inductive `t.order`
    formulation of Sub-lemma A.
  - If broom₃ resists in 1 cycle: pivot to Route A (inner-tableau
    substitution lemma), a multi-cycle infrastructure effort.

- **Stretch option**: also ship the general-`m` cherry closed form
  `powRep_inv_cherry_closed_form` per cycle 367 strategy §C.2.
  Cycle 367 deferred this; cycle 368 may attempt it if broom₃
  closed form lands quickly. The cycle 367 strategy §C.2 risk
  assessment (inductive step needs `Φ_{η₁·η₂}(cherry)` closed form
  decomposition) still holds — this is graceful-degradation
  stretch, not mandatory.

The §422 streak target for cycle 368 is **33 → 34** if either
broom₃ closed form or general-`m` cherry form lands axiom-clean.

**Phase D.3.d (`underlyingOneStepMethod_aux`) remains blocked** on
Sub-lemma A's general body. The cherry m=0 witness does not
unblock D.3.d on its own; cycle 367 ship is purely additive
infrastructure / second-tree-non-vacuity for Sub-lemma A's
specialised-witness library.
