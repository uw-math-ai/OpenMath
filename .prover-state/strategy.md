# Cycle 376 Strategy — §422 Sub-lemma A Phase γ ship

## §A Bottom-line directive (worker, read first)

Ship **Phase γ** of `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md` §5:
the closed-subtree-agreement theorem for `inversePolynomial`. This is the cycle
375 worker's recommended Option B (cycle 375 task results §"Suggested next
approach"), and per Discovery #3 of cycle 375 it reduces to four trivial case
splits given the cycle 374 pattern-match form.

**Deliverable**: one new axiom-clean public theorem
`inversePolynomial_eq_of_subtree_agreement` in
`OpenMath/Chapter4/Section422.lean`, appended after cycle 375's
`elementaryWeightQ_phi_inv_eq_inversePolynomial_on_ladder` block (currently the
last public theorem in the file, around line 4426). Estimated 50–90 LOC.

**Do NOT**:
- Touch the cycle 365 grandfathered sorry at line 2279 (Phase ε, projected
  cycle 378+).
- Add any new sorries beyond that one.
- Attempt Phase α.2 (extending the pattern match to `bushy`/`mk [broom₃]`/
  `mk [vertex, cherry]`) — that is the alternative Option A from cycle 375
  and is strictly less leverage than Phase γ.
- Pivot to a fresh entity. `def:422B` remains the active multi-cycle target
  with the streak at 40 substantive + 1 doc cycles.
- Re-prove the cycle 341/367/368/369 closed forms. Phase γ only uses the
  cycle 374 `inversePolynomial` definition.

## §B Target statement

```lean
theorem inversePolynomial_eq_of_subtree_agreement
    (t : RT) (f g : RT → ℝ)
    (h_closed : ∀ s : RT, s.order ≤ t.order → f s = g s) :
    inversePolynomial t f = inversePolynomial t g
```

Location: `OpenMath/Chapter4/Section422.lean`, appended after line 4426 (after
the aggregator `elementaryWeightQ_phi_inv_eq_inversePolynomial_on_ladder`),
before the closing `end OpenMath.Chapter4.Section422`.

The hypothesis is **closed-subtree** agreement (`s.order ≤ t.order`, including
`s = t`), per the scoping doc §6.3 and the cycle 365 update (the form is
strictly weaker than strict-subtree and sufficient for Phase D.3.d).

## §C Pre-flight (do these before writing any Lean)

1. **Read the current `inversePolynomial` definition.** It lives near line
   4196 of `OpenMath/Chapter4/Section422.lean` (cycle 374 shipped it). Verify
   the four matched branches:
   - `vertex` ↦ `-(f vertex)`
   - `cherry` ↦ `(f vertex)^2 - f cherry`
   - `broom₃` ↦ `-(f vertex)^3 + 2*(f vertex)*(f cherry) - f broom₃`
   - `mk [cherry]` ↦ `-(f vertex)^3 + 2*(f vertex)*(f cherry) - f (mk [cherry])`
   - everything else ↦ `0`

   Each matched RHS depends only on `f` at trees that are subtrees (in the
   tree-structural sense) of the matched `t`. By `RootedTree.order`'s
   structural definition (cycle 343 infrastructure), each referenced tree
   has order ≤ the matched tree's order. Confirm via `lean_hover_info` if
   uncertain about the exact tree-order values.

2. **Verify tree-order values** at the four matched trees (used by the
   `h_closed` calls):
   - `vertex.order = 1`
   - `cherry.order = 2`
   - `broom₃.order = 3`
   - `(mk [cherry]).order = 3` (one child of order 2, plus 1 for the root)

   These should reduce by `decide` or `rfl`. If `decide` is slow on
   `mk [cherry]`, fall back to explicit `unfold RootedTree.order`.

3. **Verify the cycle 365 grandfathered sorry is untouched** by grepping
   `OpenMath/Chapter4/Section422.lean` for `sorry` and confirming the count
   is exactly 5 lines (4 docstring references + the actual sorry at
   line 2279).

## §D Proof recipe (worker follows literally)

The pattern-match shape of `inversePolynomial` means the proof reduces to a
4-way case split on `t` (matching the definition's branches), plus a default
case for everything else.

### Sketch

```lean
theorem inversePolynomial_eq_of_subtree_agreement
    (t : RT) (f g : RT → ℝ)
    (h_closed : ∀ s : RT, s.order ≤ t.order → f s = g s) :
    inversePolynomial t f = inversePolynomial t g := by
  unfold inversePolynomial
  -- Goal is now nested if-then-else over t = vertex, cherry, broom₃, mk [cherry].
  by_cases h_vertex : t = RootedTree.vertex
  · subst h_vertex
    -- Goal reduces to: -(f vertex) = -(g vertex)
    simp only [if_pos rfl]
    rw [h_closed RootedTree.vertex (le_refl _)]
  by_cases h_cherry : t = RootedTree.cherry
  · subst h_cherry
    -- Goal reduces to: (f vertex)^2 - f cherry = (g vertex)^2 - g cherry
    simp only [if_neg h_vertex, if_pos rfl]
    -- vertex.order = 1 ≤ cherry.order = 2; cherry.order = 2 ≤ cherry.order
    have hv : f RootedTree.vertex = g RootedTree.vertex :=
      h_closed RootedTree.vertex (by decide)
    have hc : f RootedTree.cherry = g RootedTree.cherry :=
      h_closed RootedTree.cherry (le_refl _)
    rw [hv, hc]
  by_cases h_broom : t = RootedTree.broom₃
  · subst h_broom
    -- Goal reduces to: -(f vertex)^3 + 2·f vertex·f cherry - f broom₃ = ... (same with g)
    simp only [if_neg h_vertex, if_neg h_cherry, if_pos rfl]
    have hv : f RootedTree.vertex = g RootedTree.vertex :=
      h_closed RootedTree.vertex (by decide)
    have hc : f RootedTree.cherry = g RootedTree.cherry :=
      h_closed RootedTree.cherry (by decide)
    have hb : f RootedTree.broom₃ = g RootedTree.broom₃ :=
      h_closed RootedTree.broom₃ (le_refl _)
    rw [hv, hc, hb]
  by_cases h_mkCherry : t = OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]
  · subst h_mkCherry
    -- Goal reduces to: -(f vertex)^3 + 2·f vertex·f cherry - f (mk [cherry]) = ... (same with g)
    simp only [if_neg h_vertex, if_neg h_cherry, if_neg h_broom, if_pos rfl]
    have hv : f RootedTree.vertex = g RootedTree.vertex :=
      h_closed RootedTree.vertex (by decide)
    have hc : f RootedTree.cherry = g RootedTree.cherry :=
      h_closed RootedTree.cherry (by decide)
    have hm : f (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry])
            = g (OpenMath.Chapter3.Section310.RootedTree.mk [RootedTree.cherry]) :=
      h_closed _ (le_refl _)
    rw [hv, hc, hm]
  -- Default: t is none of the four matched trees, both sides = 0
  · simp only [if_neg h_vertex, if_neg h_cherry, if_neg h_broom, if_neg h_mkCherry]
```

### Key tactics

- **`by_cases h : t = <tree>` then `subst h`**: standard pattern for case-splitting
  on a tree equality. After `subst`, `t` is replaced literally throughout the goal.
- **`simp only [if_neg h₁, if_neg h₂, ..., if_pos rfl]`**: reduces the nested if-then-else
  to the matched branch's RHS. Use the disequality hypotheses gathered from earlier
  `by_cases` to discharge the `if_neg`s; `if_pos rfl` discharges the matched branch.
- **`h_closed <tree> (proof of tree.order ≤ t.order)`**: extracts the per-tree equality.
  Use `le_refl _` for the matched tree itself, and `by decide` (or `Nat.le_succ_of_le`
  chains) for strict subtrees.
- **`rw [hv, hc, ...]`**: substitutes the per-tree equalities to identify the two
  sides of the goal.

### Likely fallbacks if the sketch stalls

1. **`by_cases` motive issues** (R1): if `subst` fails because the equality is
   in the wrong direction or because of decidable-eq elaboration issues, try
   `cases h` or `rcases h with rfl`. Memory note
   `feedback_indexed_inductive_cases_disjoint.md` flags `cases` as the robust
   primitive for indexed-inductive equality.

2. **`by decide` slow at `(mk [cherry]).order ≤ (mk [cherry]).order`** (R2):
   replace with `le_refl _`. The slow case is usually only when comparing
   different trees; same-tree comparison is `le_refl _`.

3. **`simp only [if_neg ...]` doesn't fire** (R3): the if-then-else might be
   inside a coercion or under a definitional binder. Replace `simp only` with
   explicit `rw [if_neg h_vertex]` calls in sequence. If even `rw` doesn't fire,
   the issue is the `Decidable.decide` instance disagreeing with the
   `by_cases` witness; reformulate using `if h : t = ... then ... else ...` form
   via `dif_pos`/`dif_neg`.

4. **Name resolution on `mk [cherry]`** (R4): the cycle 374 Discovery #1 noted
   that `RootedTree.mk [...]` at the top level resolves to Mathlib's
   `_root_.RootedTree.mk` instead of `OpenMath.Chapter3.Section310.RootedTree.mk`.
   Use the fully qualified name `OpenMath.Chapter3.Section310.RootedTree.mk [...]`,
   matching the convention at line 2774+ of `Section422.lean`. This already
   applies in `inversePolynomial`'s definition, so the `by_cases` and `subst`
   must reference the fully qualified form.

## §E Verification (after the ship lands)

1. `lake env lean OpenMath/Chapter4/Section422.lean` — should exit clean,
   with only the pre-existing cycle 365 grandfathered sorry warning at
   line 2272.

2. `grep -c sorry OpenMath/Chapter4/Section422.lean` — should return `5`
   (unchanged from HEAD: 1 actual code sorry + 4 docstring mentions).

3. `lake build OpenMath.Chapter4.Section422` — should rebuild clean.

4. `#print axioms inversePolynomial_eq_of_subtree_agreement` via a
   temporary axiom-check file — must return `[propext, Classical.choice,
   Quot.sound]` only. **No `sorryAx` permitted.** If `sorryAx` appears,
   the proof has an undischarged sorry somewhere.

5. Pre-existing cycle 374/375 theorems should still be axiom-clean (this
   ship only adds; it does not modify the existing infrastructure).

## §F Non-vacuity (stretch, optional)

If the main theorem ships in well under the LOC budget, append 2–3
example witnesses exercising the theorem on the four matched trees with
explicit `f` and `g` choices (e.g. `f := fun _ => 1`, `g := fun _ => 1`)
to confirm the theorem fires cleanly. These should each close by
`apply inversePolynomial_eq_of_subtree_agreement; intro s _; rfl`.

This is optional per the cycle 375 worker's experience (the cycle 374
calibration examples already provide downstream consumer evidence).

## §G LOC budget and abort threshold

- **Target**: 50–90 LOC including docstring.
- **Soft ceiling**: 130 LOC. If approaching, audit whether the four-way
  case split is being inflated by repeated `have` bindings; consider
  extracting a single `have h_at_all_lower : ∀ s, s.order ≤ t.order → f s = g s
  := h_closed` shorthand to avoid restating the hypothesis in each branch.
- **Hard ceiling / abort**: 200 LOC. If the proof exceeds 200 LOC the
  recipe has stalled; ship whatever closes axiom-clean (even a
  one-tree-only specialised lemma) and file a sub-issue documenting the
  obstacle. **Do NOT introduce `sorry` to hit the target.**

## §H Faithfulness check (worker performs after ship)

`inversePolynomial_eq_of_subtree_agreement` is **internal infrastructure**
for the multi-cycle `def:422B` formalization (Sub-lemma A → Sub-lemma B →
`def:422B` chain). It is not a textbook-named concept; no individual
`formalization_data` entity exists. Its role is the Phase γ deliverable
promised by the cycle 373 scoping doc §5 and explicitly called for by
cycle 375's "Suggested next approach" §B.

Per the CLAUDE.md pre-commit checklist:
- **Tautology check**: the conclusion (`inversePolynomial t f =
  inversePolynomial t g`) does not appear verbatim as a hypothesis.
- **Identity check**: the proof is a four-way case split, not a single
  `exact h_closed _`; it materially uses the per-tree closed-form
  structure of `inversePolynomial`.
- **Hypothesis strength check**: the `h_closed` form is the cycle 365
  closed-subtree form (`s.order ≤ t.order`), the weakest sufficient
  hypothesis for the eventual Phase D.3.d consumer. Strict-subtree
  agreement (`s.order < t.order`) would be the "stretch" stronger
  variant; the closed-subtree form is the right ship per scoping doc §5.
- **Absent theorem check**: no promised content references; the proof
  is self-contained.

## §I Why this is the right cycle 376 target

Per the cycle 375 worker's task results §"Suggested next approach":

> **Recommended cycle 376 plan**: **Option B (Phase γ)**. Given Discovery
> #3's "shorter than Phase β.1" estimate, Phase γ is the highest-leverage
> single-cycle deliverable.

And from Discovery #3:

> **Phase γ feasibility check**: `inversePolynomial` being a pattern match
> (not a recursion) means `inversePolynomial_eq_of_subtree_agreement`
> (Phase γ in the issue plan §5) reduces to four trivial case splits:
> each matched closed form's RHS depends only on `f` at strict subtrees
> of the matched tree (by inspection of the four matched closed forms).
> This is shorter than Phase β.1 itself, confirming the issue plan §I
> cycle 376 outlook estimate.

The scoping doc §5 phase table projects Phase γ at ~50–100 LOC across
one cycle. Combined with cycle 374's Phase α.1 (pattern-match definition)
and cycle 375's Phase β.1 (four per-tree bridges), Phase γ completes the
"closed-form polynomial sidesteps the cycle 366 heterogeneity obstruction"
infrastructure for the four small trees. Subsequent cycles (377+) can
then either extend the ladder to more trees (Phase α.2 + Phase β.2)
or — if the four matched trees are sufficient for the eventual Phase ε
closure of the cycle 365 grandfathered sorry — proceed directly to
Phase D.3.d (`underlyingOneStepMethod_aux` recursion).

## §J Post-cycle housekeeping

After the ship lands axiom-clean:

1. **Append a Phase γ update** to `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md`
   §10 (similar in form to the cycle 374 and cycle 375 update entries
   already in §10.3 and §10.4). Document:
   - The shipped theorem name and signature.
   - Confirmation that the four-way case split worked as predicted by
     Discovery #3 of cycle 375.
   - The §422 streak count update (40 substantive + 1 doc → 41
     substantive + 1 doc).

2. **`lean_status.json`**: `def:422B` row stays `partial`. Phase γ is one
   more piece of the multi-phase chain; no status promotion.

3. **`plan.md`**: no row change needed (`def:422B` already at `[~]`).

4. **`task_results/cycle_376.md`**: standard sections per CLAUDE.md
   template. Document any discoveries (e.g. if the recipe needed
   adjustments not anticipated in §D's sketch above).

## §K If Phase γ stalls (graceful degradation)

If the four-way case split proves intractable in a single cycle:

1. **Ship a single-tree specialised lemma first** (e.g. just the `vertex`
   case as `inversePolynomial_vertex_eq_of_subtree_agreement`). This
   axiom-cleanly delivers infrastructure even if the four-way packaging
   fails.

2. **File a sub-issue** at `.prover-state/issues/phase_gamma_obstacle.md`
   documenting the specific case that stalled and the recovery plan.

3. **Pivot to Option A (Phase α.2)** as a cycle 376 fallback: extend
   `inversePolynomial` with three more pattern-match branches for
   `bushy`/`mk [broom₃]`/`mk [vertex, cherry]`. This is mechanical
   extension of the cycle 374 template (per cycle 375 Option A) and is
   guaranteed to ship axiom-clean if attempted.

The streak preservation rule applies: **either ship axiom-clean or ship
nothing**. Do not introduce sorries to meet the deliverable bar.
