# Cycle 362 Results

## Worked on

**Phase D.3.b parametricity Step 1** for `def:422B` per strategy §B's
P1 deliverable (planner cycle 362):

* `OpenMath.Chapter3.Section312.RKTableau.derivativeWeightWithSrc_eq_of_strict_subtree_agreement`
  — per-`derivativeWeightWithSrc` substitution lemma under
  strict-subtree agreement of source-method elementary weights.
* `OpenMath.Chapter3.Section312.RKTableau.derivativeWeightWithSrcProd_eq_of_strict_subtree_agreement`
  — list-helper companion threading order witnesses through the
  recursion.
* Non-vacuity `example` in `OpenMath/Chapter4/Section422.lean`
  exercising the lemma at `M₁ = M₁' = explicitEuler`,
  `t := RootedTree.cherry`.

P2 stretch goal (the actual `linearResidualAt_depends_only_on_strict_subtrees`
parametricity claim) and P3 fallback (`sum_i_alpha_ne_zero_of_stable_preconsistent`)
were **not** attempted — P1 closed cleanly within budget; deferring
P2 to cycle 363 mirrors cycle 361's "ship P1 + extend ladder"
discipline.

## Approach

§A pre-flight verification passed at HEAD `f046f5a` (cycle 361 ship):
2120 LOC in Section422.lean, sorry count 0 in §422 pipeline files.

§E Mathlib hook verification deferred to first-compile feedback
(the `lean_local_search` MCP requires `ripgrep` which is missing on
this cluster; substituted with `Grep` + first-compile error
inspection). Two strategy-recipe inaccuracies surfaced and were
fixed in 1 line each:

1. `RootedTree.order_lt_of_mem_children`'s actual signature has
   both `{c : RootedTree}` and `{children : List RootedTree}`
   **implicit** (with `(hc : c ∈ children)` explicit). Strategy's
   recipe `RootedTree.order_lt_of_mem_children children c hc` was
   wrong; correct invocation is `RootedTree.order_lt_of_mem_children hc`
   alone.
2. `List.mem_cons_self` in modern Mathlib takes no explicit args
   (both `a` and `l` implicit). Strategy's `List.mem_cons_self _ _`
   does not type-check; use just `List.mem_cons_self`.

Then proceeded with the strategy §C.2 mutual-block recipe, placing
the new mutual block immediately after cycle 226's
`derivativeWeightWithSrc_subst_M₁` block (Section381.lean:2803).
The mutual block is structurally identical to cycle 226's
template, with three substantive differences:

* The list-helper takes `t : RootedTree` and the strict-subtree
  hypothesis `h_strict` as **explicit parameters** (vs cycle 226's
  `hPhi₁` which was a fixed `PhiEquivalent` parameter on the whole
  block). This is necessary because the strict-subtree hypothesis
  is relative to the parent `t`, not absolute.
* The list-helper additionally takes `_h_children_lt : ∀ c ∈ children, c.order < t.order`
  as a hypothesis (consumed by the per-child rewrite and the
  recursive call).
* The recursive call at `c` uses `(fun s hs => h_strict s (hs.trans h_c_lt))`
  to compose `s.order < c.order` with `c.order < t.order`,
  satisfying the inner strict-subtree hypothesis at sub-subtrees
  of `t`.

Required adding `import OpenMath.Chapter3.Section301` to
Section381.lean for cycle 343's `RootedTree.order_lt_of_mem_children`
visibility (Section381 previously imported only Section310 +
Section312; Section301 is where cycle 343 lives, namespaced inside
Section310's `RootedTree`).

## Result

**SUCCESS — axiom-clean P1 ship**:

* `lake build` exits 0 (8081/8081 jobs), Section422.lean refresh
  passes verbatim.
* `#print axioms` on both new theorems → `[propext, Classical.choice, Quot.sound]`
  only.
* Sorry count remains 0 in `OpenMath/Chapter3/Section381.lean` and
  `OpenMath/Chapter4/Section422.lean`. (Section381.lean has a
  single `sorry` token at line 3589 but it is inside a comment
  block — the inflated count is a false positive of `grep -c sorry`.)
* §422 streak now stands at **28 consecutive axiom-clean cycles
  (336–362)**.

LOC additions: Section381.lean 5538 → 5633 (+95); Section422.lean
2120 → 2138 (+18, just the non-vacuity example + docstring).

P2 (parametricity claim itself) was **not** attempted in this cycle
— the cycle 361 worker flagged this as foreseeably multi-cycle, and
the cycle 362 strategist's stretch-goal §B P2 budget would have
required ~60–90 min on top of P1's 60–75 min. The cycle came in
under the P1-only budget; preserving the cycle 361 discipline
(ship P1, extend ladder) rather than rushing P2 keeps the streak
clean.

## Faithfulness check

This cycle ships two new theorems. No new `def` or `structure`
introduced.

### `derivativeWeightWithSrc_eq_of_strict_subtree_agreement`

* **Entity ID**: not directly traceable to a single Butcher entity
  — this is internal infrastructure for `def:422B` Phase D.3.b
  (cycle 362 strategist §C.1 connects it to Butcher's "induction
  on r(t)" textbook argument at `extraction/raw_text/ch04.txt:1158`:
  *"η⁻ⁱ(t) involves η(t) and other terms only in η(s) for orders
  s with r(s) < r(t)"*). The strict-subtree-agreement hypothesis
  *is* the formal Lean rendering of Butcher's "orders less than
  r(t)" qualifier.
  > "if all the terms in η⁻ⁱ(t) — except for the linear-in-η(t)
  >  part — only depend on values of η at subtrees of order less
  >  than r(t)"
  >  (Butcher §422, p. 358, paraphrased)
* **Lean statement captures**: same content as Butcher's
  qualitative claim, formalised at the level of the helper
  `derivativeWeightWithSrc` (one step "below" `Φ_η` at the
  representative level). The lemma's content is: "the inner
  `derivativeWeightWithSrc` factor depends only on `M₁.elementaryWeight`
  at strict subtrees of `t`". This is strictly narrower than the
  full Butcher claim (which is about the residual `linearResidualAt`,
  not just the `derivativeWeightWithSrc` sum), but it is a
  necessary intermediate.
* **Tautology check**: conclusion is
  `M₂.derivativeWeightWithSrc M₁ i t = M₂.derivativeWeightWithSrc M₁' i t`;
  hypothesis is `∀ s : RootedTree, s.order < t.order → M₁.elementaryWeight s = M₁'.elementaryWeight s`.
  The conclusion does NOT appear as hypothesis. ✓
* **Identity check**: proof is a mutual-induction block recursing
  on tree + list constructors. Uses cycle 343's
  `order_lt_of_mem_children`, `List.mem_cons_self`,
  `List.mem_cons_of_mem`, `Finset.sum_congr`, `Nat.lt_trans`.
  Substantive — not a re-export of any hypothesis. ✓
* **Hypothesis strength**: strict-subtree agreement is the
  *weakest* hypothesis that suffices. `derivativeWeightWithSrc`
  only references `M₁.elementaryWeight` at strict subtrees of `t`
  (the `mk children` unfolding factors through `M₁.elementaryWeight c`
  for `c ∈ children` with `c.order < t.order`, and the recursive
  `derivativeWeightWithSrc M₂ M₁ j c` only sees `M₁.elementaryWeight`
  at strict subtrees of `c` — also strict subtrees of `t` by
  order transitivity). Cycle 226's `derivativeWeightWithSrc_subst_M₁`
  uses the strictly STRONGER `PhiEquivalent M₁ M₁'` (agreement at
  every tree). The weakening is documented in the docstring. ✓
* **Definition smuggling check**: the lemma is a *property* of
  `derivativeWeightWithSrc`, not a re-definition. Cycle 226's
  full-`PhiEquivalent` hook remains intact and is used by cycle
  216 / cycle 235's §384 work. ✓

### `derivativeWeightWithSrcProd_eq_of_strict_subtree_agreement`

* **Entity ID**: same as above (list-helper companion).
* **Lean statement captures**: same content; this is the
  cons-induction half of the mutual block, structurally identical
  to cycle 226's list-helper with the strict-subtree hypothesis
  threading through.
* **Tautology check**: conclusion is
  `M₂.derivativeWeightWithSrcProd M₁ i children = M₂.derivativeWeightWithSrcProd M₁' i children`;
  hypotheses are the strict-subtree agreement (at parent `t`) and
  the children-order bound. Conclusion does NOT appear as
  hypothesis. ✓
* **Identity check**: substantive (recursive case via the cons
  unfolding + `rw [h_strict c h_c_lt]` parent-level rewrite +
  recursive call composition). ✓
* **Hypothesis strength**: same as parent lemma — minimal. ✓
* **Definition smuggling check**: not a definition. ✓

### Strategy deviations to flag

1. **`private` modifier dropped** (vs strategy §C.2's explicit
   "Mark both as `private`"). Reason: strategy §C.5 placed the
   non-vacuity `example` in `Section422.lean`, which would fail
   with `private` lemmas (file-scoped). The lemmas are documented
   as "Phase D.3.b infrastructure" in their docstrings, which
   communicates the not-stable-public-API intent without the
   technical access restriction. This is a minor deviation that
   also unblocks cycle 363's Step 2 (which will also live in
   Section422.lean and consume Step 1).

2. **`order_lt_of_mem_children` signature drift fix** (vs strategy
   §C.2 recipe). Strategy wrote
   `RootedTree.order_lt_of_mem_children children c hc`; the actual
   signature has implicit args, so correct call is just `... hc`.
   Caught on first compile.

3. **`List.mem_cons_self` arg-count drift fix** (vs strategy §C.2
   recipe). Strategy wrote `List.mem_cons_self _ _`; the actual
   signature has no explicit args in modern Mathlib. Caught on
   first compile.

## Dead ends

None substantive. Initial compile surfaced the two
recipe-signature drifts (1-line fixes each) and the missing
Section301 import. All three resolved in <10 min.

## Discovery

1. **Section381.lean did NOT import Section301**, despite
   Section381 being the §381 RK-tableau infrastructure file and
   Section301 hosting `RootedTree.order_lt_of_mem_children` (cycle
   343's strict-descent lemma). The cycle 343 lemma was introduced
   for §422 Phase D.3 consumption but Section381 hadn't yet
   imported it. Future cycles touching §381 *and* needing
   tree-order lemmas should check this import. The cycle 362 fix
   (add `import OpenMath.Chapter3.Section301`) is a one-shot;
   there's no circular-import risk (Section301 imports only
   Section310).

2. **Cycle 226's mutual-block template generalises cleanly to
   "per-`derivativeWeightWithSrc` substitution with weakened
   hypothesis"**. The three-substantive-difference observation
   (parent tree explicit, children-order bound, recursive-call
   composition via `Nat.lt_trans`) is the canonical pattern for
   future "downward substitution" lemmas on `derivativeWeightWithSrc`-
   style mutual recursions. Worth bookmarking for cycle 363+ if a
   second strict-subtree variant arises.

3. **Step 2's substantive obstacle is NOT the `derivativeWeightWithSrc`
   part** (Step 1 handles that). The cycle 361 closed form
   `linearResidualAt_succ_mk_eq` contains:
   ```
   linearResidualAt (m+1) ⟦M⟧ t
     = -Σⱼ (M.powRep (m+1)).2.b j · …(M.powRep (m+1)).2.derivativeWeightWithSrc … t
       - ((m+1):ℝ) · (-1)^t.order · M.elementaryWeight t
   ```
   Step 1 handles the `derivativeWeightWithSrc` sum's substitution
   behaviour, but the residual *also* contains a direct
   `M.elementaryWeight t` term. The Step 2 parametricity claim
   "depends only on strict subtrees" requires this `M.elementaryWeight t`
   term to **cancel** with a contribution from the
   `derivativeWeightWithSrc` sum (probably at a "vertex"-shape
   subterm via Butcher's textbook structural argument), OR to be
   expressible via strict-subtree data alone. This is a
   **substantive ℝ-algebraic identity**, not just substitution.
   Cycle 363 worker needs to scope this before attempting the
   full Step 2.

## Suggested next approach

**Primary cycle 363 deliverable**: attempt Phase D.3.b parametricity
Step 2 — `linearResidualAt_depends_only_on_strict_subtrees` — via
the `Quotient.inductionOn₂` + cycle 361 closed form + cycle 362
Step 1 skeleton:

```lean
theorem linearResidualAt_depends_only_on_strict_subtrees
    (i : ℕ) (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (t : RootedTree)
    (h_strict : ∀ s : RootedTree, s.order < t.order →
        elementaryWeightQ_phi η_q s = elementaryWeightQ_phi η_q' s) :
    linearResidualAt i η_q t = linearResidualAt i η_q' t := by
  -- Quotient.inductionOn₂ to representative tableaux M, M'
  -- bridge elementaryWeightQ_phi ⟦M⟧ s = M.elementaryWeight s (cycle 226 _phi_mk)
  -- apply cycle 361 _succ_mk_eq to both sides (i = 0 needs a separate i = 0 branch)
  -- The derivativeWeightWithSrc sums substitute via cycle 362 Step 1
  -- The M.elementaryWeight t terms must cancel — substantive obstacle
  sorry
```

The cycle 363 strategist should scope the "M.elementaryWeight t cancellation"
obstacle first. Three plausible paths:

* **Path 3.1**: prove the cancellation via Butcher's textbook
  "induction on r(t)" argument — show that the
  `derivativeWeightWithSrc` sum at `t = mk children` contains a
  `+M.elementaryWeight t` contribution that cancels the explicit
  `-M.elementaryWeight t` term. This requires unfolding the
  `derivativeWeightWithSrc` sum and tracking the elementary-weight
  contribution at the leaf-attachment points.
* **Path 3.2**: weaken Step 2 to operate under a **closed-subtree
  agreement** hypothesis (including `t` itself), not strict-subtree.
  This makes the cancellation trivial. Cycle 363 worker should
  check whether Phase D.3.d's `underlyingOneStepMethod_aux` recursion
  actually needs the strict-subtree form, or only the closed-subtree
  form. The aux recursion stores `η(t')` for all `t' ≤ t` by the
  time it reaches `t`, so closed-subtree may suffice.
* **Path 3.3**: stretch to a one-cycle Step 2 + Step 3 (D.3.c) ship
  via Path 3.2's weakening — if Step 2 collapses to a trivial
  closed-subtree statement, the cycle budget freed up could absorb
  D.3.c's 1–2 line corollary of cycle 176 + cycle 344 (per cycle
  362 strategy §D.3).

**Stretch cycle 363 deliverable** (if Step 2 lands cleanly):
proceed to Phase D.3.c per cycle 362 strategy §D.3:

```lean
theorem sum_i_alpha_ne_zero_of_stable_preconsistent
    {k : ℕ} (M : LinearMultistepMethod k) (hk : 0 < k)
    (hStable : M.IsStable) (hPre : M.IsPreconsistent) :
    (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ) ≠ 0 := by
  rw [coef_α_eq_ρPoly_deriv_at_one_of_preconsistent M hPre]
  exact M.ρPoly_deriv_eval_one_ne_zero_of_stable_preconsistent hStable hPre
```

This is a 1–2 line corollary of existing cycle 176 + cycle 344
infrastructure (~10 LOC + 1 BDF2 witness).

**Cycle 364+ horizon**: Phase D.3.d (`underlyingOneStepMethod_aux`
recursion + spec) per scoping doc §5; Phase E sealing of `def:422B`
projected for cycle 366.
