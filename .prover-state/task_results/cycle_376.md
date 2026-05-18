# Cycle 376 Results

## Worked on

§422 Sub-lemma A Phase γ — closed-subtree-agreement theorem for the
cycle 374 pattern-match definition `inversePolynomial`. Single new
public theorem `inversePolynomial_eq_of_subtree_agreement` appended
to `OpenMath/Chapter4/Section422.lean` after cycle 375's aggregator
`elementaryWeightQ_phi_inv_eq_inversePolynomial_on_ladder`.

## Approach

Followed the cycle 376 strategy §D recipe verbatim. Key steps:

1. Verified the cycle 374 `inversePolynomial` definition still
   matches the four-branch nested if-then-else over
   `{vertex, cherry, broom₃, mk [cherry]}` with `0` default
   (file lines 4234–4248).

2. Wrote the four-way `by_cases h_<tree> : t = <tree>` case split.
   After each `subst h_<tree>`, the goal reduces (via
   `if_neg ... if_pos rfl` rewrites discharged from the prior-case
   inequalities) to an arithmetic identity in `f` and `g`
   evaluated at the four matched trees, plus the matched tree
   itself. Per-tree `h_closed` invocations identify the `f` and
   `g` evaluations, after which `rw` closes each branch.

3. Default branch (`t` outside the ladder) closes by `if_neg`
   discharges on both sides yielding `0 = 0`, which `rw` does
   reflexively.

4. Built `OpenMath.Chapter4.Section422` via `lake build` to refresh
   the `.olean` (the cycle-355 NVMe toolchain handles this in ~4
   minutes), then ran `#print axioms` on the new theorem via a
   temporary file `OpenMath/AxiomCheck376.lean` imported into the
   built target.

## Result

**SUCCESS — Phase γ shipped axiom-clean.**

`inversePolynomial_eq_of_subtree_agreement` compiles, file diagnostics
show only the pre-existing cycle 365 grandfathered sorry warning at
line 2272 (now 2272 because the new theorem is appended after the
existing public ladder), and `#print axioms` returns
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

Sorry count: `grep -c sorry OpenMath/Chapter4/Section422.lean = 5`
(4 docstring mentions + 1 actual code sorry at line 2279) —
unchanged from HEAD.

Axiom-clean streak: 40 substantive + 1 doc → **41 substantive +
1 doc**.

## Faithfulness check

For the one new theorem introduced this cycle:

- **Entity ID and textbook statement**:
  `inversePolynomial_eq_of_subtree_agreement` is internal infrastructure
  for the multi-cycle `def:422B` (Sub-lemma A → Sub-lemma B → `def:422B`)
  formalization chain. **No individual `formalization_data` entity
  exists** — this is the Phase γ deliverable promised by the
  cycle 373 scoping doc §5 and explicitly called for by cycle 375's
  task-results "Suggested next approach". The role is to provide the
  closed-subtree-agreement helper for the eventual Phase D.3.d
  (`underlyingOneStepMethod_aux` recursion) consumer.

- **Lean statement captures**: same content as the Phase γ
  specification in §6.3 of the scoping doc. The hypothesis is
  closed-subtree (`s.order ≤ t.order`), matching the cycle 365
  scoping-doc update (the form is strictly weaker than strict-
  subtree and is the weakest sufficient hypothesis given that the
  matched closed forms reference `f t` itself — e.g. `-f cherry`
  in the cherry branch).

- **Tautology check**: the conclusion
  `inversePolynomial t f = inversePolynomial t g` does NOT appear
  verbatim as a hypothesis. `h_closed` is a per-subtree equality of
  `f` and `g`, not of `inversePolynomial t f` and `inversePolynomial
  t g`.

- **Identity check**: the proof is a four-way case split + default
  branch, not a single `exact h_closed _`. It materially uses the
  closed-form polynomial structure of `inversePolynomial` at each
  matched branch.

- **Hypothesis strength check**: `h_closed` is the closed-subtree
  form (`s.order ≤ t.order`). The strict-subtree form
  (`s.order < t.order`) would NOT suffice because the matched closed
  forms (cycles 367, 368, 369) reference `f t` itself
  (e.g. `f cherry` in the cherry branch as the subtracted term).
  No hypothesis is stronger than the textbook requires.

- **Absent theorem check**: the proof is self-contained; no
  forward-referenced lemmas. The cycles 341, 367, 368, 369
  closed-form theorems are NOT invoked — Phase γ operates at the
  level of `inversePolynomial` (a definitional pattern match), not
  at the level of the bridge theorems.

## Dead ends

None during execution. The cycle 375 Discovery #3 prediction —
that the four-way case split would be trivial given the cycle 374
pattern-match shape — held verbatim. The only minor surprise was
that `lake env lean <file>` does NOT update the `.olean` (it just
runs the file fresh), so I had to invoke `lake build
OpenMath.Chapter4.Section422` to refresh the cached `.olean` before
the `#print axioms` check in a downstream file could resolve the
new identifier. Going forward, the axiom check pattern is:
`lake build <target>; lake env lean <axiom_check_file>`.

## Discovery

1. **`lake env lean` does not refresh `.olean`**: `lake env lean
   OpenMath/Foo.lean` runs the file in-process but does NOT update
   `.lake/build/lib/lean/OpenMath/Foo.olean`. For downstream axiom
   checks via `import OpenMath.Foo`, you must run `lake build
   OpenMath.Foo` first. This is the canonical axiom-check workflow
   confirmed empirically this cycle:

   ```
   lake build OpenMath.Chapter4.Section422   # ~4 min, refreshes .olean
   lake env lean OpenMath/AxiomCheck.lean    # imports the fresh .olean
   ```

2. **`by decide` discharges `RootedTree.order` comparisons**: thanks
   to the cycle 343 structurally-recursive `RootedTree.order`, all
   per-tree closed-subtree-agreement order-comparisons (e.g.
   `RootedTree.vertex.order ≤ RootedTree.cherry.order`,
   `RootedTree.cherry.order ≤ RootedTree.broom₃.order`,
   `RootedTree.vertex.order ≤
     (OpenMath.Chapter3.Section310.RootedTree.mk
       [RootedTree.cherry]).order`)
   discharge by `by decide`. Same-tree reflexivity uses `le_refl _`
   to avoid even that overhead.

3. **`unfold + rw [if_*]` works symmetrically on both sides**: after
   `unfold inversePolynomial` and `subst h_<tree>`, the goal has
   the same nested if-then-else expression appearing on both LHS
   (with `f`) and RHS (with `g`). The `rw [if_neg ..., if_pos rfl]`
   chain rewrites both occurrences in a single `rw` call — no need
   to split into per-side tactics. This kept the per-case LOC tight.

4. **Phase γ LOC came in at ~110 LOC** (the four-way case split has
   a verbose `mk [cherry]` case due to the fully-qualified name
   needing repetition in each `if_neg` proof). Well under the
   strategy's 130 LOC soft ceiling and the 200 LOC hard ceiling.

## Suggested next approach

**Cycle 377 candidate options**:

1. **Option A (Phase α.2 + β.2 extension)**: extend
   `inversePolynomial` with three more pattern-match branches
   (`bushy`, `mk [broom₃]`, `mk [vertex, cherry]`) per cycles
   370–372, and ship the corresponding three Phase β.2 per-tree
   bridges + a refreshed aggregator. **Cost**: ~150 LOC
   (3 calibration witnesses + 3 bridges + aggregator update +
   extended Phase γ case split). **Leverage**: more closed forms
   available for Phase ε (closing the cycle 365 grandfathered
   sorry).

2. **Option B (proceed to Phase δ)**: with Phase γ now in place,
   attempt the `powRep`-based extension to general `m`
   (Phase δ in the scoping doc §6.4). This is the closer-to-
   headline option but is multi-cycle (the scoping doc estimates
   1 cycle with possible spillover; the §387 D-operator
   integration may surface complications).

3. **Option C (audit Phase ε feasibility)**: write a single-file
   sketch attempting to close the cycle 365 grandfathered sorry
   at line 2279 using the Phases α.1, β.1, γ tower. If the proof
   goes through on the four-tree ladder, ship Phase ε directly
   and the streak hits 42 substantive cycles. If it requires
   Phase α.2 / δ infrastructure first, document the obstacle as
   a sub-issue and pivot.

**Recommended**: **Option C (Phase ε feasibility audit)** —
this is the highest-leverage next step. With Phase γ shipped,
the §6.5 scoping doc's outline of Phase ε is now realizable in
principle, and a feasibility audit either closes the headline
(maximum leverage) or surfaces the next concrete obstacle
(constraining Option A vs B). Option A is fallback if Phase ε
needs more tree-ladder coverage; Option B is the deep-dive
research path.
