# Cycle 604 Results

## Worked on

Pivoted off the depth-by-depth associativity ladder per strategy.
Created `OpenMath/ButcherGroup/Section386Aug/CutAssoc.lean` and
added the umbrella import in `OpenMath/ButcherGroup.lean`.

## Approach

1. **Verified the actual `cutAggregate` reductions before submitting.**
   The strategy's candidate sanity values for `cutAggregate_leaf` and
   `cutAggregate_node_nil` were stated tentatively. Walking the
   definitions:
   - `BTree.leaf.innerCut α = [(some leaf, 1), (none, α leaf)]`, so
     `cutAggregate α F leaf = 1 * F leaf = F leaf`.
   - `(BTree.node []).innerCut α = [(none, α (node [])), (some (node []), 1)]`,
     so `cutAggregate α F (node []) = F (node [])`.
   The strategy's guesses (`α leaf * F (node [])` and `0`) were both
   wrong; landed the correct shapes instead, as the strategy
   explicitly authorised.

2. **Bridge `bSeriesConvAug_eq_cutAggregate` simplified to**
   `bSeriesConvAug α β τ = cutAggregate α.toFun β.toFun τ + α.toFun τ * β.emptyVal`.
   The `β.toFun τ` term that appeared in the strategy's candidate is
   already inside `cutAggregate` (it is the trivial-trunk cut, weight
   `1`, contributing `F τ`). Adding it back would double-count.
   Proved sorry-free via two helpers:
   - `list_aug_split` (induction on the cut list): augmented sum =
     proper-cut sum + `e * (none-branch sum)`.
   - `sum_none_innerCut`: the only `none` entry in `τ.innerCut α` is
     the full-prune `(none, α τ)`, so the none-branch sum is `α τ`.
   The proof of `sum_none_innerCut` mirrors the existing pattern in
   `bSeriesConvAug_innerForest_cons` (Section386Aug.lean:935-958).

3. **Headline `cutAggregate_bSeriesConvAug` shape pinned to**
   ```
   cutAggregate (fun t => bSeriesConvAug α β t) F c
     = cutAggregate α.toFun (fun t => cutAggregate β.toFun F t) c
   ```
   under `β.IsUnital`. This matches the cut-associativity identity
   from the obstruction issue (lines 76–84) directly: the LHS is
   `Σ_{(some s, w) ∈ c.innerCut (αβ)} w * F s` and the RHS is the
   double aggregate `Σ_{(some t, w_e) ∈ c.innerCut α} w_e *
   Σ_{(some s, w_f) ∈ t.innerCut β} w_f * F s`.

   The strategy's candidate had an extra `+ cutAggregate β.toFun F c`
   tail term, which fails at `c = leaf` (it gives `2 * F leaf`
   vs the LHS's `F leaf`). Removed.

4. **Three sanity cases close sorry-free:**
   - `_leaf` and `_node_nil`: both sides reduce to `F leaf` /
     `F (node [])` via the `@[simp]` base lemmas.
   - `_node_singleton_leaf`: the unitality hypothesis `β.emptyVal = 1`
     collapses the `α.toFun leaf * β.emptyVal` correction in the LHS,
     leaving `F (node [leaf]) + (β leaf + α leaf) * F (node [])` on
     both sides. Closed by `simp only` + `ring`.

## Result

SUCCESS. `OpenMath/ButcherGroup/Section386Aug/CutAssoc.lean` compiles
with **exactly one** sorry (the headline `cutAggregate_bSeriesConvAug`,
as authorised by the strategy). Full `lake build` passes; the
umbrella `OpenMath.ButcherGroup` re-exposes the new module.

## Dead ends

- First pass at the bridge used `unfold bSeriesConvAug cutAggregate`
  followed by direct `rw [list_aug_split ...]`, but the `rw` failed
  to unify the `match`-binder names against the elaborator's choice
  of `trunk`. Worked around by inserting an explicit `show` to fix
  the goal to the exact lemma shape before rewriting.

- Initial draft of the singleton-leaf sanity case used a long
  `rw` chain including `cutAggregate_leaf`. After the `simp only`
  with the other `cutAggregate_*` lemmas, the `cutAggregate_leaf`
  rewrite no longer fired (no remaining occurrences). Removed it.

## Discovery

- The `cutAggregate` definition as written (proper-cut filterMap, no
  trivial-cut subtraction) **already includes** the trivial-trunk
  contribution `F τ`. So `cutAggregate` is closer to "all cuts that
  keep a root" than to "cuts that strictly subdivide". This makes
  the bridge to `bSeriesConvAug` clean — the only correction needed
  is the full-prune `α τ * β.emptyVal`.

- The cut-associativity identity, restated in the cleaner
  `cutAggregate` form, is **purely structural**: it says that the
  proper-cut Hopf coproduct co-associates after one substitutes
  `α * β` for the cut-weight function. The unitality of `β` is
  load-bearing because the LHS sees `bSeriesConvAug α β t` for
  intermediate trunks, which contains a `β.emptyVal`-weighted full
  prune that the RHS double aggregate does not see.

## Suggested next approach

The headline `cutAggregate_bSeriesConvAug` should close by induction
on `c`:
- base `c = leaf`, `c = node []`, `c = node [leaf]`: already
  available as the three sanity lemmas.
- inductive step on `c = node children`: expand
  `(node children).innerCut (bSeriesConvAug α β)` via `innerCut_node`,
  then expand each "keep-root" trunk's contribution by induction on
  `BTree.innerCutForest children`. Each forest entry's cut weight
  product is a product over child contributions, where each child
  contribution is `bSeriesConvAug α β`-cut of that child. Apply the
  IH at each child to convert into a double aggregate through `α`
  then `β`, then re-collect as the outer `α` cut of `node children`.

The cleanest form is likely a mutually recursive pair of lemmas
indexed on `BTree` and on `List BTree` (matching the `innerCut` /
`innerCutForest` mutual recursion). Estimated 200-400 lines.

Once that headline closes, the parametric
`forestSum_assoc_children_order_le p` follows immediately by the
algebra walk in `section386aug_strong_induction_obstruction.md`,
collapsing the entire `mul_assoc_at_node_depth_<k>_children` ladder.

## File-size status

- `Section386Aug/CutAssoc.lean`: 174 lines (new). Well under cap.
- `ButcherGroup.lean`: 2969 lines (was 2968; one new import line).
