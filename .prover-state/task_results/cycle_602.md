# Cycle 602 Results

## Worked on
Butcher Section 386 depth-3 unital augmented associativity headline in
`OpenMath/ButcherGroup/Section386Aug.lean`:

- `private theorem forestSum_assoc_depth_three`
- `theorem mul_assoc_at_node_depth_three_children`

## Approach
Sorry-first: added both theorem statements with `sorry` placeholders
and verified the file compiles. Then extracted two new top-level
private aggregate-shift helpers (mirroring cycle 601's `shift_pair_agg`
/ `shift_singleton_node_singleton_agg`):

- `shift_one_agg` (depth-1 head shape, `m.order ≤ 1`)
- `shift_node_singleton_agg` (singleton head shape, `node [d]` with
  `d.order ≤ 1`)

These are top-level versions of the `have shift_depth_one_agg` and
`have shift_singleton_agg` lemmas inlined inside cycle 599's
`forestSum_assoc_depth_two`, parameterised by an explicit
tail-IH `hih`. The cycle 599 inline copies are left untouched.

Then added four top-level head-case helpers, one per cohort of
shapes from `BTree.order_le_three_iff`:

- `forestSum_assoc_three_one_head` (head = `leaf` or `node []`)
- `forestSum_assoc_three_singleton_head` (head = `node [d]`,
  `d.order ≤ 1`)
- `forestSum_assoc_three_pair_head` (head = `node [a, b]`, both
  `a.order ≤ 1`, `b.order ≤ 1`)
- `forestSum_assoc_three_singleton_node_singleton_head`
  (head = `node [node [e]]`, `e.order ≤ 1`)

Each replays the cycle 599 `singleton_head_case` template:

1. compute `bSeriesConvAug α β` reductions for every relevant
   sub-tree of the head (`hgβ_*` family),
2. expand the cons via the matching `forestSum_cons_*_compact`
   recurrence three times (LHS twice, RHS once),
3. `change` the goal into a uniform shape with `bSeriesConvAug α β`
   factors on the LHS and `(⟨1, ...⟩ : AugSeries).shiftBy *` factors
   on the RHS,
4. substitute the `hgβ_*` rewrites and apply the relevant
   shift-aggregate lemmas (`shift_one_agg`, `shift_node_singleton_agg`,
   `shift_pair_agg`, `shift_singleton_node_singleton_agg`) on the RHS,
5. close with `linear_combination α.toFun (head) * hih_γ`.

`forestSum_assoc_depth_three` is then a short list induction over
`children` that dispatches the head via `BTree.order_le_three_iff`
into the four helpers (ten leaf cases collapsed into four cohorts).

`mul_assoc_at_node_depth_three_children` mirrors the cycle 599
`mul_assoc_at_node_depth_two_children` recipe verbatim: `bSeriesConvAug_node`
on both sides, substitute unitality of `β` and `γ`, take
`forestSum_assoc_depth_three` as `key`, and close with `linarith`.
The only delta from cycle 599 is one extra `simp only [forestSum] at
key` after the `rw [hγ', mul_one] at key` step, since
`forestSum_assoc_depth_three` is stated in `forestSum` form whereas
`forestSum_assoc_depth_two` was stated in the explicit unfolded form.

## Result
SUCCESS. Both theorems landed sorry-free.

Verification:

- `rg -n "sorry" OpenMath/ButcherGroup/Section386Aug.lean` returned no
  matches.
- `lake env lean OpenMath/ButcherGroup/Section386Aug.lean` exit 0.
- `lake build` exit 0 (8086 jobs).

File grew from 2427 → 3038 lines (delta +611 lines). Still well
under the 6000-line hard cap.

## Dead ends
First draft of `hgβ_pair` inside `forestSum_assoc_three_pair_head`
used `bSeriesConvAug_node α β [a, b]` and then tried to rewrite
`forestSum α.toFun β [a, b]`. The `bSeriesConvAug_node` lemma yields
the explicit unfolded form (not the `forestSum` abbreviation), so the
`forestSum_cons_depth_one_compact` rewrite did not match. Switched to
`bSeriesConvAug_node_cons_depth_one_expand_compact α β a ha [b]`
(which is already stated in `forestSum` form), then chained two
`forestSum_cons_depth_one_compact` rewrites to expand `[b]`, then
closed via `simp only [forestSum, BTree.innerCutForest, ...]; ring`.

Initial draft of `mul_assoc_at_node_depth_three_children` failed at
the closing `linarith` because the `key` produced by
`forestSum_assoc_depth_three` was in folded `forestSum` form whereas
the goal (after `bSeriesConvAug_node` rewrites) was in explicit
unfolded form. Adding `simp only [forestSum] at key` between
`rw [hγ', mul_one] at key` and the `show ...` step closed the gap.

## Discovery
The natural top-level layout of the depth-`d` ladder is:

- `shift_*_agg` lemmas, one per head shape that appears at depth ≤ d,
  parameterised by an explicit tail-IH `hih`.
- `forestSum_assoc_d_*_head` lemmas, one per cohort, each consuming
  the relevant `shift_*_agg` lemmas plus the `hih`.
- `forestSum_assoc_depth_d` as a thin list induction with head
  dispatch via `BTree.order_le_d_iff`.

This layout makes the cycle-by-cycle increment from depth `d` to
depth `d+1` surgical: only the new head cohort at depth `d+1`
introduces fresh `shift_*_agg` and `forestSum_assoc_d+1_*_head`
lemmas, while the older head cohorts reuse the existing top-level
agg-shift helpers verbatim by passing the new (depth-`d+1`)
tail-IH. The cycle 601 lemmas (`shift_pair_agg`,
`shift_singleton_node_singleton_agg`) already followed this pattern;
this cycle confirms the rest.

For depth 4 the next required head shapes are `node [a, b, c]` (with
each `a, b, c` of order ≤ 1), `node [a, b]` with one of `a, b` of
order ≤ 2, `node [node [a, b]]`, `node [node [node [d]]]`, and a few
others. By `BTree.order_le_four_iff`, we expect a dispatch with
roughly 25 leaf shapes grouped into ~8 cohorts.

## Suggested next approach
Plan cycle 603 either (a) adds `BTree.order_le_four_iff` plus the new
head-shape cohorts and depth-4 ladder rung, mirroring this cycle
exactly, or (b) attempts to abstract the four cohort head-case
templates into a generic `forestSum_assoc_head_via_agg` helper
parameterised by the head shape, the matching `forestSum_cons_*`
recurrence, the matching `shift_*_agg` family, and the `hgβ_*`
reductions. Option (b) would shrink the depth-`d` ladder per rung
from O(150 lines / cohort) to O(20–30 lines / cohort) and is the
clear next refactor. The mathematical content is identical; only the
template extraction is new.

If neither (a) nor (b) is desirable, an alternative is to start
attacking the generic `forestSum_assoc_children_order_le p` strong
induction again, but cycle 600 already documented why this stalls on
a Hopf-algebra-style cut associativity identity (see the relevant
issue file). The depth-by-depth ladder remains the agreed path.
