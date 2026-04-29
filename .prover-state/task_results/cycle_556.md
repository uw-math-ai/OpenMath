# Cycle 556 Results

## Worked on
§384 three-way mixed leaf / singleton-leaf / double-leaf product slice:
`BTree.node (List.replicate a BTree.leaf ++
  List.replicate b (BTree.node [BTree.leaf]) ++
  List.replicate c (BTree.node [BTree.leaf, BTree.leaf]))`.

This composes the simple cut/keep machinery on the leaf axis with the
cycle 547 singleton-leaf machinery (`Fin 2` inner cut/keep) and the
cycle 553 double-leaf machinery (`Fin 3` inner choice via
`doubleLeafChoiceCoef`).

## Approach
Followed the strategy's Step 1 → Step 7 plan with a five-level expansion:
- root powerset `S_l ⊆ Fin a` (which leaves are cut at the root)
- root powerset `S_sl ⊆ Fin b` (which singleton-leaves are cut at the
  root)
- root powerset `S_dl ⊆ Fin c` (which double-leaves are cut at the
  root)
- inner powerset `T ⊆ S_slᶜ` over `Fin b` (per kept singleton-leaf, the
  `Fin 2` cut/keep)
- inner choice `χ : Fin (c - S_dl.card) → Fin 3` (per kept double-leaf,
  the `Fin 3` choice from cycle 553)

The cut-form summand tree shape is
```
BTree.node
  (List.replicate ((a - S_l.card) + T.card + cnt0 χ) BTree.leaf
    ++ List.replicate ((S_slᶜ.card - T.card) + cnt1 χ) (BTree.node [BTree.leaf])
    ++ List.replicate (cnt2 χ) (BTree.node [BTree.leaf, BTree.leaf]))
```
which reuses
`bSeries_node_replicate_leaf_append_replicate_singleton_leaf_append_replicate_double_leaf`
and the cycle 554 polynomial expand directly.

The polynomial expand factors as `pow_add_eq_powerset X R a` (for the
new leaf axis) followed by cycle 554's
`mixed_singleton_leaf_double_leaf_stage_polynomial_expand X Y_sl Y_dl R C D b c`,
with the resulting `R^(a - S_l.card) * R^…` collapsed by
`rw [← pow_add, ← Nat.add_assoc]`.

Manual closure only — no Aristotle scaffolds were submitted, matching
the strategy's instruction.

## Result
SUCCESS.

Landed in `OpenMath/ButcherGroup/Section384SlicesMixed.lean`:
- `convAt_node_mixed_leaf_singleton_leaf_double_leaf_at_i_eq`
- `mixed_leaf_singleton_leaf_double_leaf_stage_polynomial_expand`
- `weighted_mixed_leaf_singleton_leaf_double_leaf_stage_sum_expand`
- `bWeighted_convAt_node_mixed_leaf_singleton_leaf_double_leaf_cut_eq`
- `ButcherProduct.bSeries_node_mixed_leaf_singleton_leaf_double_leaf_cut_eq`

Landed in `OpenMath/ButcherGroup.lean`:
- `QuotEquiv.bSeriesHom_product_node_mixed_leaf_singleton_leaf_double_leaf`
  (`Quotient.inductionOn₂` lift)
- `IsG1Equiv.product_congr_node_mixed_leaf_singleton_leaf_double_leaf`
  (hypothesis `(BTree.node ...).order ≤ p`, which unfolds to
   `1 + a + 2*b + 3*c ≤ p` via the existing
   `order_node_replicate_leaf_append_replicate_singleton_leaf_append_replicate_double_leaf`).

`lake build` is green; no live `sorry`s in `OpenMath/`.

File sizes after this cycle:
- `Section384SlicesMixed.lean`: 2546 lines
- `ButcherGroup.lean`: 2415 lines

Both under the 3000-line hard cap.

## Dead ends
The first attempt at the per-stage proof used a helper-based `hLa /
hLb / hLc` extraction (length-aware accessors for each segment of
`replicate a leaf ++ replicate b … ++ replicate c …`) that ran into an
`omega` failure because `(a + b) + k < L.length` wasn't visible at the
right binder depth. Switched to cycle 554's inline pattern: prove
`hL : L = …` once and let `simp [hL, List.get_eq_getElem,
List.getElem_append, List.getElem_replicate, List.length_replicate]
<;> split_ifs with h1 h2 <;> [omega; omega; rfl]` close each factor.

A separate hiccup was the `simp`-driven re-association of
`(replicate a leaf ++ replicate b …) ++ replicate c …` into the
right-associated normal form — once `simp` re-associates, explicit
`List.getElem_append_right` rewrites stop matching. Using the unified
`List.getElem_append` (the if-then-else version) plus `split_ifs`
sidesteps the issue.

A third hiccup: the QuotEquiv lift initially failed with "Unknown
constant" because the `Section384SlicesMixed.lean` `.olean` had not yet
been written by `lake env lean` for this session — `lake build
OpenMath.ButcherGroup.Section384SlicesMixed` produced the artifact and
the umbrella file built clean afterwards.

## Discovery
The order arithmetic for this family is `1 + a + 2*b + 3*c`. The
summand tree's order bound
`1 + ((a - S_l.card) + T.card + cnt0) + 2*((S_slᶜ.card - T.card) + cnt1)
  + 3*cnt2`
collapses against `cnt0 + cnt1 + cnt2 ≤ c`, `T.card ≤ S_slᶜ.card ≤ b`,
and `S_l.card ≤ a` to `≤ 1 + a + 2*b + 3*c`, so a single `omega` after
`doubleLeafChoiceCount_sum` closes the G1 ordering hypothesis.

For the leaf axis itself, the rewriting is unconditional: `BTree.leaf`
has order 1, and the order hypothesis `1 + a + 2*b + 3*c ≤ p` always
implies `1 ≤ p`. So a single up-front `rw [hleaf]` rewrites every
occurrence of `q.bSeriesHom BTree.leaf` (including those inside
`doubleLeafChoiceCoef` and inside the kept-singleton-leaf inner power
factor `(q.leaf)^T.card`) before we step into the triple powerset
sum, which simplifies the per-S_l/S_sl/S_dl reasoning.

The singleton-leaf and double-leaf power factors at the root still need
`by_cases hzero` on the cardinality, since their per-tree orders (2 and
3) only fit under `p` when the corresponding root cardinality is
positive.

## Suggested next approach
The natural continuation is to extend the §384 mixed library along
either of two axes:
- `(node [leaf, leaf], node [leaf, leaf, leaf])` — pair the cycle 553
  `Fin 3` expansion with a `Fin 4` expansion for triple-leaf children.
- A four-axis `(leaf, node [leaf], node [leaf, leaf], node [leaf, leaf,
  leaf])` family — one more recursion level on top of today's three
  axes.

Either reuses today's five-level expansion pattern; the new ingredient
is the `Fin k` choice helper for the larger keep-side. Cycle 553's
`doubleLeafChoiceCoef / doubleLeafChoiceCount` pair generalises directly
to `Fin (k+1)` with a `(k+1)`-fold sum.
