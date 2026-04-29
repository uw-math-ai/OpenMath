# Cycle 554 Results

## Worked on
§384 mixed singleton-leaf / double-leaf product slice:
`BTree.node (List.replicate a (BTree.node [BTree.leaf]) ++
  List.replicate b (BTree.node [BTree.leaf, BTree.leaf]))`.

This combines cycle 547's singleton-leaf machinery (`Fin 2` inner cut /
keep choice) with cycle 553's double-leaf machinery (`Fin 3` inner choice
via `doubleLeafChoiceCoef`).

## Approach
Followed the strategy's Step 1 → Step 5 plan, with the tighter four-level
expansion:
- root powerset `S_sl ⊆ Fin a` (which singleton-leaves are cut at the
  root)
- root powerset `S_dl ⊆ Fin b` (which double-leaves are cut at the root)
- inner powerset `T ⊆ S_slᶜ` (per kept singleton-leaf, the `Fin 2`
  cut/keep)
- inner choice `χ : Fin (b - S_dl.card) → Fin 3` (per kept double-leaf,
  the `Fin 3` choice from cycle 553)

The cut-form summand tree shape is
```
BTree.node
  (List.replicate (T.card + cnt0 χ) BTree.leaf
    ++ List.replicate ((S_slᶜ.card - T.card) + cnt1 χ) (BTree.node [BTree.leaf])
    ++ List.replicate (cnt2 χ) (BTree.node [BTree.leaf, BTree.leaf]))
```
which reuses the existing
`bSeries_node_replicate_leaf_append_replicate_singleton_leaf_append_replicate_double_leaf`
lemma directly.

Manual closure only — no Aristotle scaffolds were submitted, matching the
strategy's instruction to skip the 429 pattern.

## Result
SUCCESS.

Landed in `OpenMath/ButcherGroup/Section384Slices.lean`:
- `convAt_node_mixed_singleton_leaf_double_leaf_at_i_eq`
- `mixed_singleton_leaf_double_leaf_stage_polynomial_expand`
- `weighted_mixed_singleton_leaf_double_leaf_stage_sum_expand`
- `bWeighted_convAt_node_mixed_singleton_leaf_double_leaf_cut_eq`
- `ButcherProduct.bSeries_node_mixed_singleton_leaf_double_leaf_cut_eq`

Landed in `OpenMath/ButcherGroup.lean`:
- `QuotEquiv.bSeriesHom_product_node_mixed_singleton_leaf_double_leaf`
  (Quotient.inductionOn₂ lift)
- `IsG1Equiv.product_congr_node_mixed_singleton_leaf_double_leaf`
  (hypothesis `(BTree.node ...).order ≤ p`, which unfolds to
   `1 + 2*a + 3*b ≤ p` via the existing
   `order_node_replicate_singleton_leaf_append_replicate_double_leaf`).

`lake build` is green; no live `sorry`s in `OpenMath/`.

## Dead ends
First attempt at the calc step that combines the per-stage closed form
with `bWeighted_kept_double_leaf_summand_eq` used `congr 1; · show … rfl`
on each of the two power factors. The first `congr 1` only splits the
outer `t₂.b i * (… * …)`, leaving the entire `_^a * _^b` as one goal, so
the per-factor `show … rfl` failed with a type-mismatch against the full
power product.  Switched to cycle 552's pattern: prove `hsl` and `hdl`
inner equalities up front and `rw [hsl, hdl]` to find both patterns
inside the product.

A separate parser error at the end of the third calc step's RHS came
from miscounted close parens — the four-level nesting (S_sl, S_dl, T, χ)
plus the explicit summand `BTree.node` closure needed five close parens,
not four.

## Discovery
The order arithmetic for this family is `1 + 2*a + 3*b`, since
`BTree.node [BTree.leaf]` has order 2 and `BTree.node [BTree.leaf,
BTree.leaf]` has order 3.  The summand tree's order bound
`1 + (T.card + cnt0) + 2*((S_slᶜ.card - T.card) + cnt1) + 3*cnt2`
collapses against `cnt0 + cnt1 + cnt2 ≤ b` and `T.card ≤ S_slᶜ.card ≤ a`
to `≤ 1 + 2*a + 3*b`, so a single `omega` after
`doubleLeafChoiceCount_sum` closes the G1 ordering hypothesis.

Both the singleton-leaf-power and double-leaf-power factors at the root
need `by_cases hzero` on the cardinality being zero before invoking the
G1 equivalence — when the cardinality is zero, the factor is `1` and we
need not bound the inner subtree's order, but otherwise we can use the
existing trees' fixed orders (2 and 3 respectively, which are bounded by
`p` whenever the corresponding cardinality is positive and `1 + 2*a +
3*b ≤ p`).

## Suggested next approach
Continue with another mixed §384 slice for the next root family on the
strategy queue.  Reasonable candidates:
- `(node [leaf, leaf], node [leaf, leaf, leaf])` — pair the cycle 553
  Fin 3 expansion with a Fin 4 expansion.
- `(node [leaf], node [leaf], leaf)` triples — extend the cycle 547
  singleton-leaf machinery to a longer keep-side.

Either reuses today's four-level expansion pattern; the new ingredient
is the `Fin k` choice helper for the larger keep-side.
