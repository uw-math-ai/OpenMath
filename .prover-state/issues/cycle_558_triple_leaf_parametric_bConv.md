# Issue: bConv_node_replicate_triple_leaf_eq remains a sorry

## Blocker

`ButcherProduct.bConv_node_replicate_triple_leaf_eq` in
`OpenMath/ButcherGroup/Section384SlicesTripleLeaf.lean` is a sorry. All
downstream cycle-558 deliverables (`bSeries_node_replicate_triple_leaf_eq`,
`bSeriesHom_product_node_replicate_triple_leaf`,
`product_congr_node_replicate_triple_leaf`) are otherwise fully proved
modulo this inner sorry.

## Context

The statement asserts the §384 honest convolution closed form for the
all-triple-leaf parametric family. Mathematically:

```
bConv (t₁.bSeries) t₂ (node (replicate n (node [leaf, leaf, leaf])))
  = t₁.bSeries (node (replicate n (node [leaf, leaf, leaf])))
    + ∑ S ∈ powerset(Fin n),
        (t₁.bSeries (node [leaf, leaf, leaf])) ^ S.card *
          (∑ χ : Fin (n - S.card) → Fin 4,
            tripleLeafChoiceProductCoef X χ *
              t₂.bSeries (tripleLeafChoiceTree χ))
```

where `X = t₁.bSeries leaf`, `tripleLeafChoiceFiber χ k` counts kept root
children with cut count `k`, and the aggregate `tripleLeafChoiceTree`
groups the four fibers as
`replicate f0 (node [leaf,leaf,leaf]) ++ replicate f1 (node [leaf,leaf]) ++
 replicate f2 (node [leaf]) ++ replicate f3 leaf`.

## What was tried

- Submitted to Aristotle (project `61b2eb7c-0cca-4df3-9dd0-6f8338b39754`)
  with directives pointing at the cycle-547 singleton-leaf template. As of
  cycle 558 commit, project status was still QUEUED.

## Possible solutions

The proof should mirror cycle 547's auxiliary chain:

1. `bWeighted_convAt_node_replicate_triple_leaf_eq_length`: kept-side
   decomposition over a `Fin (replicate n).length` powerset (≡ Fin n).
2. Auxiliary expansion lemma analogous to
   `bWeighted_kept_singleton_leaf_product_eq`:

   For each kept root child `node [leaf, leaf, leaf]`, the per-stage factor
   is `c_0 f_0(i) + c_1 f_1(i) + c_2 f_2(i) + c_3 f_3(i)` where
   `c_k = tripleLeafChoiceCoef k X 1` and
   `f_k(i) = el-wt t₂ (node[node(replicate (3-k) leaf)]) i`.

   Use `Finset.prod_univ_sum` (or `Finset.prod_add` iterated) to expand
   the product over `Sᶜ` of these 4-term sums into a sum over choice
   functions `χ : Sᶜ → Fin 4`.

   Group the resulting product `∏_p f_(χ p)(i)` by χ-fiber to obtain
   `el-wt t₂ (tripleLeafChoiceTree χ) i` (modulo a fiber-card permutation).

3. `bConv_node_replicate_triple_leaf_eq` then follows from `unfold
   ButcherProduct.bConv` plus the helper.

The fiber-grouping step is the structurally novel ingredient over
cycle-547 (which only has 2 fibers via T ⊆ Sᶜ); for triple-leaf the 4
fibers require something like:
- `Fintype.prod_equiv` between `Sᶜ` and the disjoint union of fibers;
- or `Finset.prod_filter` decomposed across the four `Fin 4` filter
  conditions.

## Notes

The structurally analogous mixed leaf/double-leaf cycle 553 used a
similar `Fin 3` per-kept-child fiber (`doubleLeafChoiceCoef`,
`doubleLeafChoiceTree`). Its proof in `Section384SlicesMixed.lean` is a
better template than cycle 547's binary version; specifically
`bWeighted_convAt_node_mixed_leaf_double_leaf_cut_eq` and its supporting
chain.
