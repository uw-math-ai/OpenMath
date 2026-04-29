# Issue: Reindex `bSeriesConv` all-leaves list enumeration by powersets

## Blocker

Cycle 567 defined the coefficient-only admissible-cut enumeration
`BTree.innerCut` / `bSeriesConv` and proved the singleton-leaf
consistency check against cycle 540. The parametric all-leaves
consistency check reduces to a pure combinatorial reindexing lemma that
was not closed in-cycle:

```lean
(List.filterMap
    ((fun c => Option.map (fun t => c.2 * β t) c.1) ∘ fun cs =>
      (some (BTree.node (List.filterMap (fun c => c.1) cs)),
       List.foldr (fun c acc => c.2 * acc) 1 cs))
    (BTree.innerCutForest (List.replicate n BTree.leaf) α)).sum
  =
    ∑ S : Finset (Fin n),
      α BTree.leaf ^ S.card *
        β (BTree.node (List.replicate (n - S.card) BTree.leaf))
```

## Context

The landed definition uses direct mutual recursion:

- `BTree.innerCut τ α` returns `(Option BTree × ℝ)` choices, including
  `none` for pruning the current root.
- `BTree.innerCutForest children α` is the list-level cartesian product
  of one cut choice per child.
- `bSeriesConv α β τ` filters for root-preserving cuts and sums
  `weight * β trunk`.

For `BTree.node (List.replicate n BTree.leaf)`, each child contributes
exactly two choices:

- keep the leaf: `(some BTree.leaf, 1)`
- cut the leaf: `(none, α BTree.leaf)`

The list enumeration is therefore morally indexed by subsets of `Fin n`,
where the subset records cut leaves. The existing cycle 542 product
closed form is already indexed by `Finset (Fin n)`, so the missing proof
is only the bridge between these two enumerations.

## What was tried

After rewriting by `ButcherProduct.bSeries_node_replicate_leaf_eq`, the
goal simplified to the lemma displayed above. Direct induction on `n`
left the same bridge in the successor case. `simp` unfolds the base case
cleanly but does not synthesize the powerset reindexing; `grind` also
does not discover it.

The likely induction invariant needs a prefix parameter:

```lean
G m n =
  sum over cuts of n leaf children with m leaves already kept in the trunk
```

so that the successor step splits into a kept-head branch
`G (m + 1) n` and a cut-head branch `(α BTree.leaf) * G m n`.

## Possible solutions

1. Prove a dedicated list-to-powerset lemma for
   `BTree.innerCutForest (List.replicate n BTree.leaf) α`, probably with
   the prefix-generalized invariant above.

2. Use `Finset.sum_powerset_apply_card` to convert the powerset side to
   a binomial/cardinality sum, then prove the list enumeration satisfies
   the same Pascal recurrence.

3. Define an explicit equivalence between the child-choice list for
   `List.replicate n BTree.leaf` and `Finset (Fin n)`, and use it to
   reindex the `List.sum` into the existing cycle 542 powerset sum.
