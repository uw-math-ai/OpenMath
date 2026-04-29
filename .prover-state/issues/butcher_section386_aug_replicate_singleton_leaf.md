# Issue: parametric `bSeriesConvAug` closed form on `replicate n (BTree.node [BTree.leaf])`

## Blocker

The §386 unital associativity headline for the entire `BTree` lattice
needs a parametric closed form for

```lean
bSeriesConvAug α β (BTree.node (List.replicate n (BTree.node [BTree.leaf])))
```

analogous to `bSeriesConvAug_node_replicate_leaf` (cycle 586) and
`bSeriesConvAug_node_replicate_node_nil` (cycle 588).  Cycle 587 showed
the naive replicate-subtree form (a single `Finset (Fin n)` powerset
with `α(τ)^|S|`) is **false** because each order-≥2 child
`τ = BTree.node [BTree.leaf]` carries its own partial-trunk inner cut.

## Context

Each child position `i ∈ Fin n` independently picks one of three
choices on the child shape `X = BTree.node [BTree.leaf]`:

- **A**: fully cut at the child root.  Option `none`, weight
  `α.toFun X`.  Removes the child from the trunk.
- **B**: partial-trunk cut keeping the root and pruning the inner leaf.
  Option `some (BTree.node [])`, weight `α.toFun BTree.leaf`.
- **C**: fully kept.  Option `some X`, weight `1`.  Trunk child is `X`.

These are the three entries of `BTree.innerCut X` (modulo a `none`
header that aggregates with the top-level prune).

## Pinned closed form (parametric)

Encode the per-child choice as a disjoint pair
`(S₁, S₂) : Finset (Fin n) × Finset (Fin n)` with `S₁ ∩ S₂ = ∅`,
where `S₁ = {i : choice = A}` and `S₂ = {i : choice = B}` (so the
remaining `n − |S₁| − |S₂|` positions are choice C).

Then

```
bSeriesConvAug α β (node (replicate n X))
  = α.toFun (node (replicate n X)) * β.emptyVal
    + Σ_{(S₁, S₂) disjoint in Fin n}
        α.toFun X ^ |S₁|
          * α.toFun BTree.leaf ^ |S₂|
          * β.toFun (node (trunk_children S₁ S₂))
```

where `trunk_children S₁ S₂` is the list of length `n − |S₁|`
obtained by walking positions `0, 1, …, n−1` in order, dropping the
positions in `S₁`, and emitting `BTree.node []` for positions in `S₂`
or `X` for positions in neither.  **Order matters** — `BTree.node`
takes a `List BTree`, not a `Multiset BTree`, so two configurations
that differ only by which positions hold `B` vs `C` produce different
trunks (e.g. cycle 590's
`BTree.node [BTree.node [BTree.leaf], BTree.node []]` vs
`BTree.node [BTree.node [], BTree.node [BTree.leaf]]`).

The cycle 590 closed form `bSeriesConvAug_two_singleton_leaves`
matches this with `n = 2`: the four `(S₁, S₂)` configurations
`(∅, ∅)`, `(∅, {0})`, `(∅, {1})`, `(∅, {0,1})` produce
`β(node [X, X])`, `β(node [node [], X])`, `β(node [X, node []])`,
`β(node [node [], node []])` respectively, with the asymmetric
`B`-position contributions explicit.

## What was tried

- Cycle 587 attempted the false symmetric-replicate closed form with
  a single `Finset (Fin n)` power and was reverted in cycle 587b after
  a counterexample was constructed at `n = 1` (the sole partial-trunk
  branch is missed).
- Cycle 588 closed the order-1 case `node []` (only two per-child
  options, A and C, no partial-trunk B branch).
- Cycle 589 closed the `n = 1` case `node [X]`
  (`bSeriesConvAug_singleton_singleton_leaf`), which already shows the
  three-branch structure.
- Cycle 590 closed the `n = 2` case
  (`bSeriesConvAug_two_singleton_leaves`) plus three asymmetric inner
  trunks needed for the depth-3 associativity check.

## Possible solutions

A list-level combinator on `BTree.innerCutForest` that mirrors
`innerCutForest_replicate_leaf_sum` and
`innerCutForest_replicate_node_nil_sum_aux` but takes the *three-way*
per-child choice and emits a sum over disjoint
`(S₁, S₂) : Finset (Fin n) × Finset (Fin n)`.

The cleanest API is probably a function

```lean
def threeChoice (n : ℕ) : Finset (Finset (Fin n) × Finset (Fin n)) :=
  Finset.univ.filter (fun p => p.1 ∩ p.2 = ∅)
```

and a `List.recOn`-driven lemma showing

```
(BTree.innerCutForest (List.replicate n X) α).map weight_and_trunk
  = (threeChoice n).image (fun (S₁, S₂) => contribution S₁ S₂)
```

after which the sum reindexing is purely combinatorial.  The order
preservation of trunk children — the part the symmetric powerset form
fails to capture — falls out from `replicate`'s positional encoding
because `List.replicate n X` has a canonical positional ordering.

The downstream associativity proof would then mirror cycle 586 / 588:
combine the parametric closed form with a binomial-style identity on
`(α(X) + β.something)^|S₁|` summed against the `(βγ)` closed form on
the trunk.  The tricky part is that the binomial identity must be
disjoint-pair (cf. `replicate_leaf_assoc_aux` in cycle 586) and the
trunk function on the inner side has the asymmetric `B`-position
trees baked in, so the inner expansion is not a pure powerset sum
over `Fin (n - |S₁| - |S₂|)` — it depends on which positions are
B vs C.

## Suggested next cycle

A planning cycle to design the combinator API before any Lean
sorry-first scaffold lands.  The associativity headline for this
shape requires both:

1. The parametric closed form above (one new theorem).
2. A disjoint-pair binomial identity bridging
   `(α(X) + β.something)^|S₁| · (α(leaf) + β.something_else)^|S₂|`
   to the right-associated double sum.

Step 2 is genuinely new combinatorics — it is not a direct rewrite of
`replicate_leaf_assoc_aux`.
