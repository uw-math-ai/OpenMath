# Issue: §386 augmented forest associativity cons step

## Blocker
Cycle 597 localized the generic unital associativity proof to one
forest-level invariant:

```lean
bSeriesConvAugForest α β cs
  + bSeriesConvAugForest ⟨1, fun σ => bSeriesConvAug α β σ⟩ γ cs
  = bSeriesConvAugForest α ⟨1, fun σ => bSeriesConvAug β γ σ⟩ cs
```

The `cs = []` case is closed.  The `c :: cs` case rewrites both sides with
`bSeriesConvAug_innerForest_cons`, but the tail IH only closes the
head-root-prune contribution.  The remaining keep-root contribution needs a
stronger peeled invariant on the transformed forest
`trunk :: forest.filterMap (fun e => e.1)`.

## Context
The live residual gap is in
`OpenMath/ButcherGroup/Section386Aug.lean`, theorem
`bSeriesConvAug_forest_assoc`, cons case:

```lean
| cons c cs ih =>
    unfold bSeriesConvAugForest
    rw [bSeriesConvAug_innerForest_cons, bSeriesConvAug_innerForest_cons,
      bSeriesConvAug_innerForest_cons]
    -- Residual cycle-597 gap.
    sorry
```

After the three cons rewrites, the proof state has the expected split:

- `α.toFun c * ...` tail terms, where `ih` applies after unfolding
  `bSeriesConvAugForest`;
- keep-root `flatMap` sums over `c.innerCut ...`, with terms containing
  `BTree.node (trunk :: forest.filterMap ...)`.

## What was tried
The direct list induction on `cs` was enough to close the nil case and to
expose the cons split, but not enough to close the keep-root terms.  The
plain tail IH is too weak because it knows only the tail forest `cs`, while
the residual terms require associativity after adding a trunk produced by
an inner cut of `c`.

## Possible solutions
Use the strong-induction fallback from the cycle strategy.  A suitable next
lemma should generalize the forest invariant so it can be applied to
`trunk :: forest.filterMap ...` after peeling the per-entry
`bSeriesConvAug_node` expansion.  Equivalently, prove a continuation-style
forest cut associativity lemma parameterized by the trunk context, then use
it to discharge the current `flatMap` residual.
