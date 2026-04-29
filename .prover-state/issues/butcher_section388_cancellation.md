# Issue: §388 cancellation peeling lemma blocked on canonical-cut count

## Blocker

The peeling lemma

```lean
theorem bSeriesConv_eq_root_plus_nonRoot
    (α β : BTree → ℝ) (τ : BTree) :
    bSeriesConv α β τ
      = β τ + bSeriesConvNonRoot α τ (fun σ _ => β σ)
```

(Step 1 of cycle 576) reduces, via the strengthened structural lemma
`innerCut_root_only_at_full_order`, to a purely combinatorial counting
claim:

```lean
((τ.innerCut α).countP (· = ((some τ, (1 : ℝ)) : Option BTree × ℝ))) = 1
```

and the parallel forest claim

```lean
((BTree.innerCutForest children α).countP
    (· = children.map (fun c => ((some c, (1 : ℝ)) : Option BTree × ℝ)))) = 1
```

The strengthened invariant only gives the disjunction "cs is
sum-decreasing OR cs = canon_cs children" (existence of the canonical
plus a structural classification). It does **not** by itself rule out
the canonical cs occurring more than once in `BTree.innerCutForest
children α`.

## Context

Cycle 576 landed:

- `OpenMath/ButcherGroup/Section386Conv.lean`:
  - `canon_filterMap`, `canon_foldr`, `canon_order_sum` helpers.
  - `innerCut_root_only_at_full_order` strengthened to identify the
    canonical no-cut as `cs = children.map (fun c => (some c, 1))` at
    the forest level (rather than the weaker
    `cs.filterMap c.1 = children ∧ cs.foldr ... = 1`).
- `OpenMath/ButcherGroup.lean`:
  - `QuotEquiv.inverseCoeff_node_eq` (Step 2).
  - `bSeriesConv_inverseCoeff_cancel_leaf` (Step 4).

Steps 1 and 3 are blocked. Step 3 (`bSeriesConv_inverseCoeff_cancel_node`)
needs the peeling lemma to rewrite `bSeriesConv q.bSeries q.inverseCoeff
(node children)` as `q.inverseCoeff (node children) + ...`, which
combined with Step 2 gives the cancellation.

The leaf checksum (Step 4) does not require `q.IsUnit` because
`bSeriesConv α β leaf = β leaf` and `q.inverseCoeff leaf = 1` make the
identity unconditional. The current `bSeriesConv_inverseCoeff_cancel_leaf`
is therefore stated without the `hq` hypothesis.

## What was tried

Five proof outlines for the count = 1 claim were sketched in cycle 576;
all required mutual recursion between tree and forest count claims.
Nothing was committed because each path expands to a non-trivial Lean
proof (~50–100 lines per direction):

1. **`List.countP` mutual induction** with `DecidableEq (Option BTree
   × ℝ)` from `Classical` and `DecidableEq BTree` (already noncomputable
   via `Classical.decEq` in `OpenMath.RootedTree`). At the forest cons
   step, push `countP` through `List.flatMap` and `List.map` using
   `List.countP_flatMap`, `List.countP_map`, and the tree IH "(some
   head, 1) appears exactly once in head.innerCut α".

2. **Direct `List.filter = [canon]` mutual induction**: state the
   stronger
   ```lean
   (BTree.innerCutForest children α).filter
       (· = children.map (fun c => (some c, (1 : ℝ)))) =
     [children.map (fun c => (some c, (1 : ℝ)))]
   ```
   and the leaf-level dual. Same `List.filter_flatMap` /
   `List.filter_map` chain.

3. **Forest-level peeling identity** parametric in `B : List BTree → ℝ`,
   bypassing count by a single direct induction on `children`. The cons
   case still ends up case-splitting on `c ∈ head.innerCut α` and uses
   the tree-level structural disjunction; the canonical-`c` branch
   absorbs a `B (head :: tail)` term that requires the IH on `tail` with
   the shifted functional `B'(L) := B (head :: L)`.

4. **`List.mem_iff_append` split** at `canon_cs children`: write
   `innerCutForest children α = pre ++ canon_cs :: post`, then sum.
   Doesn't avoid the count since `pre`/`post` may also contain
   `canon_cs`.

5. **`Finset.sum` reindexing**: convert lists to `Finset (Fin n)` sums
   and use `Finset.sum_eq_single` at the canonical position. Same
   underlying count requirement.

## Possible solutions

Path (1) is the most direct and likely the one the next cycle should
land. Concrete sketch:

```lean
mutual
  private theorem innerCut_canon_count
      (α : BTree → ℝ) (τ : BTree) :
      ((τ.innerCut α).countP
        (· = ((some τ, (1 : ℝ)) : Option BTree × ℝ))) = 1
  private theorem innerCutForest_canon_count
      (α : BTree → ℝ) (children : List BTree) :
      ((BTree.innerCutForest children α).countP
        (· = children.map (fun c => ((some c, (1 : ℝ)) : Option BTree × ℝ)))) = 1
end
```

For the tree leaf case, both entries are explicit. For tree node, drop
the `(none, _)` head and reduce to the forest count via the
`innerCut_root_only_at_full_order` characterization. For the forest
nil case, the singleton list trivially has count 1. For the forest cons
case, reduce
```
countP innerCutForest (head :: tail) α (· = (some head, 1) :: canon_cs tail)
  = countP head.innerCut α (· = (some head, 1))
    * countP innerCutForest tail α (· = canon_cs tail)
  = 1 * 1
```
using `List.countP_flatMap` and `List.countP_map`.

Once both counts are 1, the peeling lemma follows from a list-level
identity
```
(L.map f).sum = (L.countP (· = canon)) * f canon
                + (L.filter (· ≠ canon)).map f .sum
```
combined with the strengthened invariant that every `cs ≠ canon` is
sum-decreasing (so `g cs = f cs` and the second sum equals the
proper-cut helper sum).

Step 3 then follows from Step 1 + Step 2 by `linarith`:
```
bSeriesConv q.bSeries q.inverseCoeff (node children)
  = q.inverseCoeff (node children)
    + bSeriesConvNonRoot q.bSeries (node children) (fun σ _ => q.inverseCoeff σ)
```
adding `q.bSeries (node children)` to both sides and applying
`inverseCoeff_node_eq` collapses to `0`.
