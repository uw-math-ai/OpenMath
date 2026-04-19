# Issue: One-big-child factorization needs occurrence-level uniqueness

## Blocker
The intended `erase tb` proof for the final `gen_tree_cond` branch needs every child remaining after erasing `tb` to have order `≤ n`.

The available hypothesis is only:

```lean
htb_unique : ∀ ch ∈ children, n < ch.order → ch = tb
```

This gives uniqueness up to **tree equality**, not uniqueness as a **list occurrence**. If `children` contains two copies of the same subtree value `tb`, erasing one occurrence still leaves another child of order `> n`, so the planned `foldr_small_simplified` argument is not justified.

## Context
Current target: `OpenMath/Collocation.lean`, one-big-child branch of `gen_tree_cond`.

The planner strategy suggested:

1. factor `tb` out with `children.erase tb`
2. show all children in `children.erase tb` are small
3. simplify the small-child fold with `C(n)`

Step 2 is not derivable from the current hypotheses without an additional no-duplicate/occurrence-uniqueness fact.

## What was tried
- Introduced a structured local proof block and isolated the remaining branch as `hmain`.
- Attempted to formalize the `erase tb` factoring route directly.
- Checked both top-level helper theorems and local `have` proofs.
- Confirmed the file compiles with the structured placeholder, but the `erase` route stalls on the missing occurrence-level uniqueness fact.

## Possible solutions
- Strengthen the branch proof with an occurrence-level uniqueness lemma, e.g. prove that two positions with children of order `> n` force `node.order > 2n`.
- Replace `erase tb` with a split-by-membership argument and explicitly analyze whether another occurrence equal to `tb` can remain.
- Prove duplicates of a child with order `> n` are impossible from `hq'u : q' + node.order ≤ 2*n`; this would recover the intended `erase` strategy.
