# Cycle 547 Results

## Worked on

Butcher §38 / §384: the parametric all-singleton-leaf-children family
`BTree.node (List.replicate n (BTree.node [BTree.leaf]))`.

Added in `OpenMath/ButcherGroup/Section384.lean`:
- private helpers for `convAt (node [leaf])`, elementary weights of
  all-singleton-leaf nodes, and mixed leaf/singleton-leaf kept subtrees
- `ButcherProduct.bConv_node_replicate_singleton_leaf_eq`
- `ButcherProduct.bSeries_node_replicate_singleton_leaf_eq`

Added in `OpenMath/ButcherGroup.lean`:
- `QuotEquiv.bSeriesHom_product_node_replicate_singleton_leaf`
- private order helpers for `1 + 2 * n` and mixed `1 + a + 2 * b`
  leaf/singleton-leaf nodes
- `IsG1Equiv.product_congr_node_replicate_singleton_leaf`

Also appended the cycle 547 progress note to the §38 Current Target
section in `plan.md`.

## Approach

Used the cycle 539 kept-child `convAt` layer rather than the cycle 546
reduce-to-all-leaves transport. A kept child `BTree.node [BTree.leaf]`
has

`convAt t₂ coef (BTree.node [BTree.leaf]) i =
coef BTree.leaf + ∑ j, t₂.A i j`,

so each kept root child contributes an internal cut/keep choice. The
closed form therefore has:
- an outer powerset `S` over root children cut to `t₁.bSeries
  (BTree.node [BTree.leaf])`
- an inner powerset `T` over the kept root children whose singleton
  leaves are internally cut to `t₁.bSeries BTree.leaf`
- a kept-side `t₂.bSeries` summand on
  `BTree.node (List.replicate T.card BTree.leaf ++
  List.replicate ((Sᶜ).card - T.card) (BTree.node [BTree.leaf]))`

The quotient lift is the standard `Quotient.inductionOn₂ + simpa`.
The G1 slice follows the cycle 542 pattern, with an extra mixed-order
helper for the kept-side `t₂` summands.

## Result

SUCCESS. The parametric singleton-leaf-children closed form, quotient
lift, and fifth tracked `G1.mul`-direction slice all landed with no
tracked `sorry`.

Verification:
- `rg -n 'sorry' OpenMath/ButcherGroup OpenMath/ButcherGroup.lean` —
  empty output.
- `lake env lean OpenMath/ButcherGroup/Section384.lean` — clean.
- `lake env lean OpenMath/ButcherGroup.lean` — clean.
- `lake build OpenMath.ButcherGroup.Section384` — clean.
- `lake build OpenMath.ButcherGroup` — clean.

## Dead ends

The planner note suggested that the kept side might collapse directly to
`t₂.bSeries (BTree.node (List.replicate (n - |S|)
(BTree.node [BTree.leaf])))`. That omits the internal cut term
`t₁.bSeries BTree.leaf` in `convAt (node [leaf])`, so it is not the
right formula for unrestricted coefficients. The proof was adjusted to
the mathematically correct nested-powerset form instead of trying to
force the false direct collapse.

No Aristotle jobs were submitted and no 30-minute wait was used because
the cycle-specific strategy explicitly said to skip Aristotle unless a
novel obstruction appeared after at least one deliverable had landed.

## Discovery

The all-singleton-leaf family is the first parametric slice where the
root-level powerset is not enough: node children introduce another
powerset even in the simplest nontrivial child shape. This points toward
the eventual full `(trunk, cuts)` convolution: each kept node child must
carry its own internal cut set, and the resulting `t₂.bSeries` summand
is generally mixed rather than all one shape.

For `G1`, the edge case `n = 0` matters. The root order hypothesis
`1 + 2 * n ≤ p` does not imply order-2 agreement on
`BTree.node [BTree.leaf]` when there are no such children. The proof
therefore only invokes the order-2 hypothesis when the outer cut set has
positive cardinality; exponent-zero cut factors close by `simp`.

## Suggested next approach

Generalize the new nested-powerset slice to mixed root children made of
`BTree.leaf` and `BTree.node [BTree.leaf]`, or revisit the cycle 545
finite mixed-arity fallback with this internal-cut structure. This is a
more faithful next step toward the full §384 `(trunk, cuts)`
convolution than another elementary-weight transport theorem.
