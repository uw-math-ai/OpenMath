# Issue: `convAt` unit alone does not imply §384 kept-side `bSeries` unit

## Blocker

The planned cycle 545 theorem `bWeighted_convAt_node_all_unit_eq` used only

`∀ j, ButcherProduct.convAt t₂ coef c j = 1`

for each child `c`, but its RHS packages kept children into
`t₂.bSeries (BTree.node kept)`. That conclusion also requires the kept
children to have elementary weight `1` under `t₂`.

## Context

`convAt` is defined from the §384 coefficient recursion and depends on
`coef`. `ButcherTableau.elementaryWeight` depends only on the tableau. These
are equal to `1` for the two intended trivial shapes, `BTree.leaf` and
`BTree.node []`, but they are not equivalent for arbitrary trees satisfying
`convAt = 1`.

## What was tried

The sorry-first scaffold for cycle 545 compiled, and Aristotle was attempted.
Aristotle returned HTTP 429 before creating a project. During manual closure,
the kept-side reduction reached the point where `convAt = 1` collapses the
rightAux/convAt trunk factor to a row sum, but the RHS `t₂.bSeries` still
needs `t₂.elementaryWeight child = 1`.

## Possible solutions

Use a stronger predicate for future all-trivial-children work:

`IsConvAtUnit t₂ coef c ∧ (∀ j, t₂.elementaryWeight c j = 1)`

or state the theorem with the concrete shape hypothesis

`∀ p, children.get p = BTree.leaf ∨ children.get p = BTree.node []`.

Either form matches the actual leaf/node-nil family and should support the
canonical kept-list reindexing in a later cycle.
