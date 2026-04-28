# Issue: Butcher §384 tree-coefficient convolution remains to be defined

## Blocker

Cycle 503 landed the identity-prep side of the quotient-facing
Butcher-series map, but did not define the non-tautological product on
tree-indexed coefficients needed for the headline statement
`QuotEquiv.bSeriesHom_product`.

The problem is not proving equality once the operation exists; it is choosing
and formalizing the right recursive tree split operation. Defining
`bSeriesConvolution q₁ q₂ τ := (QuotEquiv.product q₁ q₂).bSeries τ` would
make the theorem trivial but would not express Butcher's §384 homomorphism.

## Context

The live code now has:

```lean
theorem ButcherProduct.bSeries_one_left
theorem ButcherProduct.bSeries_one_right
theorem QuotEquiv.product_bSeries_one_left
theorem QuotEquiv.product_bSeries_one_right
noncomputable def QuotEquiv.bSeriesHom
theorem QuotEquiv.bSeriesHom_one
theorem QuotEquiv.bSeriesHom_assoc
```

For the product tableau, the b-series coefficient splits over the two stage
blocks:

```lean
∑ i : Fin (s + t),
  (ButcherProduct t₁ t₂).b i *
    (ButcherProduct t₁ t₂).elementaryWeight τ i
```

The first block reduces to the `t₁` coefficient. The second block is
recursive: at a node, each child contribution in a second-method stage has a
lower-left term

```lean
∑ j : Fin s, t₁.b j * t₁.elementaryWeight child j
```

plus a lower-right term

```lean
∑ k : Fin t, t₂.A i k * Φ₂ child k
```

so the product coefficient expands over choices of which children have
already been completed by the first method and which children remain attached
to the second method.

## What was tried

Cycle 503 inspected the landed block lemmas
`butcherProduct_b_castAdd`, `butcherProduct_b_natAdd`, and the definition of
`ButcherProduct.A`. The raw one-sided identity proofs succeeded by reindexing
`Fin (0+t)` / `Fin (s+0)` through `finCongr` and applying
`elementaryWeight_eq_of_A`.

No honest convolution definition was added. The candidate direct definition
via `QuotEquiv.product` was rejected because it would hide, rather than
formalize, the tree-indexed product.

## Possible solutions

1. Define the product recursively over `BTree`. For `leaf`, the coefficient
   should be additive on the two non-empty-tree coefficient functions. For
   `node children`, expand the `List.foldr` product into a finite sum over
   choices of children assigned to the first-method coefficient versus the
   recursive second-method contribution.

2. Add list-level infrastructure first: a lemma turning
   `children.foldr (fun child acc => acc * (x child + y child)) 1` into a
   finite sum over subsets/subsequences of `children`. This would match the
   actual `elementaryWeight` definition and keep the proof local.

3. Alternatively, introduce a Connes-Kreimer-style coproduct on rooted trees
   and prove it matches the current `List.foldr` elementary-weight recursion.
   This is more canonical for Butcher's group, but is a larger build-out than
   the local list-split expansion.
