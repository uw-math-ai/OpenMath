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

No honest convolution definition was added in cycle 503. The candidate
direct definition via `QuotEquiv.product` was rejected because it would
hide, rather than formalize, the tree-indexed product.

Cycle 504 landed the §386 list-split infrastructure (option 2 above), and
the placeholder symbol that the cycle-505+ body will fill in:

- `ButcherGroup.foldr_mul_add_eq_prod` — converts the elementary-weight
  `List.foldr (fun a acc => acc * (x a + y a)) 1` into
  `(xs.map (fun a => x a + y a)).prod`.
- `ButcherGroup.foldr_mul_add_eq_sum_powerset` — list-flavoured
  `Finset.prod_add`: rewrites the same fold into a sum over subsets of
  `Fin xs.length` selecting which positions take the `x`-summand vs
  `y`-summand.
- `ButcherGroup.prod_add_finset_indexed` — direct `Finset.prod_add` for
  the `Fin n`-indexed (no `List`) case.
- `butcherProduct_A_natAdd_castAdd` and `butcherProduct_A_natAdd_natAdd`
  — simp lemmas for the second-block row of the lower-left and
  lower-right blocks of `(ButcherProduct t₁ t₂).A`.
- `ButcherProduct.innerSum_natAdd_split` — at a second-block stage
  `Fin.natAdd s i`, the inner sum `∑ k : Fin (s+t), A · k * EW · k`
  decomposes into a first-block `∑ k₁, t₁.b k₁ * EW (Fin.castAdd t k₁)`
  plus a second-block `∑ k₂, t₂.A i k₂ * EW (Fin.natAdd s k₂)`.
- `ButcherProduct.elementaryWeight_node_natAdd` — the §386 node-case
  unfolding: at a second-block stage and a `BTree.node τs`, the
  elementary weight is exactly `τs.foldr (fun child acc => acc *
  (x child + y child)) 1` with `x` the first-block contribution and
  `y` the second-block contribution.
- `QuotEquiv.bSeriesConv` — the §386 recursive product placeholder
  symbol (sole tracked `sorry`). Cycle 505+ will give it a body via
  `BTree.rec` using
  `ButcherGroup.foldr_mul_add_eq_sum_powerset` at the `node` case and
  the additive split at `leaf`.

## Possible solutions

1. Define the product recursively over `BTree` using cycle 504's
   list-split lemma. For `leaf`, both `x` and `y` reduce to constants
   (the singleton sums, since `elementaryWeight .leaf k = 1`); the
   coefficient should be defined to handle that base case. For
   `node children`, the body is exactly
   `ButcherGroup.foldr_mul_add_eq_sum_powerset` applied to the two
   per-child contributions, with the recursion landing inside the
   `x` summand on each child.

2. (DONE — cycle 504) List-level infrastructure: the lemma turning
   `children.foldr (fun child acc => acc * (x child + y child)) 1` into
   a finite sum over subsets of children-positions
   (`ButcherGroup.foldr_mul_add_eq_sum_powerset`) is now landed. The
   §386 node-case unfolding `ButcherProduct.elementaryWeight_node_natAdd`
   makes its application to the actual elementary-weight recursion
   immediate.

3. Alternatively, introduce a Connes-Kreimer-style coproduct on rooted
   trees and prove it matches the current `List.foldr` elementary-weight
   recursion. This is more canonical for Butcher's group, but is a
   larger build-out than the local list-split expansion that cycle 504
   already landed.
