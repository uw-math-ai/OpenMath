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

## Cycle 512 update

The §384 seam now exists in `OpenMath/ButcherGroup.lean`:

```lean
noncomputable def bSeriesConv (β₁ β₂ : BTree → ℝ) : BTree → ℝ
  | .leaf => β₁ .leaf + β₂ .leaf
  | .node _ => sorry

theorem QuotEquiv.bSeriesHom_product_leaf : closed
theorem QuotEquiv.bSeriesHom_product_node_nil : closed
theorem QuotEquiv.bSeriesHom_product : leaf branch closed; node branch sorry
```

`bSeriesHom_product_node_nil` was added because for `.node []` the elementary
weight reduces to `1` exactly as for `.leaf`, so the same `butcherProduct_b_sum`
identity closes that case without needing the convolution recursion.

### What blocks the node branch

Define for tableaux `t₁ : ButcherTableau s`, `t₂ : ButcherTableau t`:
- `Φ_prod(τ, castAdd t i₁) = t₁.elementaryWeight τ i₁` (zero upper-right A).
  This makes the *top-block* contribution `∑ i₁, t₁.b i₁ * Φ_prod(τ, castAdd t i₁)`
  reduce to `q₁.bSeriesHom τ` independently of `τ`.
- `Φ_prod(τ, natAdd s i₂)` satisfies a recursive equation:
  ```
  Φ_prod(.leaf, natAdd s i₂) = 1
  Φ_prod(.node ts, natAdd s i₂) =
    ∏ child ∈ ts, ( q₁.bSeriesHom child + ∑ k, t₂.A i₂ k * Φ_prod(child, natAdd s k) )
  ```
  This is *not* `t₂.elementaryWeight` — it has an extra `q₁.bSeriesHom child`
  inside the inner sum.

The convolution `bSeriesConv β₁ β₂` would need to be defined so that the
*bottom-block* contribution `∑ i₂, t₂.b i₂ * Φ_prod(τ, natAdd s i₂)` is a
function of `(β₁, β₂)` alone, not of the full tableau `t₂`.

Concretely the dependence on the full `t₂` (not just `β₂ = q₂.bSeriesHom`)
appears intrinsic — the recursion above iterates `t₂.A` and only contracts
with `t₂.b` at the outermost step. The standard route is to introduce a
**rooted-forest** coefficient extension and a **cut sum** so that the
convolution becomes a sum over admissible cuts of `τ`:
`(β₁ ⋆ β₂)(τ) = ∑ cuts c : β₂(R_c τ) * ∏ component ∈ P_c τ : β₁(component)`
where `P_c τ` is the pruned forest above the cut and `R_c τ` is the trunk
containing the root.

For `.leaf` this gives `β₂(.leaf)·1 + 1·β₁(.leaf)` = `β₁(.leaf) + β₂(.leaf)`. ✓
For `.node []` the cuts are: full pruning gives `β₂(.leaf as trunk) · 1` =
`β₂(.node [])` and no pruning gives `β₁(.node [])`. But the cut analysis on
forests with no children needs the convention that the empty forest product
is `1` and corresponds to `β₂` evaluating on the root. (The §384
`bSeriesHom_product_node_nil` confirms this is consistent.)

### What this still needs

A concrete tree-recursive definition of `bSeriesConv` matching this
admissible-cut sum, *without* introducing a separate forest type. One
candidate:

```lean
noncomputable def bSeriesConv (β₁ β₂ : BTree → ℝ) : BTree → ℝ
  | .leaf => β₁ .leaf + β₂ .leaf
  | .node ts =>
      ts.foldr
        (fun child acc => acc * (β₁ child + bSeriesConv β₁ β₂ child)) 1
        + (β₂ (.node ts) - 1)
```

This must be carefully checked against `node []` (where the foldr is `1` and
the `β₂(.node []) - 1` correction recovers `β₁ leaf + β₂ leaf` modulo the
convention that `β` at the empty forest equals `1`). The `(β₂ … - 1)` shift
encodes the additive contribution of the trunk. Verification is open.

The simpler list-split lemma `foldr_mul_add_split` (sum over child labellings)
is *not* sufficient on its own because the recursive bottom-block
`Φ_prod(child, natAdd s k)` is not just `β₂(child)`.

## Status

- Cycle 503: §384 identified, no convolution defined.
- Cycle 504 (reverted): list-split lemmas added too early.
- Cycle 512: `bSeriesConv` skeleton landed with leaf branch concrete and
  node branch as a sorry; `bSeriesHom_product_leaf` and
  `bSeriesHom_product_node_nil` closed; `bSeriesHom_product` leaf branch
  closed in-line, node branch left as a single sorry. Definition of the
  convolution body in the node case remains the open math problem.
