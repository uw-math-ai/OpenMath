# Cycle 512 Results

## Worked on

§384 tree-coefficient convolution seam in `OpenMath/ButcherGroup.lean` per
the cycle 512 strategy:
- `bSeriesConv : (BTree → ℝ) → (BTree → ℝ) → BTree → ℝ`
- `QuotEquiv.bSeriesHom_product_leaf`
- `QuotEquiv.bSeriesHom_product_node_nil` (bonus, not in the strategy)
- `QuotEquiv.bSeriesHom_product` (leaf branch closed in-line, node branch sorry)

## Approach

1. Surveyed the existing `ButcherProduct` / `bSeries_one_left` /
   `butcherProduct_b_sum` infrastructure plus the bSeriesHom/bSeries lifting
   conventions.
2. Inserted the §384 scaffold immediately below the existing
   `QuotEquiv.bSeriesHom_assoc` block and above the §387 power section, per
   the strategy's location instruction.
3. Defined `bSeriesConv` with a concrete leaf branch
   (`β₁ .leaf + β₂ .leaf`) and a `sorry` node branch.
4. Proved `bSeriesHom_product_leaf` via `Quotient.inductionOn₂` and
   `butcherProduct_b_sum` once `simp` was redirected to `bSeriesConv_leaf`
   (using `bSeriesConv` directly in the simp set propagates the body sorry
   into the proof term).
5. Added bonus lemma `bSeriesHom_product_node_nil`: same proof shape, since
   `elementaryWeight (.node []) i = 1` (empty `foldr`).
6. Restructured the headline `bSeriesHom_product` so the leaf branch is
   closed in-line via `bSeriesHom_product_leaf`; only the genuine node
   branch is left as a `sorry`.
7. Tried to submit one Aristotle scaffold (`foldr_prod_finset.lean`); 429
   on first attempt, so per strategy did not retry the batch.
8. Updated `.prover-state/issues/butcher_section384_convolution.md` with a
   detailed §384 cycle-512 note recording the structural obstruction in
   the node case and a candidate convolution body for the next worker.

## Result

SUCCESS — partial:
- `bSeriesConv` definition landed with the leaf branch concrete.
- `bSeriesHom_product_leaf` closed.
- `bSeriesHom_product_node_nil` closed (bonus).
- `bSeriesHom_product` reduced from a global sorry to a single node-branch
  sorry; the leaf branch now uses the closed leaf lemma in-line.
- Final live sorries in `OpenMath/ButcherGroup.lean`: 2
  (`bSeriesConv` node body, `bSeriesHom_product` node case). Both are the
  load-bearing combinatorial step explicitly identified by the strategy.
- Full `lake build` is clean.

## Dead ends

- Aristotle: HTTP 429 on first submit, matching cycles 504/509/511. Did not
  retry per strategy.
- `bSeriesConv` in the simp set propagates the node-body sorry into proof
  terms: had to use the dedicated `bSeriesConv_leaf` simp lemma instead.

## Discovery

For tableaux `t₁`, `t₂` and the product tableau `T = t₁ ⊗ t₂`:
- The *top-block* contribution to
  `∑ i, T.b i * T.elementaryWeight τ i` is exactly `q₁.bSeriesHom τ`,
  because the top-right A block is zero and the top-left A and b blocks are
  `t₁.A`, `t₁.b`. This depends only on `q₁`.
- The *bottom-block* contribution involves an auxiliary
  `Ψ(τ, k) = Φ_prod(τ, natAdd s k)` satisfying
  `Ψ(.node ts, k) = ∏ child ∈ ts, (q₁.bSeriesHom child + ∑ j, t₂.A k j * Ψ(child, j))`,
  which depends on `t₂`'s tableau structure (not just on `q₂.bSeriesHom`).

  This means the §384 convolution `bSeriesConv β₁ β₂` cannot just iterate
  `β₂` tree-recursively on top of `β₁ child + β₂ child` per child — the
  inner recursion goes *back into* the bottom block via `t₂.A`, and the
  closed form is the admissible-cut sum on rooted trees.

A candidate concrete recursion that the next planner cycle should verify
against `.node []` and `.node [τ]`:

```lean
| .node ts =>
    ts.foldr
      (fun child acc => acc * (β₁ child + bSeriesConv β₁ β₂ child)) 1
      + (β₂ (.node ts) - 1)
```

The `-1` correction encodes the unit/empty-forest convention for `β₂`. Not
yet verified — recorded in the issue file for the next cycle.

## Suggested next approach

Two paths the planner could take:

1. **Verify and land the candidate body above.** Compute both sides on
   `.node []`, `.node [.leaf]`, and `.node [.node [.leaf]]` using
   `butcherProduct_b_sum` and `elementaryWeight_singleton` and confirm the
   formula reproduces the bottom-block recursion. If yes, replace the sorry
   in `bSeriesConv` and prove `bSeriesHom_product` by `BTree.rec` with a
   `motive_2` that mirrors cycle 510's `padRight_elementaryWeight_castAdd`
   structure.

2. **Side-step §384 for one cycle** by attacking a parallel identity
   instead — e.g. a one-cycle `QuotEquiv.bSeriesHom_npow` corollary at the
   leaf tree only, which would compose with the existing power chain.

Path 1 is the right way; path 2 is a fallback if path 1 stalls again.
The main risk in path 1 is the `+ (β₂ τ - 1)` correction not aligning with
the actual bottom-block sum on multi-child nodes; this is exactly the
combinatorial check that needs to happen on paper before scaffolding.

## Files changed

- `OpenMath/ButcherGroup.lean`: added §384 seam (~50 lines).
- `.prover-state/issues/butcher_section384_convolution.md`: cycle-512 update.
- `.prover-state/aristotle_scaffolds/cycle_512/`: three scratch scaffolds
  (one submitted to Aristotle, 429'd; two unused).
