# Issue: §386 replicate-subtree closed form needs partial-trunk cuts

## Blocker

The planned closed form

```lean
bSeriesConvAug α β (BTree.node (List.replicate n τ))
  = α.toFun (BTree.node (List.replicate n τ)) * β.emptyVal
    + ∑ S : Finset (Fin n),
        α.toFun τ ^ S.card *
          β.toFun (BTree.node (List.replicate (n - S.card) τ))
```

is false for arbitrary `τ`.  It is valid for `τ = BTree.leaf` and for
other two-branch children such as `BTree.node []`, but a general subtree has
inner cuts whose trunk is a proper subtree of `τ`.  Those partial-trunk
branches survive in the root-preserving `innerCutForest` sum and are not
represented by the powerset over fully cut child positions.

## Context

For `τ = BTree.node [BTree.leaf]`, `BTree.innerCut τ α` has a partial branch
with trunk `BTree.node []` and weight `α BTree.leaf`.  In
`BTree.node [τ]`, this contributes the term

```lean
α.toFun BTree.leaf * β.toFun (BTree.node [BTree.node []])
```

in addition to the naive "keep `τ`" and "cut `τ`" terms.

The scratch file
`.prover-state/aristotle_scaffolds/cycle_587/closed_form_counterexample.lean`
checks this in Lean:

```lean
private noncomputable def alphaCounter : AugSeries :=
  ⟨1, fun τ => match τ with | BTree.leaf => 1 | _ => 0⟩

private noncomputable def betaCounter : AugSeries :=
  ⟨1, fun τ => match τ with | BTree.node [BTree.node []] => 1 | _ => 0⟩

private theorem actual_counterexample_value :
    bSeriesConvAug alphaCounter betaCounter
        (BTree.node [BTree.node [BTree.leaf]]) = 1 := by
  simp [bSeriesConvAug, BTree.innerCut, BTree.innerCutForest,
    alphaCounter, betaCounter]

private theorem naive_counterexample_rhs :
    alphaCounter.toFun (BTree.node [BTree.node [BTree.leaf]])
        * betaCounter.emptyVal
      + ∑ S : Finset (Fin 1), alphaCounter.toFun (BTree.node [BTree.leaf]) ^ S.card
          * betaCounter.toFun
              (BTree.node (List.replicate (1 - S.card) (BTree.node [BTree.leaf])))
      = 0 := by
  ...
```

So the naive RHS is `0` while the actual convolution value is `1`.

## What was tried

- Added the cycle 587 sorry-first API scaffold in
  `OpenMath/ButcherGroup/Section386Aug.lean`.
- Submitted the naive closed-form payload to Aristotle as project
  `4449050d-0ce6-4a92-8a2f-9bae4930ecfb`; it was still `QUEUED` after the
  required 30-minute wait.
- The other four Aristotle payloads returned HTTP 429 immediately.
- Compiled a Lean counterexample showing the naive closed-form statement
  cannot be closed as stated.

## Possible solutions

1. Replace the naive powerset closed form with a nested reindexing over each
   child position's full `BTree.innerCut τ α`, not just the two choices
   `some τ` and `none`.
2. Prove the arbitrary-children scaffold directly by a convolution-of-cuts
   associativity lemma: first decompose the outer root-preserving
   `innerCutForest children`, then compose child cuts without collapsing them
   to `α τ` powers.
3. As an intermediate step, prove a restricted predicate for two-branch
   children (`innerCut τ α = [(none, α τ), (some τ, 1)]` up to order) and use
   it to recover the binomial proof for `τ = BTree.node []` before tackling
   arbitrary `τ`.
