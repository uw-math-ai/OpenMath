# Issue: Butcher Section386 General Consistency

## Blocker
The general theorem

```lean
theorem ButcherProduct.bSeriesConv_consistency
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) (τ : BTree) :
    (ButcherProduct t₁ t₂).bSeries τ
      = t₁.bSeries τ + bSeriesConv (t₁.bSeries) (t₂.bSeries) τ
```

does not reduce cleanly by tree induction directly on `bSeriesConv`.
After rewriting with `ButcherProduct.bSeries_eq_split`, the missing
identity is

```lean
bSeriesConv α (t₂.bSeries) τ
  = ∑ i : Fin t, t₂.b i * ButcherProduct.convAt t₂ α τ i
```

but the node case needs a stagewise version before summing over `t₂.b`.

## Context
`bSeriesConv` evaluates each root-preserving inner cut by multiplying its
cut weight against `t₂.bSeries trunk`. This expands to a stage sum
`∑ i, t₂.b i * t₂.elementaryWeight trunk i`. The `convAt` recursion,
however, needs the child-level inner-cut sum at each stage `j` inside

```lean
∑ j : Fin t, t₂.A i j * ButcherProduct.convAt t₂ α child j
```

So the required invariant is not just a `bSeries`-weighted cut sum. It
should first prove a stagewise root-preserving cut lemma, roughly:

```lean
def cutAt (α : BTree → ℝ) (t₂ : ButcherTableau t) (τ : BTree) (i : Fin t) :=
  ((τ.innerCut α).filterMap fun c =>
    c.1.map (fun trunk => c.2 * t₂.elementaryWeight trunk i)).sum

theorem cutAt_eq_convAt
    (α : BTree → ℝ) (t₂ : ButcherTableau t) (τ : BTree) (i : Fin t) :
    cutAt α t₂ τ i = ButcherProduct.convAt t₂ α τ i
```

The node step for `cutAt_eq_convAt` needs a prefix/list invariant for
`BTree.innerCutForest children α`:

```lean
(List.map
  (fun cs =>
    cs.foldr (fun c acc => c.2 * acc) 1 *
      t₂.elementaryWeight
        (BTree.node (cs.filterMap fun c => c.1)) i)
  (BTree.innerCutForest children α)).sum
= ∑ S : Finset (Fin children.length),
    (∏ p ∈ S, α (children.get p)) *
      ∏ p ∈ Sᶜ,
        (∑ j : Fin t, t₂.A i j *
          ButcherProduct.convAt t₂ α (children.get p) j)
```

with per-child induction hypotheses replacing the stagewise cut sums by
`convAt`.

## What was tried
- Added the sorry-first headline theorem after steps 1 and 2 compiled.
- Submitted `Section386Conv.lean` to Aristotle with the single remaining
  general theorem sorry. Project `acf8c051-c67d-43e4-b735-e0571dd2773a`
  was still `QUEUED` after the required 30-minute wait, so no proof was
  available to incorporate.
- Manually rewrote the goal using `ButcherProduct.bSeries_eq_split`.
  This exposes the identity above but does not provide enough recursive
  structure for the child terms, because `bSeriesConv` has already
  summed over stages.

## Possible solutions
1. Add a local `cutAt` definition in `Section386Conv.lean`.
2. Prove `cutAt_leaf` and `cutAt_node_nil` by unfolding.
3. Prove the list-level forest invariant by induction on `children`.
   This is the general version of the cycle 568 and cycle 569
   replicate-family reindexing: each head contributes either the root-cut
   term `α head` or the kept-root term transported through
   `∑ j, A i j * cutAt α t₂ head j`.
4. Use the per-child induction hypotheses to rewrite kept-root terms to
   `convAt`.
5. Derive
   `bSeriesConv α (t₂.bSeries) τ =
    ∑ i, t₂.b i * ButcherProduct.convAt t₂ α τ i`
   by unfolding `t₂.bSeries` and exchanging the finite list sum with the
   finite stage sum.
6. Finish `ButcherProduct.bSeriesConv_consistency` with
   `ButcherProduct.bSeries_eq_split`.
