# Cycle 542 Results

## Worked on

§38 / §384 — first parametric (all-orders) `G1.mul`-direction
well-definedness deliverable. Followed the cycle 542 strategy directly:

- Step 1 landed: `ButcherProduct.bConv_node_replicate_leaf_eq` in
  `OpenMath/ButcherGroup/Section384.lean`.
- Step 2 landed: `ButcherProduct.bSeries_node_replicate_leaf_eq` in
  the same file.
- Step 3 landed: `QuotEquiv.bSeriesHom_product_node_replicate_leaf`
  in `OpenMath/ButcherGroup.lean`.
- Step 4 landed: `IsG1Equiv.product_congr_node_replicate_leaf` in
  the same file (with a small private helper
  `order_node_replicate_leaf` for
  `(BTree.node (List.replicate n BTree.leaf)).order = n + 1`).

## Approach

### Steps 1 and 2: bConv / bSeries closed form on the all-leaves family

`ButcherProduct.bConv_node_replicate_leaf_eq` unfolds `bConv` and applies
the cycle 538 lemma
`ButcherProduct.bWeighted_convAt_node_all_leaves_eq` to the children
list `List.replicate n BTree.leaf`. The cycle 538 result indexes its
powerset sum over `Fin children.length`, while the headline statement
indexes over `Fin n`. Bridging the two required transporting the sum
across the type isomorphism `Fin (List.replicate n leaf).length ≃ Fin n`
induced by `List.length_replicate`. After trying several routes
(`rfl`, `simp only [List.length_replicate]`, `subst`, an inline
`Fin.castIso` — which does not exist in this mathlib snapshot), the
clean approach was to build the equiv manually with `Fin.cast hlen` /
`Fin.cast hlen.symm`, lift it via `Equiv.finsetCongr` to a powerset
equivalence, and apply `Finset.sum_equiv`. The card-and-power closure
inside the per-summand goal is `Finset.prod_const`, then a final
`simp only [List.length_replicate]` to collapse the residual
`(replicate n leaf).length - S.card` to `n - S.card`.

`ButcherProduct.bSeries_node_replicate_leaf_eq` is a one-line
`bSeries_eq_bConv` rewrite on top of Step 1, mirroring the cycle 540
`bSeries_singleton_leaf_eq` shape exactly.

Strategy convention answer: the powerset is indexed by
`Finset.univ : Finset (Fin n)` on the headline RHS. The cycle 538
lemma indexes by `Finset.univ : Finset (Fin children.length)`, which
becomes `Finset.univ : Finset (Fin (List.replicate n leaf).length)`
once `children := List.replicate n BTree.leaf` is plugged in. The
length-`n` rewrite uses `List.length_replicate`, and the actual
type-level transport is via the manually-built equiv described above.

### Step 3: quotient lift

`QuotEquiv.bSeriesHom_product_node_replicate_leaf` is the standard
`Quotient.inductionOn₂ + simpa` lift, mirroring cycle 540 / 541:

```lean
  refine Quotient.inductionOn₂ q r ?_
  intro t₁ t₂
  simpa [bSeriesHom, bSeries, product, ButcherTableau.bSeries] using
    ButcherProduct.bSeries_node_replicate_leaf_eq t₁ t₂ n
```

Required a `lake build OpenMath.ButcherGroup.Section384` between
adding Steps 1/2 and Step 3 so the umbrella file's LSP could see the
new constants.

### Step 4: IsG1Equiv corollary

`IsG1Equiv.product_congr_node_replicate_leaf`. After rewriting both
sides via Step 3, the goal splits into:
- the head term `q.bSeriesHom (node (replicate n leaf))`, closed by
  `hq` and the `n + 1 ≤ p` hypothesis using
  `order_node_replicate_leaf`;
- the powerset-sum term, closed pointwise: each summand pairs a
  `q.bSeriesHom leaf` factor (handled by `hq` at order 1 ≤ p) with
  an `r.bSeriesHom (node (replicate (n - S.card) leaf))` factor
  (handled by `hr` at order `(n - S.card) + 1 ≤ n + 1 ≤ p`).

Subset-card bound `S.card ≤ n` extracted via `Finset.mem_powerset` +
`Finset.card_le_card`.

## Result

SUCCESS — all four planned theorems landed with no live `sorry`.

Verification:
- `lake env lean OpenMath/ButcherGroup/Section384.lean` — clean.
- `lake build OpenMath.ButcherGroup.Section384` — clean.
- `lake env lean OpenMath/ButcherGroup.lean` — clean.
- `lake build OpenMath.ButcherGroup` — clean
  (`Build completed successfully (8031 jobs)`).
- `grep -n "sorry" OpenMath/ButcherGroup.lean OpenMath/ButcherGroup/Section384.lean`
  — empty output, no new sorries.

## Dead ends

- `Fin.castIso` does not exist in this mathlib snapshot (only
  `finCongr` appears, and only as a private/locally-namespaced
  helper; no public top-level definition). Resolved by manually
  building the `Equiv` from `Fin.cast` / `Fin.cast .symm`.
- `simp only [List.length_replicate]` after the cycle 538 rewrite
  does not propagate into the implicit `Fintype` instance attached
  to `Finset.univ : Finset (Fin (replicate n leaf).length)`; this is
  what blocked the naive one-liner. Resolved by the manual
  `Equiv.finsetCongr` + `Finset.sum_equiv` route.
- An initial `subst hlen` attempt failed because `subst` substitutes
  the local var `n` in the wrong direction (it would rewrite `n` to
  `(replicate n leaf).length`, producing a non-terminating loop on
  the inner `replicate n` occurrences).
- A `rw [List.length_replicate]` deep in the per-summand goal hits a
  motive-typing failure inside `BTree.node (List.replicate (...) leaf)`
  because of how `replicate` and `length` interact with congruence.
  `simp only [List.length_replicate]` succeeds where `rw` fails.

## Discovery

- The `Finset.sum_equiv` + `Equiv.finsetCongr` pattern is the right
  bridge between two `Finset.powerset (Finset.univ : Finset (Fin _))`
  sums when the two `Fin _` cardinalities are propositionally equal
  but not definitionally so. Worth keeping in mind for future
  parametric `Fin n.length`-vs-`Fin n` situations in the §384 chain.
- `(BTree.node (List.replicate n BTree.leaf)).order = n + 1` is a
  three-line induction on `n` using `List.replicate_succ` plus
  `BTree.order_node` / `List.foldr` reduction. No `BTree.order_node_*`
  helper currently exists in `OpenMath/RootedTree.lean`, so it is
  inlined locally as a `private theorem` in `OpenMath/ButcherGroup.lean`
  (the strategy explicitly forbids touching `RootedTree.lean` this
  cycle).

## Aristotle outcome

Did not submit any jobs this cycle. The cycle 542 strategy explicitly
allowed at most one quick batch; given that Step 1 was a 12-line
proof, Step 2 a one-line corollary, Step 3 a `Quotient.inductionOn₂ +
simpa` follow-on, and Step 4 a powerset-pointwise rewrite, an
Aristotle batch would have been wasted compute. Aristotle has been
returning HTTP 429 / QUEUED on this seam for many cycles; saving the
budget seemed strictly better than burning it on trivial follow-ons.

## Suggested next approach

Per the strategy's "after this cycle" note: the next §384 milestone
is the kept-children mixed branch. Cycle 539 already landed the
depth-1 case-split (`bWeighted_convAt_node_kept_eq`); the next
structural lift is to package the kept-side into a recursive
bSeries-only auxiliary so the `(trunk, cuts)` decomposition closes
for arbitrary trees. That is the final blocker on unrestricted
`IsG1Equiv.product_congr`.

A natural intermediate could also be a closed form on the family
`BTree.node (BTree.node (List.replicate m leaf) :: List.replicate k leaf)`
(one kept-node child plus `k` leaf children) using the cycle 540
`bWeighted_kept_node_all_leaves_summand_eq` helper. That would
extend the all-leaves family to the next mixed shape without
attempting the full `(trunk, cuts)` closure.
