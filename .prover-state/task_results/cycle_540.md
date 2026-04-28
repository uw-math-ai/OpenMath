# Cycle 540 Results

## Worked on

§38 / §384 — first fully bSeries-only product closed form on a concrete
tree. Followed the cycle 540 strategy directly:

- Step 1 (primary, landed): `ButcherProduct.bConv_singleton_leaf_eq` and
  the headline corollary `ButcherProduct.bSeries_singleton_leaf_eq` in
  `OpenMath/ButcherGroup/Section384.lean`.
- Step 2 (secondary, landed): `QuotEquiv.bSeriesHom_product_singleton_leaf`
  in `OpenMath/ButcherGroup.lean`.
- Step 3 (stretch, deferred): `IsG1Equiv.product_congr_le_two` —
  documented in "Result" below why this is genuinely blocked by missing
  ergonomic helpers.

## Approach

### Step 1: bSeries-only closed form on `BTree.node [BTree.leaf]`

Wrote two new theorems at the bottom of `Section384.lean` (after the
existing depth-2 cycle 538/539 chain):

```lean
theorem ButcherProduct.bConv_singleton_leaf_eq
    {s t : ℕ} (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    ButcherProduct.bConv (t₁.bSeries) t₂ (BTree.node [BTree.leaf])
      = t₁.bSeries (BTree.node [BTree.leaf])
        + t₂.bSeries (BTree.node [BTree.leaf])
        + t₂.weightsSum * t₁.bSeries BTree.leaf
```

Proof: unfold `bConv` to `t₁.bSeries τ + ∑ i, b i * convAt …`, apply
`bWeighted_convAt_singleton_node_eq` with `c := BTree.leaf` to split off
the `weightsSum`-scaled cut term, apply `bWeighted_convAt_kept_leaf_eq`
to collapse the remaining inner term to `t₂.bSeries (node [leaf])`,
then close with `ring`.

The headline corollary `bSeries_singleton_leaf_eq` follows immediately
from `bSeries_eq_bConv` and `bConv_singleton_leaf_eq`.

Note on the strategy theorem statement: the strategy text omitted the
leading `t₁.bSeries (node [leaf])` summand from the `bConv` LHS form.
This is because `bConv φ t₂ τ = φ τ + ∑ …` includes the `φ τ` term;
the strategy step 1 unfolding "to `∑ i, b_i * convAt …`" elided that
term. The corrected statement above includes it; the headline
corollary `bSeries_singleton_leaf_eq` matches the strategy verbatim
once `bSeries_eq_bConv` is applied.

### Step 2: lift to the quotient layer

In `OpenMath/ButcherGroup.lean`, immediately after `bSeriesHom_assoc`,
inside `namespace ButcherTableau ; namespace QuotEquiv`:

```lean
theorem bSeriesHom_product_singleton_leaf
    {s t : ℕ} (q₁ : QuotEquiv s) (q₂ : QuotEquiv t) :
    (q₁.product q₂).bSeriesHom (BTree.node [BTree.leaf])
      = q₁.bSeriesHom (BTree.node [BTree.leaf])
        + q₂.bSeriesHom (BTree.node [BTree.leaf])
        + q₂.weightsSum * q₁.bSeriesHom BTree.leaf
```

Proof: `Quotient.inductionOn₂` on `q₁`, `q₂`, then `simpa` with
`bSeriesHom`, `bSeries`, `product`, `weightsSum`, `ButcherTableau.bSeries`,
`ButcherTableau.weightsSum` against the cycle 540 representative-level
result.

## Result

**SUCCESS** — steps 1 and 2 both landed and compile cleanly. No live
sorry's; full module build succeeds.

`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build
OpenMath.ButcherGroup` returned `Build completed successfully (8031
jobs)` after the new theorems were added.

Step 3 (`IsG1Equiv.product_congr_le_two`) deliberately deferred. The
hold-up is a real BTree-order-≤-2 enumeration gap, not a missing
algebraic step:

- `IsG1Equiv 2` requires the bSeries-map agreement on **every**
  `τ : BTree` with `τ.order ≤ 2`. The set of such τ is **not** just
  `{leaf, node [leaf]}`. Specifically, `(node []).order = 1` and
  `(node [node []]).order = 2`, so `{leaf, node [], node [leaf],
  node [node []]}` are all order ≤ 2.
- The cycle 540 closed form covers `node [leaf]`. We do **not** yet
  have closed forms for `(t₁.product t₂).bSeries (node [])` or
  `(t₁.product t₂).bSeries (node [node []])`. (Both collapse via
  `elementaryWeight (node []) i = 1` and an `elementaryWeight_singleton`
  application, but neither is a one-line corollary of an existing
  lemma in the §384 chain.)
- A clean version of step 3 needs a `BTree.order_le_two_iff`
  characterization plus collapse lemmas for the two extra trees.
  Per the strategy ("If step 3 turns out to need additional
  `BTree.order` enumeration helpers … leave step 3 for the next
  cycle"), I stopped at steps 1-2.

## Dead ends

None this cycle. The proof recipe in the strategy was clean and the
`ring` close on step 1 worked on the first try; step 2 needed
`ButcherTableau.bSeries` / `ButcherTableau.weightsSum` added to the
`simpa` lemma set so the representative-level identity unfolded into the
`bSeriesHom_mk` / `weightsSum_mk` shapes, but otherwise no detours.

## Discovery

- The `bConv` closed form on `node [leaf]` was a one-`ring` finish from
  the cycle 538 building blocks. The cycle 525-539 ladder genuinely was
  load-bearing for this cycle's deliverable, even though several
  intermediate cycles scored 0 — the ladder collapsed into a real
  bSeries-only result on its first concrete consumer.
- `BTree.order ≤ 2` admits four trees, not two: the `node []` and
  `node [node []]` trees both have `order = 1` and `order = 2`
  respectively. This is the missing infrastructure that blocks
  `IsG1Equiv.product_congr_le_two` from being a one-cycle drop-in
  follow-up; the next planner cycle should schedule a small
  `BTree.order_le_two` enumeration helper plus the `node []` and
  `node [node []]` `bSeries` collapse lemmas before retrying step 3.

## Aristotle outcome

Did not submit any jobs this cycle. The strategy permitted up to 5
jobs but step 1 was a 4-line proof that the cycle 538 building blocks
already discharged, and step 2 was a `Quotient.inductionOn₂ + simpa`
follow-on, so an Aristotle batch would have been wasted compute.
Aristotle has been returning HTTP 429 / QUEUED on this seam for many
cycles in a row, per the planner status note; saving the budget seemed
strictly better than burning it on trivial follow-ons.

## Suggested next approach

Concrete seam for the next planner cycle:

1. Add `BTree.order_le_two_iff` (or an explicit enumeration lemma) to
   `OpenMath/RootedTree.lean`: `τ.order ≤ 2 ↔ τ ∈ {leaf, node [],
   node [leaf], node [node []]}` (or the more useful disjunction
   form).
2. Add tableau-level `bSeries` collapse lemmas for the two extra
   trees:
   - `ButcherTableau.bSeries_node_nil : t.bSeries (BTree.node []) =
     t.weightsSum`
   - `ButcherTableau.bSeries_node_node_nil : t.bSeries
     (BTree.node [BTree.node []]) = t.bSeries (BTree.node [BTree.leaf])`
     (since `elementaryWeight (node []) k = 1 = elementaryWeight leaf k`).
3. Add the matching `(t₁.product t₂).bSeries` collapse lemmas (each
   should be an immediate consequence of `bSeries_eq_split` plus the
   tableau-level collapses).
4. Then `IsG1Equiv.product_congr_le_two` becomes a four-case split on
   the enumeration: each case discharges by either the existing
   `weightsSum` law, the cycle 540 closed form, or one of the two new
   collapse lemmas.

Total expected size: ~80 lines, no Aristotle dependency, and the
result is the **first** piece of `G1.mul`'s well-definedness in
tracked code (the headline §38 deliverable beyond closed forms).
