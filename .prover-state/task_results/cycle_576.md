# Cycle 576 Results

## Worked on

Butcher §388 inverse-coefficient cancellation, four ordered steps:

1. **Step 1** — peeling lemma `bSeriesConv_eq_root_plus_nonRoot` in
   `OpenMath/ButcherGroup/Section386Conv.lean`. Optional structural
   helper `innerCut_root_only_at_full_order`.
2. **Step 2** — `QuotEquiv.inverseCoeff_node_eq` in
   `OpenMath/ButcherGroup.lean`.
3. **Step 3** — `bSeriesConv_inverseCoeff_cancel_node` in
   `OpenMath/ButcherGroup.lean`.
4. **Step 4** — `bSeriesConv_inverseCoeff_cancel_leaf` (leaf checksum).

## Approach

- Strengthened the structural lemma. The cycle-575 invariant was
  `(cs.filterMap c.1 = children) ∧ (cs.foldr ... = 1)` at the canonical
  no-cut. Cycle 576 promotes this to the explicit identification
  `cs = children.map (fun c => (some c, 1))`. To do so I introduced
  three pure-list helpers `canon_filterMap`, `canon_foldr`,
  `canon_order_sum`, then ran a single `BTree.rec` with
  `motive_2 := fun children => ∀ cs ∈ BTree.innerCutForest children α,
   (sum-decreasing) ∨ cs = canon`. The forest cons step splits on
  `c.1 = none` versus `c.1 = some t` versus `c = (some head, 1)` and
  uses the IH on `tail` to pick the canonical branch.
- Step 2 reduces to one `rw [inverseCoeff]` followed by `ring`.
- Step 4 drops the `(hq : q.IsUnit)` hypothesis: at the leaf
  `bSeriesConv α β leaf = β leaf` and `q.inverseCoeff leaf = 1`
  unconditionally, so the leaf checksum is `1` for every `q`.
- For Step 1, I attempted five proof outlines (`List.countP` mutual
  induction, `List.filter = [canon]` mutual induction, forest-level
  parametric peeling, `List.mem_iff_append`, `Finset.sum` reindexing).
  All require a fresh mutual induction proving the canonical entry
  appears exactly once in `BTree.innerCutForest`. None landed inside
  the cycle budget.
- Aristotle: a focused scaffold
  `.prover-state/aristotle_scaffolds/cycle_576/peel_sum.lean` was
  prepared and submitted. The submission returned HTTP 429
  (rate-limited). Per strategy I did not retry.

## Result

PARTIAL SUCCESS.

- LANDED:
  - `Section386Conv.lean` helpers `canon_filterMap`, `canon_foldr`,
    `canon_order_sum`.
  - Strengthened `innerCut_root_only_at_full_order` (forest-level
    canonical identification).
  - `QuotEquiv.inverseCoeff_node_eq` (Step 2).
  - `bSeriesConv_inverseCoeff_cancel_leaf` (Step 4, no `hq`).
- BLOCKED:
  - Step 1 peeling lemma (canonical-cut `countP = 1`).
  - Step 3 cancellation (depends on Step 1).
- Build: `lake env lean OpenMath/ButcherGroup.lean` exits 0;
  `lake env lean OpenMath/ButcherGroup/Section386Conv.lean` exits 0.
- Sizes: `ButcherGroup.lean` = 2944 lines, `Section386Conv.lean` =
  1158 lines (both under the 3000-line cap).
- Issue file `.prover-state/issues/butcher_section388_cancellation.md`
  records the precise blocker and a concrete next-cycle plan.

## Dead ends

- `simp only [List.mem_cons, List.mem_singleton]` followed by
  `rw [hc]` failed: the membership disjunction did not reduce far
  enough. Switched to a full `simp at hc` to expose the equality.
- `Option.noConfusion hopt` errored on the `none = some t` direction
  inside the structural lemma; replaced with `cases hnone` after
  rewriting.
- `Option.some.inj` direction mismatch: needed `.symm` to flip
  `some t' = some t` before applying.
- `omega` failed against an unreduced `match c.1 with` pattern;
  pushed `simp only [List.filterMap_cons, hopt, ...]` first.
- Inlining the `canon_filterMap`-type identities inside the structural
  lemma's branch left `(fun c => c.1) ∘ (fun c => (some c, 1))`
  unsolved subgoals — pulled them out as standalone helpers.
- All five proof outlines for Step 1 required a fresh mutual induction
  proving the canonical forest entry occurs exactly once. The shortest
  (`List.countP` mutual) is ~50–100 lines per direction; not landable
  inside this cycle while keeping the structural lemma stable.

## Discovery

- The cycle-575 invariant (`filterMap = children` ∧ `foldr = 1`) is
  *strictly weaker* than what the peeling lemma needs: those
  conditions identify the canonical *trunk*, not the canonical *cut
  list*. Promoting the disjunct to `cs = children.map (fun c => (some
  c, 1))` is the right strengthening and lands cleanly via mutual
  `BTree.rec` with `motive_2` over forests.
- Step 4's `q.IsUnit` hypothesis is unnecessary: leaf cancellation
  holds for *every* `QuotEquiv s`, regardless of augmentation, because
  `bSeriesConv α β leaf = β leaf` and `inverseCoeff leaf = 1` are
  unconditional. The strategy's `hq` parameter is dead weight at the
  leaf.
- The proper-cut helper `bSeriesConvNonRoot α τ β`, with `β` requiring
  `σ.order < τ.order`, makes the proper-trunk contribution definable
  at the leaf as `(BTree.leaf.innerCut α).filterMap ... = []`. This
  avoids any `<` proof obligation at the leaf and lets Step 4 close by
  pure rewrite.

## Suggested next approach

Cycle 577 should land the `List.countP` mutual induction outlined in
`butcher_section388_cancellation.md` (Path 1):

```lean
mutual
  private theorem innerCut_canon_count
      (α : BTree → ℝ) (τ : BTree) :
      ((τ.innerCut α).countP (· = ((some τ, (1 : ℝ)))) = 1
  private theorem innerCutForest_canon_count
      (α : BTree → ℝ) (children : List BTree) :
      ((BTree.innerCutForest children α).countP
        (· = children.map (fun c => ((some c, (1 : ℝ)))))) = 1
end
```

Then conclude Step 1 with the list-level identity

```
(L.map f).sum
  = (L.countP (· = canon)) * f canon
    + (L.filter (· ≠ canon)).map f .sum
```

and the strengthened structural disjunction (every `cs ≠ canon` is
sum-decreasing). Step 3 then follows from Step 1 + Step 2 by `linarith`
after `inverseCoeff_node_eq`.

After §388 is closed, the strategy already noted `inverseCoeff_bSeries_cancel`
(symmetric direction) and `G1.inv` definition as the §389 entry points.
