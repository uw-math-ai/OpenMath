# Cycle 592 Results

## Worked on
Cycle 592 strategy: pivot from concrete `node (replicate n (node [leaf]))`
anchors (cycles 589/590/591) to a parametric combinator API in
`OpenMath/ButcherGroup/Section386Aug.lean`, plus n=1 / n=2 sanity
bridges to existing closed forms.

## Approach
Per strategy Steps 1–5:

1. Defined `threeChoice n : Finset (Finset (Fin n) × Finset (Fin n))`,
   the disjoint-pair index set for the three-way per-position cut.
2. Defined `trunkChildren n S₁ S₂ : List BTree`: walk positions
   `Fin n` in order via `List.finRange n`, drop `S₁` entries, emit
   `node []` for `S₂` entries and `node [leaf]` otherwise.
3. Defined `repSingletonLeafContrib α β n S₁ S₂ : ℝ` as the per-pair
   contribution `α(node[leaf])^|S₁| · α(leaf)^|S₂| · β(node trunk)`.
4. Added the parametric headline theorem
   `bSeriesConvAug_node_replicate_singleton_leaf` with a single
   `sorry`, marked `TODO cycle 593+`.
5. Added two sorry-free sanity bridges:
   - `bSeriesConvAug_node_replicate_singleton_leaf_one`: rewrites the
     parametric RHS at `n = 1` and matches the cycle-589 closed form
     `bSeriesConvAug_singleton_singleton_leaf`.
   - `bSeriesConvAug_node_replicate_singleton_leaf_two`: matches the
     cycle-590 closed form `bSeriesConvAug_two_singleton_leaves`.

For both sanity bridges, `decide` enumerates `threeChoice n` as an
explicit literal Finset (3 pairs for n=1, 9 pairs for n=2). The n=2
case then iterates `Finset.sum_insert (by decide)` to expand the sum
ahead of `simp` + `ring`.

## Result
SUCCESS.

- `OpenMath/ButcherGroup/Section386Aug.lean` builds cleanly with the
  single expected sorry warning at the parametric headline (line 786).
- `OpenMath/ButcherGroup.lean` umbrella builds.
- Three new private definitions and one new tracked sorry in the active
  §38 target file. Two sorry-free sanity bridges land alongside.

## Aristotle batch
Two scaffolds prepared under
`.prover-state/aristotle_scaffolds/cycle_592/`:

1. `bSeriesConvAug_node_replicate_singleton_leaf` — parametric headline.
2. `bSeriesConvAug_node_replicate_singleton_leaf_two` — n=2 bridge.

Both submission attempts returned HTTP 429 ("too many requests in
progress"). This matches the recurring 429 pattern noted in cycles
584/586/589/590/591. Per strategy, recorded and did not retry. The
Aristotle queue contained 15 active jobs at submission time, including
the cycle-591 three-singleton-leaves scaffold still QUEUED.

## Dead ends
- First attempt at the n=1 bridge tried `simp [threeChoice,
  Finset.sum_filter, Fin.sum_univ_succ, Finset.disjoint_iff_inter_eq_empty]`
  but `simp` did not enumerate the universe of `Finset (Fin 1) × Finset
  (Fin 1)` and left a `∑ x, if x.1 ∩ x.2 = ∅ then ... else 0`. Replaced
  with `decide` to compute `threeChoice n` as an explicit literal Finset.
- For n=2, the same `decide` approach left a 9-element literal sum that
  `simp` would not expand. Resolution: explicit `Finset.sum_insert (by
  decide)` chain followed by `Finset.sum_singleton`.

## Discovery
- `decide` reliably computes `threeChoice n` as a Finset literal up to
  n=2; this should keep working for moderate `n` (the universe is
  `4^n`) but will not scale to the parametric statement.
- `Finset.sum_insert (by decide)` with literal Finsets is a clean
  pattern for expanding small enumerated sums where `simp` does not
  fire automatically.
- The sum order produced by `decide` for `threeChoice n` follows the
  Fintype enumeration of `Finset (Fin n) × Finset (Fin n)` and is
  stable enough to hard-code in proofs.

## Suggested next approach (cycle 593)

**Goal**: prove the parametric headline
`bSeriesConvAug_node_replicate_singleton_leaf` by induction on `n`.

**Setup**:
1. Use `List.replicate_succ` to peel the head position. The recursion
   `BTree.innerCutForest (x :: xs) α =
     List.flatMap (fun c => (innerCutForest xs α).map (fun cs => c :: cs))
       (x.innerCut α)` is the load-bearing identity.
2. For the head child `BTree.node [BTree.leaf]`, the inner cut has
   three options, matching the three-way per-position split.
3. Need a combinatorial bijection
   `threeChoice (n + 1) ≃ Option (Fin 3) × threeChoice n` (or similar)
   that aligns the head-position choice with the `S₁`/`S₂` membership
   of position `0`.

**Likely supporting lemma**: a `cons`-style identity for `trunkChildren`,
something like

```lean
trunkChildren (n + 1) S₁.succ S₂.succ
  = (if 0 ∈ S₂ then BTree.node [] else BTree.node [BTree.leaf])
    :: trunkChildren n (S₁.preimage Fin.succ ...) ...
```

mediated by `Fin.cases` on position 0.

**Risk**: the `Fin.succ` index pushdown and the `Disjoint` preservation
under `Fin.preimage Fin.succ` are fiddly. If the direct induction
proves intractable, the fallback is `Finset.sum_bij` from
`threeChoice (n + 1)` to a `Sum`-shaped split based on which of the
three options position 0 takes.

**Cycle 594 follow-up** (after the parametric headline closes): lift to
`mul_assoc_at_node_replicate_singleton_leaf` for the entire family,
likely via the `replicate_leaf_assoc_aux` pattern generalized to
disjoint pairs (a binomial-style identity over `threeChoice`).

## Files changed
- `OpenMath/ButcherGroup/Section386Aug.lean` — added 87 lines
  (definitions + parametric headline + two sanity bridges).
- `.prover-state/aristotle_scaffolds/cycle_592/` — two scaffold dirs
  (not yet submitted due to 429).
- `.prover-state/task_results/cycle_592.md` — this file.
